##  Copyright (c) 2018 Alberto Griggio <griggio@fbk.eu>
##
##  Modified and extended 2022 Cole Vick <cvick@utexas.cs.edu>
##  This is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This software is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this software.  If not, see <http://www.gnu.org/licenses/>.

from mathsat import (
    msat_term,
    msat_env,
    msat_make_and,
    msat_term_repr,
    msat_term_get_type,
    msat_declare_function,
    msat_make_constant,
    msat_make_true,
    msat_type,
    msat_apply_substitution,
    msat_to_smtlib2,
    msat_to_smtlib2_term,
    msat_to_smtlib2_ext,
    msat_assert_formula,
    msat_solve,
    msat_type_repr,
    msat_make_not,
    msat_create_env,
    msat_term_get_decl,
    msat_decl_get_name,
    msat_from_string,
    msat_annotated_list_to_smtlib2,
)
from mathsat import *
import copy
from z3 import Bool, Int, Solver, Const
from z3_defs import Arr
import re
from collections import defaultdict
from encoding_specifier import EncodingSpecifier

CHAR_OFFSET = 65


class VmtModel(object):
    def __init__(
        self,
        env,
        statevars: list[tuple[msat_term, msat_term]],  # cur[0] and next[1]
        init: msat_term,
        trans: msat_term,
        props: msat_term,
        spec: type,
    ):
        self.specifier: EncodingSpecifier = spec(env, statevars, trans, props)

        self.statevars = statevars
        self.nextvars: set[msat_term] = set(p[1] for p in statevars)
        self.curvars: set[msat_term] = set(p[0] for p in statevars)
        self.nextmap: dict[msat_term, msat_term] = dict(statevars)
        self.curmap: dict[msat_term, msat_term] = dict((n, c) for (c, n) in statevars)
        self.str_vars = [msat_term_repr(cv) for cv in self.curvars]

        self.imm_vars: list[msat_term] = self.specifier.get_imm_vars()
        self.env: msat_env = env
        self.init = self.abstract_constants(init)
        self.trans = self.herbrandize_imm_vars(trans)
        self.props = props

        self.prop_fails = self.specifier.prop_fails()
        self.prop_msat_expr = self.specifier.get_prop_expr()

        self.def_sexprs: list[str] = [
            "(declare-sort Arr 0)",
            "(declare-fun read_int_int (Arr Int) Int)",
            "(declare-fun write_int_int (Arr Int Int) Arr)",
        ]
        self.interp_sexprs: list[str] = [
            "(set-option :produce-proofs true)",
            "(set-option :interpolant-check-mode true)",
            "(set-logic QF_ALIA)",
        ]

        self.statevars_bmc: dict[msat_term, dict[int, msat_term]] = {
            v: defaultdict(lambda: defaultdict(list)) for v in self.curvars
        }
        self.bmc_var_str_to_statevar: dict[str, msat_term] = {}
        self.cur_N: int = 0
        self.msat_int_type = msat_get_integer_type(self.env)
        self.var_str_to_z3_def = None
        self.var_str_to_next_z3_def = None

    def refine(self, violation):
        sexpr = violation.axiom_instance.sexpr()
        msat_inst = msat_from_string(self.env, sexpr)
        sub: tuple[list[msat_term], list[msat_term]] = ([], [])
        max_frame = max(violation.frame_numbers)
        for var_str, val_str in violation.get_var_vals():
            sub[0].append(msat_from_string(self.env, var_str))
            if val_str == "cur":
                sub[1].append(self.bmc_var_str_to_statevar[var_str])
            elif val_str == "next":
                sub[1].append(self.nextmap[self.bmc_var_str_to_statevar[var_str]])
                pass
            else:
                hv, pv = violation.create_proph_and_hist(var_str)
                self.add_history_var(hv)
                self.add_prophecy_var(pv)
                sub[1].append(msat_from_string(self.env, pv.name))
        msat_inst = msat_apply_substitution(self.env, msat_inst, sub[0], sub[1])
        #print(f"AXIOM VIOLATION: {msat_term_repr(msat_inst)}")
        # self.init = msat_make_and(self.env, self.init, msat_inst)
        self.trans = msat_make_and(self.env, self.trans, msat_inst)

    def get_bmc_sexprs(self, N: int):
        self.cur_N = N
        decls, asserts = self._get_bmc_sexprs()
        ret = []
        for sexpr in asserts:
            ret.append(f"(assert {sexpr})")
        if self.var_str_to_z3_def is None:
            self.var_str_to_z3_def = self.get_all_vars_to_z3_def()
            self.var_str_to_next_z3_def = self.get_all_next_vars_to_z3_def()
        return [d for d in self.def_sexprs] + decls + ret

    def get_interp_sexprs(self):
        decls, asserts = self._get_bmc_sexprs()
        decls = [self.cleanup_interp_decls(d) for d in decls]
        ret = []
        names = []
        for i, sexpr in enumerate(asserts):
            interp_sexpr = self.cleanup_sexprs_for_interpolation(sexpr)
            name = chr(int(i) + CHAR_OFFSET)
            names.append(name)
            ret.append(f"(assert (! {interp_sexpr} :named {name}))")
        ret.append("(check-sat)")
        all_names = " ".join(names)
        ret.append(f"(get-interpolants {all_names})")
        return [d for d in self.interp_sexprs] + decls + ret

    def _get_bmc_sexprs(self) -> tuple[list[str], str]:
        decls = []
        sexprs = []
        for i in range(self.cur_N):
            cur_fm = self.get_formula_at_i(i, self.cur_N)
            for var, next_var in self.statevars:
                var_name: str = msat_term_repr(var)
                var_n: msat_term = self.get_var_at_n(i, var, var_name, decls)
                var_n_plus_one: msat_term = self.get_var_at_n(
                    i + 1, var, var_name, decls
                )
                cur_fm = msat_apply_substitution(
                    self.env, cur_fm, [var, next_var], [var_n, var_n_plus_one]
                )
            sexpr_term = self.cleanup_mathsat_repr(cur_fm)
            sexprs.append(sexpr_term)
        return decls, sexprs

    def get_prop_expr_sexpr(self, N=None) -> str:
        if not N:
            N = self.cur_N
        cur_fm = self.prop_msat_expr
        for var, next_var in self.statevars:
            var_name: str = msat_term_repr(var)
            var_n: msat_term = self.get_var_at_n(
                N - (self.prop_fails + 1), var, var_name, []
            )
            var_n_plus_one: msat_term = self.get_var_at_n(
                N - (self.prop_fails), var, var_name, []
            )
            cur_fm = msat_apply_substitution(
                self.env, cur_fm, [var, next_var], [var_n, var_n_plus_one]
            )
        return f"(assert {self.cleanup_mathsat_repr(cur_fm)})"

    def get_var_at_n(
        self, n: int, var: msat_term, var_name: str, decls: list[str]
    ) -> msat_term:
        var_type: msat_type = msat_term_get_type(var)
        type_string = self.get_type_str(msat_type_repr(var_type))
        var_n_str = f"{var_name}-{n}"
        declaration = f"(declare-fun {var_n_str} () {type_string})"
        if declaration not in decls:
            decls.append(declaration)
        if not self.statevars_bmc[var][n]:
            decl_n = msat_declare_function(self.env, f"{var_n_str}", var_type)
            const = msat_make_constant(self.env, decl_n)
            self.statevars_bmc[var][n] = const
            self.bmc_var_str_to_statevar[var_n_str] = var
            return const
        else:
            return self.statevars_bmc[var][n]

    def get_type_str(self, msat_type_str: str) -> str:
        if "Array" in msat_type_str:
            if "Int, Int" in msat_type_str:
                return "Arr"
            else:
                raise ValueError("Not implemented " + msat_type_str)
        return msat_type_str

    def get_formula_at_i(self, i, N):
        if i == 0:
            return msat_make_and(self.env, self.trans, self.init)
        elif i == N - 1:
            return msat_make_not(self.env, self.props)
        else:
            return self.trans

    def cleanup_mathsat_repr(self, mathsat_fm: msat_term) -> str:
        cur_repr = msat_term_repr(mathsat_fm)
        cur_repr = cur_repr.replace("`", "")
        cur_repr = cur_repr.replace("'", "")
        cur_repr = cur_repr.replace("=_int", "=")
        cur_repr = cur_repr.replace("+_int", "+")
        cur_repr = cur_repr.replace("*_int", "*")
        cur_repr = cur_repr.replace("=_Arr", "=")
        cur_repr = cur_repr.replace("ite_Arr", "ite")
        return cur_repr

    def cleanup_sexprs_for_interpolation(self, sexpr):
        sexpr = sexpr.replace("read_int_int", "select")
        sexpr = sexpr.replace("write_int_int", "store")
        # removes negations of the form (* var-name -1) because
        # smtinterpol does not do non-linear arithmetic
        sexpr = re.sub(r"[(][*][ ]([A-Za-z]*[-][0-9]+)[ ][-][1][)]", r"(- \1)", sexpr)
        sexpr = re.sub(r"[(][*][ ][-][1][ ]([A-Za-z]*[-][0-9]+)[)]", r"(- \1)", sexpr)
        # removes negative ones
        sexpr = re.sub(r"[ ][-][1]", r"(- 1)", sexpr)
        return sexpr

    def cleanup_interp_decls(self, sexpr):
        sexpr = sexpr.replace("Arr", "(Array Int Int)")
        return sexpr

    def add_prophecy_var(self, pv):
        msat_pv = msat_declare_function(
            self.env, pv.name, msat_get_integer_type(self.env)
        )  # only proph ints
        msat_npv = msat_declare_function(
            self.env, pv.next_name, msat_get_integer_type(self.env)
        )  # only proph ints
        tpv, ntpv = self.decl_to_term([msat_pv, msat_npv])
        self.add_state_var(tpv, ntpv)
        msat_pv_trans = msat_from_string(self.env, pv.get_trans_constraints_sexpr())
        self.trans = msat_make_and(self.env, self.trans, msat_pv_trans)
        self.props = msat_make_or(
            self.env,
            msat_make_not(
                self.env, msat_from_string(self.env, pv.get_prop_antecedent_sexpr())
            ),
            self.props,
        )

    def add_history_var(self, hv):
        msat_hv = msat_declare_function(
            self.env, hv.name, msat_get_integer_type(self.env)
        )  # only proph ints
        msat_nhv = msat_declare_function(
            self.env, hv.next_name, msat_get_integer_type(self.env)
        )  # only proph ints
        msat_cap = msat_declare_function(
            self.env, hv.cap.name, msat_get_bool_type(self.env)
        )
        msat_cap_next = msat_declare_function(
            self.env, hv.cap.next_name, msat_get_bool_type(self.env)
        )
        thv, tnhv = self.decl_to_term([msat_hv, msat_nhv])
        tc, tnc = self.decl_to_term([msat_cap, msat_cap_next])
        self.add_state_var(thv, tnhv)
        self.add_state_var(tc, tnc)
        if hv.get_init_constraints_sexpr():
            msat_hv_init = msat_from_string(self.env, hv.get_init_constraints_sexpr())
            print(f"init: {msat_term_repr(msat_hv_init)}")
        msat_hv_trans = msat_from_string(self.env, hv.get_trans_constraints_sexpr())
        self.init = msat_make_and(self.env, self.init, msat_hv_trans)
        self.trans = msat_make_and(self.env, self.trans, msat_hv_trans)

    def get_all_vars_to_z3_def(self):
        ret = {}
        for v_z3, n_z3 in self.get_z3_subs_for_step(0):
            ret[str(v_z3.decl())] = v_z3
        return ret

    def get_all_next_vars_to_z3_def(self):
        ret = {}
        for v_z3, n_z3 in self.get_z3_subs_for_next_step(0):
            ret[str(v_z3.decl())] = v_z3
        return ret

    def get_z3_subs_for_step(self, N: int):
        subs = []
        for sv in self.curvars:
            var_n = self.statevars_bmc[sv][N]
            var_type = msat_type_repr(msat_term_get_type(var_n))
            var_n_str = msat_term_repr(var_n)
            var_str = var_n_str.split("-")[0]
            if var_type == "Int":
                subs.append((Int(var_str), Int(var_n_str)))
            elif var_type == "Bool":
                subs.append((Bool(var_str), Bool(var_n_str)))
            elif var_type == "Arr":
                subs.append((Const(var_str, Arr), Const(var_n_str, Arr)))
            else:
                # if var_type == msat_get_array_type(
                #     self.env,
                #     self.msat_int_type,
                #     msat_get_array_type(
                #         self.env, self.msat_int_type, self.msat_int_type
                #     ),
                # ):
                raise ValueError("no array of array type")
        return subs

    def get_z3_subs_for_next_step(self, N: int):
        subs = []
        for sv in self.curvars:
            var_n = self.statevars_bmc[sv][N]
            var_type = msat_type_repr(msat_term_get_type(var_n))
            var_n_str = msat_term_repr(var_n)
            var_str = f"{var_n_str.split('-')[0]}_next"
            if var_type == "Int":
                subs.append((Int(var_str), Int(var_n_str)))
            elif var_type == "Bool":
                subs.append((Bool(var_str), Bool(var_n_str)))
            elif var_type == "Arr":
                subs.append((Const(var_str, Arr), Const(var_n_str, Arr)))
            else:
                # if var_type == msat_get_array_type(
                #     self.env,
                #     self.msat_int_type,
                #     msat_get_array_type(
                #         self.env, self.msat_int_type, self.msat_int_type
                #     ),
                # ):
                raise ValueError("no array of array type")
        return subs

    def decl_to_term(self, lod):
        for decl in lod:
            yield msat_make_term(self.env, decl, [])

    def add_state_var(self, v, vn):
        self.nextmap[v] = vn
        self.statevars.append((v, vn))
        self.nextvars.add(vn)
        self.curvars.add(v)
        self.curmap[vn] = v
        self.statevars_bmc[v] = defaultdict(lambda: defaultdict(list))

    def remove_state_var(self, v):
        vn = self.nextmap[v]
        del self.nextmap[v]
        del self.curmap[vn]
        self.curvars.remove(v)
        self.nextvars.remove(vn)
        self.statevars = [
            (c, n) for (c, n) in self.statevars if msat_term_id(c) != msat_term_id(v)
        ]

    def next(self, term):
        return msat_apply_substitution(
            self.env,
            term,
            [t[0] for t in self.statevars],
            [t[1] for t in self.statevars],
        )

    def cur(self, term):
        return msat_apply_substitution(
            self.env,
            term,
            [t[1] for t in self.statevars],
            [t[0] for t in self.statevars],
        )

    def is_statevar(self, v):
        return v in self.curvars

    def is_nextstatevar(self, v):
        return v in self.nextvars

    def is_inputvar(self, v):
        return (
            msat_term_is_constant(self.env, v)
            and not self.is_statevar(v)
            and not self.is_nextstatevar(v)
        )

    def abstract_constants(self, fm):
        if msat_term_is_and(self.env, fm):
            lhs = self.abstract_constants(msat_term_get_arg(fm, 0))
            rhs = self.abstract_constants(msat_term_get_arg(fm, 1))
            return msat_make_and(self.env, lhs, rhs)
        elif msat_term_is_equal(self.env, fm):
            for i in range(2):
                other_var_int = 0 if i == 1 else 1
                try:
                    val = int(msat_term_repr(msat_term_get_arg(fm, i)))
                    if val > 50:
                        val = 1
                        msat_num = msat_make_number(self.env, str(val))
                        return msat_make_leq(
                            self.env, msat_num, msat_term_get_arg(fm, other_var_int)
                        )
                except ValueError:
                    continue
        return fm

    def herbrandize_imm_vars(self, trans: msat_term):
        if self.specifier.herbrandize():
            for var in self.imm_vars:
                var_str = msat_term_repr(var)
                next_var_str = msat_term_repr(self.nextmap[var])
                trans = msat_make_and(
                    self.env,
                    trans,
                    msat_from_string(self.env, f"(= {var_str} {next_var_str})"),
                )
        return trans

    def copy(self):
        ret = VmtModel(
            self.env,
            copy.copy(self.statevars),
            self.init,
            self.trans,
            copy.copy(self.props),
            copy.copy(self.liveprops),
        )
        return ret

    def get_str_imm_vars(self):
        return [msat_term_repr(iv) for iv in self.imm_vars]

    def write_vmt(self, filename: str):
        terms = [self.init, self.trans, self.props]
        annots = ["init", "true", "trans", "true", "invar-property", "0"]
        for c, n in self.statevars:
            terms.append(c)
            annots.append("next")
            d = msat_term_get_decl(n)
            annots.append("|%s|" % msat_decl_get_name(d))
        annots = [a.encode() for a in annots]
        with open(filename, "w+") as out:
            out.write(msat_annotated_list_to_smtlib2(self.env, terms, annots))
