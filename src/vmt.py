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
from collections import defaultdict
from violation import Violation
from encoding_specifier import EncodingSpecifier


class VmtModel(object):
    def __init__(
        self,
        env,
        statevars: list[tuple[msat_term, msat_term]],  # cur[0] and next[1]
        init: msat_term,
        trans: msat_term,
        props: msat_term,
        spec: type
    ):
        self.specifier: EncodingSpecifier = spec(env, statevars, trans, props)

        self.statevars = statevars
        self.nextvars: set[msat_term] = set(p[1] for p in statevars)
        self.curvars: set[msat_term] = set(p[0] for p in statevars)
        self.nextmap: dict[msat_term, msat_term] = dict(statevars)
        self.curmap: dict[msat_term, msat_term] = dict((n, c) for (c, n) in statevars)

        self.imm_vars: list[msat_term] = self.find_imm_vars(trans)
        self.env: msat_env = env
        self.init = self.abstract_constants(init)
        self.trans = self.herbrandize_imm_vars(trans)
        self.props = props

        self.array_violation_time = self.specifier.prop_fails()
        self.prop_msat_expr = self.specifier.get_prop_expr()

        self.def_sexprs: list[str] = [
            "(declare-sort Arr 0)",
            "(declare-fun read_int_int (Arr Int) Int)",
            "(declare-fun write_int_int (Arr Int Int) Arr)",
        ]

        self.statevars_bmc: dict[msat_term, dict[int, msat_term]] = {
            v: defaultdict(lambda: defaultdict(list)) for v in self.curvars
        }
        self.bmc_var_str_to_statevar: dict[str, msat_term] = {}

    def refine(self, violation: Violation):
        sexpr = violation.axiom_instance.sexpr()
        msat_inst = msat_from_string(self.env, sexpr)
        sub: tuple[list[msat_term], list[msat_term]] = ([], [])
        is_trans = violation.is_trans_violation()
        # is_proph = violation.
        max_frame = max(violation.frame_numbers)
        for var_str in list(violation.vars_used_in_instance):
            sub[0].append(msat_from_string(self.env, var_str))
            if "i1_0" in var_str:
                sub[1].append(self.bmc_var_str_to_statevar[var_str])
            elif is_trans and int(var_str.split("-")[1]) == max_frame:
                sub[1].append(self.nextmap[self.bmc_var_str_to_statevar[var_str]])
            # elif is_proph:
            #     breakpoint()
            else:
                sub[1].append(self.bmc_var_str_to_statevar[var_str])
        msat_inst = msat_apply_substitution(self.env, msat_inst, sub[0], sub[1])
        self.init = msat_make_and(self.env, self.init, msat_inst)
        self.trans = msat_make_and(self.env, self.trans, msat_inst)

    def get_bmc_sexprs(self, N: int) -> tuple[list[str], str]:
        sexprs: list[str] = [d for d in self.def_sexprs]
        for i in range(N):
            if i == 0:
                cur_fm = msat_make_and(self.env, self.trans, self.init)
            elif i == N - 1:
                cur_fm = msat_make_not(self.env, self.props)
            else:
                cur_fm = self.trans
            for var, next_var in self.statevars:
                var_name: str = msat_term_repr(var)
                var_n: msat_term = self.get_var_at_n(i, var, var_name, sexprs)
                var_n_plus_one: msat_term = self.get_var_at_n(
                    i + 1, var, var_name, sexprs
                )
                cur_fm = msat_apply_substitution(
                    self.env, cur_fm, [var, next_var], [var_n, var_n_plus_one]
                )
            sexpr_term = self.cleanup_mathsat_repr(cur_fm)
            assert_term = f"(assert {sexpr_term})"
            sexprs.append(assert_term)
        return sexprs, self.get_prop_expr_sexpr(N)

    def get_prop_expr_sexpr(self, N: int) -> str:
        cur_fm = self.prop_msat_expr
        for var, next_var in self.statevars:
            var_name: str = msat_term_repr(var)
            var_n: msat_term = self.get_var_at_n(
                N - (self.array_violation_time + 1), var, var_name, []
            )
            var_n_plus_one: msat_term = self.get_var_at_n(
                N - (self.array_violation_time), var, var_name, []
            )
            cur_fm = msat_apply_substitution(
                self.env, cur_fm, [var, next_var], [var_n, var_n_plus_one]
            )
        return f"(assert {self.cleanup_mathsat_repr(cur_fm)})"

    def get_var_at_n(
        self, n: int, var: msat_term, var_name: str, sexprs: list[str]
    ) -> msat_term:
        var_type: msat_type = msat_term_get_type(var)
        type_string = self.get_type_str(msat_type_repr(var_type))
        var_n_str = f"{var_name}-{n}"
        declaration = f"(declare-fun {var_n_str} () {type_string})"
        if declaration not in sexprs:
            sexprs.append(declaration)
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
        return f"(assert {cur_repr})"

    def add_state_var(self, v, vn):
        self.nextmap[v] = vn
        self.statevars.append((v, vn))
        self.nextvars.add(vn)
        self.curvars.add(v)
        self.curmap[vn] = v

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
        if self.specifier.herbrandize:
            for var in self.imm_vars:
                var_str = msat_term_repr(var)
                next_var_str = msat_term_repr(self.nextmap[var])
                trans = msat_make_and(
                    self.env,
                    trans,
                    msat_from_string(self.env, f"(= {var_str} {next_var_str})"),
                )
        return trans

    def find_imm_vars(self, trans: msat_term):
        imm_vars: list[msat_term] = []
        term_repr = msat_term_repr(trans)
        for var in self.nextvars:
            str_var = msat_term_repr(var)
            if str_var not in term_repr:
                imm_vars.append(self.curmap[var])
        return imm_vars

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
        for (c, n) in self.statevars:
            terms.append(c)
            annots.append("next")
            d = msat_term_get_decl(n)
            annots.append("|%s|" % msat_decl_get_name(d))
        annots = [a.encode() for a in annots]
        with open(filename, "w+") as out:
            out.write(msat_annotated_list_to_smtlib2(self.env, terms, annots))
