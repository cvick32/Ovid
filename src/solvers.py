from z3 import UserPropagateBase, SimpleSolver, Solver, BoolSort
from z3_defs import *
from egraph import EGraph
from array_axioms import ARRAY_AXIOMS, V, L, Z, A_ax

from violation import Violation

class OvidSolver(UserPropagateBase):
    def __init__(self, prop_expr, tool, vmt, num_proph):
        self.diseqs = set()
        self.eqs = set()
        self.seen = set()
        ss = SimpleSolver()
        self.match_against = []
        self.prop = prop_expr
        self.tool_name = tool
        self.vmt_model = vmt
        self.num_proph = num_proph
        super().__init__(ss)

    def add_assertion(self, fm):
        self.solver.add(fm)

    def add_array_exprs(self, expr, loc_or_val=False):
        """
        heuristic of what expressions we actually want to register
        """
        if len(expr.children()) == 0:
            if expr.sort() in [Arr, ArrOfArr]:
                self.add(expr)
            elif loc_or_val:
                self.add(expr)
                # why am i adding expressions?
                # shouldn't i only be concerned with when arrays
                # get set to values?
        elif expr.decl() in [Write, Read, ArrWrite, ArrRead, ConstArr]:
            # have to "add" all array functions so that they appear in
            # the egraph when use "get_equiv_enodes_with_matching_head"
            loc_or_val = True
            self.add(expr)
            self.seen.add(expr)
        else:
            loc_or_val = False
        for ch in expr.children():
            self.add_array_exprs(ch, loc_or_val)

    def check(self):
        self.add_eq(self.eq_override)
        self.add_diseq(self.diseq_override)
        self.push_on_match_term_stack(self.prop)
        for expr in self.solver.assertions():
            # instead of doing this, could i instead only add the
            # array variables, like a-1, b-2, etc. and "add" them to
            # the watch set. (further notes in 3-5-22)
            self.add_array_exprs(expr)
        return self.solver.check()

    def get_model(self):
        self.model = self.solver.model()
        return self.model

    def eq_override(self, arg1, arg2):
        self.eqs.add(tuple([arg1, arg2]))
        self.eqs.add(tuple([arg2, arg1]))
        if arg1.decl() in [Read, ArrRead]:
            self.seen.add(arg1)
        if arg2.decl() in [Read, ArrRead]:
            self.seen.add(arg2)

    def diseq_override(self, arg1, arg2):
        self.diseqs.add(tuple([arg1, arg2]))
        self.diseqs.add(tuple([arg2, arg1]))
        if arg1.decl() in [Read, ArrRead]:
            self.seen.add(arg1)
        if arg2.decl() in [Read, ArrRead]:
            self.seen.add(arg2)

    def push(self):
        pass

    def pop(self, pop_scopes):
        pass

    def next(self, expr):
        potential = self.solver.next(expr)
        if self.is_var_expr(potential):
            return potential
        else:
            potential_root = self.solver.root(potential)
            for s in self.seen:
                if self.solver.root(s).get_id() == potential_root.get_id():
                    return s

    def is_var_expr(self, expr):
        return (
            (isinstance(expr, ExprRef))
            and not (isinstance(expr, IntNumRef))
            and all(self.is_var_expr(c) for c in expr.children())
        )

    def check_roots_equal(self, ze1, ze2):
        return self.solver.root(ze1).get_id() == self.solver.root(ze2).get_id()

    def next_is_root(self, expr):
        return self.solver.next(expr).get_id() == self.solver.root(expr).get_id()

    def get_root(self, expr):
        return self.solver.root(expr)

    def get_seen(self):
        """
        Returns the list of expressions we're going to ematch over.
        """
        for m in self.match_against:
            yield m
        for s in self.seen:
            yield s

    def push_on_match_term_stack(self, z3_expr):
        for child in z3_expr.children():
            self.push_on_match_term_stack(child)
        if z3_expr.decl() in [Read, ArrRead]:
            self.match_against.append(z3_expr)
        if not z3_expr.children():
            # add all terms in prop
            if not isinstance(z3_expr, IntNumRef):
                self.add(z3_expr)
                self.match_against.append(z3_expr)

    def get_axiom_violations(self):
        return [EGraph(self, self.vmt_model, self.tool_name).get_axiom_violation()]

    def get_str_imm_vars(self):
        return self.vmt_model.get_str_imm_vars()


class UnCondHistSolver:
    def __init__(self, tool, vmt, num_proph):
        self.constarr_terms = []
        self.constarr_term_set = set([])
        self.write_terms = []
        self.write_term_set = set([])
        self.index_terms = []
        self.index_term_set = set([])
        self.tool_name = tool
        self.vmt_model = vmt
        self.num_proph = num_proph
        self.solver = Solver()
        self.axioms = ARRAY_AXIOMS
        self.violations = []

    def add_assertion(self, fm):
        self.solver.add(fm)

    def add_array_exprs(self, expr, loc_or_val=False):
        """
        heuristic of what expressions we actually want to register
        """
        args = expr.children()
        if expr.decl() == Write:
            self.write_term_set.add(expr)
            self.write_terms.append(expr)
            self.add_index_term(args[1])
        elif expr.decl() == Read:
            self.add_index_term(args[1])
        elif expr.decl() == ConstArr:
            if expr not in self.constarr_term_set:
                self.constarr_term_set.add(expr)
                self.constarr_terms.append(expr)
        for ch in expr.children():
            self.add_array_exprs(ch, loc_or_val)

    def add_index_term(self, z3_def):
        if z3_def not in self.index_term_set:
            self.index_term_set.add(z3_def)
            self.index_terms.append(z3_def)

    def check(self):
        for expr in self.solver.assertions():
            # instead of doing this, could i instead only add the
            # array variables, like a-1, b-2, etc. and "add" them to
            # the watch set. (further notes in 3-5-22)
            self.add_array_exprs(expr)
        return self.solver.check()

    def get_model(self):
        return self.solver.model()

    def check_violated(self, violated):
        s = Solver()
        flags = []
        cnstrs = list(self.solver.assertions())
        for idx, exp in enumerate(violated):
            flag = Const("$fl{}".format(idx), BoolSort())
            flags.append(flag)
            cnstrs.append(Implies(flag, exp))
        cond = And(cnstrs)
        s.add(cond)
        check = s.check(flags)
        if str(check) == "unsat":
            used = []
            core = s.unsat_core()
            for fl, exp in zip(flags, violated):
                if fl in core:
                    used.append(exp)
            return used
        else:
            self.model = s.model()
            return None

    def get_axiom_violations(self):
        violated = []
        model = self.get_model()
        while True:
            new_violated = []
            for constarr in self.constarr_terms:
                val = constarr.children()[0]
                for idx in self.index_terms:
                    axiom = substitute(self.axioms[0].z3_def, [(V, val), (L, idx)])
                    if not model.eval(axiom):
                        new_violated.append(axiom)
            for write in self.write_terms:
                arr, wid, val = write.children()
                axiom = substitute(
                    self.axioms[1].z3_def, [(A_ax, arr), (V, val), (L, wid)]
                )
                if not model.eval(axiom):
                    new_violated.append(axiom)
                for idx in self.index_terms:
                    axiom = substitute(
                        self.axioms[2].z3_def,
                        [(A_ax, arr), (V, val), (L, wid), (Z, idx)],
                    )
                    if not model.eval(axiom):
                        new_violated.append(axiom)
            if len(new_violated) == 0:
                print("no new violations")
                raise ValueError("Should not be doing this")
                break
            violated.extend(new_violated)
            used = self.check_violated(violated)
            if used is not None:
                for thing in used:
                    print("violation: {}".format(thing))
                break
        for axiom in used:
            self.violations.append(
                Violation(
                    axiom,
                    self,
                    self.tool_name,
                )
            )
        return self.violations

    def get_str_imm_vars(self):
        return self.vmt_model.get_str_imm_vars()
