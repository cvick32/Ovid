from z3 import BoolRef, ModelRef, ExprRef, substitute, IntNumRef
from z3_defs import PropagateSolver
from array_axioms import ARRAY_AXIOMS
from violation import Violation
from utils import NumProph
from vmt import VmtModel


class EGraph:
    def __init__(
        self,
        model: ModelRef,
        prop_expr: BoolRef,
        imm_vars: list[str],
        ps: PropagateSolver,
        np: NumProph,
        vmt: VmtModel,
    ):
        self.debug = False
        self.model: ModelRef = model
        self.prop_expr: BoolRef = prop_expr
        self.str_imm_vars: list[str] = imm_vars
        self.ps = ps
        self.vmt_model = vmt

        self.violation: Violation = None
        self.seen_subs: list[dict] = []
        self.control_path = set()
        self.num_proph = np
        self.recur_match_stack = []

    def get_axiom_violation(self) -> [Violation]:
        for axiom in ARRAY_AXIOMS:
            self.debug_print(f"Matching Axiom: {axiom}")
            try:
                self.match_axiom(axiom, axiom.trigger, {})
            except FoundViolation:
                return self.violation

    def match_axiom(self, axiom, match_term: ExprRef, cur_sub):
        for sub in self.match_term(match_term, cur_sub):
            if not sub or not all(sub.values()) or sub in self.seen_subs:
                continue
            self.seen_subs.append(sub)
            subs = self.get_sub_from_sub_list(sub)
            substitution = substitute(axiom.z3_def, subs)
            self.debug_print(f"Full Sub: {sub}")
            if not self.eval_to_bool(substitution):
                self.debug_print(f"AXIOM VIOLATION: {substitution}")
                self.violation = Violation(substitution, self)
                raise FoundViolation
            else:
                self.debug_print(f"Valid Axiom Instansiation: {substitution}")
                if axiom.recur_term is not None:
                    recur_sub = substitute(axiom.recur_term, subs)
                    self.recur_match_stack.append([recur_sub])
                    self.get_axiom_violation()
                    if self.violation:
                        raise FoundViolation
                    else:
                        self.recur_match_stack = self.recur_match_stack[:-1]

    def match_term(self, t, sub):
        func, args = t.decl(), t.children()
        seen = []
        for enode in self.get_enodes_matching_head(func):
            for phi in self.match_list(args, enode.children(), sub):
                if phi not in seen:
                    seen.append(phi)
                    yield phi

    def match_list(self, args, enode_args, sub):
        if len(args) == 0:
            yield sub
        else:
            if enode_args:
                for phi in self.match(args[0], enode_args[0], sub):
                    for psi in self.match_list(args[1:], enode_args[1:], phi):
                        yield psi

    def match(self, t, enode, sub):
        if t.num_args() == 0:
            yield self.get_sub_for_single_term(t, enode, sub)
        else:
            func, args = t.decl(), t.children()
            for en in self.get_equiv_enodes_with_matching_head(enode, func):
                self.debug_print(f"previous enode: {enode}")
                self.debug_print(f"equiv enode with matching head: {en}")
                for phi in self.match_list(args, en.children(), sub):
                    if phi:
                        # required enode be equal to the matching head en
                        self.control_path.add((enode, en))
                        yield phi
                    else:
                        continue

    def get_sub_for_single_term(self, t, enode, sub):
        self.debug_print(f"get_sub: {t} {sub} {enode}")
        if t not in sub.keys():
            new_sub = dict(sub)
            new_sub[t] = [enode]
            return new_sub
        if self.ps.check_roots_equal(enode, sub[t][0]):
            # check if enode is in e-class of current sub for t
            # store fact that sub is dependent being in eclass of t
            # by appending to the list of matches
            new_sub = dict(sub)
            new_list = list(new_sub[t])
            new_list.append(enode)
            new_sub[t] = new_list
            return new_sub
        else:
            return

    def get_enodes_matching_head(self, head) -> ExprRef:
        head_id = head.get_id()
        match_against = None
        if self.recur_match_stack:
            match_against = self.recur_match_stack[-1]
        else:
            match_against = self.ps.get_seen()
        for z3_obj in match_against:
            if z3_obj.decl().get_id() == head_id:
                yield z3_obj

    def get_equiv_enodes_with_matching_head(self, enode, head) -> ExprRef:
        head_id = head.get_id()
        seen = set()
        while self.ps.next(enode) not in seen:
            enode = self.ps.next(enode)
            if enode.decl().get_id() == head_id:
                yield enode
            seen.add(enode)
        if self.ps.solver.root(enode).get_id() == head_id:
            yield enode

    def get_enodes_in_equiv_class(self, expr):
        expr = self.ps.get_root(expr)
        while not self.ps.next_is_root(expr):
            expr = self.ps.next(expr)
            yield expr
        yield expr

    def eval_to_bool(self, expr):
        cur_expr = expr
        while not (str(cur_expr) == "True" or str(cur_expr) == "False"):
            cur_expr = self.model.eval(cur_expr)
        return cur_expr

    def get_sub_from_sub_list(self, sub):
        ret_sub = []
        for x in sub:
            ret_sub.append((x, sub[x][0]))
        return ret_sub

    def debug_print(self, s):
        if self.debug:
            print(s)


class FoundViolation(ValueError):
    pass
