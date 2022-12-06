from z3 import Goal, Tactic, BoolRef, ModelRef, ExprRef, substitute
from z3 import *
from collections import defaultdict

from utils import ENode
from array_axioms import ARRAY_AXIOMS
from violation import Violation
from typing import Optional


class EGraph:
    def __init__(self, model: ModelRef, prop_expr: BoolRef, bmc_formula: BoolRef):
        self.debug = False
        self.model = model
        self.prop_expr = prop_expr

        self.enode_to_id_class: dict[ENode, int] = {}
        self.id_class_to_enodes: dict[int, list[ENode]] = defaultdict(list)
        self.match_enode_stack: list[set[ENode]] = []
        self.violations: list[Violation] = []
        self.control_path: set[tuple[ENode, ENode]] = set()
        self.seen_subs: list[dict] = []

        self.add_to_egraph(bmc_formula)
        #self.create_match_terms(bmc_formula)
        self.create_match_terms()

    # def create_match_terms(self, bmc_fm: BoolRef):
    #     goal = Goal()
    #     goal.add(bmc_fm)
    #     res = Tactic("solve-eqs")(goal)
    #     assert len(res) == 1
    #     self.cur_match: set[ENode] = set()
    #     for z3_term in res[0]:
    #         z3_str = str(z3_term)
    #         if "read" in z3_str or "write" in z3_str:
    #             self.push_on_match_enode_stack_help(z3_term)
    #     self.match_enode_stack.append(self.cur_match)

    def create_match_terms(self):
        self.cur_match: set[ENode] = set()
        self.push_on_match_enode_stack_help(self.prop_expr)
        self.match_enode_stack.append(self.cur_match)


    def add_to_egraph(self, z3_def: ExprRef) -> ENode:
        head = self.get_head_from_def(z3_def)
        args = self.get_args_from_def(z3_def, self.add_to_egraph)
        id_num = self.get_id_for_cur_def(z3_def)
        enode = ENode(head, args, z3_def)
        self.enode_to_id_class[enode] = id_num
        if enode not in self.id_class_to_enodes[id_num]:
            self.id_class_to_enodes[id_num].append(enode)
        return enode

    def push_on_match_enode_stack(self, z3_def: ExprRef):
        self.cur_match = set()
        self.push_on_match_enode_stack_help(z3_def)
        self.match_enode_stack.append(self.cur_match)

    def push_on_match_enode_stack_help(self, z3_def: ExprRef) -> Optional[ENode]:
        id_num = self.get_id_for_cur_def(z3_def)
        head = self.get_head_from_def(z3_def)
        args = self.get_args_from_def(z3_def, self.push_on_match_enode_stack_help)
        enode = ENode(head, args, z3_def)
        self.enode_to_id_class[enode] = id_num
        if enode not in self.id_class_to_enodes[id_num]:
            self.id_class_to_enodes[id_num].append(enode)
        if "read" in str(head):
            self.cur_match.add(enode)
        return enode

    def get_axiom_violations(self, needed_subs=[]):
        for axiom in ARRAY_AXIOMS:
            ns = needed_subs.copy()
            self.debug_print(f"Matching Axiom: {axiom}")
            violations = self.match_axiom(axiom, axiom.trigger, {}, ns)
            self.violations.extend(violations)
            if violations:
                return self.violations
        self.control_path = set()
        self.debug_print(f"Match enode stack: {self.match_enode_stack}")
        self.match_enode_stack = self.match_enode_stack[:-1]
        return self.violations

    def match_axiom(self, axiom, match_term, cur_sub, needed_subs):
        axiom_violations = []
        for sub in self.match_term(match_term, cur_sub):
            if not sub:
                continue
            #sub = self.remove_constants(sub)
            if not all(sub.values()) or sub in self.seen_subs:
                continue
            self.seen_subs.append(sub)
            subs = self.get_sub_from_sub_list(sub)
            substitution = substitute(axiom.z3_def, subs)
            self.debug_print(f"Full Sub: {sub}")
            if not self.eval_to_bool(substitution):
                needed_subs.append(sub)
                self.debug_print(f"AXIOM VIOLATION: {substitution}")
                axiom_violations.append(Violation(substitution, needed_subs, self))
                return axiom_violations
            else:
                self.debug_print(f"Valid Axiom Instansiation: {substitution}")
                if not axiom.recur_term == None:
                    recur_sub = substitute(axiom.recur_term, subs)
                    if recur_sub.children():
                        self.push_on_match_enode_stack(recur_sub)
                        needed_subs.append(sub)
                        self.get_axiom_violations(needed_subs)
        return axiom_violations

    def match_term(self, t, sub):
        func, args = self.get_func_and_args_from_term(t)
        seen = []
        for enode in self.get_enodes_matching_head(func):
            for phi in self.match_list(args, enode.args, sub):
                if not phi in seen:
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
            func, args = self.get_func_and_args_from_term(t)
            for en in self.get_equiv_enodes_with_matching_head(enode, func):
                self.debug_print(f"match previous enode: {enode}")
                self.debug_print(f"match enode matching head: {en}")
                for phi in self.match_list(args, en.args, sub):
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
        if self.enode_to_id_class[enode] == self.enode_to_id_class[sub[t][0]]:
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

    def get_enodes_matching_head(self, head):
        str_head = str(head)
        for enode in self.match_enode_stack[-1]:
            if str(enode.head) == str_head:
                yield enode

    def get_equiv_enodes_with_matching_head(self, enode, head):
        str_head = str(head)
        for en in self.get_enodes_in_equiv_class(enode):
            if str(en.head) == str_head:
                yield en

    def get_enodes_in_equiv_class(self, enode):
        class_id = self.enode_to_id_class[enode]
        return self.id_class_to_enodes[class_id]

    def get_func_and_args_from_term(self, t):
        return self.get_head_from_def(t), self.get_args(t)

    def eval_to_bool(self, expr):
        cur_expr = expr
        while not (str(cur_expr) == "True" or str(cur_expr) == "False"):
            cur_expr = self.model.eval(cur_expr)
        return cur_expr

    def get_sub_from_sub_list(self, sub):
        ret_sub = []
        for x in sub:
            ret_sub.append((x, sub[x][0].z3_obj))
        return ret_sub

    def get_head_from_def(self, z3_def: ExprRef) -> ExprRef:
        if z3_def.num_args():
            return z3_def.decl()
        else:
            return z3_def

    def get_args_from_def(self, z3_def: ExprRef, recur_func) -> list:
        args = []
        for i in range(0, z3_def.num_args()):
            cur_arg = z3_def.arg(i)
            arg_enode = recur_func(cur_arg)
            args.append(arg_enode)
        return args

    def get_args(self, ax):
        args = []
        for i in range(0, ax.num_args()):
            args.append(ax.arg(i))
        return args

    def get_id_for_cur_def(self, z3_def: ExprRef) -> int:
        cur_z3_expr = z3_def
        cur_id = z3_def.get_id()
        while True:
            try:
                return self.model[cur_z3_expr].get_id()
            except Exception:
                new_z3_expr = self.model.eval(cur_z3_expr)
                new_z3_id = new_z3_expr.get_id()
            if cur_id == new_z3_id:
                return cur_id
            else:
                cur_id = new_z3_id
                cur_z3_expr = new_z3_expr
        return cur_id

    def remove_constants(self, sub: dict) -> dict:
        '''
        Removes any non-variables in `sub`
        '''
        str_decls = [str(d) for d in self.model.decls()]
        new_sub = defaultdict(list)
        for k in sub:
            for enode in sub[k]:
                if not enode.z3_obj.children() and str(enode.z3_obj) not in str_decls:
                    new_sub[k].append(self.find_decl_in_eclass(enode, str_decls))
                else:
                    new_sub[k].append(enode)
        return new_sub

    def find_decl_in_eclass(self, enode, str_decls):
        for e in self.get_enodes_in_equiv_class(enode):
            if str(e.z3_obj) in str_decls:
                return e

    def debug_print(self, s):
        if self.debug:
            print(s)

    def __repr__(self):
        return f"Current EGraph: {self.enode_to_id_class}\nCurrent Memo: {self.id_class_to_enodes}"
