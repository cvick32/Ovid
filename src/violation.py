from z3 import ExprRef, substitute
from utils import ENode


class Violation:
    def __init__(self, axiom_instance: ExprRef, egraph):
        self.axiom_instance = axiom_instance
        self.egraph = egraph
        self.debug = True
        self.vars_used_in_instance: set[str] = set()
        self.set_frame_numbers()
        if not self.is_single_frame_violation() and not self.is_trans_violation():
            self.check_for_immutable_var_instance()

    def set_frame_numbers(self):
        self.highest_frame = -1
        self.highest_frame_expr = None
        self.frame_numbers = set()
        self._set_frame_numbers_help(self.axiom_instance)

    def check_for_immutable_var_instance(self):
        if not self.is_single_frame_violation() and not self.is_trans_violation():
            for equal_enode in self.egraph.get_enodes_in_equiv_class(self.highest_frame_expr):
                if equal_enode.children():
                    continue
                var_str = str(equal_enode).split("-")[0]
                print(var_str)
                print(self.egraph.str_imm_vars)
                if var_str in self.egraph.str_imm_vars:
                    print("Saved a Prophecy Variable by Instantiating with Immutable")
                    self.axiom_instance = substitute(
                        self.axiom_instance,
                        (self.highest_frame_expr, equal_enodej),
                    )
                    self.set_frame_numbers()
                    break

    def get_var_sub_vals(self):
        for v in self.vars_used_in_instance:
            if v in self.egraph.str_imm_vars:
                yield v, "cur"
            elif self.is_single_frame_violation():
                yield v, "cur"
            elif self.is_trans_violation():
                if int(v.split("-")[1]) == max(self.frame_numbers):
                    yield v, "next"
                else:
                    yield v, "cur"
            else:
                if int(v.split("-")[1]) == max(self.frame_numbers):
                    v = self.create_proph(v)
                    yield v, "proph"
                elif int(v.split("-")[1]) == min(self.frame_numbers):
                    yield v, "cur"
                else:
                    yield v, "next"

    def create_proph(v):
        pass

    def get_history_condition(self):
        pass


    def _set_frame_numbers_help(self, z3_term: ExprRef):
        children = z3_term.children()
        if children:
            for child in children:
                self._set_frame_numbers_help(child)
        else:
            z3_str = str(z3_term)
            fn = self.get_frame_number(z3_str)
            if fn == "Immutable":
                self.vars_used_in_instance.add(z3_str)
            elif fn is not None:
                self.vars_used_in_instance.add(z3_str)
                self.frame_numbers.add(fn)
                if fn > self.highest_frame:
                    self.highest_frame = fn
                    self.highest_frame_expr = z3_term

    def is_single_frame_violation(self):
        return len(self.frame_numbers) == 1

    def is_trans_violation(self):
        return max(self.frame_numbers) - min(self.frame_numbers) == 1

    def get_frame_number(self, var_str):
        try:
            var, step = var_str.split("-")
            assert var != ""
            if var in self.egraph.str_imm_vars:
                return "Immutable"
            return int(step)
        except:
            return None

    def __repr__(self):
        return f"{self.axiom_instance}"

    def __eq__(self, other):
        return str(self.axiom_instance) == str(other.axiom_instance)
