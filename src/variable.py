from z3 import Const, And, Implies, Or, Not, substitute, Bool, IntNumRef
from copy import copy


class Variable:
    def __init__(self, var_def, next_var_def):
        self.var_def = var_def
        self.sort_sexpr = self.var_def.sort().sexpr()
        self.name = str(self.var_def)
        self.next_var_def = next_var_def
        self.next_name = str(self.next_var_def)

    def get_def_sexpr(self):
        return f"(declare-fun {self.name} () {self.sort_sexpr})\n(declare-fun {self.next_name} () {self.sort_sexpr})\n(define-fun .{self.name} () {self.sort_sexpr} (! {self.name} :next {self.next_name}))"

    def get_name(self):
        return self.name

    def get_next_name(self):
        return self.next_name

    def get_init_condition_sexpr(self):
        return None

    def get_trans_condition_sexpr(self):
        return None

    def get_init_constraints(self):
        return None

    def get_trans_constraints(self):
        return None

    def get_prop_antecedent(self):
        return None

    def __repr__(self):
        return f"{self.var_def.__repr__()} => {self.next_var_def.__repr__()}"


class Capture(Variable):
    def __init__(self, hist_var_name):
        name = f"capture{hist_var_name}"
        var_def = Bool(name)
        next_var_def = Bool(f"{name}_next")
        self.name = name
        self.next_name = f"{name}_next"
        super().__init__(var_def, next_var_def)
        self.init_constraints = [Not(var_def)]
        self.trans_constraints = [Implies(var_def, next_var_def)]

    def get_history_antecedent(self):
        return Not(self.var_def)

    def get_trans_sexpr(self):
        return f"(=> {self.name} {self.next_name})"

    def get_trans_constraints(self):
        return self.trans_constraints

    def get_init_constraints(self):
        return self.init_constraints

    def get_init_sexpr(self):
        return f"(not {self.name})"

    def get_history_consequent_for_capture(self):
        return self.next_var_def

    def get_history_consequent_for_not_capture(self):
        return self.var_def == self.next_var_def


class HistoryVariable(Variable):
    """
    Could keep a list of needed equalities here and
    cycle through if we're not making refinement progress.
    """

    def __init__(
        self,
        var_name,
        var_to_proph,
        control_path_exprs,
        pc_var,
        pc_val,
        num_proph,
    ):
        self.var_name = var_name
        name = f"{var_name}H{num_proph}"
        var_def = Const(name, var_to_proph.sort())
        next_var_def = Const(f"{name}_next", var_to_proph.sort())
        self.cap = Capture(name)
        super().__init__(var_def, next_var_def)
        self.antecedents = []
        self.capture_consequents = []
        self.else_consequents = []
        self.var_to_proph = var_to_proph
        self.trans_constraints = self.build_trans(control_path_exprs, pc_var, pc_val)
        self.is_trigger = False

    def build_trans(self, cpes, pc_var, pc_val):
        if cpes:
            cpe_expr = And([cpe[0] == cpe[1] for cpe in cpes])
        else:
            cpe_expr = True
        self.pc_ante = []
        if pc_var is not None and pc_val is not None:
            self.pc_ante = [pc_var == pc_val]
        # self.antecedents = [cpe_expr]
        self.antecedents = []
        self.capture_consequents = [self.var_to_proph == self.next_var_def]
        self.else_consequents = [self.var_def == self.next_var_def]
        self.current_history_cond = And(self.antecedents + self.pc_ante)
        return [
            Implies(
                And(
                    self.antecedents
                    + self.pc_ante
                    + [self.cap.get_history_antecedent()]
                ),
                And(
                    self.capture_consequents[0],
                    self.cap.get_history_consequent_for_capture(),
                ),
            ),
            Implies(
                Not(
                    And(
                        self.antecedents
                        + self.pc_ante
                        + [self.cap.get_history_antecedent()]
                    )
                ),
                And(
                    self.else_consequents[0],
                    self.cap.get_history_consequent_for_not_capture(),
                ),
            ),
        ]

    def get_trans_constraints(self):
        return self.trans_constraints

    def get_init_constraints_sexpr(self):
        if self.cap.get_init_constraints():
            return And(self.cap.get_init_constraints()).sexpr()
        return ""

    def get_trans_constraints_sexpr(self):
        if self.cap.get_trans_constraints():
            return And(
                And(self.trans_constraints), And(self.cap.get_trans_constraints())
            ).sexpr()
        return And(self.trans_constraints).sexpr()

    def get_current_history_condition(self):
        return self.current_history_cond

    def set_safe_interp_trans(self, interp):
        new_ante = copy(self.pc_ante)
        new_ante.append(interp)
        new_ante.append(self.cap.get_history_antecedent())
        new_cap_cons = copy(self.capture_consequents)
        new_cap_cons.append(self.cap.get_history_consequent_for_capture())
        new_else_cons = copy(self.else_consequents)
        new_else_cons.append(self.cap.get_history_consequent_for_not_capture())
        self.trans_constraints = [
            Implies(And(new_ante), And(new_cap_cons)),
            Implies(Not(And(new_ante)), And(new_else_cons)),
        ]
        return self.trans_constraints

    def set_trigger_interp_trans(self, interp):
        new_ante = copy(self.pc_ante)
        new_ante.append(interp)
        new_cap_cons = copy(self.capture_consequents)
        new_else_cons = copy(self.else_consequents)
        self.trans_constraints = [
            Implies(And(new_ante), And(new_cap_cons)),
            Implies(Not(And(new_ante)), And(new_else_cons)),
        ]
        self.is_trigger = True
        self.cap.init_constraints = []
        self.cap.trans_constraints = []
        return self.trans_constraints


class ProphecyVariable(Variable):
    def __init__(self, var_str, var_to_proph, hist_var, num_proph):
        name = f"{var_str}P{num_proph}"
        var_def = Const(name, var_to_proph.sort())
        next_var_def = Const(f"{name}_next", var_to_proph.sort())
        super().__init__(var_def, next_var_def)
        self.prop_antecedent = var_def == hist_var.var_def
        self.trans_constraints = [next_var_def == var_def]

    def get_trans_constraints(self):
        return self.trans_constraints

    def get_prop_antecedent(self):
        return self.prop_antecedent

    def get_prop_antecedent_sexpr(self):
        return self.prop_antecedent.sexpr()

    def get_trans_constraints_sexpr(self):
        return self.trans_constraints[0].sexpr()
