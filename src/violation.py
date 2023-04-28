from z3 import ExprRef, substitute, Int
from utils import run_smt_interpol_from_sexprs
from variable import ProphecyVariable, HistoryVariable
from synthesizer import Synthesizer


class Violation:
    def __init__(self, axiom_instance: ExprRef, solver, tool, egraph=None):
        self.axiom_instance = axiom_instance
        self.egraph = egraph
        self.debug = False
        self.str_imm_vars = solver.get_str_imm_vars()
        self.z3_model = solver.get_model()
        self.solver = solver
        self.num_proph = solver.num_proph
        self.vars_used_in_instance: set[str] = set()
        self.set_frame_numbers()
        self.tool = tool
        if self.tool != "UnCondHist1":
            if not self.is_single_frame_violation() and not self.is_trans_violation():
                self.check_for_immutable_var_instance()
        self.var_vals = self._get_var_sub_vals()

    def set_frame_numbers(self):
        self.highest_frame = -1
        self.highest_frame_expr = None
        self.frame_numbers = set()
        self._set_frame_numbers_help(self.axiom_instance)

    def check_for_immutable_var_instance(self):
        if not self.is_single_frame_violation() and not self.is_trans_violation():
            seen = []
            for equal_enode in self.egraph.get_enodes_in_equiv_class(
                self.highest_frame_expr
            ):
                if equal_enode in seen or equal_enode is None:
                    break
                seen.append(equal_enode)
                print(equal_enode)
                if equal_enode.children():
                    continue
                var_str = str(equal_enode).split("-")[0]
                if var_str in self.str_imm_vars:
                    print("Saved a Prophecy Variable by Instantiating with Immutable")
                    self.axiom_instance = substitute(
                        self.axiom_instance,
                        (self.highest_frame_expr, equal_enode),
                    )
                    self.set_frame_numbers()
                    break

    def get_var_vals(self):
        return self.var_vals

    def create_proph_and_hist(self, v) -> tuple[list[HistoryVariable], ProphecyVariable]:
        var_str, frame_str = v.split("-")
        var_to_proph = Int(var_str)  # always prophecy Integers...
        pc_val = self.z3_model[Int(f"pc-{frame_str}")]
        self.solver.num_proph.set_next_proph_num()
        num_proph = self.solver.num_proph.get_num_proph()
        if "UnCondHist" in self.tool:
            hvs = []
            hv = var_to_proph
            for i in range(int(frame_str)):
                hv = HistoryVariable(var_str, hv, None, Int("pc"), pc_val, num_proph, self.tool)
                hvs.append(hv)
            pv = ProphecyVariable(var_str, var_to_proph, hv, num_proph)
            return hvs, pv
        cpes = self.egraph.control_path
        hv = HistoryVariable(var_str, var_to_proph, cpes, Int("pc"), pc_val, num_proph, self.tool)
        if not self.check_history_kills(hv):
            i_type, interp = self.get_interpolant(hv)
            if i_type == "safe":
                hv.set_safe_interp_trans(interp)
            else:
                hv.set_trigger_interp_trans(interp)
        pv = ProphecyVariable(var_str, var_to_proph, hv, num_proph)
        return [hv], pv

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
            if var in self.str_imm_vars:
                return "Immutable"
            return int(step)
        except:
            return None

    def get_interpolant(self, hist):
        interp_sexprs = self.solver.vmt_model.get_interp_sexprs()
        interp_clauses = run_smt_interpol_from_sexprs(
            interp_sexprs, self.solver.vmt_model
        )
        synth = Synthesizer(
            interp_clauses, int(max(self.frame_numbers)), hist, self.solver
        )
        return synth.get_top_interpolant()

    def get_interpolant_clauses(self):
        return Interpolator().get_interpolant_clauses()

    def check_history_kills(self, hist):
        clause = hist.get_current_history_condition()
        for i in range(0, self.highest_frame):
            if not self.check_clause_on_model_and_step(clause, i):
                return False
        return self.check_clause_on_model_and_step(clause, self.highest_frame)

    def check_clause_on_model_and_step(self, clause, step):
        sub_clause = substitute(
            substitute(clause, self.solver.vmt_model.get_z3_subs_for_step(step)),
            self.solver.vmt_model.get_z3_subs_for_step(step + 1),
        )
        return self.z3_model.eval(sub_clause)

    def _get_var_sub_vals(self):
        var_vals = []
        for v in self.vars_used_in_instance:
            var_str, frame = v.split("-")
            if var_str in self.str_imm_vars:
                var_vals.append((v, "cur"))
            elif self.is_single_frame_violation():
                var_vals.append((v, "cur"))
            elif self.is_trans_violation():
                if int(frame) == max(self.frame_numbers):
                    var_vals.append((v, "next"))
                else:
                    var_vals.append((v, "cur"))
            else:
                if int(frame) == max(self.frame_numbers):
                    var_vals.append((v, "proph"))
                elif int(frame) == min(self.frame_numbers):
                    var_vals.append((v, "cur"))
                else:
                    var_vals.append((v, "next"))
        return var_vals

    def __repr__(self):
        return f"{self.axiom_instance}"

    def __eq__(self, other):
        return str(self.axiom_instance) == str(other.axiom_instance)
