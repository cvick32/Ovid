import subprocess
import pprint

from utils import parse_vmt, abstract_vmt, NumProph
from z3 import Solver, ModelRef
from violation import Violation
from egraph import EGraph, FoundViolation
from vmt import VmtModel
from solvers import OvidSolver, UnCondHistSolver
from z3_defs import PropagateSolver

IC3IA = "ic3ia"
CYCLES = 50


class Ovid:
    def __init__(self, fname: str, spec: type, num_proph: NumProph, tool: str, debug=False):
        self.debug: bool = False
        self.cur_cex_steps: int = 0
        filename = abstract_vmt(open(fname))
        self.vmt_model: VmtModel = parse_vmt(open(filename), spec, tool)
        self.seen_violations = list()
        self.used_interpolants = []
        self.num_proph = num_proph
        self.tool_name = tool

    def run_loop(self) -> bool:
        if self.run_ic3ia():
            return True
        for count in range(1, CYCLES):
            z3_prop_expr, solver = self.run_z3_bmc()
            violations = solver.get_axiom_violations()
            self.seen_violations.extend(violations)
            assert violations, "No Axiom Violations!"
            self.vmt_model.refine(violations)
            if self.run_ic3ia():
                self.num_refinements = count
                print(f"Total cycles needed: {count}")
                print(f"Total Auxiliary Variables needed: {self.num_proph.get_num_proph()}")
                if self.used_interpolants:
                    print(f"Used Interpolants: {self.used_interpolants}")
                return True
        raise ValueError(f"Used more than {CYCLES} cycles.")

    def run_ic3ia(self) -> bool:
        print("Running IC3IA...")
        fname = "out.vmt"
        self.vmt_model.write_vmt(fname)
        out = subprocess.run([IC3IA, "-w", fname], capture_output=True)
        return self.check_ic3ia_out(out)

    def run_z3_bmc(self) -> ModelRef:
        """
        Runs Z3 at current counterexample depth.
        Returns the Z3 model.
        """
        str_solver = Solver()
        bmc_sexprs = self.vmt_model.get_bmc_sexprs(self.cur_cex_steps)
        bmc_string = " ".join(bmc_sexprs)
        str_solver.from_string(bmc_string)
        asserts = str_solver.assertions()
        z3_prop_expr = asserts[-1]
        if self.tool_name == "UnCondHist1":
            solver = UnCondHistSolver(self.tool_name, self.vmt_model, self.num_proph)
        else:
            solver = OvidSolver(z3_prop_expr, self.tool_name, self.vmt_model, self.num_proph)
        solver.add_assertion(asserts)
        print("Running Z3...")
        check = solver.check()
        if str(check) == "unsat":
            raise ValueError("Z3 unsat when finding countermodel")
        else:
            pass
        model = solver.get_model()
        self.print_bmc_model(model)
        return z3_prop_expr, solver

    def check_ic3ia_out(self, out):
        """
        Inteprets the result (out) of a call to ic3ia. Most commonly
        results in a counterexample or a proof, but also accounts
        for error in witness computation and ic3ia return 'unknown'.
        """
        stdout = out.stdout.decode()
        if "counterexample" in stdout:
            cex = stdout.split("search stats:")[0]
            self.cur_cex_steps = len(cex.split("step")[1:])
            print(f"ic3ia Length: {self.cur_cex_steps}")
            return False
        elif "invariant" in stdout:
            print("Proved!")
            self.invariant = stdout.split("search stats:")[0].replace(
                "invariant", "Invariant:"
            )
            print(self.invariant)
            return True
        elif "computing witness" in stdout:
            print("Proved, but no witness")
            return True
        else:
            if "unknown" in stdout:
                raise ValueError("IC3IA gives 'Unknown'")
            else:
                raise ValueError(f"Error in Vmt: {stdout}")

    def debug_print(self, s):
        if self.debug:
            print(s)

    def print_bmc_model(self, model: ModelRef):
        if not self.debug:
            return
        model_dict = {}
        for expr in model:
            expr_name = expr.name()
            interp_string = f"{expr_name} = {model.get_interp(expr)}"
            frame_num = expr_name.split("-")[-1]
            if not frame_num in model_dict:
                model_dict[frame_num] = []
            model_dict[frame_num].append(interp_string)
        for k in model_dict:
            model_dict[k] = sorted(model_dict[k])

        print("Z3 BMC Model:")
        pprint.pprint(model_dict)
