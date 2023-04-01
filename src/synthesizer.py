from z3 import substitute, And
from collections import defaultdict


class Synthesizer:
    def __init__(self, clauses, step, hist, solver):
        cond = hist.pc_ante[0]
        self.all_clauses = set(clauses)
        self.safe_clauses = set(clauses)
        self.trigger_clauses = set(clauses)
        self.z3_model = solver.model
        self.vmt_model = solver.vmt_model
        for i in range(0, step):
            self.check_clauses_on_model_and_step(
                self.safe_clauses, i, negate=True, cond=cond
            )
        self.check_clauses_on_model_and_step(
            self.safe_clauses, step, negate=False, cond=cond
        )
        self.check_clauses_on_model_and_step(
            self.trigger_clauses, step, negate=False, cond=cond
        )
        length = solver.vmt_model.cur_N
        for i in range(step + 1, length - 1):
            self.check_clauses_on_model_and_step(
                self.trigger_clauses, i, negate=True, cond=cond
            )
        self.used_vars = defaultdict(int)
        self.used_funcs = defaultdict(int)
        self.used_consts = defaultdict(int)
        # self.setup_ranking_dicts(self.vmt_model.get_z3_prop_expr)
        self.rank_clauses()

    def check_clauses_on_model_and_step(self, clauses, step, negate, cond):
        old_clauses = list(clauses)
        clauses.clear()
        for cur_clause in old_clauses:
            sub_clause = substitute(
                substitute(
                    And(cur_clause, cond), self.vmt_model.get_z3_subs_for_step(step)
                ),
                self.vmt_model.get_z3_subs_for_next_step(step + 1),
            )
            eval_bool = self.z3_model.eval(sub_clause)
            if negate and not eval_bool or not negate and eval_bool:
                clauses.add(cur_clause)

    def get_top_interpolant(self):
        try:
            top = sorted(self.ranking)[-1]
            top_interp = self.ranking[top]
            if top_interp in self.trigger_clauses:
                return "trigger", top_interp
            else:
                return "safe", top_interp
        except IndexError:
            return "trigger", list(self.all_clauses)[-1]

    # def setup_ranking_dicts(self, cur_prop_term):
    #     if cur_prop_term.children():
    #         self.used_funcs[str(cur_prop_term.decl())] += 1
    #         for child in cur_prop_term.children():
    #             self.setup_ranking_dicts(child)
    #     else:
    #         str_term = str(cur_prop_term)
    #         if str_term in self.vmt_model.str_vars:
    #             self.used_vars[str_term] += 1
    #         else:
    #             self.used_consts[str_term] += 1

    def rank_clauses(self):
        ranking = {}
        for clause in self.trigger_clauses:
            # prefer triggers
            ranking[self.get_rank(clause) * 2] = clause
        for clause in self.safe_clauses:
            ranking[self.get_rank(clause)] = clause
        self.ranking = ranking

    def get_rank(self, clause):
        str_clause = str(clause)
        rank = -1 * len(str_clause)  # prefer shorter
        # for v in self.used_vars:
        #     if v in str_clause:
        #         rank += 20 * self.used_vars[v]
        # for f in self.used_funcs:
        #     if f in str_clause:
        #         rank += 15 * self.used_funcs[f]
        # for c in self.used_consts:
        #     if c in str_clause:
        #         rank += 10 * self.used_consts[c]
        return rank
