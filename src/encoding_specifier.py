from mathsat import *


class EncodingSpecifier:
    """
    This class takes an msat env and two msat_terms, 1 is the trans
    relation the other is the property as stated in the vmt problem.

    An EncodingSpecifier decides the following:
       - how to obtain the property expression from the transition
         relation and the property
       - if herbrandization should be used
       - when the prop_expr will fail in relation to the counterexample length
         - returning 1 means prop_expr is false at N - 1
    """

    def __init__(
        self,
        env: msat_env,
        statevars: list[tuple[msat_term, msat_term]],
        trans: msat_term,
        prop: msat_term,
    ):
        self.env = env
        self.statevars = statevars
        self.trans = trans
        self.prop = prop

    def get_prop_expr(self) -> msat_term:
        pass

    def herbrandize(self) -> bool:
        pass

    def prop_fails(self) -> int:
        pass


class CondHistSpecifier(EncodingSpecifier):
    def __init__(self, env, statevars, trans, prop):
        super().__init__(env, statevars, trans, prop)
        self.nextvars: set[msat_term] = set(p[1] for p in statevars)
        self.curmap: dict[msat_term, msat_term] = dict((n, c) for (c, n) in statevars)

    def get_prop_expr(self):
        return self.prop

    def herbrandize(self):
        return False

    def prop_fails(self):
        return 0

    def get_imm_vars(self) -> list[msat_term]:
        imm_vars: list[msat_term] = []
        trans_repr = msat_term_repr(self.trans)
        for cv, nv in self.statevars:
            vars_equal = msat_term_repr(msat_make_equal(self.env, cv, nv))
            if trans_repr.count(vars_equal) == 1:
                if trans_repr.count(msat_term_repr(nv)) == 1:
                    imm_vars.append(cv)
        return imm_vars


class ProphicSpecifier(EncodingSpecifier):
    """
    This class takes an msat env and two msat_terms, 1 is the trans
    relation the other is the property as a boolean variable, it
    returns the actual property expression.
    """

    def __init__(self, env, statevars, trans, prop):
        super().__init__(env, statevars, trans, prop)
        self.prop = dict(statevars)[msat_make_not(self.env, self.prop)]

    def herbrandize(self):
        return True

    def prop_fails(self):
        return 1

    def get_imm_vars(self) -> list[msat_term]:
        imm_vars: list[msat_term] = []
        trans_repr = msat_term_repr(self.trans)
        for var in self.nextvars:
            str_var = msat_term_repr(var)
            if str_var not in trans_repr:
                imm_vars.append(self.curmap[var])
        return imm_vars

    def get_prop_expr(self):
        or_expr = self.find_or_expr(self.trans)
        for i in range(2):
            cur_term = msat_term_get_arg(or_expr, i)
            if msat_term_get_arg(cur_term, 1) == self.prop:
                return msat_term_get_arg(cur_term, 0)
            if msat_term_get_arg(cur_term, 0) == self.prop:
                return msat_term_get_arg(cur_term, 1)

    def find_or_expr(self, cur_term):
        if msat_term_is_or(self.env, cur_term):
            return cur_term
        elif msat_term_is_and(self.env, cur_term):
            for i in range(2):
                or_expr = self.find_or_expr(msat_term_get_arg(cur_term, i))
                if or_expr:
                    return or_expr
        else:
            return None
