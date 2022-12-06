
from mathsat import *

class BoolProp:
    '''
    This class takes an msat env and two msat_terms, 1 is the trans
    relation the other is the property as a boolean variable, it
    returns the actual property expression.
    '''

    def __init__(self, env: msat_env, trans: msat_term, prop: msat_term):
        self.env = env
        self.trans = trans
        self.prop = prop

    def find_prop_expr(self):
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
