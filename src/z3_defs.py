from z3 import (
    Sort,
    IntSort,
    BoolSort,
    ArraySort,
    Function,
    Const,
    DeclareSort,
    Not,
    And,
    Implies,
    Or,
    substitute,
    UserPropagateBase,
    SimpleSolver,
    ExprRef,
    IntNumRef
)


Val = IntSort()
Pos = IntSort()

Arr = DeclareSort("Arr")
ArrOfArr = DeclareSort("ArrOfArr")
Bool = BoolSort()

ConstArr = Function("ConstArr", Val, Arr)
Read = Function("read_int_int", Arr, Pos, Val)
ArrRead = Function("read_int_arr", ArrOfArr, Pos, Arr)

Write = Function("write_int_int", Arr, Pos, Val, Arr)
ArrWrite = Function("write_int_arr", ArrOfArr, Pos, Arr, ArrOfArr)

all_sorts = [Arr, ArrOfArr]
all_funcs = [ConstArr, Read, ArrRead, ArrWrite, Write]

class PropagateSolver(UserPropagateBase):

    def __init__(self):
        self.diseqs = set()
        self.eqs = set()
        self.seen = set()
        ss = SimpleSolver()
        super().__init__(ss)

    def add_assertion(self, fm):
        self.solver.add(fm)

    def add_array_exprs(self, expr, loc_or_val=False):
        '''
        heuristic of what expressions we actually want to register
        '''
        if len(expr.children()) == 0:
            if expr.sort() in [Arr, ArrOfArr]:
                pass
            elif loc_or_val:
                self.add(expr)
        elif expr.decl() in [Write, Read, ArrWrite, ArrRead, ConstArr]:
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
        for expr in self.solver.assertions():
            self.add_array_exprs(expr)
        return self.solver.check()

    def get_model(self):
        return self.solver.model()

    def eq_override(self, arg1, arg2):
        self.eqs.add(tuple([arg1, arg2]))
        self.eqs.add(tuple([arg2, arg1]))
        self.seen.add(arg1)
        self.seen.add(arg2)

    def diseq_override(self, arg1, arg2):
        self.diseqs.add(tuple([arg1, arg2]))
        self.diseqs.add(tuple([arg2, arg1]))
        self.seen.add(arg1)
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
            return self.next(potential)

    def is_var_expr(self, expr):
        return (isinstance(expr, ExprRef)) and not(isinstance(expr, IntNumRef)) and all(self.is_var_expr(c) for c in expr.children())

    def check_roots_equal(self, ze1, ze2):
        return self.solver.root(ze1).get_id() == self.solver.root(ze2).get_id()

    def next_is_root(self, expr):
        return self.solver.next(expr).get_id() == self.solver.root(expr).get_id()

    def get_root(self, expr):
        return self.solver.root(expr)
