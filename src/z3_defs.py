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



