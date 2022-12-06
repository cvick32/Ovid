smt_abstract_defs = [
    "(declare-sort Arr 0)",
    "(declare-sort ArrOfArr 0)",
    "(declare-fun ConstArr (Int) Arr)",
    "(declare-fun read_int_int (Arr Int) Int)",
    "(declare-fun read_int_arr (ArrOfArr Int) Arr)",
    "(declare-fun write_int_arr (ArrOfArr Int Arr) ArrOfArr)",
    "(declare-fun write_int_int (Arr Int Int) Arr)",
]
