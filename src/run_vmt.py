import os
from datetime import datetime
from utils import timeout, NumProph
from encoding_specifier import ProphicSpecifier, CondHistSpecifier
from ovid import Ovid
import pstats
import cProfile
from pstats import SortKey, Stats

BENCHMARKS = "../examples/benchmarks/"


TIMEOUT_TIME = 1200


def print_profile(p, key=SortKey.CUMULATIVE):
    ps = Stats(p).sort_stats(key)
    ps.print_stats()


single_good = ['../examples/benchmarks/condhist/single/array_init_ite_jump.vmt', '../examples/benchmarks/condhist/single/array_tiling_poly1.vmt', '../examples/benchmarks/condhist/single/array_two_counters_replace.vmt', '../examples/benchmarks/condhist/single/array_copy_increment_ind.vmt', '../examples/benchmarks/condhist/single/array_tiling_rewnifrev.vmt', '../examples/benchmarks/condhist/single/array_tiling_poly3.vmt', '../examples/benchmarks/condhist/single/array_copy_ind.vmt', '../examples/benchmarks/condhist/single/array_doub_access_init.vmt', '../examples/benchmarks/condhist/single/array_init_batches.vmt', '../examples/benchmarks/condhist/single/array_tiling_skipped.vmt', '../examples/benchmarks/condhist/single/array_init_upto_nondet.vmt', '../examples/benchmarks/condhist/single/array_two_counters_min_max.vmt', '../examples/benchmarks/condhist/single/array_tiling_poly5.vmt', '../examples/benchmarks/condhist/single/array_index_compl.vmt', '../examples/benchmarks/condhist/single/array_min_swap.vmt', '../examples/benchmarks/condhist/single/array_copy_inverse.vmt', '../examples/benchmarks/condhist/single/array_init_both_ends_simpl.vmt', '../examples/benchmarks/condhist/single/array_tiling_pnr3.vmt', '../examples/benchmarks/condhist/single/array_two_counters_min_max_prog.vmt', '../examples/benchmarks/condhist/single/array_copy_increment.vmt', '../examples/benchmarks/condhist/single/array_init_ite.vmt', '../examples/benchmarks/condhist/single/array_copy_sum.vmt', '../examples/benchmarks/condhist/single/array_tiling_pnr2.vmt', '../examples/benchmarks/condhist/single/array_two_counters_max_subtr.vmt', '../examples/benchmarks/condhist/single/array_init_ite_jump_two.vmt', '../examples/benchmarks/condhist/single/array_init_var.vmt', '../examples/benchmarks/condhist/single/array_init_both_ends.vmt', '../examples/benchmarks/condhist/single/array_tiling_rew.vmt', '../examples/benchmarks/condhist/single/array_init_ite_dupl.vmt', '../examples/benchmarks/condhist/single/array_init_var_plus_ind.vmt', '../examples/benchmarks/condhist/single/array_init_select_copy.vmt', '../examples/benchmarks/condhist/single/array_init_tuples.vmt', '../examples/benchmarks/condhist/single/array_tiling_pnr5.vmt', '../examples/benchmarks/condhist/single/array_min_max.vmt', '../examples/benchmarks/condhist/single/array_copy_sum_ind.vmt', '../examples/benchmarks/condhist/single/array_min_ind.vmt', '../examples/benchmarks/condhist/single/array_tiling_pnr4.vmt', '../examples/benchmarks/condhist/single/array_two_counters_init_var.vmt', '../examples/benchmarks/condhist/single/array_init_depend.vmt', '../examples/benchmarks/condhist/single/array_tiling_pr2.vmt', '../examples/benchmarks/condhist/single/array_init_double.vmt', '../examples/benchmarks/condhist/single/array_tiling_rewrev.vmt', '../examples/benchmarks/condhist/single/array_tiling_tcpy.vmt', '../examples/benchmarks/condhist/single/array_init_nondet_vars.vmt', '../examples/benchmarks/condhist/single/array_standard_password.vmt', '../examples/benchmarks/condhist/single/array_tiling_pr3.vmt', '../examples/benchmarks/condhist/single/array_init_tuples_relative.vmt', '../examples/benchmarks/condhist/single/array_init_var_plus_ind3.vmt', '../examples/benchmarks/condhist/single/array_min_swap_and_shift.vmt', '../examples/benchmarks/condhist/single/array_init_var_plus_ind2.vmt', '../examples/benchmarks/condhist/single/array_tiling_pr4.vmt', '../examples/benchmarks/condhist/single/array_tiling_tcpy2.vmt', '../examples/benchmarks/condhist/single/array_tiling_tcpy3.vmt', '../examples/benchmarks/condhist/single/array_tiling_pr5.vmt', '../examples/benchmarks/condhist/single/array_init_reverse.vmt', '../examples/benchmarks/condhist/single/array_standard_partition.vmt', '../examples/benchmarks/condhist/single/array_init_depend_incr.vmt', '../examples/benchmarks/condhist/single/array_copy.vmt', '../examples/benchmarks/condhist/single/array_init_both_ends2.vmt', '../examples/benchmarks/condhist/single/array_partial_init.vmt', '../examples/benchmarks/condhist/single/array_append2_array_horn.vmt', '../examples/benchmarks/condhist/single/array_tiling_rewnif.vmt', '../examples/benchmarks/condhist/single/array_init_var_ind.vmt', '../examples/benchmarks/condhist/single/array_init_drop.vmt', '../examples/benchmarks/condhist/single/array_init_batches_ind.vmt', '../examples/benchmarks/condhist/single/array_tripl_access_init.vmt', '../examples/benchmarks/condhist/single/array_tiling_rewnifrev2.vmt', '../examples/benchmarks/condhist/single/array_tripl_access_init_const.vmt', '../examples/benchmarks/condhist/single/array_init_both_ends_simpl_const.vmt', '../examples/benchmarks/condhist/single/array_two_counters_init_const.vmt', '../examples/benchmarks/condhist/single/array_init_ite_jump_two_const.vmt', '../examples/benchmarks/condhist/single/array_init_double_const.vmt', '../examples/benchmarks/condhist/single/array_split_02.vmt', '../examples/benchmarks/condhist/single/array_split_03.vmt', '../examples/benchmarks/condhist/single/array_init_const.vmt', '../examples/benchmarks/condhist/single/array_split_15.vmt', '../examples/benchmarks/condhist/single/array_init_const_ind.vmt', '../examples/benchmarks/condhist/single/array_min_swap_const.vmt', '../examples/benchmarks/condhist/single/array_split_04.vmt', '../examples/benchmarks/condhist/single/array_split_11.vmt', '../examples/benchmarks/condhist/single/array_init_batches_const.vmt']

single_bad = {'../examples/benchmarks/condhist/single/array_min.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_init_monot_ind.vmt': 'No Axiom Violations!', '../examples/benchmarks/condhist/single/array_nonlin_init_depend.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_nonlin_init_mult.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_single_elem_increm.vmt': 'No Axiom Violations!', '../examples/benchmarks/condhist/single/array_init_select.vmt': 'No Axiom Violations!', '../examples/benchmarks/condhist/single/array_init_nondet_vars2.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_nonlin_square.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_even_odd_1.vmt': 'b\'(error "line 1 column 690: unknown constant /2")\\n\'', '../examples/benchmarks/condhist/single/array_init_nondet_var_mult.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/single/array_even_odd_2.vmt': 'b\'(error "line 1 column 702: unknown constant /2")\\n\'', '../examples/benchmarks/condhist/single/array_split_16.vmt': 'b\'(error "line 1 column 1453: unknown constant ConstArr (Int) ")\\n\'', '../examples/benchmarks/condhist/single/array_split_17.vmt': 'b\'(error "line 1 column 652: unknown constant /2")\\n(error "line 1 column 949: unknown constant /2")\\n\'', '../examples/benchmarks/condhist/single/array_split_10.vmt': "IC3IA gives 'Unknown'"}

mult_good = ['../examples/benchmarks/condhist/multiple/array_init_addvar6.vmt', '../examples/benchmarks/condhist/multiple/array_max_min.vmt', '../examples/benchmarks/condhist/multiple/array_init_reverse_mult.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm.vmt', '../examples/benchmarks/condhist/multiple/array_nest_split_01.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar7.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar5.vmt', '../examples/benchmarks/condhist/multiple/array_nest_split_03.vmt', '../examples/benchmarks/condhist/multiple/array_tiling_poly2.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar4.vmt', '../examples/benchmarks/condhist/multiple/array_nest_split_02.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_two_arrs_const.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar3.vmt', '../examples/benchmarks/condhist/multiple/array_nest_split_05.vmt', '../examples/benchmarks/condhist/multiple/array_init_both_ends_multiple.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_const.vmt', '../examples/benchmarks/condhist/multiple/array_tiling_poly4.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar2.vmt', '../examples/benchmarks/condhist/multiple/array_nest_split_04.vmt', '../examples/benchmarks/condhist/multiple/array_init_addvar.vmt', '../examples/benchmarks/condhist/multiple/array_max_min_approx.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_two_arrs_antisym.vmt', '../examples/benchmarks/condhist/multiple/array_horn_copy2.vmt', '../examples/benchmarks/condhist/multiple/array_bubble_sort.vmt', '../examples/benchmarks/condhist/multiple/array_init_doubl3.vmt', '../examples/benchmarks/condhist/multiple/array_init_doubl2.vmt', '../examples/benchmarks/condhist/multiple/array_bubble_sort_rev.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_twice_const.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_two_arrs.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_twice.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_add.vmt', '../examples/benchmarks/condhist/multiple/array_init_doubl.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_nest_4.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_nest_5.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_nest_1.vmt', '../examples/benchmarks/condhist/multiple/array_init_increm_two_arrs_antisym_const.vmt', '../examples/benchmarks/condhist/multiple/array_min_and_copy_shift.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_nest_2.vmt', '../examples/benchmarks/condhist/multiple/array_min_and_copy_inverse.vmt', '../examples/benchmarks/condhist/multiple/array_min_and_copy.vmt', '../examples/benchmarks/condhist/multiple/array_hybr_nest_3.vmt']

mult_bad = {'../examples/benchmarks/condhist/multiple/array_init_pair_sum_const.vmt': '', '../examples/benchmarks/condhist/multiple/array_double_inverse.vmt': "name 'equal_enodej' is not defined", '../examples/benchmarks/condhist/multiple/array_init_pair_sum.vmt': '', '../examples/benchmarks/condhist/multiple/array_copy_nondet_add.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_tiling_poly6.vmt': '', '../examples/benchmarks/condhist/multiple/array2dim_init.vmt': '', '../examples/benchmarks/condhist/multiple/array_standard_copy4.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_symmetr_swap.vmt': "name 'equal_enodej' is not defined", '../examples/benchmarks/condhist/multiple/array_init_symmetr_swap_const.vmt': "name 'equal_enodej' is not defined", '../examples/benchmarks/condhist/multiple/array_equiv_1.vmt': "in method 'msat_term_get_type', argument 1 of type 'msat_term'", '../examples/benchmarks/condhist/multiple/array_init_and_copy.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_and_copy_inverse.vmt': '', '../examples/benchmarks/condhist/multiple/array_equiv_2.vmt': "True, False or Z3 Boolean expression expected. Received T of type <class 'str'>", '../examples/benchmarks/condhist/multiple/array_equiv_3.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array2dim_rec2.vmt': '', '../examples/benchmarks/condhist/multiple/array2dim_init_j.vmt': '', '../examples/benchmarks/condhist/multiple/array_hybr_sum.vmt': '', '../examples/benchmarks/condhist/multiple/array_two_counters_add.vmt': '', '../examples/benchmarks/condhist/multiple/array_max_reverse_min.vmt': '', '../examples/benchmarks/condhist/multiple/array2dim_rec1.vmt': '', '../examples/benchmarks/condhist/multiple/array2dim_init_i.vmt': '', '../examples/benchmarks/condhist/multiple/array_max_min_shift.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/multiple/array_zero_sum_m2.vmt': '', '../examples/benchmarks/condhist/multiple/array_init_pair_symmetr2.vmt': '', '../examples/benchmarks/condhist/multiple/array_init_pair_symmetr3.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_min_and_copy_shift_sum_add.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_nondet_vars_plus_ind.vmt': '', '../examples/benchmarks/condhist/multiple/array_init_pair_symmetr4.vmt': "IC3IA gives 'Unknown'", '../examples/benchmarks/condhist/multiple/array_two_counters_sum.vmt': "name 'equal_enodej' is not defined", '../examples/benchmarks/condhist/multiple/array2dim_copy.vmt': '', '../examples/benchmarks/condhist/multiple/array_min_and_copy_shift_sum.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_and_copy_const.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_pair_symmetr.vmt': "'NoneType' object has no attribute 'children'", '../examples/benchmarks/condhist/multiple/array_init_both_ends_multiple_sum.vmt': ''}


def run_benchmark(bench_set, spec_type, filename: str):
    filename = os.path.join(bench_set, filename)
    with timeout(TIMEOUT_TIME):
        try:
            # profile = cProfile.Profile()
            # profile.enable()
            then = datetime.now()
            print(f"-----{filename}-----")
            problem = Ovid(filename, spec_type, NumProph(), debug=False)
            problem.run_loop()
            time = datetime.now() - then
            print(f"Total time: {time}")
            mult_good.append(filename)
            # profile.disable()
            # breakpoint()
            # print_profile(profile)
        except TimeoutError as v:
            print("timeout")
            mult_bad[filename] = str(v)
            return
        except Exception as v:
            mult_bad[filename] = str(v)
            raise v
            return
        except KeyboardInterrupt as v:
            mult_bad[filename] = str(v)
            return


PROPHICSINGLE = os.path.join(BENCHMARKS, "freqhorn")
CHSINGLE = os.path.join(BENCHMARKS, "condhist", "single")
CHMULTIPLE = os.path.join(BENCHMARKS, "condhist", "multiple")
CHCCOMP = os.path.join(BENCHMARKS, "chc-comp")
PARAMETRIC = os.path.join(BENCHMARKS, "parametric-protocols")

tries = 20
i = 0
# for fname in os.listdir(CHSINGLE):
#     if i > tries:
#         break
#     if fname == "array_init_disj_const.vmt":
#         # segfault before first run of ic3ia?
#         continue
#     filename = os.path.join(CHSINGLE, fname)
#     if filename in good or filename in bad:
#         continue
#     try:
#         i += 1
#         run_benchmark(CHSINGLE, CondHistSpecifier, fname)
#     except Exception as e:
#         print(e)

# for fname in os.listdir(CHMULTIPLE):
#     if i > tries:
#         break
#     filename = os.path.join(CHMULTIPLE, fname)
#     if filename in mult_good:
#         continue
#     try:
#         i += 1
#         run_benchmark(CHMULTIPLE, CondHistSpecifier, fname)
#     except Exception as e:
#         print(e)

# print("GOOD")
# print(mult_good)
# print("BAD")
# print(mult_bad)
# print(i)
# breakpoint()

#run_benchmark(CHSINGLE, CondHistSpecifier, "array_copy.vmt")

#breakpoint()

run_benchmark(CHMULTIPLE, CondHistSpecifier, "array_hybr_sum.vmt")
#run_benchmark(CHCCOMP, CondHistSpecifier, "001.vmt")
#run_benchmark(PROPHICSINGLE, ProphicSpecifier, "array_copy.vmt")
