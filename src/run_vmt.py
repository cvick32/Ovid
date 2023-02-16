import os
from datetime import datetime
from utils import timeout, parse_vmt
from encoding_specifier import ProphicSpecifier, CondHistSpecifier
from ovid import Ovid
import pstats
import cProfile
from pstats import SortKey, Stats

BENCHMARKS = "../examples/benchmarks/"


TIMEOUT_TIME = 1200

def print_profile(p):
    sortby = SortKey.CUMULATIVE
    ps = Stats(p).sort_stats(sortby)
    ps.print_stats()

def run_benchmark(bench_set, spec_type, filename: str):
    filename = os.path.join(bench_set, filename)
    with timeout(TIMEOUT_TIME):
        try:
            profile = cProfile.Profile()
            profile.enable()
            then = datetime.now()
            print(f"-----{filename}-----")
            problem = Ovid(filename, spec_type, debug=True)
            problem.run_loop()
            time = datetime.now() - then
            print(f"Total time: {datetime.now() - then}")
            profile.disable()
            #print_profile(profile)
        except TimeoutError:
            print("timeout")
            return
        except Exception as v:
            raise v
            return
        except KeyboardInterrupt as v:
            return


PROPHICSINGLE = os.path.join(BENCHMARKS, "freqhorn")
CHSINGLE = os.path.join(BENCHMARKS, "condhist", "single")
CHMULTIPLE = os.path.join(BENCHMARKS, "condhist", "multiple")

# for fname in os.listdir(CHSINGLE):
#     try:
#         run_benchmark(CHSINGLE, CondHistSpecifier, fname)
#     except Exception as e:
#         print(e)


#run_benchmark(CHSINGLE, CondHistSpecifier, "array_copy.vmt")

run_benchmark(CHMULTIPLE, CondHistSpecifier, "array_hybr_sum.vmt")
# run_benchmark(PROPHICSINGLE, ProphicSpecifier, "array_copy.vmt")
