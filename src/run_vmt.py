import os
from datetime import datetime
from utils import timeout, parse_vmt
from encoding_specifier import ProphicSpecifier, CondHistSpecifier
from ovid import Ovid

BENCHMARKS = "../examples/benchmarks/"


TIMEOUT_TIME = 1200


def run_benchmark(bench_set, spec_type, filename: str):
    filename = os.path.join(bench_set, filename)
    with timeout(TIMEOUT_TIME):
        try:
            then = datetime.now()
            print(f"-----{filename}-----")
            problem = Ovid(filename, spec_type, debug=True)
            problem.run_loop()
            time = datetime.now() - then
            print(f"Total time: {datetime.now() - then}")
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

# for f in os.listdir("../examples/benchmarks/freqhorn"):
#     try:
#         run_aeval_single("Ovid", num_bench=None, only_run=f)
#     except Exception as e:
#         print(e)


run_benchmark(CHSINGLE, CondHistSpecifier, "array_copy.vmt")
# run_benchmark(PROPHICSINGLE, ProphicSpecifier, "array_copy.vmt")
