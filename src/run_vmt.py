import os

import shutil
from datetime import datetime

from utils import timeout, parse_vmt
from encoding_specifier import ProphicSpecifier, CondHistSpecifier
from ovid import Ovid

BENCHMARKS = "../examples/benchmarks/"

SINGLE = os.path.join(BENCHMARKS, "freqhorn")
CHSINGLE = os.path.join(BENCHMARKS, "condhist", "single")
MULTIPLE = os.path.join(BENCHMARKS, "aeval-bench-horn-multiple")

TIMEOUT_TIME = 1200


def run_benchmark(filename: str):
    with timeout(TIMEOUT_TIME):
        try:
            then = datetime.now()
            print(f"-----{filename}-----")
            problem = Ovid(filename, CondHistSpecifier, debug=True)
            problem.run_loop()
            time = datetime.now() - then
            print(f"Total time: {datetime.now() - then}")
            breakpoint()
        except TimeoutError:
            print("timeout")
            return
        except Exception as v:
            raise v
            return
        except KeyboardInterrupt as v:
            return

def run_aeval_single(tool_name, num_bench, only_run):
    if num_bench is not None:
        num = num_bench
    else:
        num = 1000
    if tool_name == "Ovid":
        run_benchmark(os.path.join(CHSINGLE, only_run))
    else:
        raise ValueError(
            f"Tool {tool_name} not found. Are you on the correct branch?\nOnly Quic3, GSpacer, and CondHist are available on this branch."
        )


def run_aeval_multiple(tool_name, num_bench, only_run):
    if num_bench is not None:
        num = num_bench
    else:
        num = 1000
    if tool_name == "Ovid":
        run_benchmark(MULTIPLE, only_run)
    else:
        raise ValueError(
            f"Tool {tool_name} not found. Are you on the correct branch?\nOnly Quic3, GSpacer, and CondHist are available on this branch."
        )

# for f in os.listdir("../examples/benchmarks/freqhorn"):
#     try:
#         run_aeval_single("Ovid", num_bench=None, only_run=f)
#     except Exception as e:
#         print(e)


run_aeval_single("Ovid", num_bench=None, only_run="array_copy.vmt")
