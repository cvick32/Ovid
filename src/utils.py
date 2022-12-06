import re
import signal
import os
import sys
import subprocess

import pprint
from io import StringIO
from contextlib import contextmanager
from datetime import datetime

from vmt import VmtModel
from smt_defs import smt_abstract_defs
from mathsat import (
    msat_create_env,
    msat_annotated_list_from_smtlib2,
    msat_make_true,
    msat_make_and,
    msat_find_decl,
    MSAT_ERROR_DECL,
    msat_declare_function,
    msat_term_get_type,
    msat_make_constant,
)

from typing import IO


class Capturing(list):
    def __enter__(self):
        self._stdout = sys.stdout
        sys.stdout = self._stringio = StringIO()
        return self

    def __exit__(self, *args):
        self.extend(self._stringio.getvalue().splitlines())
        del self._stringio  # free up some memory
        sys.stdout = self._stdout


@contextmanager
def timeout(time):
    # Register a function to raise a TimeoutError on the signal.
    signal.signal(signal.SIGALRM, raise_timeout)
    # Schedule the signal to be sent after ``time``.
    signal.alarm(time)

    try:
        yield
    except TimeoutError:
        print("Timed Out")
    finally:
        # Unregister the signal so it won't be triggered
        # if the timeout is not reached.
        signal.signal(signal.SIGALRM, signal.SIG_IGN)


def raise_timeout(signum, frame):
    raise TimeoutError


def run_smt_interpol_from_sexprs(sexprs):
    with open("interp-out.smt2", "w+") as f:
        for sexpr in sexprs:
            if isinstance(sexpr, Sexpr):
                s = sexpr.writeable_string()
            else:
                s = sexpr
            f.write(s + "\n")
    print("Running SMTInterpol...")
    out = subprocess.run(
        [
            "java",
            "-jar",
            "../solvers/smtinterpol.jar",
            "-w",
            "-no-success",
            "interp-out.smt2",
        ],
        capture_output=True,
    )
    if out.returncode == 0:
        out_str = out.stdout.decode().split("\n")
        if out_str[0] == "unsat":
            return out_str[1]
        else:
            print("Counterexample was SAT in SMTInterpol!")
            return "SAT"
            # raise ValueError("Counterexample was SAT in SMTInterpol!")
    else:
        print("SMTInterpol failed!")
        # raise ValueError("SMTInterpol failed!")

def abstract_vmt(src: IO) -> str:
    vmt = src.read()
    vmt = vmt.replace("(Array Int Int)", "Arr")
    vmt = vmt.replace("(Array Int (Array Int Int))", "ArrOfArr")
    vmt = vmt.replace("(select", "(read_int_int")
    vmt = vmt.replace("(store", "(write_int_int")
    new_file = "out.vmt"
    with open(new_file, "w+") as f:
        for defi in smt_abstract_defs:
            f.write(defi)
        f.write(vmt)
    return new_file

def parse_vmt(src: IO) -> VmtModel:
    env = msat_create_env()
    val = msat_annotated_list_from_smtlib2(env, src.read())

    assert val is not None
    terms, annots = val

    def unquote(n):
        if n.startswith("|"):
            n = n[1:-1]
        return n

    init = msat_make_true(env)
    trans = msat_make_true(env)
    props = msat_make_true(env)
    statevars = []
    extra_annotated = []
    for i, t in enumerate(terms):
        key = annots[2 * i]
        if key == "init":
            init = msat_make_and(env, init, t)
        elif key == "trans":
            trans = msat_make_and(env, trans, t)
        elif key == "invar-property":
            props = msat_make_and(env, props, t)
        elif key == "next":
            name = unquote(annots[2 * i + 1])
            d = msat_find_decl(env, name)
            if MSAT_ERROR_DECL(d):
                d = msat_declare_function(env, name, msat_term_get_type(t))
            n = msat_make_constant(env, d)
            statevars.append((t, n))
        else:
            extra_annotated.append((t, key, annots[2 * i + 1]))
    ret = VmtModel(
        env, statevars, init, trans, props
    )
    return ret


class Translate:
    def parse_sexpr_string(self, str):
        complete_sexp = []
        working_sexp = []
        cur_str = ""
        count = 0
        head = False
        comment = False
        for c in str:
            if comment and not c == "\n":
                continue
            elif comment and c == "\n":
                comment = False
            elif c == ";":
                comment = True
            elif c == "(":
                working_sexp.append(Sexpr())
                count += 1
                head = True
            elif c == ")":
                cur_sexp = working_sexp[-1]
                count -= 1
                cur_str, head = self.add_str_to_sexp(cur_str, cur_sexp, head)
                if count == 0:
                    complete_sexp.append(cur_sexp)
                else:
                    working_sexp[-2].add_body(cur_sexp)
                working_sexp = working_sexp[:-1]
                head = False
            elif c == " ":
                cur_sexp = working_sexp[-1]
                cur_str, head = self.add_str_to_sexp(cur_str, cur_sexp, head)
            elif not c == "\n" and not c == "\t":
                cur_str += c
        return complete_sexp

    def add_str_to_sexp(self, s, sexp, head_flag):
        if s == "":
            return "", head_flag
        if head_flag:
            sexp.add_head(s)
            head_flag = False
        else:
            sexp.add_body(s)
            head_flag = False
        return "", head_flag

    def get_sexprs_from_filename(self, filename):
        with open(filename) as f:
            return self.parse_sexpr_string(f.read())


class ENode:
    def __init__(self, head, args=[], z3_obj=None):
        self.head = head
        self.args = args
        str_arg = ""
        if self.args:
            str_arg = " " + str(self.args).replace("[", "").replace("]", "")
        self.repr_str = f"({str(self.head)}{str_arg})"
        if z3_obj is None:
            self.z3_obj = head
        else:
            self.z3_obj = z3_obj

    def var_string(self):
        return str(self.head)

    def __repr__(self):
        return self.repr_str

    def __hash__(self):
        return hash(self.__repr__())

    def __eq__(self, other):
        try:
            return self.repr_str == other.repr_str
        except Exception:
            return False
