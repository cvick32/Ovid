import signal
import sys
import subprocess

from io import StringIO
from contextlib import contextmanager

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
from mathsat import *
from z3_defs import And, Or, Implies, Write, Read, Not, ArrWrite, ArrRead, ConstArr
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


def run_smt_interpol_from_sexprs(sexprs: list[str], vmt):
    with open("interp-out.smt2", "w+") as f:
        f.write("\n".join(sexprs))
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
            NUM_INTERPS = 2  # only consider last X interpolants
            interp_sexpr = Translate().parse_sexpr_string(out_str[1])[0]
            interps = interp_sexpr.body[-NUM_INTERPS:]
            sexprs = cleanup_interp(
                interps, (len(interp_sexpr.body) - NUM_INTERPS) + 1, vmt
            )
            return get_interp_clauses_from_sexprs(sexprs)
        else:
            print("Counterexample was SAT in SMTInterpol!")
            return "SAT"
    else:
        print("SMTInterpol failed!")


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


def parse_vmt(src: IO, spec: type, tool) -> VmtModel:
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
    ret = VmtModel(env, statevars, init, trans, props, spec, tool)
    return ret


def cleanup_interp(sexprs, start, vmt):
    los = []
    for i, sexpr in enumerate(sexprs):
        min = start + i
        max = min + 1
        sexpr.cleanup_let_statements()
        sexpr = sexpr.writeable_string()
        sexpr = sexpr.replace("(<= 0 0)", "")
        sexpr = sexpr.replace("(< 0 0)", "")
        sexpr = sexpr.replace(f"-{min}", "")
        sexpr = sexpr.replace(f"-{max}", "_next")
        sexpr = Translate().parse_sexpr_string(sexpr)[0]
        los.append(parse_sexpr_to_z3(sexpr, vmt))
    return los


def get_interp_clauses_from_sexprs(sexprs):
    clauses = set()
    for z3_sexpr in sexprs:
        get_base_clauses(z3_sexpr, clauses)
    return clauses


def get_base_clauses(z3_sexpr, clauses):
    for child in z3_sexpr.children():
        if str(child.decl()) in ["And", "Or", "Implies"]:
            get_base_clauses(child, clauses)
        else:
            clauses.add(child)


class NumProph:
    def __init__(self):
        self.num_proph = 0

    def set_next_proph_num(self):
        self.num_proph += 1

    def get_num_proph(self):
        return self.num_proph


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


class Sexpr:
    def __init__(self, head=None, body=None):
        if head is None:
            self.head = ""
        else:
            self.head = head
        if body is None:
            self.body = []
        else:
            self.body = body

    def add_head(self, str_head):
        self.head = str_head

    def add_body(self, body_part):
        self.body.append(body_part)

    def add_to_front_of_body(self, body_part):
        new_body = [body_part] + self.body.copy()
        self.body = new_body

    def extend_body(self, body_part):
        self.body.extend(body_part)

    def replace_all_in_current_body(self, old, new):
        new_body = []
        for b in self.body:
            if b == old:
                new_body.append(new)
            else:
                new_body.append(b)
        self.body = new_body

    def replace_all_in_body(self, old, new):
        new_body = []
        for b in self.body:
            if b == old:
                new_body.append(new)
            else:
                new_body.append(b)
            if isinstance(b, Sexpr):
                b.replace_all_in_body(old, new)
        self.body = new_body

    def replace_heads_in_all_body(self, old_head, new_head):
        if self.head == old_head:
            self.head = new_head
        for b in self.body:
            if isinstance(b, Sexpr):
                b.replace_heads_in_all_body(old_head, new_head)

    def remove_nested_single_ands(self):
        if self.head == "and" and len(self.body) == 1:
            if isinstance(self.body[0], Sexpr):
                self.head = self.body[0].head
                self.body = self.body[0].body
            else:
                self.head = self.body[0]
                self.body = []
        for b in self.body:
            if isinstance(b, Sexpr):
                b.remove_nested_single_ands()

    def cleanup_let_statements(self):
        # call this one
        self._simplify_all_let_expressions([])
        self._remove_all_let()

    def _simplify_all_let_expressions(self, lets):
        for let in lets:
            self.replace_all_in_body(let.head, let.body[0])
        new_body = []
        if self.head == "let":
            lets.extend(self.body[0].body)
            self.body[1]._simplify_all_let_expressions(lets)
            new_body.append(self.body[1])
            self = self.body[1]
        else:
            for b in self.body:
                if isinstance(b, Sexpr):
                    b._simplify_all_let_expressions(lets)

    def _remove_all_let(self):
        new_body = []
        for b in self.body:
            if isinstance(b, Sexpr):
                if b.head == "let":
                    b.body[1]._remove_all_let()
                    new_body.append(b.body[1])
                else:
                    b._remove_all_let()
                    new_body.append(b)
            else:
                new_body.append(b)
        if self.head == "let":
            new_head = new_body[1].head
            new_body = new_body[1].body
        else:
            new_head = self.head
        self.head = new_head
        self.body = new_body

    def __eq__(self, other):
        if isinstance(other, Sexpr):
            return self.head == other.head and self.body == other.body

    def __hash__(self):
        return hash(self.head) + hash(tuple(self.body))

    def writeable_string(self):
        s = self.__repr__()
        return s.replace("'", "")

    def __repr__(self):
        body_text = ""
        for i, b in enumerate(self.body):
            if i == len(self.body) - 1:
                body_text += f"{b.__repr__()}"
            else:
                body_text += f"{b.__repr__()} "
        body_text = body_text.replace("(None )", "()")
        return f"({self.head} {body_text})"


def get_arg_z3_expr(sexpr, vmt_model):
    var_name_to_z3 = vmt_model.var_str_to_z3_def
    next_var_name_to_z3 = vmt_model.var_str_to_next_z3_def
    if isinstance(sexpr, Sexpr) or (
        sexpr not in var_name_to_z3 and sexpr not in next_var_name_to_z3
    ):
        return parse_sexpr_to_z3(sexpr, vmt_model)
    else:
        if sexpr in next_var_name_to_z3:
            return next_var_name_to_z3[sexpr]
        return var_name_to_z3[sexpr]


def get_args(sexpr, vmt_model):
    args = []
    for i in range(len(sexpr.body)):
        s_body = sexpr.body[i]
        if not isinstance(s_body, str) and s_body.head == "as":
            args.append(None)
            continue
        args.append(get_arg_z3_expr(s_body, vmt_model))
    return args


def parse_sexpr_to_z3(sexpr, vmt_model):
    if isinstance(sexpr, str):
        if sexpr.strip("-").isnumeric():
            return int(sexpr)
        elif sexpr == "false":
            return False
        elif sexpr == "true":
            return True
    head = sexpr.head
    args = get_args(sexpr, vmt_model)
    if head == "store":
        if str(args[0].sort()) == "ArrOfArr":
            return ArrWrite(args[0], args[1], args[2])
        else:
            return Write(args[0], args[1], args[2])
    elif head == "select":
        if str(args[0].sort()) == "ArrOfArr":
            return ArrRead(args[0], args[1])
        else:
            return Read(args[0], args[1])
    elif head == "+":
        # how to generate this automatically?
        if len(args) == 3:
            return args[0] + args[1] + args[2]
        else:
            return args[0] + args[1]
    elif head == "-":
        if len(args) == 3:
            return args[0] - args[1] - args[2]
        elif len(args) == 1:
            return args[0] * -1
        else:
            return args[0] - args[1]
    elif head == "*":
        return args[0] * args[1]
    elif head == "=>":
        return Implies(args[0], args[1])
    elif head == "or":
        return Or(args[0], args[1])
    elif head == "not":
        return Not(args[0])
    elif head == ">=":
        return args[0] >= args[1]
    elif head == "<=":
        return args[0] <= args[1]
    elif head == "<":
        return args[0] < args[1]
    elif head == ">":
        return args[0] > args[1]
    elif head == "=":
        return args[0] == args[1]
    elif head == "ite":
        return And(Implies(args[0], args[1]), Implies(Not(args[0]), args[2]))
    elif head == "and":
        if len(args) == 1:
            return args[0]
        return And(args[0], args[1])
    elif head == "mod":
        return args[0] % args[1]
    elif head == "Constarr":
        return ConstArr(args[1])
    elif head == "" and sexpr.body[0].head == "as":
        return ConstArr(sexpr.body[1])
    else:
        print(f"Unimplemented function call: {head}")


def parse_actions_vmt(src: IO, spec: type) -> VmtModel:
    env = msat_create_env()
    val = msat_annotated_list_from_smtlib2(env, src.read())

    assert val is not None
    terms, annots = val

    def unquote(n):
        if n.startswith("|"):
            n = n[1:-1]
        return n

    init = msat_make_true(env)
    trans = msat_make_false(env)
    props = msat_make_true(env)
    statevars = []
    actions = []
    extra_annotated = []
    for i, t in enumerate(terms):
        key = annots[2 * i]
        if key == "init":
            init = msat_make_and(env, init, t)
        elif key == "action":
            trans = msat_make_or(env, trans, t)
            actions.append(t)
        elif key == "invar-property":
            props = msat_make_and(env, props, t)
        elif key == "next":
            name = unquote(annots[2 * i + 1])
            d = msat_find_decl(env, name)
            if MSAT_ERROR_DECL(d):
                d = msat_declare_function(env, name, msat_term_get_type(t))
            n = msat_make_constant(env, d)
            statevars.append((t, n))
    # for action in actions:
    #     neg = msat_make_not(env, action)
    #     for a2 in actions:
    #         if action != a2:
    #             # enforcing only one action may be true per step
    #             # action -> not(every_other_action)
    #             trans = msat_make_and(env, trans, msat_make_or(env, neg, msat_make_not(env, a2)))

# with open("../examples/benchmarks/parametric-protocols/paxos_forall.vmt") as f:
#     pp = parse_vmt(f, None)


