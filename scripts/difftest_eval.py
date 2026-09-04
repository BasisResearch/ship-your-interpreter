#!/usr/bin/env python3
"""difftest_eval — evaluate the encoder's emitted term on a real execution.

`experiments/smt/DIFFTEST-PLAN.md` phase 3, as the plan states it:

    1. take the entry state from the trace, assert it as `s0`;
    2. pin every summary application from its observed `(pre, post)` pair;
    3. `(get-value ...)` the exit register file from `state_exit`;
    4. compare against the trace's registers at the stop.

Done by DIRECT EVALUATION rather than through Z3. With `s0` ground and every
summary pinned the whole term is closed, so there is nothing to solve; and
evaluating it a step at a time gives what a `get-value` on `state_exit` cannot —
the ability to check EVERY intermediate state against the machine, and to name
the binding where the two first diverge.

What is evaluated is the encoder's own emitted text (`<bmc>/queries/<f>.smt2`),
so this is not a second model of the machine. It is an interpreter for the small
closed SMT-LIB fragment the encoder emits, and its own faithfulness is checked
two ways: `--selfcheck` replays every state it computes against Z3, and the
lockstep drive means each straight-line state it produces is compared with the
machine at that instruction anyway.

The fragment, in full (anything else raises rather than being guessed at):
  values     `#x…` literals, `true`, `false`
  states     `mst`, `mm`, `rr`
  arrays     `select`, `store`
  bitvector  bvadd bvsub bvand bvor bvxor bvshl bvlshr bvashr
             bvslt bvsle bvsgt bvsge bvult bvule bvugt bvuge
             `(_ extract h l)`, `(_ zero_extend n)`, `(_ sign_extend n)`, `concat`
  logic      ite and or not = =>
  macros     whatever the preamble `define-fun`s (ld1 ld2 ld4 ld8 ld1s ld2s ld4s w32)
  opaque     unmodelled_step, callee_*, loop_*, icall_*, idisp_*  → the trace
"""
import sys

M64 = (1 << 64) - 1


# ------------------------------------------------------------------ s-exprs
def tokenize(s):
    return s.replace("(", " ( ").replace(")", " ) ").split()


def parse_all(text):
    """Every top-level form, as nested lists of str."""
    out, stack = [], []
    for t in tokenize(text):
        if t == "(":
            stack.append([])
        elif t == ")":
            f = stack.pop()
            (stack[-1] if stack else out).append(f)
        else:
            (stack[-1] if stack else out).append(t)
    if stack:
        raise ValueError("unbalanced s-expression")
    return out


# ------------------------------------------------------------------- values
class RA:
    """A register array: 33 slots (x0..x31 plus the encoder's `pcIdx` 32)."""
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v

    def store(self, i, x):
        w = list(self.v)
        while len(w) <= i:
            w.append(0)
        w[i] = x & M64
        return RA(tuple(w))

    def sel(self, i):
        return self.v[i] if i < len(self.v) else 0


class MA:
    """A byte array: an explicit dict over a fallback function.

    The fallback is the machine's memory as the trace and the ELF image know it;
    an address neither knows is UNKNOWN and is recorded rather than defaulted,
    because defaulting it to zero would let a load of uninitialised memory agree
    with the encoder by accident."""
    __slots__ = ("d", "base", "unknown")

    def __init__(self, d, base, unknown):
        self.d, self.base, self.unknown = d, base, unknown

    def store(self, a, b):
        d = dict(self.d)
        d[a & M64] = b & 0xFF
        return MA(d, self.base, self.unknown)

    def sel(self, a):
        a &= M64
        if a in self.d:
            return self.d[a]
        v = self.base(a)
        if v is None:
            self.unknown.add(a)
            return 0
        return v


class St:
    __slots__ = ("mem", "regs")

    def __init__(self, mem, regs):
        self.mem, self.regs = mem, regs


class EvalError(Exception):
    pass


# ---------------------------------------------------------------- the query
class Query:
    """`<bmc>/queries/<field>.smt2`, indexed for lazy evaluation."""

    def __init__(self, text):
        self.binds = {}          # name -> term
        self.sorts = {}          # name -> 'Bool' | 'MState'
        self.macros = {}         # name -> (params, body)
        self.order = []
        self.plain = []          # non-binding asserts (kind pin, dispatch pin, exit guard)
        self.state_exit = None
        for f in parse_all(text):
            if not isinstance(f, list) or not f:
                continue
            h = f[0]
            if h == "declare-const" and len(f) == 3:
                self.sorts[f[1]] = f[2] if isinstance(f[2], str) else "MState"
            elif h == "define-fun" and len(f) == 5 and f[1] == "state_exit":
                self.state_exit = f[4]
            elif h == "define-fun" and len(f) == 5 and isinstance(f[2], list) and f[2]:
                self.macros[f[1]] = ([p[0] for p in f[2]], f[4])
            elif h == "assert" and len(f) == 2 and isinstance(f[1], list) \
                    and f[1][0] == "=" and isinstance(f[1][1], str) and f[1][1] in self.sorts:
                self.binds[f[1][1]] = f[1][2]
                self.order.append(f[1][1])
            elif h == "assert":
                self.plain.append(f[1])
        if self.state_exit is None:
            raise EvalError("query has no state_exit")


# ------------------------------------------------------------- the evaluator
BIN = {
    "bvadd": lambda a, b: (a + b),
    "bvsub": lambda a, b: (a - b),
    "bvand": lambda a, b: (a & b),
    "bvor": lambda a, b: (a | b),
    "bvxor": lambda a, b: (a ^ b),
    "bvmul": lambda a, b: (a * b),
}


def _s(v, w=64):
    m = 1 << (w - 1)
    return (v ^ m) - m


class Ev:
    """Lazy evaluation of one query against one concrete execution.

    `oracle` resolves the uninterpreted symbols — a call, a loop, an indirect
    dispatch, an unmodelled word — from the trace, and is where the plan's "pin
    every summary application from its observed (pre, post) pair" happens."""

    def __init__(self, q, s0, oracle):
        self.q, self.oracle = q, s0 and oracle
        self.env = {"s0": s0}
        self.oracle = oracle
        self.writes = []          # (addr, name) every byte the chain stores
        self.cur_bind = None
        self.trail = []           # bindings evaluated, in order

    def get(self, name):
        if name in self.env:
            return self.env[name]
        if name not in self.q.binds:
            raise EvalError(f"unbound name {name}")
        prev, self.cur_bind = self.cur_bind, name
        v = self.ev(self.q.binds[name])
        self.cur_bind = prev
        self.env[name] = v
        self.trail.append(name)
        return v

    def ev(self, t):
        if isinstance(t, str):
            if t.startswith("#x"):
                return int(t[2:], 16)
            if t.startswith("#b"):
                return int(t[2:], 2)
            if t == "true":
                return True
            if t == "false":
                return False
            return self.get(t)
        h = t[0]
        # ((_ op n) x)
        if isinstance(h, list):
            if h[0] != "_":
                raise EvalError(f"unsupported head {h}")
            op = h[1]
            x = self.ev(t[1])
            if op == "extract":
                hi, lo = int(h[2]), int(h[3])
                return (x >> lo) & ((1 << (hi - lo + 1)) - 1)
            if op == "zero_extend":
                return x
            if op == "sign_extend":
                # the encoder only sign-extends 32->64 and 8/16/32->64 through
                # the `ld*s` macros, and always to 64 bits
                n = int(h[2])
                w = 64 - n
                return _s(x & ((1 << w) - 1), w) & M64
            raise EvalError(f"unsupported indexed op {op}")
        if h == "ite":
            return self.ev(t[2]) if self.ev(t[1]) else self.ev(t[3])
        if h == "and":
            return all(self.ev(a) for a in t[1:])
        if h == "or":
            return any(self.ev(a) for a in t[1:])
        if h == "not":
            return not self.ev(t[1])
        if h == "=>":
            return (not self.ev(t[1])) or self.ev(t[2])
        if h == "=":
            a = self.ev(t[1])
            return all(self.ev(x) == a for x in t[2:])
        if h == "distinct":
            vs = [self.ev(x) for x in t[1:]]
            return len(set(vs)) == len(vs)
        if h in BIN:
            v = self.ev(t[1])
            for x in t[2:]:
                v = BIN[h](v, self.ev(x))
            return v & M64
        if h == "bvshl":
            a, b = self.ev(t[1]), self.ev(t[2])
            return (a << b) & M64 if b < 64 else 0
        if h == "bvlshr":
            a, b = self.ev(t[1]), self.ev(t[2])
            return (a >> b) if b < 64 else 0
        if h == "bvashr":
            a, b = self.ev(t[1]), self.ev(t[2])
            return (_s(a) >> min(b, 63)) & M64
        if h in ("bvslt", "bvsle", "bvsgt", "bvsge"):
            a, b = _s(self.ev(t[1])), _s(self.ev(t[2]))
            return {"bvslt": a < b, "bvsle": a <= b,
                    "bvsgt": a > b, "bvsge": a >= b}[h]
        if h in ("bvult", "bvule", "bvugt", "bvuge"):
            a, b = self.ev(t[1]), self.ev(t[2])
            return {"bvult": a < b, "bvule": a <= b,
                    "bvugt": a > b, "bvuge": a >= b}[h]
        if h == "concat":
            v, w = 0, 0
            for x in t[1:]:
                # every `concat` the encoder emits is over 8-bit selects
                v = (v << 8) | (self.ev(x) & 0xFF)
                w += 8
            return v
        if h == "mst":
            return St(self.ev(t[1]), self.ev(t[2]))
        if h == "mm":
            return self.ev(t[1]).mem
        if h == "rr":
            return self.ev(t[1]).regs
        if h == "select":
            arr, i = self.ev(t[1]), self.ev(t[2])
            return arr.sel(i)
        if h == "store":
            arr, i, v = self.ev(t[1]), self.ev(t[2]), self.ev(t[3])
            if isinstance(arr, MA):
                self.writes.append((i & M64, self.cur_bind))
            return arr.store(i, v)
        if h in self.q.macros:
            ps, body = self.q.macros[h]
            args = [self.ev(a) for a in t[1:]]
            saved = [(p, self.env.get(p, KeyError)) for p in ps]
            for p, a in zip(ps, args):
                self.env[p] = a
            try:
                return self.ev(body)
            finally:
                for p, old in saved:
                    if old is KeyError:
                        self.env.pop(p, None)
                    else:
                        self.env[p] = old
        if h.startswith(("callee_", "loop_", "icall_", "idisp_")) or h == "unmodelled_step":
            return self.oracle(h, self.ev(t[1]), self.cur_bind)
        raise EvalError(f"unsupported operator {h}")
