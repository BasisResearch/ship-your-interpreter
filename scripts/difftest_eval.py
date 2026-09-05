#!/usr/bin/env python3
"""difftest_eval — evaluate the encoder's emitted term on a real execution.

Each comparison uses the observed execution:

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
closed SMT-LIB fragment the encoder emits.  Its results are checked by the
lockstep drive: each straight-line state it produces is compared with the
machine at that instruction.  There is no separate Z3 self-check.

The fragment, in full (anything else raises rather than being guessed at):
  values     `#x…` literals, `true`, `false`
  states     `mst`, `mm`, `rr`
  arrays     `select`, `store`
  bitvector  bvadd bvsub bvmul bvsdiv bvsrem bvand bvor bvxor bvshl bvlshr bvashr
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
    __slots__ = ("d", "base", "unknown", "reads")

    def __init__(self, d, base, unknown, reads=None):
        self.d, self.base, self.unknown = d, base, unknown
        # All store-derived memories from one concrete entry share this set.
        # It records the finite byte support needed to turn a successful
        # differential execution into an independently checkable Z3 witness.
        self.reads = set() if reads is None else reads

    def store(self, a, b):
        d = dict(self.d)
        d[a & M64] = b & 0xFF
        return MA(d, self.base, self.unknown, self.reads)

    def sel(self, a):
        a &= M64
        self.reads.add(a)
        if a in self.d:
            return self.d[a]
        v = self.base(a)
        if v is None:
            self.unknown.add(a)
            return 0
        return v


class OA:
    """Finite output-byte array used by the reflected output projection."""
    __slots__ = ("d",)

    def __init__(self, d=None):
        self.d = {} if d is None else dict(d)

    def store(self, i, b):
        d = dict(self.d)
        d[i & M64] = b & 0xFF
        return OA(d)

    def sel(self, i):
        return self.d.get(i & M64, 0)

    def __eq__(self, other):
        return isinstance(other, OA) and self.d == other.d


class St:
    __slots__ = ("mem", "regs", "out", "out_len")

    def __init__(self, mem, regs, out=None, out_len=0):
        self.mem, self.regs = mem, regs
        self.out = out if out is not None else OA()
        self.out_len = out_len & M64


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


def _sdiv(a, b):
    """SMT-LIB signed division, for nonzero 64-bit operands."""
    sa, sb = _s(a), _s(b)
    if sb == 0:
        return M64 if sa >= 0 else 1
    q = abs(sa) // abs(sb)
    return (-q if (sa < 0) != (sb < 0) else q) & M64


def _cstring_bytes(mem, ptr):
    """Independent concrete meaning of the abstract Lean CStr symbols."""
    out = bytearray()
    for offset in range(M64 + 1):
        byte = mem.sel((ptr + offset) & M64)
        if byte == 0:
            return bytes(out)
        out.append(byte)
    raise EvalError("unterminated C string spans the address space")


def _load_le(mem, address, width):
    return sum(mem.sel((address + i) & M64) << (8 * i)
               for i in range(width))


def _try_load_le(mem, address, width):
    """Load only bytes known by the trace or explicit array stores."""
    out = 0
    for i in range(width):
        addr = (address + i) & M64
        byte = mem.sel(addr)
        if addr not in mem.d and addr in mem.unknown:
            return None
        out |= byte << (8 * i)
    return out


def _try_cstring_bytes(mem, ptr):
    """Decode a concrete C string without treating unknown bytes as zero."""
    out = bytearray()
    for offset in range(M64 + 1):
        addr = (ptr + offset) & M64
        byte = mem.sel(addr)
        if addr not in mem.d and addr in mem.unknown:
            return None
        if byte == 0:
            return bytes(out)
        out.append(byte)
    return None


def _env_lookup_slot(mem, env, name_ptr):
    """Concrete meaning of the two ground Lean environment symbols."""
    name = _try_cstring_bytes(mem, name_ptr)
    if name is None:
        return None
    seen = set()
    while env != 0:
        if env in seen:
            return None
        seen.add(env)
        count = _try_load_le(mem, env, 4)
        capacity = _try_load_le(mem, env + 4, 4)
        names = _try_load_le(mem, env + 8, 8)
        values = _try_load_le(mem, env + 16, 8)
        parent = _try_load_le(mem, env + 24, 8)
        if None in (count, capacity, names, values, parent) \
                or count > capacity or count > 4096:
            return None
        for index in range(count):
            candidate_ptr = _try_load_le(mem, names + 8 * index, 8)
            if candidate_ptr is None:
                return None
            candidate = _try_cstring_bytes(mem, candidate_ptr)
            if candidate is None:
                return None
            if candidate == name:
                return (values + 24 * index) & M64
        env = parent
    return 0


def _value_display_bytes(mem, value_ptr):
    """Independent executable meaning of Lean `Value.display`."""
    kind = _load_le(mem, value_ptr, 4)
    if kind == 0:
        return b"null"
    if kind == 1:
        return b"true" if _load_le(mem, value_ptr + 8, 4) else b"false"
    if kind == 2:
        return str(_s(_load_le(mem, value_ptr + 8, 8))).encode("ascii")
    if kind == 3:
        return _cstring_bytes(mem, _load_le(mem, value_ptr + 8, 8))
    if kind == 4:
        closure = _load_le(mem, value_ptr + 8, 8)
        fn_expr = _load_le(mem, closure, 8)
        name_ptr = _load_le(mem, fn_expr + 8, 8)
        if name_ptr == 0:
            return b"<fn>"
        return b"<fn " + _cstring_bytes(mem, name_ptr) + b">"
    if kind == 5:
        name_ptr = _load_le(mem, value_ptr + 8, 8)
        return b"<native fn " + _cstring_bytes(mem, name_ptr) + b">"
    raise EvalError(f"invalid Value kind {kind}")


def _print_args_bytes(mem, args, argc):
    if argc > 32:
        raise EvalError(f"argument count {argc} exceeds interpreter maximum")
    return b" ".join(
        _value_display_bytes(mem, (args + 24 * index) & M64)
        for index in range(argc))


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
        if h == "bvsdiv":
            return _sdiv(self.ev(t[1]), self.ev(t[2]))
        if h == "bvsrem":
            a, b = self.ev(t[1]), self.ev(t[2])
            if b == 0:
                return a
            return (_s(a) - _s(_sdiv(a, b)) * _s(b)) & M64
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
            if len(t) == 3:  # legacy generated campaigns
                return St(self.ev(t[1]), self.ev(t[2]))
            if len(t) != 5:
                raise EvalError(f"mst expects 2 or 4 fields, got {len(t)-1}")
            return St(self.ev(t[1]), self.ev(t[2]), self.ev(t[3]), self.ev(t[4]))
        if h == "mm":
            return self.ev(t[1]).mem
        if h == "rr":
            return self.ev(t[1]).regs
        if h == "oo":
            return self.ev(t[1]).out
        if h == "ol":
            return self.ev(t[1]).out_len
        if h == "select":
            arr, i = self.ev(t[1]), self.ev(t[2])
            return arr.sel(i)
        if h == "store":
            arr, i, v = self.ev(t[1]), self.ev(t[2]), self.ev(t[3])
            if isinstance(arr, MA):
                self.writes.append((i & M64, self.cur_bind))
            return arr.store(i, v)
        if h == "lean_cstring_eq":
            mem, left, right = self.ev(t[1]), self.ev(t[2]), self.ev(t[3])
            return _cstring_bytes(mem, left) == _cstring_bytes(mem, right)
        if h == "lean_cstring_cmp3":
            mem, left, right = self.ev(t[1]), self.ev(t[2]), self.ev(t[3])
            left, right = _cstring_bytes(mem, left), _cstring_bytes(mem, right)
            return ((left > right) - (left < right)) & M64
        if h in ("lean_env_lookup_found", "lean_env_lookup_slot"):
            mem, env, name = self.ev(t[1]), self.ev(t[2]), self.ev(t[3])
            slot = _env_lookup_slot(mem, env, name)
            if slot is None:
                raise EvalError("Lean environment lookup reads unknown or malformed bytes")
            return slot != 0 if h == "lean_env_lookup_found" else slot
        if h == "lean_print_args_len":
            mem, args, argc = (self.ev(t[1]), self.ev(t[2]), self.ev(t[3]))
            return len(_print_args_bytes(mem, args, argc)) & M64
        if h == "lean_print_args_out":
            mem, args, argc = (self.ev(t[1]), self.ev(t[2]), self.ev(t[3]))
            out, out_len = self.ev(t[4]), self.ev(t[5])
            for offset, byte in enumerate(_print_args_bytes(mem, args, argc)):
                out = out.store((out_len + offset) & M64, byte)
            return out
        if h == "lean_print_args_same":
            left_mem, right_mem = self.ev(t[1]), self.ev(t[2])
            args, argc = self.ev(t[3]), self.ev(t[4])
            return (_print_args_bytes(left_mem, args, argc)
                    == _print_args_bytes(right_mem, args, argc))
        if h == "lean_malloc16_rel":
            # The abstract allocator invariant is not reconstructible from a
            # byte trace.  It is consumed only by the dedicated closure audit,
            # which checks the observable result and mutation set separately.
            raise EvalError("lean_malloc16_rel requires allocator ghost state")
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
        if h.startswith(("callee_", "loop_", "loopexit_", "icall_", "idisp_")) or h == "unmodelled_step":
            return self.oracle(h, self.ev(t[1]), self.cur_bind)
        raise EvalError(f"unsupported operator {h}")
