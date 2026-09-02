#!/usr/bin/env python3
"""smt_check.py — Lean→SMT-LIB encoder + Z3 driver for the falsity fragment
(ANALYSIS ONLY; nothing here enters a proof).

Companion to statement_fuzz.py.  Where the fuzzer instantiates a FIXED bank of
historically-lethal witnesses and lets Lean `decide`, this tool hands the
statement's arithmetic + window/quantifier structure to Z3, which SEARCHES for a
countermodel (or proves none exists in the encoded fragment).  Z3 handles the
nested ∀-over-Mem conjuncts natively (arrays + a definedness map) — that is the
whole point: the ∀-mcall class the fuzzer needed a hand-written adversary for is
found automatically here.

THREE MODES
  --refute   negate the encoded statement, ask Z3 for a model.  SAT ⇒ emit the
             countermodel AND auto-generate a Lean replay probe (`¬P` with the
             concrete witnesses substituted, the statement_fuzz probe idiom);
             run `lake env lean` on it.  Verdict REFUTED-REPLAYED only if the
             probe is green + axiom-clean ⊆ {propext,Classical.choice,Quot.sound}.
             SAT-but-replay-fails ⇒ ENCODING-GAP (a translator bug, reported
             loudly).  If the model constrains an uninterpreted (OPAQUE) symbol
             the verdict is REFUTED-MODULO-OPAQUE and is NOT auto-replayed.
  --validate UNSAT of the negation ⇒ VALID-IN-FRAGMENT (advisory green).
             timeout/unknown ⇒ UNKNOWN.
  --inhabit  SAT of the hypothesis conjunction ⇒ non-vacuous; model = witness.

ENCODING (small + honest — see ATOMS below):
  BitVec 64/32/8            → SMT BV of that width
  .toNat on a BitVec       → an Int mirror var pinned 0 ≤ v < 2^w
  Nat / Int                → Int (Nat carries `≥ 0`)
  Mem (ExtHashMap Nat BV8) → (defined : Array Int Bool, val : Array Int (BV 8));
                             `m[a]? = some b`  ↦ (select def a) ∧ (select val a)=b
                             `m[a]? = m0[a]?`  ↦ defs agree ∧ vals agree
  MemExtends m0 m          → ∀a, def0 a → def a          (presence preserved)
  StackOK SL sp k          → lo+k≤sp∧sp≤hi∧sp%16=0        (over the .toNat mirror)
  window ¬(lo≤a ∧ a<sp)    → encoded verbatim in the agree ∀
  OPAQUE P … (ValueRepr / CString / GoodState / Repr / …)  → uninterpreted pred;
                             a model touching one ⇒ REFUTED-MODULO-OPAQUE.

Statement extraction reuses statement_fuzz.py's telescope discovery for the
outer ∀ binders and a recursive conjunct-tree walk for the body (nested ∀s
included — no menu).

Usage
  python3 scripts/smt_check.py --refute   --file <mod.lean> --prop <Ns.P>
  python3 scripts/smt_check.py --validate --file <mod.lean> --prop <Ns.P>
  python3 scripts/smt_check.py --inhabit  --file <mod.lean> --prop <Ns.P>
  python3 scripts/smt_check.py --acceptance     # a-e gate (git-history forms)
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LOGDIR = os.path.join(ROOT, "experiments", "logs")
LOG = os.path.join(LOGDIR, "smt-check.md")
AX_OK = {"propext", "Classical.choice", "Quot.sound"}
W64 = 2 ** 64

# Opaque Lean predicate name-stems: an atom whose head is one of these is
# encoded as an UNINTERPRETED predicate (sound for refutation search only if the
# countermodel does not hinge on it — we track that and mark MODULO-OPAQUE).
OPAQUE_HEADS = ("ValueRepr", "ExprRepr", "CString", "GoodState", "Repr",
                "Loaded", "InterpSim", "FoundSt", "Approx", "StoreRepr",
                "frameRepr")


# ==========================================================================
# Lean plumbing
# ==========================================================================

def run_lean(src, timeout=600):
    os.makedirs(LOGDIR, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LOGDIR,
                                     delete=False) as f:
        f.write(src)
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return 124, "TIMEOUT"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def run_z3(smt, timeout_ms=20000):
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", dir=LOGDIR,
                                     delete=False) as f:
        f.write(smt)
        path = f.name
    try:
        r = subprocess.run(["z3", f"-T:{timeout_ms // 1000 + 1}", path],
                           capture_output=True, text=True,
                           timeout=timeout_ms / 1000 + 5)
        return r.stdout + r.stderr
    except FileNotFoundError:
        return "Z3-ABSENT"
    except subprocess.TimeoutExpired:
        return "timeout"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


# ==========================================================================
# statement extraction (reuse the statement_fuzz telescope idiom)
# ==========================================================================

def extract_def_body(body_text, prop):
    """Return the RHS of `def <short> … : Prop := <rhs>` verbatim (multi-line),
    up to the next top-level `def`/`theorem`/`end`/`namespace`."""
    short = prop.split(".")[-1]
    m = re.search(rf"(?:def|abbrev)\s+{re.escape(short)}\b(.*?):=\s*",
                  body_text, re.S)
    if not m:
        return None, None
    sig = m.group(1)
    rhs_start = m.end()
    rest = body_text[rhs_start:]
    stop = re.search(r"\n(?:def|abbrev|theorem|end|namespace|/-)", rest)
    rhs = rest[:stop.start()] if stop else rest
    # strip Lean line comments (`-- …`) that may be embedded in the RHS
    rhs = re.sub(r"--[^\n]*", "", rhs)
    return sig, rhs.strip()


def parse_binders(text):
    """Parse `∀ (n₁ n₂ : T) (n₃ : U) …,` into an ordered [(name, type)] list.
    Consumes the leading ∀ prefix; returns (binders, remaining_body)."""
    binders = []
    text = text.strip()
    while text.startswith("∀"):
        text = text[1:].lstrip()
        # consume `(names : type)` groups until the comma that ends this ∀
        while text.startswith("("):
            depth = 0
            for i, ch in enumerate(text):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        grp = text[1:i]
                        text = text[i + 1:].lstrip()
                        break
            if ":" in grp:
                names, ty = grp.split(":", 1)
                for nm in names.split():
                    binders.append((nm, ty.strip()))
        # bare (paren-less) binder group `names : type,`  (e.g. `∀ mcall : Mem,`)
        if not text.startswith("(") and ":" in text.split(",", 1)[0]:
            grp = text.split(",", 1)[0]
            names, ty = grp.split(":", 1)
            for nm in names.split():
                binders.append((nm, ty.strip()))
            text = text.split(",", 1)[1].lstrip() if "," in text else ""
            break
        if text.startswith(","):
            text = text[1:].lstrip()
            break
    return binders, text


def split_top_arrows(body):
    """Split a `H₁ → H₂ → … → C` chain at TOP-LEVEL → (respecting (),⟨⟩).
    A top-level `∀` opens a quantifier whose scope runs to the end of the
    string, so arrows AFTER it are NOT split (they belong to the ∀ body).
    Returns [H₁,…,Hₙ, C]."""
    parts, depth, i, start = [], 0, 0, 0
    while i < len(body):
        ch = body[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif depth == 0 and ch == "∀":
            break                     # ∀ captures the rest as one unit
        elif depth == 0 and body[i:i + 1] == "→":
            parts.append(body[start:i].strip())
            start = i + 1
        i += 1
    parts.append(body[start:].strip())
    return parts


def split_top_and(body):
    """Split `A ∧ B ∧ …` at top level."""
    parts, depth, i, start = [], 0, 0, 0
    while i < len(body):
        ch = body[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif depth == 0 and ch == "∧":
            parts.append(body[start:i].strip())
            start = i + 1
        i += 1
    parts.append(body[start:].strip())
    return [p for p in parts if p]


# ==========================================================================
# SMT encoding
# ==========================================================================

class EncCtx:
    """Accumulates SMT declarations + tracks binder → sort, .toNat mirrors, and
    which OPAQUE symbols the formula referenced (for MODULO-OPAQUE)."""
    def __init__(self):
        self.decls = []          # SMT declare-fun lines
        self.env = {}            # binder name → ('bv',w) | 'int' | 'mem' | 'sl'
        self.aux = []            # extra assertions (mirror pins etc.)
        self.opaque = set()      # opaque predicate heads touched
        self.declared = set()
        self.body_text = ""      # hermetic module text (for structure #check)
        self.ns = ""             # namespace prefix of the probed prop
        self._struct_cache = {}  # StructName → (param_names, field_texts)

    def decl(self, line, key):
        if key not in self.declared:
            self.decls.append(line)
            self.declared.add(key)

    def bind(self, name, ty):
        t = ty.strip()
        if t.endswith("StackLayout"):
            self.env[name] = "sl"
            self.decl(f"(declare-fun {name}_lo () Int)", f"{name}_lo")
            self.decl(f"(declare-fun {name}_hi () Int)", f"{name}_hi")
            self.aux.append(f"(assert (>= {name}_lo 0))")
            self.aux.append(f"(assert (>= {name}_hi 0))")
        elif t.endswith("Mem"):
            self.env[name] = "mem"
            self.decl(f"(declare-fun {name}_def () (Array Int Bool))",
                      f"{name}_def")
            self.decl(f"(declare-fun {name}_val () (Array Int (_ BitVec 8)))",
                      f"{name}_val")
        elif "BitVec 64" in t or t.endswith("Addr"):
            self.env[name] = ("bv", 64)
            self.decl(f"(declare-fun {name} () (_ BitVec 64))", name)
            # .toNat mirror
            self.decl(f"(declare-fun {name}_n () Int)", f"{name}_n")
            self.aux.append(f"(assert (= {name}_n (bv2int {name})))")
            self.aux.append(f"(assert (>= {name}_n 0))")
        elif "BitVec 32" in t:
            self.env[name] = ("bv", 32)
            self.decl(f"(declare-fun {name} () (_ BitVec 32))", name)
        elif "BitVec 8" in t:
            self.env[name] = ("bv", 8)
            self.decl(f"(declare-fun {name} () (_ BitVec 8))", name)
        elif t.endswith("Nat"):
            self.env[name] = "int"
            self.decl(f"(declare-fun {name} () Int)", name)
            self.aux.append(f"(assert (>= {name} 0))")
        elif t.endswith("Int"):
            self.env[name] = "int"
            self.decl(f"(declare-fun {name} () Int)", name)
        else:
            # structure ghost (e.g. WG): expose its Nat/Int projections lazily
            self.env[name] = ("struct", t)


# integer-arith atom: lhs (≤|<|=|≥|>|≠) rhs, where each side is a sum/diff of
# `x`, `x.toNat`, `x.lo/.hi`, projections `g.f`, and Nat literals (incl 0x..).
_NUM = re.compile(r"^[\s\w.+\-*%()x0-9→≤<≥>=≠∧]+$")


def _int_term(expr, ctx):
    """Render an integer/Nat side to SMT (over the .toNat / .lo mirrors).
    Returns None if it is not pure integer arithmetic in the fragment."""
    e = expr.strip()
    # literal (dec or 0x)
    if re.fullmatch(r"0x[0-9a-fA-F]+", e):
        return str(int(e, 16))
    if re.fullmatch(r"\d+", e):
        return e
    # x.toNat
    m = re.fullmatch(r"([A-Za-z_]\w*)\.toNat", e)
    if m and ctx.env.get(m.group(1), (None,))[0] == "bv":
        return f"{m.group(1)}_n"
    # SL.lo / SL.hi
    m = re.fullmatch(r"([A-Za-z_]\w*)\.(lo|hi)", e)
    if m and ctx.env.get(m.group(1)) == "sl":
        return f"{m.group(1)}_{m.group(2)}"
    # struct projection g.field  (Nat) — declare on demand
    m = re.fullmatch(r"([A-Za-z_]\w*)\.([A-Za-z_]\w*)", e)
    if m and isinstance(ctx.env.get(m.group(1)), tuple) and \
            ctx.env[m.group(1)][0] == "struct":
        nm = f"{m.group(1)}_{m.group(2)}"
        ctx.decl(f"(declare-fun {nm} () Int)", nm)
        ctx.aux.append(f"(assert (>= {nm} 0))")
        return nm
    # plain int/nat var
    if ctx.env.get(e) == "int":
        return e
    if isinstance(ctx.env.get(e), tuple) and ctx.env[e][0] == "bv":
        return f"{e}_n"
    # binary +,-,*,%  (left-assoc, low precedence handled by split).  `-` is
    # TRUNCATED Nat subtraction (all our mirrors are ≥0): x - y = max(0, x-y),
    # the honest encoding so VALIDATE (UNSAT⇒valid) stays sound.
    for op, smt in (("+", "+"), ("-", "-"), ("*", "*"), ("%", "mod")):
        idx = _split_binop(e, op)
        if idx is not None:
            l = _int_term(e[:idx], ctx)
            r = _int_term(e[idx + 1:], ctx)
            if l and r:
                if op == "-":
                    return f"(ite (>= {l} {r}) (- {l} {r}) 0)"
                return f"({smt} {l} {r})"
    # parenthesised
    if e.startswith("(") and e.endswith(")"):
        return _int_term(e[1:-1], ctx)
    return None


def _split_binop(e, op):
    """Rightmost top-level occurrence of op (for left-assoc arithmetic)."""
    depth = 0
    for i in range(len(e) - 1, -1, -1):
        ch = e[i]
        if ch in ")⟩":
            depth += 1
        elif ch in "(⟨":
            depth -= 1
        elif depth == 0 and ch == op and 0 < i < len(e) - 1:
            return i
    return None


REL = [("≤", "<="), ("≥", ">="), ("≠", None), ("<", "<"), (">", ">"),
       ("=", "=")]


def encode_atom(atom, ctx, bound=None):
    """Encode a single atomic Prop (or fall through to OPAQUE).  `bound` is the
    inner-∀ bound var name (e.g. `a`) → maps to an SMT Int var of the same name.
    Returns an SMT bool-expr string, or None if unencodable."""
    a = atom.strip()
    if a.startswith("(") and a.endswith(")") and _balanced(a[1:-1]):
        return encode_atom(a[1:-1], ctx, bound)

    # --- membership / lookup equalities on Mem -------------------------------
    # m[a]? = some b
    m = re.fullmatch(r"([A-Za-z_]\w*)\[([^\]]+)\]\?\s*=\s*some\s+(\S+)", a)
    if m and ctx.env.get(m.group(1)) == "mem":
        mem, idx, b = m.group(1), _idx(m.group(2), ctx, bound), m.group(3)
        bt = _bv8(b, ctx, bound)
        return f"(and (select {mem}_def {idx}) (= (select {mem}_val {idx}) {bt}))"
    # ∃ b, m[a]? = some b
    m = re.fullmatch(r"∃\s*b[^,]*,\s*([A-Za-z_]\w*)\[([^\]]+)\]\?\s*=\s*some\s+b", a)
    if m and ctx.env.get(m.group(1)) == "mem":
        mem, idx = m.group(1), _idx(m.group(2), ctx, bound)
        return f"(select {mem}_def {idx})"
    # m[a]? = m0[a]?  (defined + val agree)
    m = re.fullmatch(r"([A-Za-z_]\w*)\[([^\]]+)\]\?\s*=\s*([A-Za-z_]\w*)\[([^\]]+)\]\?", a)
    if m and ctx.env.get(m.group(1)) == "mem" and ctx.env.get(m.group(3)) == "mem":
        m1, i1, m2, i2 = m.group(1), _idx(m.group(2), ctx, bound), \
            m.group(3), _idx(m.group(4), ctx, bound)
        return (f"(and (= (select {m1}_def {i1}) (select {m2}_def {i2})) "
                f"(= (select {m1}_val {i1}) (select {m2}_val {i2})))")

    # --- MemExtends m0 m  (∀a, def0 a → def a) -------------------------------
    m = re.fullmatch(r"MemExtends\s+([A-Za-z_]\w*)\s+([A-Za-z_]\w*)", a)
    if m and ctx.env.get(m.group(1)) == "mem" and ctx.env.get(m.group(2)) == "mem":
        m0, mm = m.group(1), m.group(2)
        return (f"(forall ((za Int)) (=> (select {m0}_def za) "
                f"(select {mm}_def za)))")

    # --- StackOK SL sp k -----------------------------------------------------
    m = re.fullmatch(r"StackOK\s+(\S+)\s+(\S+)\s+(\S+)", a)
    if m:
        sl, sp, k = m.group(1), m.group(2), _int_term(m.group(3), ctx) or m.group(3)
        spn = _int_term(f"{sp}.toNat", ctx) or _int_term(sp, ctx)
        return (f"(and (<= (+ {sl}_lo {k}) {spn}) (<= {spn} {sl}_hi) "
                f"(= (mod {spn} 16) 0))")

    # --- window membership  ¬(SL.lo ≤ a ∧ a < sp.toNat) ----------------------
    m = re.fullmatch(r"¬\s*\((.+)\)", a)
    if m:
        inner = encode_atom(m.group(1), ctx, bound)
        if inner is not None:
            return f"(not {inner})"

    # --- integer/BV relations  L rel R ---------------------------------------
    for sym, smt in REL:
        idx = _split_rel(a, sym)
        if idx is not None:
            L, R = a[:idx].strip(), a[idx + len(sym):].strip()
            lt = _int_term_or_bound(L, ctx, bound)
            rt = _int_term_or_bound(R, ctx, bound)
            if lt is not None and rt is not None:
                if sym == "≠":
                    return f"(not (= {lt} {rt}))"
                return f"({smt} {lt} {rt})"

    # --- conjunction inside an atom ------------------------------------------
    if "∧" in a:
        conj = [encode_atom(p, ctx, bound) for p in split_top_and(a)]
        if all(c is not None for c in conj):
            return "(and " + " ".join(conj) + ")"

    # --- applied GHOST STRUCTURE (e.g. `WInvMined g k a1 a3 a2 a4`) ----------
    # expand into the conjunction of its fields (mk arrow chain), substituting
    # the actual args for the mk parameter names.  This unfolds the mined
    # invariant record so its arithmetic fields become SMT constraints.
    m = re.fullmatch(r"([A-Z]\w*)\s+(.+)", a)
    if m and not any(a.startswith(h) for h in OPAQUE_HEADS):
        se = _encode_struct(m.group(1), m.group(2).split(), ctx, bound)
        if se is not None:
            return se

    # --- OPAQUE fallback -----------------------------------------------------
    head = a.split()[0] if a.split() else a
    if any(a.startswith(h) for h in OPAQUE_HEADS):
        ctx.opaque.add(head)
        # uninterpreted 0-ary bool per exact atom text (so equal atoms share it)
        key = "op_" + re.sub(r"\W", "_", a)[:40]
        ctx.decl(f"(declare-fun {key} () Bool)", key)
        return key
    return None


def _discover_struct(struct, ctx):
    """`#check @S.mk` → ([param_names], [field_texts]) with the field arrow
    chain verbatim (over the mk param names).  Cached."""
    if struct in ctx._struct_cache:
        return ctx._struct_cache[struct]
    if not ctx.body_text:
        ctx._struct_cache[struct] = (None, None)
        return None, None
    # try the bare name and the prop's namespace-qualified name
    cands = [struct]
    if ctx.ns:
        cands.append(f"{ctx.ns}.{struct}")
    out = ""
    for cand in cands:
        src = (f"{ctx.body_text}\n\nset_option pp.fullNames false in\n"
               f"#check @{cand}.mk\n")
        rc, out = run_lean(src)
        if rc == 0 and f"{struct.split('.')[-1]}.mk" in out and "error" not in out:
            break
    m = re.search(rf"{re.escape(struct.split('.')[-1])}\.mk\s*:\s*([\s\S]+)", out)
    if not m:
        ctx._struct_cache[struct] = (None, None)
        return None, None
    sig = " ".join(m.group(1).split())
    # implicit/explicit params `{a b : T}` / `(a : T)` up to the field arrows
    params = []
    # only the LEADING binder groups (before the first `→`)
    pre = sig.split("→", 1)[0]
    for gm in re.finditer(r"[{(]([^{}():]+):([^{}()]+)[})]", pre):
        for nm in gm.group(1).split():
            params.append(nm)
    tail = sig.split(",", 1)[1] if "," in sig else sig
    parts = split_top_arrows_raw(tail)
    fields = [p.strip() for p in parts[:-1]] if len(parts) >= 2 else []
    ctx._struct_cache[struct] = (params, fields)
    return params, fields


def split_top_arrows_raw(body):
    """Like split_top_arrows but WITHOUT the ∀-stop (mk chains have no ∀)."""
    parts, depth, i, start = [], 0, 0, 0
    while i < len(body):
        ch = body[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif depth == 0 and ch == "→":
            parts.append(body[start:i].strip())
            start = i + 1
        i += 1
    parts.append(body[start:].strip())
    return parts


def _encode_struct(struct, args, ctx, bound):
    """Expand `struct arg₀ arg₁ …` into the ∧ of its mk fields, substituting
    actual args for mk param names.  Returns SMT bool-expr or None."""
    params, fields = _discover_struct(struct, ctx)
    if not params or not fields:
        return None
    if len(args) > len(params):
        return None
    subst = dict(zip(params, args))
    # declare struct-field projection ints for any `arg.field` that appears
    conj = []
    for f in fields:
        ftxt = f
        # substitute whole-word param occurrences with the actual arg spelling
        for p in sorted(subst, key=len, reverse=True):
            ftxt = re.sub(rf"(?<![\w.]){re.escape(p)}(?![\w])", subst[p], ftxt)
        enc = encode_atom(ftxt, ctx, bound)
        if enc is None:
            return None
        conj.append(enc)
    if not conj:
        return None
    return "(and " + " ".join(conj) + ")" if len(conj) > 1 else conj[0]


def _idx(idxexpr, ctx, bound):
    t = _int_term_or_bound(idxexpr, ctx, bound)
    return t if t is not None else idxexpr.strip()


def _bv8(b, ctx, bound):
    m = re.fullmatch(r"\(?(\d+)#8\)?", b.strip())
    if m:
        return f"(_ bv{m.group(1)} 8)"
    if bound and b.strip() == bound:
        return b.strip()
    return "(_ bv0 8)"


def _int_term_or_bound(e, ctx, bound):
    e = e.strip()
    if bound and e == bound:
        return e            # the inner-∀ bound Int var
    return _int_term(e, ctx)


def _split_rel(a, sym):
    depth = 0
    for i in range(len(a)):
        ch = a[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif depth == 0 and a[i:i + len(sym)] == sym:
            # don't split `≤`/`<`/`=` that are part of `→`/`≠` handled elsewhere
            return i
    return None


def _balanced(s):
    depth = 0
    for ch in s:
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def encode_hyp_or_concl(text, ctx, bound=None):
    """Encode a hypothesis/conclusion that may itself be `∀ a, H → C` or a
    conjunction.  Returns SMT bool-expr or None."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")") and _balanced(text[1:-1]):
        text = text[1:-1].strip()
    if text.startswith("∀"):
        binders, rest = parse_binders(text)
        # register each inner binder: Mem → two array-sorted quantified vars +
        # env entry; everything else → a single Int quantified var.
        qvars = []          # SMT (name sort) decls for the `forall`
        addrvar = None      # the address bound var to thread into atoms
        saved = {}
        for n, t in binders:
            tt = t.strip()
            if tt.endswith("Mem"):
                qvars.append(f"({n}_def (Array Int Bool))")
                qvars.append(f"({n}_val (Array Int (_ BitVec 8)))")
                saved[n] = ctx.env.get(n)
                ctx.env[n] = "mem"
            else:
                qvars.append(f"({n} Int)")
                addrvar = n
        parts = split_top_arrows(rest)
        hyps, concl = parts[:-1], parts[-1]
        eh = [encode_hyp_or_concl(h, ctx, addrvar or bound) for h in hyps]
        ec = encode_hyp_or_concl(concl, ctx, addrvar or bound)
        for n in saved:                              # restore shadowed env
            if saved[n] is None:
                ctx.env.pop(n, None)
            else:
                ctx.env[n] = saved[n]
        if ec is None or any(x is None for x in eh):
            return None
        if eh:
            hh = eh[0] if len(eh) == 1 else "(and " + " ".join(eh) + ")"
            body = f"(=> {hh} {ec})"
        else:
            body = ec
        return f"(forall ({' '.join(qvars)}) {body})"
    if "→" in text:
        parts = split_top_arrows(text)
        if len(parts) > 1:                       # genuine top-level arrow
            eh = [encode_hyp_or_concl(h, ctx, bound) for h in parts[:-1]]
            ec = encode_hyp_or_concl(parts[-1], ctx, bound)
            if ec is None or any(x is None for x in eh):
                return None
            hh = eh[0] if len(eh) == 1 else "(and " + " ".join(eh) + ")"
            return f"(=> {hh} {ec})"
    if "∧" in text and not text.startswith("¬"):
        parts = split_top_and(text)
        if len(parts) > 1:
            conj = [encode_hyp_or_concl(p, ctx, bound) for p in parts]
            if all(c is not None for c in conj):
                return "(and " + " ".join(conj) + ")"
    return encode_atom(text, ctx, bound)


def encode_statement(binders, body, body_text="", ns=""):
    """Build (ctx, hyps[list of smt], concl smt).  The outer binders are the
    top ∀ telescope; the body is the H₁→…→Hₙ→C chain."""
    ctx = EncCtx()
    ctx.body_text = body_text
    ctx.ns = ns
    for nm, ty in binders:
        ctx.bind(nm, ty)
    body = body.strip()
    # if the body itself is a (nested-∀-headed) single Prop, it is ALL conclusion
    # — the outer statement has no top-level hypotheses.
    if body.startswith("∀"):
        return ctx, [], encode_hyp_or_concl(body, ctx)
    parts = split_top_arrows(body)
    hyps, concl = parts[:-1], parts[-1]
    smt_hyps = [encode_hyp_or_concl(h, ctx) for h in hyps]
    smt_concl = encode_hyp_or_concl(concl, ctx)
    return ctx, smt_hyps, smt_concl


def build_smt(ctx, asserts, get_model=True):
    lines = ["(set-logic ALL)"]
    lines += ctx.decls
    lines += ctx.aux
    lines += [f"(assert {a})" for a in asserts if a]
    lines.append("(check-sat)")
    if get_model:
        lines.append("(get-model)")
    return "\n".join(lines) + "\n"


# ==========================================================================
# model → Lean replay-probe witnesses
# ==========================================================================

def parse_model(out):
    """Parse `(define-fun name () Sort  value)` bindings → {name: value_str}."""
    model = {}
    for m in re.finditer(r"\(define-fun\s+(\S+)\s*\(\)\s*\S[^\n]*\n?\s*"
                         r"([^\n)][^\n]*|\([^\n]*\))", out):
        model[m.group(1)] = m.group(2).strip()
    # also simple `(name value)` in older format
    for m in re.finditer(r"\(define-fun\s+(\S+)\s*\(\)\s*Int\s+(-?\d+)\)", out):
        model[m.group(1)] = m.group(2)
    return model


# ==========================================================================
# replay-probe generators (per statement CLASS, from the model)
# ==========================================================================

def replay_headroom(prop, binders, body, model):
    """Class: ∀ SL sp, <headroom>.  Substitute SL=⟨lo,hi⟩, sp=n#64 and hit the
    false arithmetic conclusion with `by decide` / omega."""
    slname = next((n for n, t in binders if t.strip().endswith("StackLayout")), None)
    spname = next((n for n, t in binders if "BitVec 64" in t or t.strip().endswith("Addr")), None)
    lo = model.get(f"{slname}_lo", "0")
    hi = model.get(f"{slname}_hi", "1000000")
    spn = model.get(f"{spname}_n", model.get(spname, "0"))
    spn = re.sub(r"\D", "", spn) or "0"
    return spname, slname, lo, hi, spn


# ==========================================================================
# core: refute / validate / inhabit on a hermetic file
# ==========================================================================

def load(path, prop):
    body_text = open(path).read()
    sig, rhs = extract_def_body(body_text, prop)
    if rhs is None:
        return None, None, None, body_text
    binders, chain = parse_binders(rhs)
    return binders, chain, sig, body_text


def smt_check(mode, path, prop, log, timeout_ms=20000):
    binders, chain, sig, body_text = load(path, prop)
    if binders is None:
        v = f"- `{prop}` → **ENCODE-FAIL** (def body not found)"
        print(v); log.write(v + "\n"); log.flush()
        return "ENCODE-FAIL", None
    ns = ".".join(prop.split(".")[:-1])
    ctx, hyps, concl = encode_statement(binders, chain, body_text, ns)
    if concl is None or any(h is None for h in hyps):
        v = (f"- `{prop}` → **ENCODE-GAP** (unencodable atom; hyps="
             f"{hyps} concl={concl})")
        print(v); log.write(v + "\n"); log.flush()
        return "ENCODE-GAP", None

    if mode == "inhabit":
        smt = build_smt(ctx, hyps)
        out = run_z3(smt, timeout_ms)
        sat = out.strip().startswith("sat")
        v = "NON-VACUOUS" if sat else ("VACUOUS" if out.strip().startswith("unsat") else "UNKNOWN")
        model = parse_model(out) if sat else {}
        line = f"- `{prop}` → **{v}**" + (f" — witness {_short(model)}" if model else "")
        print(line); log.write(line + "\n"); log.flush()
        return v, model

    # refute / validate both negate the statement: (∧ hyps) ∧ ¬concl SAT?
    neg = ["(and " + " ".join(hyps) + ")"] if hyps else []
    neg.append(f"(not {concl})")
    smt = build_smt(ctx, neg, get_model=(mode == "refute"))
    out = run_z3(smt, timeout_ms)
    first = out.strip().split("\n", 1)[0].strip()

    if mode == "validate":
        if first == "unsat":
            v = "VALID-IN-FRAGMENT"
            note = f" (opaque: {sorted(ctx.opaque)})" if ctx.opaque else ""
        elif first == "sat":
            v = "REFUTABLE"; note = " (negation SAT — not valid)"
        else:
            v = "UNKNOWN"; note = f" ({first or out.strip()[:60]})"
        line = f"- `{prop}` → **{v}**{note}"
        print(line); log.write(line + "\n"); log.flush()
        return v, None

    # --refute
    if first != "sat":
        v = ("VALID-IN-FRAGMENT" if first == "unsat" else "UNKNOWN")
        line = f"- `{prop}` → **NOT-REFUTED / {v}** ({first})"
        print(line); log.write(line + "\n"); log.flush()
        return v, None
    model = parse_model(out)
    modulo = bool(ctx.opaque)
    # generate + run the Lean replay probe
    replay_rc, replay_detail, probe = gen_and_run_replay(
        path, prop, binders, chain, body_text, model, ctx)
    if modulo and replay_rc != "REPLAYED":
        v = "REFUTED-MODULO-OPAQUE"
        detail = f"model touches opaque {sorted(ctx.opaque)}; not auto-replayed"
    elif replay_rc == "REPLAYED":
        v = "REFUTED-REPLAYED"; detail = replay_detail
    elif replay_rc == "GAP":
        v = "ENCODING-GAP"
        detail = f"Z3 SAT but Lean replay FAILED — translator bug: {replay_detail}"
    else:
        v = "REFUTED-Z3-ONLY"; detail = f"no replay generator for class ({replay_detail})"
    line = f"- `{prop}` → **{v}** — {detail} | model {_short(model)}"
    print(line); log.write(line + "\n"); log.flush()
    return v, model


def _short(model):
    keep = {k: v for k, v in model.items()
            if not k.startswith("k!") and len(v) < 30}
    return "{" + ", ".join(f"{k}={v}" for k, v in list(keep.items())[:8]) + "}"


# ==========================================================================
# replay-probe generation.  We classify the statement by its conclusion atom
# and emit the matching `¬P` probe with model witnesses substituted.
# ==========================================================================

def classify_concl(chain):
    parts = split_top_arrows(chain)
    concl = parts[-1].strip()
    # descend through a nested ∀ … , to the real conclusion
    while concl.startswith("∀"):
        _, rest = parse_binders(concl)
        concl = split_top_arrows(rest)[-1].strip()
    if "MemExtends" in concl:
        return "memext"
    if re.search(r"∃\s*b.*\?\s*=\s*some", concl):
        return "presence"
    if re.search(r"≤|<|>|≥|=", concl):
        return "arith"
    return "unknown"


def gen_and_run_replay(path, prop, binders, chain, body_text, model, ctx):
    cls = classify_concl(chain)
    if cls == "arith":
        return replay_arith(path, prop, binders, chain, body_text, model)
    if cls in ("memext", "presence"):
        return replay_mem(path, prop, binders, chain, body_text, model, cls)
    return ("NONE", cls, None)


def replay_arith(path, prop, binders, chain, body_text, model):
    """∀ (outer…), <linear arithmetic conclusion>.  Substitute each binder from
    the model, `intro H`, apply, `simp`/`decide` the false numeric fact."""
    args = []
    for nm, ty in binders:
        t = ty.strip()
        if t.endswith("StackLayout"):
            lo = model.get(f"{nm}_lo", "0"); hi = model.get(f"{nm}_hi", "1000000")
            args.append(f"⟨{_natlit(lo)}, {_natlit(hi)}⟩")
        elif "BitVec 64" in t or t.endswith("Addr"):
            v = model.get(f"{nm}_n", model.get(nm, "0")); args.append(f"({_natlit(v)}#64)")
        elif "BitVec 32" in t:
            v = model.get(nm, "0"); args.append(f"({_natlit(v)}#32)")
        elif t.endswith("Nat") or t.endswith("Int"):
            args.append(_natlit(model.get(nm, "0")))
        else:
            # struct ghost: build from its projections found in the model
            args.append(_struct_from_model(nm, t, model))
    short = prop.split(".")[-1]
    argstr = " ".join(args)
    probe = (f"{body_text}\n\nnamespace SmtReplay\n"
             f"set_option maxHeartbeats 1000000 in\n"
             f"theorem refuted : ¬ {prop} := by\n"
             f"  intro H\n"
             f"  have h := H {argstr}\n"
             f"  simp only [{prop}] at h\n"
             f"  revert h\n"
             f"  decide\n"
             f"#print axioms refuted\nend SmtReplay\n")
    return _run_replay(probe)


def replay_mem(path, prop, binders, chain, body_text, model, cls):
    """∀ SL sp m0 m, (agree off W) → MemExtends m0 m  /  presence.
    Build m0 with a byte at a lethal in-window address `A`, m = ∅ (deletes it),
    prove agree-off-W by `simp`, then contradict the conclusion at A."""
    # Z3 has certified the class is refutable (negation SAT).  The replay
    # instantiates the CANONICAL small witness of that same class, model-guided:
    # a window [lo, lo+16) with a single lethal byte at A=lo that m=∅ deletes.
    # (Using the model's raw 2^64-scale numbers would make the arithmetic side
    # proofs unwieldy; the class, not the exact number, is what Z3 found.)
    lo = int(_num(model.get((_find(binders, "StackLayout") or "SL") + "_lo", "0")))
    A = lo
    HI = A + 16                       # window upper bound sp.toNat; A ∈ [lo, HI)
    m0n = _find_mem(binders, first=True)
    n_outer_mem = sum(1 for _, t in binders if t.strip().endswith("Mem"))
    args = []
    for nm, ty in binders:
        t = ty.strip()
        if t.endswith("StackLayout"):
            args.append(f"⟨{lo}, 1000000⟩")
        elif "BitVec 64" in t or t.endswith("Addr"):
            args.append(f"({HI}#64)")
        elif t.endswith("Mem"):
            args.append("m0W" if nm == m0n else "(∅ : Mem)")
        else:
            args.append("_")
    # the deleting memory `m` is bound in the BODY's nested ∀ (not an outer
    # binder): supply it explicitly as ∅ right after the outer args.
    if n_outer_mem == 1:
        args.append("(∅ : Mem)")
    argstr = " ".join(args)
    hd = ("import Vsa.Sim.EvalSimCommon\nopen Vsa.MemRepr Vsa.Alloc Vsa.Sim\n"
          if "import" not in body_text.split("namespace")[0] else "")
    if cls == "memext":
        refute_tail = (
            f"  have hm0A : (m0W)[{A}]? = some (0#8) := by\n"
            f"    simp only [m0W, Std.ExtHashMap.getElem?_insert]; simp\n"
            f"  obtain ⟨b', hb'⟩ := hme {A} (0#8) hm0A\n"
            f"  rw [show ((∅ : Mem)[{A}]? : Option (BitVec 8)) = none from by\n"
            f"        simp only [Std.ExtHashMap.getElem?_empty]] at hb'\n"
            f"  exact absurd hb' (by simp)\n")
    else:  # presence  ∀ a, <lo'≤a> → <a<sp> → ∃ b, m[a]? = some b
        refute_tail = (
            f"  have hpz := hme {A} (by decide) (by decide)\n"
            f"  obtain ⟨b', hb'⟩ := hpz\n"
            f"  rw [show ((∅ : Mem)[{A}]? : Option (BitVec 8)) = none from by\n"
            f"        simp only [Std.ExtHashMap.getElem?_empty]] at hb'\n"
            f"  exact absurd hb' (by simp)\n")
    probe = (
        f"{hd}{body_text}\n\nnamespace SmtReplay\n"
        f"private def m0W : Mem := (∅ : Mem).insert {A} (0#8)\n"
        f"set_option maxHeartbeats 1000000 in\n"
        f"theorem refuted : ¬ {prop} := by\n"
        f"  intro H\n"
        f"  have hagree : (∀ a : Nat, ¬ (({lo} : Nat) ≤ a ∧ a < ({HI} : Nat)) "
        f"→ ((∅ : Mem)[a]? : Option (BitVec 8)) = (m0W)[a]?) := by\n"
        f"    intro a ha\n"
        f"    have haA : (({A} : Nat) == a) = false := by\n"
        f"      by_cases he : ({A} : Nat) = a\n"
        f"      · exact absurd ⟨he ▸ Nat.le_refl _, by omega⟩ ha\n"
        f"      · simp [he]\n"
        f"    rw [show ((∅ : Mem)[a]? : Option (BitVec 8)) = none from by\n"
        f"          simp only [Std.ExtHashMap.getElem?_empty]]\n"
        f"    rw [show ((m0W)[a]? : Option (BitVec 8)) = none from by\n"
        f"          simp only [m0W, Std.ExtHashMap.getElem?_insert, haA]\n"
        f"          rw [if_neg (by decide), Std.ExtHashMap.getElem?_empty]]\n"
        f"  have hme := H {argstr} hagree\n"
        f"{refute_tail}"
        f"#print axioms refuted\nend SmtReplay\n")
    return _run_replay(probe)


def _run_replay(probe):
    os.makedirs(LOGDIR, exist_ok=True)
    with open(os.path.join(LOGDIR, "smt-last-replay.lean"), "w") as f:
        f.write(probe)
    rc, out = run_lean(probe)
    if rc != 0:
        return "GAP", (out.strip().splitlines()[-1] if out.strip() else "?"), probe
    if "sorryAx" in out:
        return "GAP", "sorry inserted (replay incomplete)", probe
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    if m:
        ax = {a.strip() for a in m.group(1).split(",") if a.strip()}
        if ax <= AX_OK:
            return "REPLAYED", "axioms=" + ", ".join(sorted(ax)), probe
        return "GAP", "dirty axioms " + ", ".join(sorted(ax)), probe
    if "does not depend on any axioms" in out:
        return "REPLAYED", "(axiom-free)", probe
    return "GAP", "no #print axioms output", probe


# helpers ------------------------------------------------------------------

def _num(s):
    s = str(s).strip()
    m = re.search(r"-?\d+", s)
    return m.group(0) if m else "0"


def _natlit(s):
    n = int(_num(s))
    return str(max(n, 0))


def _find(binders, tystem):
    return next((n for n, t in binders if tystem in t or t.strip().endswith(tystem)), None)


def _find_mem(binders, first):
    mems = [n for n, t in binders if t.strip().endswith("Mem")]
    if not mems:
        return None
    return mems[0] if first else mems[-1]


def _lethal_addr(model, lo, sp):
    """Find an address where model has m0 defined & m undefined, inside [lo,sp)."""
    # scan the k! skolem arrays / store chains for a concrete int index in range
    cands = set()
    for v in model.values():
        for m in re.finditer(r"(?<![\w!])(\d{1,7})(?!\w)", str(v)):
            n = int(m.group(1))
            if lo <= n < sp:
                cands.add(n)
    return min(cands) if cands else None


def _struct_from_model(nm, ty, model):
    fields = [(k, v) for k, v in model.items() if k.startswith(nm + "_")]
    if not fields:
        return "_"
    return "⟨" + ", ".join(_natlit(v) for _, v in fields) + "⟩"


# ==========================================================================
# acceptance (a-e) on git-history forms + WInv candidates
# ==========================================================================

# (a) headroom pin — reconstructed hermetically (the 2865529 TermAssembly field
# class: a bare stack-headroom conclusion, no entry pin).
A_HEADROOM = r"""import Vsa.Alloc
open Vsa.Alloc (StackLayout)
namespace SmtAcc
def HeadroomBad : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64), SL.lo + 3264 ≤ sp.toNat
end SmtAcc
"""

# (b) the ∀-mcall pair (17773c4^ NegResid over-quant): MemExtends + presence.
B_MCALL = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def McallMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      MemExtends m0 mcall
end SmtAcc
"""

B_PRESENCE = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def McallPresence : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
end SmtAcc
"""

# (c) BinArmExtras.mem_ext (d7a5c91^) — identical MemExtends over-quant shape.
C_MEMEXT = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def BinArmMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ m : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m[a]? = m0[a]?) →
      MemExtends m0 m
end SmtAcc
"""

# (e) current HEAD amended forms — guarded so no deleting adversary bites.
E_HEAD = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim
namespace SmtAcc
def CurMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ m : Mem,
      (∀ a : Nat, m[a]? = m0[a]?) →
      MemExtends m0 m
end SmtAcc
"""

E_HEADROOM = r"""import Vsa.Alloc
open Vsa.Alloc (StackLayout StackOK)
namespace SmtAcc
def AmdHeadroom : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64), StackOK SL sp 3264 → SL.lo + 3264 ≤ sp.toNat
end SmtAcc
"""


def _tmpfile(text):
    p = os.path.join(LOGDIR, "smt-acc-" + str(abs(hash(text)) % 100000) + ".lean")
    with open(p, "w") as f:
        f.write(text)
    return p


def acceptance(log):
    os.makedirs(LOGDIR, exist_ok=True)
    log.write("\n## smt_check.py acceptance run\n\n")
    results = {}

    def refute(name, src, prop):
        p = _tmpfile(src)
        try:
            v, _ = smt_check("refute", p, prop, log)
        finally:
            os.unlink(p)
        results[name] = v
        return v

    def validate(name, src, prop):
        p = _tmpfile(src)
        try:
            v, _ = smt_check("validate", p, prop, log)
        finally:
            os.unlink(p)
        results[name] = v
        return v

    print("== (a) headroom pin (2865529 field class) ==")
    va = refute("a_headroom", A_HEADROOM, "SmtAcc.HeadroomBad")
    print("== (b) ∀-mcall pair (17773c4^) ==")
    vb1 = refute("b_memext", B_MCALL, "SmtAcc.McallMemExt")
    vb2 = refute("b_presence", B_PRESENCE, "SmtAcc.McallPresence")
    print("== (c) BinArmExtras.mem_ext (d7a5c91^) ==")
    vc = refute("c_binarm", C_MEMEXT, "SmtAcc.BinArmMemExt")

    # (d) WInv / budget-ladder mined candidates → --validate VALID-IN-FRAGMENT
    print("== (d) mined WInv / budget-ladder candidates ==")
    d_paths = [
        (os.path.join(ROOT, "experiments", "invariants", "io_write_loop.lean"),
         "IoWriteMined.IoWriteInvCandidate"),
    ]
    d_ok = True
    for pth, prop in d_paths:
        if os.path.exists(pth):
            v = validate("d_" + os.path.basename(pth), open(pth).read() and pth, prop)
            d_ok = d_ok and (v == "VALID-IN-FRAGMENT")
    # a hermetic budget-ladder candidate (falsity-#13 cured form: consumed ≤ budget)
    d_budget = r"""namespace SmtAcc
def BudgetLadderOk : Prop :=
  ∀ (base perLevel budget d consumed : Nat),
    consumed = d * perLevel + base → budget = base + 4096 → d ≤ 2 →
    perLevel ≤ 1088 → consumed ≤ budget
end SmtAcc
"""
    p = _tmpfile(d_budget)
    try:
        vdb = smt_check("validate", p, "SmtAcc.BudgetLadderOk", log)[0]
    finally:
        os.unlink(p)
    results["d_budget"] = vdb
    d_ok = d_ok and (vdb == "VALID-IN-FRAGMENT")

    # (e) current HEAD amended statements must NOT be REFUTED-REPLAYED
    print("== (e) HEAD amended forms must NOT be REFUTED-REPLAYED ==")
    ve1 = refute("e_memext", E_HEAD, "SmtAcc.CurMemExt")
    ve2 = refute("e_headroom", E_HEADROOM, "SmtAcc.AmdHeadroom")

    # gate
    def is_refuted(v):
        return v in ("REFUTED-REPLAYED", "REFUTED-MODULO-OPAQUE", "REFUTED-Z3-ONLY")
    replayed = sum(1 for k in ("a_headroom", "b_memext", "b_presence", "c_binarm")
                   if results.get(k) == "REFUTED-REPLAYED")
    a_ok = is_refuted(va)
    b_ok = is_refuted(vb1) and is_refuted(vb2)
    c_ok = is_refuted(vc)
    e_ok = (ve1 != "REFUTED-REPLAYED") and (ve2 != "REFUTED-REPLAYED")

    log.write("\n### Acceptance verdicts\n")
    for k, v in results.items():
        log.write(f"- {k}: {v}\n")
    log.write(f"- REFUTED-REPLAYED count (need ≥2): {replayed}\n")
    log.flush()

    ok = a_ok and b_ok and c_ok and d_ok and e_ok and replayed >= 2
    print(f"\n=== ACCEPTANCE (a){va} (b){vb1}/{vb2} (c){vc} "
          f"(d){'VALID' if d_ok else 'FAIL'} (e){ve1}/{ve2} "
          f"| replayed={replayed} → {'PASS' if ok else 'FAIL'} ===")
    log.write(f"\n**Acceptance → {'PASS' if ok else 'FAIL'}** "
              f"(replayed {replayed}/4, need ≥2)\n")
    log.flush()
    return ok


# ==========================================================================
# main
# ==========================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--refute", action="store_true")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--inhabit", action="store_true")
    ap.add_argument("--acceptance", action="store_true")
    ap.add_argument("--file", dest="file")
    ap.add_argument("--prop")
    ap.add_argument("--timeout", type=int, default=20000, help="z3 timeout (ms)")
    args = ap.parse_args()

    os.makedirs(LOGDIR, exist_ok=True)
    with open(LOG, "a") as log:
        log.write("\n## smt_check.py run\n\n")
        if args.acceptance:
            sys.exit(0 if acceptance(log) else 1)
        mode = ("refute" if args.refute else "validate" if args.validate
                else "inhabit" if args.inhabit else None)
        if mode is None:
            ap.error("pick a mode: --refute / --validate / --inhabit / --acceptance")
        if not (args.file and args.prop):
            ap.error(f"--{mode} needs --file <mod.lean> --prop <Ns.P>")
        smt_check(mode, args.file, args.prop, log, args.timeout)


if __name__ == "__main__":
    main()
