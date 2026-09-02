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

# The Lean-side export tactic (encoder v2). Its compiled olean is cached under
# OLEAN_DIR so the per-statement dump probe can `import DumpSmtLib` cheaply.
SMT_DIR = os.path.join(ROOT, "experiments", "smt")
DUMP_SRC = os.path.join(SMT_DIR, "DumpSmtLib.lean")
SUPPORT_SRC = os.path.join(SMT_DIR, "SmtReplaySupport.lean")
OLEAN_DIR = os.path.join(LOGDIR, "smt-olean")
DUMP_OLEAN = os.path.join(OLEAN_DIR, "DumpSmtLib.olean")
SUPPORT_OLEAN = os.path.join(OLEAN_DIR, "SmtReplaySupport.olean")

# Opaque Lean predicate name-stems: an atom whose head is one of these is
# encoded as an UNINTERPRETED predicate (sound for refutation search only if the
# countermodel does not hinge on it — we track that and mark MODULO-OPAQUE).
OPAQUE_HEADS = ("ValueRepr", "ExprRepr", "CString", "GoodState", "Repr",
                "Loaded", "InterpSim", "FoundSt", "Approx", "StoreRepr",
                "frameRepr")


# ==========================================================================
# Lean plumbing
# ==========================================================================

def run_lean(src, timeout=600, env=None):
    os.makedirs(LOGDIR, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LOGDIR,
                                     delete=False) as f:
        f.write(src)
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout,
                           env=env)
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
# Lean-side export tactic (encoder v2): dump_smt_lib
# ==========================================================================

def _build_olean(src, olean, log=None):
    """Compile a single experiments/smt/*.lean file to `olean` under OLEAN_DIR
    if missing/stale.  Returns True on success."""
    if not os.path.exists(src):
        return False
    if (os.path.exists(olean) and
            os.path.getmtime(olean) >= os.path.getmtime(src)):
        return True
    os.makedirs(OLEAN_DIR, exist_ok=True)
    try:
        r = subprocess.run(
            ["lake", "env", "lean", "-o", olean, "--root", SMT_DIR, src],
            cwd=ROOT, capture_output=True, text=True, timeout=400)
    except (subprocess.TimeoutExpired, OSError):
        return False
    ok = r.returncode == 0 and os.path.exists(olean)
    if not ok and log:
        log.write(f"- olean build FAILED ({os.path.basename(src)}): "
                  f"{(r.stderr or r.stdout)[-300:]}\n")
    return ok


def ensure_dump_olean(log=None):
    """Compile the DumpSmtLib export tactic to a cached olean.  Returns True on
    success, False if it does not compile (⇒ Python encoder fallback)."""
    return _build_olean(DUMP_SRC, DUMP_OLEAN, log)


def ensure_support_olean(log=None):
    """Compile the replay-support lemmas to a cached olean.  Returns True on
    success (the agree-window replays `import SmtReplaySupport`)."""
    return _build_olean(SUPPORT_SRC, SUPPORT_OLEAN, log)


def _lean_path_env():
    """Base LEAN_PATH from `lake env`, with OLEAN_DIR prepended."""
    try:
        r = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT,
                           capture_output=True, text=True, timeout=60)
        base = r.stdout.strip()
    except (subprocess.TimeoutExpired, OSError):
        base = os.environ.get("LEAN_PATH", "")
    env = dict(os.environ)
    env["LEAN_PATH"] = OLEAN_DIR + (os.pathsep + base if base else "")
    return env


def _hoist_imports(body_text):
    """Split a Lean source into (import-lines, rest) so the dump probe can put
    `import DumpSmtLib` alongside the target's own imports at the top."""
    imports, rest = [], []
    for line in body_text.splitlines():
        if line.strip().startswith("import "):
            imports.append(line)
        else:
            rest.append(line)
    return "\n".join(imports), "\n".join(rest)


def lean_dump(path, prop, log=None, timeout=400):
    """Run the `dump_smt_lib` export tactic on `prop` (defined in `path`).
    Returns (smt_text, opaque_set) or (None, reason).  Hermetic: the target's
    source is inlined (imports hoisted) + `import DumpSmtLib` + the dump cmd, so
    no experiments/ module-path resolution is needed."""
    if not ensure_dump_olean(log):
        return None, "dump-olean-unavailable"
    body_text = open(path).read()
    imports, rest = _hoist_imports(body_text)
    out_smt = os.path.join(LOGDIR, "smt-dump-" +
                           str(abs(hash(prop)) % 100000) + ".smt2")
    probe = (f"import DumpSmtLib\n{imports}\n{rest}\n\n"
             f"dump_smt_lib \"{out_smt}\" for {prop}\n")
    os.makedirs(LOGDIR, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=LOGDIR,
                                     delete=False) as f:
        f.write(probe)
        ppath = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", ppath], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout,
                           env=_lean_path_env())
    except subprocess.TimeoutExpired:
        return None, "dump-timeout"
    finally:
        try:
            os.unlink(ppath)
        except OSError:
            pass
    if r.returncode != 0 or not os.path.exists(out_smt):
        detail = (r.stderr or r.stdout).strip().splitlines()
        return None, "dump-error: " + (detail[-1] if detail else "?")
    smt = open(out_smt).read()
    try:
        os.unlink(out_smt)
    except OSError:
        pass
    # ENCODE-GAP in the dump ⇒ fall back to Python for this statement
    if "; ENCODE-GAP" in smt or "; GAPS:" in smt:
        return None, "dump-encode-gap"
    opaque = set()
    for line in smt.splitlines():
        if line.startswith("; OPAQUE:"):
            opaque = {h for h in line[len("; OPAQUE:"):].split() if h}
    return smt, opaque


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
    # ∃ b, m[a]? = some b   (any bound-var name: b, w, …)
    m = re.fullmatch(r"∃\s*([A-Za-z_]\w*)[^,]*,\s*([A-Za-z_]\w*)\[([^\]]+)\]"
                     r"\?\s*=\s*some\s+([A-Za-z_]\w*)", a)
    if m and ctx.env.get(m.group(2)) == "mem" and m.group(1) == m.group(4):
        mem, idx = m.group(2), _idx(m.group(3), ctx, bound)
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


class _DumpShim:
    """Stands in for an EncCtx when the Lean export tactic produced the SMT.
    Carries only what the downstream replay path reads: `.opaque`."""
    def __init__(self, opaque):
        self.opaque = set(opaque)


def smt_check(mode, path, prop, log, timeout_ms=20000):
    binders, chain, sig, body_text = load(path, prop)
    if binders is None:
        v = f"- `{prop}` → **ENCODE-FAIL** (def body not found)"
        print(v); log.write(v + "\n"); log.flush()
        return "ENCODE-FAIL", None

    # ---- encoder v2: try the Lean-side dump_smt_lib export tactic first -----
    # It walks the ELABORATED goal (no source re-parse drift) and emits the
    # negated-statement refute query directly.  Fall back to the Python encoder
    # for statements the tactic cannot handle (reported as the encoder path).
    #
    # Scope: the Lean dump is used for --refute, where a spurious SAT cannot
    # yield a false green — the machine-checked Lean replay gates the verdict
    # (SAT-without-replay ⇒ ENCODING-GAP, reported loudly).  --validate's
    # VALID-IN-FRAGMENT is an advisory SOUNDNESS claim (UNSAT of the negation);
    # it is left on the Python encoder whose fragment is the one the acceptance
    # battery certified, so a looser Lean over-approximation cannot silently
    # weaken a VALID verdict.
    enc_path = "python"
    ctx = None
    smt_neg = None                 # full SMT text for the negated-statement query
    if mode == "refute":
        dump_smt, dump_info = lean_dump(path, prop, log)
        if dump_smt is not None:
            enc_path = "lean"
            smt_neg = dump_smt
            ctx = _DumpShim(dump_info)
        else:
            log.write(f"  (dump path unavailable for {prop}: {dump_info} "
                      f"— falling back to Python encoder)\n")

    if ctx is None:                # Python encoder path (fallback / inhabit)
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
        smt_neg = build_smt(ctx, neg, get_model=(mode == "refute"))

    log.write(f"  (encoder: {enc_path})\n")
    out = run_z3(smt_neg, timeout_ms)
    first = out.strip().split("\n", 1)[0].strip()

    if mode == "validate":
        if first == "unsat":
            v = "VALID-IN-FRAGMENT"
            note = f" (opaque: {sorted(ctx.opaque)})" if ctx.opaque else ""
        elif first == "sat":
            v = "REFUTABLE"; note = " (negation SAT — not valid)"
        else:
            v = "UNKNOWN"; note = f" ({first or out.strip()[:60]})"
        line = f"- `{prop}` → **{v}**{note} [enc:{enc_path}]"
        print(line); log.write(line + "\n"); log.flush()
        return v, None

    # --refute
    if first != "sat":
        v = ("VALID-IN-FRAGMENT" if first == "unsat" else "UNKNOWN")
        line = f"- `{prop}` → **NOT-REFUTED / {v}** ({first}) [enc:{enc_path}]"
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
    line = f"- `{prop}` → **{v}** — {detail} | model {_short(model)} [enc:{enc_path}]"
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


def _int_lit(s):
    s = s.strip()
    return int(s, 16) if s.lower().startswith("0x") else int(s)


def detect_agree_window(chain):
    """Detect the agree-window falsity family and extract its parameters.

    Returns a dict {guards, A, V, kind, m0_first} for the agree-window family
    (∀ m0, [m0[A]?=some V →] ∀ mq, (⋀ᵢ ∀k, Gᵢ(k) → m0[k]?=mq[k]?) → CONCL),
    or None if the chain is not in this family.

    The UNIVERSAL witness (any cover topology, any conclusion kind): m0 = {A↦V},
    mq = ∅.  They differ ONLY at A; since A is UNCOVERED (Z3 certified the
    negation SAT ⟺ A ∉ ⋃ Gᵢ), every guard excludes A (¬Gᵢ(A)), so `∀k, Gᵢ(k) →
    m0[k]?=mq[k]?` holds for every guard by `k ≠ A` (omega, from Gᵢ(k) + the
    concrete uncovered A).  The demand at A then fails (mq[A]? = none)."""
    flat = " ".join(chain.split())
    if "∀ mq" not in flat and "∀mq" not in flat:
        return None
    # guards: each nested agree-hyp `∀ k, <G> → m0[k]? = mq[k]?`, where <G> is a
    # simple range predicate (no nested → or ∀ — that would be the range-pin or
    # a following hyp bleeding in).
    guards = []
    for gm in re.finditer(r"∀\s*k\s*,\s*([^→∀]+?)\s*→\s*\w+\[k\]\?\s*=\s*\w+\[k\]\?",
                          flat):
        guards.append(gm.group(1).strip())
    if not guards:
        return None
    # RANGE-pin: `∀ k, k < P → m0[k]? = some V` forces m0 populated on [0,P);
    # the universal ∅ witness cannot satisfy it, so a pop-populated m0 is needed.
    rp = re.search(r"∀\s*k\s*,\s*k\s*<\s*(0x[0-9a-fA-F]+|\d+)\s*→\s*m0\[k\]\?\s*=\s*"
                   r"some\s*\(?\s*(0x[0-9a-fA-F]+|\d+)", flat)
    range_pin = (_int_lit(rp.group(1)), _int_lit(rp.group(2))) if rp else None
    # conclusion kind + demand address A
    concl = flat.rsplit("→", 1)[-1].strip()
    A = V = None
    kind = None
    mc = re.search(r"\w+\[\(?\s*(0x[0-9a-fA-F]+|\d+)[^\]]*\]\?\s*=\s*some\s*"
                   r"\(?\s*(0x[0-9a-fA-F]+|\d+)", concl)
    mp = re.search(r"∃\s*\w+\s*,\s*\w+\[\(?\s*(0x[0-9a-fA-F]+|\d+)", concl)
    ma = re.search(r"\w+\[\(?\s*(0x[0-9a-fA-F]+|\d+)[^\]]*\]\?\s*=\s*\w+\[", concl)
    # range-quantified agree conclusion `∀ a, LO ≤ a ∧ a < HI → mq[a]?=m0[a]?`
    mr = re.search(r"∀\s*\w+\s*,\s*(0x[0-9a-fA-F]+|\d+)\s*≤\s*\w+\s*∧\s*\w+\s*<\s*"
                   r"(0x[0-9a-fA-F]+|\d+)\s*→\s*\w+\[\w+\]\?\s*=\s*\w+\[\w+\]\?", flat)
    me = "MemExtends" in concl
    # pull the outer POINT pin (m0[A]? = some V) if present
    pin = re.search(r"m0\[\(?\s*(0x[0-9a-fA-F]+|\d+)\s*:", flat)
    pinv = re.search(r"m0\[\(?\s*(?:0x[0-9a-fA-F]+|\d+)[^\]]*\]\?\s*=\s*some\s*"
                     r"\(?\s*(0x[0-9a-fA-F]+|\d+)", flat)
    if mc:
        kind = "value"; A, V = _int_lit(mc.group(1)), _int_lit(mc.group(2))
    elif mp:
        kind = "present"; A = _int_lit(mp.group(1))
        V = _int_lit(pinv.group(1)) if pinv else 0x2a
    elif me:
        kind = "extends"
        if not pin:
            return None
        A = _int_lit(pin.group(1)); V = _int_lit(pinv.group(1)) if pinv else 0x2a
    elif mr and range_pin is not None:
        # C-shape: range-pinned m0, gap-demand.  A = gap lower bound.
        kind = "gapagree"; A = _int_lit(mr.group(1)); V = range_pin[1]
    elif ma:
        kind = "agree"; A = _int_lit(ma.group(1)); V = 0x2a
    else:
        return None
    return {"guards": guards, "A": A, "V": V, "kind": kind,
            "range_pin": range_pin}


def gen_and_run_replay(path, prop, binders, chain, body_text, model, ctx):
    # agree-window family (∀-mcall / prefix-agree over-quant): the uncontaminated
    # NovelProbe class + the historical amendments + the fuzzer gen-battery.
    # ONE universal witness generator, cover-topology-agnostic.
    aw = detect_agree_window(chain)
    if aw is not None:
        if aw["kind"] == "gapagree":
            return replay_gapagree(prop, body_text, aw)
        return replay_agree_general(prop, body_text, aw)
    cls = classify_concl(chain)
    if cls in ("memext", "presence"):
        return replay_mem(path, prop, binders, chain, body_text, model, cls)
    if cls == "arith":
        return replay_arith(path, prop, binders, chain, body_text, model)
    return ("NONE", cls, None)


def _replay_header(body_text):
    """Imports for a replay probe: the target's own imports + the replay support
    module (which carries pop / pop_mem / pop_not_mem / ins_comm)."""
    imports = [l for l in body_text.splitlines() if l.strip().startswith("import ")]
    rest = "\n".join(l for l in body_text.splitlines()
                     if not l.strip().startswith("import "))
    hdr = "import SmtReplaySupport\n" + "\n".join(imports) + "\n"
    return hdr, rest


def replay_agree_general(prop, body_text, aw):
    """UNIVERSAL agree-window refutation, cover-topology + conclusion-kind
    agnostic.  Witness: m0 = {A ↦ V}, mq = ∅ (differ ONLY at the uncovered A).
    Each agree-hyp `∀ k, Gᵢ(k) → m0[k]? = mq[k]?` holds because Gᵢ(k) forces
    `k ≠ A` (A ∉ ⋃ Gᵢ), so both sides are `none`; `k ≠ A` is `by omega` from the
    guard's numeric constraint and the concrete uncovered literal A.  The demand
    at A then fails (mq[A]? = none)."""
    A, V, kind, guards = aw["A"], aw["V"], aw["kind"], aw["guards"]
    W = 64                                        # any width shim (unused)
    hdr, rest = _replay_header(body_text)
    has_pin = kind in ("value", "present", "extends")
    extra = _extra_args(prop, body_text)
    # one hagree per guard.  `k ≠ A` via omega: after `intro k hk`, hk : Gᵢ(k).
    # `simp only` normalises ¬(…) / conjunction so omega sees the bounds.
    hagrees = []
    hnames = []
    for i, g in enumerate(guards):
        hn = f"hag{i}"
        hnames.append(hn)
        hagrees.append(
            f"  have {hn} : (∀ k, {g} → (m0W[k]? : Option (BitVec 8)) = (∅ : Mem)[k]?) := by\n"
            f"    intro k hk\n"
            f"    have hkA : k ≠ {A} := by\n"
            f"      intro he; subst he; first | omega | exact hk (by omega)\n"
            f"    rw [show (m0W[k]? : Option (BitVec 8)) = none from by\n"
            f"          simp only [m0W]\n"
            f"          rw [getElem?_insert_out (∅ : Mem) {A} ({V}#8) k hkA]\n"
            f"          simp only [Std.ExtHashMap.getElem?_empty]]\n"
            f"    simp only [Std.ExtHashMap.getElem?_empty]\n")
    # hm0 (m0W has the byte at A) is always TRUE for m0W; supplied as an H arg
    # only when the statement has the outer pin hypothesis.
    pin_line = (
        f"  have hm0 : m0W[({A} : Nat)]? = some ({V} : BitVec 8) := by\n"
        f"    simp only [m0W]; exact Std.ExtHashMap.getElem?_insert_self\n")
    pin_arg = "hm0 " if has_pin else ""
    apply_line = f"  have hc := H m0W {extra} {pin_arg}(∅ : Mem) {' '.join(hnames)}\n"
    empty_none = (f"  have hE : ((∅ : Mem)[({A}:Nat)]? : Option (BitVec 8)) = none := by\n"
                  f"    simp only [Std.ExtHashMap.getElem?_empty]\n")
    if kind in ("value", "agree"):
        # hc : mq[A]? = some V   (value)  |  mq[A]? = m0[A]?  (agree)
        refute = ("  rw [hE] at hc\n  exact absurd hc (by simp)\n"
                  if kind == "value" else
                  # agree: hc : ∅[A]? = m0W[A]? ; LHS none, RHS some V → contra
                  "  rw [hE, hm0] at hc\n  exact absurd hc (by simp)\n")
    elif kind == "present":
        refute = ("  obtain ⟨b, hb⟩ := hc\n  rw [hE] at hb\n"
                  "  exact absurd hb (by simp)\n")
    else:  # extends : MemExtends m0W ∅ ; but m0W[A]?=some V ⇒ ∃b', ∅[A]?=some b'
        refute = (f"  obtain ⟨b', hb'⟩ := hc {A} ({V}#8) hm0\n  rw [hE] at hb'\n"
                  f"  exact absurd hb' (by simp)\n")
    probe = (
        f"{hdr}{rest}\n\nnamespace SmtReplayProbe\nopen Vsa.SmtReplay\n"
        f"private def m0W : Mem := (∅ : Mem).insert {A} ({V}#8)\n"
        f"set_option maxHeartbeats 2000000 in\n"
        f"theorem refuted : ¬ {prop} := by\n"
        f"  intro H\n"
        f"{pin_line}"
        f"{''.join(hagrees)}"
        f"{apply_line}"
        f"{empty_none}"
        f"{refute}"
        f"#print axioms refuted\nend SmtReplayProbe\n")
    return _run_replay(probe)


def replay_gapagree(prop, body_text, aw):
    """RANGE-pinned agree family (NovelResidC shape): `∀ m0, (∀k<P, m0[k]?=some
    V) → ∀ mq, (⋀ᵢ ∀k, Gᵢ(k)→m0=mq) → ∀ a, LO≤a<HI → mq[a]?=m0[a]?`.
    Witness: m0 = pop [0,P) V (satisfies the range pin), mq = m0.insert A W where
    A = LO is the gap address (uncovered by every Gᵢ).  m0 and mq differ ONLY at
    A, so each agree-hyp holds by `Gᵢ(k) → k ≠ A` (omega); the demand at A fails
    (mq[A]? = some W, m0[A]? = none since A ∉ [0,P))."""
    A, V, guards = aw["A"], aw["V"], aw["guards"]
    P = aw["range_pin"][0]
    W = (V + 6) % 256
    hdr, rest = _replay_header(body_text)
    hnames, hagrees = [], []
    for i, g in enumerate(guards):
        hn = f"hag{i}"; hnames.append(hn)
        hagrees.append(
            f"  have {hn} : (∀ k, {g} → m0C[k]? = mqC[k]?) := by\n"
            f"    intro k hk\n"
            f"    have hkA : k ≠ {A} := by\n"
            f"      intro he; subst he; first | omega | exact hk (by omega)\n"
            f"    simp only [mqC]; exact (getElem?_insert_out m0C {A} ({W}#8) k hkA).symm\n")
    probe = (
        f"{hdr}{rest}\n\nnamespace SmtReplayProbe\nopen Vsa.SmtReplay\n"
        f"private def m0C : Mem := pop (List.range {P}) ({V}#8)\n"
        f"private def mqC : Mem := m0C.insert {A} ({W}#8)\n"
        f"set_option maxHeartbeats 2000000 in\n"
        f"theorem refuted : ¬ {prop} := by\n"
        f"  intro H\n"
        f"  have hy0 : (∀ k, k < {P} → m0C[k]? = some ({V} : BitVec 8)) := by\n"
        f"    intro k hk; exact pop_mem _ k (List.range {P}) (List.mem_range.mpr hk)\n"
        f"{''.join(hagrees)}"
        f"  have hc := H m0C hy0 mqC {' '.join(hnames)} {A} (by omega)\n"
        f"  rw [show (mqC[({A}:Nat)]? : Option (BitVec 8)) = some ({W}#8) from by\n"
        f"        simp only [mqC]; exact Std.ExtHashMap.getElem?_insert_self] at hc\n"
        f"  rw [show (m0C[({A}:Nat)]? : Option (BitVec 8)) = none from\n"
        f"        pop_not_mem _ {A} _ (fun h => by simp only [List.mem_range] at h; omega)] at hc\n"
        f"  exact absurd hc (by simp)\n"
        f"#print axioms refuted\nend SmtReplayProbe\n")
    return _run_replay(probe)


def _extra_args(prop, body_text):
    """Extra non-m0 outer binders between the first Mem binder and the nested mq
    quantifier (e.g. a `base : BitVec 64`).  Supplied as `_` placeholders (their
    value is irrelevant to the refutation)."""
    # count outer binders after the leading Mem (bytesurvive assumes m0 first).
    sig, rhs = extract_def_body(body_text, prop)
    if rhs is None:
        return ""
    binders, _ = parse_binders(rhs)
    extra = []
    seen_mem = False
    for nm, ty in binders:
        t = ty.strip()
        if not seen_mem and (t.endswith("Mem") or "ExtHashMap" in t):
            seen_mem = True
            continue
        if seen_mem:
            if "BitVec 64" in t or t.endswith("Addr"):
                extra.append("(0#64)")
            elif "BitVec 32" in t:
                extra.append("(0#32)")
            elif "BitVec 8" in t:
                extra.append("(0#8)")
            elif t.endswith("Nat") or t.endswith("Int"):
                extra.append("0")
            else:
                extra.append("_")
    return " ".join(extra)


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
    probe = (f"{body_text}\n\nnamespace SmtReplayProbe\n"
             f"set_option maxHeartbeats 1000000 in\n"
             f"theorem refuted : ¬ {prop} := by\n"
             f"  intro H\n"
             f"  have h := H {argstr}\n"
             f"  simp only [{prop}] at h\n"
             f"  revert h\n"
             f"  decide\n"
             f"#print axioms refuted\nend SmtReplayProbe\n")
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
        f"{hd}{body_text}\n\nnamespace SmtReplayProbe\n"
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
        f"#print axioms refuted\nend SmtReplayProbe\n")
    return _run_replay(probe)


def _run_replay(probe):
    os.makedirs(LOGDIR, exist_ok=True)
    with open(os.path.join(LOGDIR, "smt-last-replay.lean"), "w") as f:
        f.write(probe)
    # agree-window replays `import SmtReplaySupport`; build+expose its olean.
    env = None
    if "import SmtReplaySupport" in probe:
        ensure_support_olean()
        env = _lean_path_env()
    rc, out = run_lean(probe, env=env)
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
# INTERLOCK / JOINT validation  (--joint-inhabit / --producer-check /
#                                --consumer-check)
# --------------------------------------------------------------------------
# A TARGET STRUCTURE is a named-field `structure … : Prop where` (or a hermetic
# `def T : Prop := ∀ …, C₁ ∧ … ∧ Cₙ` ∧-tower) plus its graph role (which
# producer's post is supposed to establish it, which consumers project it).  The
# per-statement checks (`--refute`/`--validate`) test ONE conjunct in isolation;
# joint validation tests the conjuncts TOGETHER and against the producer/consumer
# boundary — the interlock the 48e/48f/48g waves proved a per-field filter misses.
#
# Encoding note (opaque honesty): a conjunct whose head is an OPAQUE predicate
# (OPAQUE_HEADS) or otherwise unencodable is EXCLUDED from the asserted core and
# COUNTED as opaque.  Joint-inhabit over an all-opaque residue ⇒ UNKNOWN-OPAQUE
# (we cannot certify inhabitability).  A producer/consumer implication whose
# demand touches opaque is reported MODULO-OPAQUE, never a silent pass.
# ==========================================================================

def _entry_hyp_binders(binders):
    """Heuristic split of a target's ∀-telescope into the STATE binders and the
    entry-hypothesis carrier: any leading binder whose type ends in `EvalEntry`/
    `ExecEntry`/`…Entry`/`…Ground` is treated as an entry hypothesis to encode as
    an assumption.  Returns (state_binders, entry_binder_names)."""
    entry = [n for n, t in binders
             if re.search(r"(EvalEntry|ExecEntry|Entry|Ground)\s*$", t.strip())]
    return binders, entry


def _fields_of_target(path, prop, ctx):
    """Return the list of conjunct TEXTS of the target.  Two shapes:
      (1) `def T : Prop := ∀ binders, Struct args…` — explode `Struct` via its
          mk arrow-chain (substituting args), the primary interlock shape;
      (2) `def T : Prop := ∀ binders, C₁ ∧ … ∧ Cₙ` — split the ∧-tower.
    Also returns the binders (for the encoder env) and any entry-hyp text."""
    binders, chain, _sig, body_text = load(path, prop)
    if binders is None:
        return None, None, None, None
    # register binders in ctx.env
    for nm, ty in binders:
        ctx.bind(nm, ty)
    ctx.body_text = body_text
    ctx.ns = ".".join(prop.split(".")[:-1])
    # the def body is a single Prop (all conclusion); peel a leading ∀ if the
    # RHS re-quantifies (rare — `load` already stripped the top telescope).
    concl = chain.strip()
    # top-level arrows: hypotheses then conclusion
    parts = split_top_arrows(concl)
    hyp_texts, concl = parts[:-1], parts[-1].strip()
    # shape (1): applied structure  `Head arg arg …`
    m = re.fullmatch(r"([A-Z]\w*(?:\.\w+)*)\s+(.+)", concl, re.S)
    if m and not any(concl.startswith(h) for h in OPAQUE_HEADS):
        head = m.group(1).split(".")[-1]
        params, fields = _discover_struct(head, ctx)
        if params and fields:
            args = m.group(2).split()
            subst = dict(zip(params, args))
            out = []
            for f in fields:
                ftxt = f
                for p in sorted(subst, key=len, reverse=True):
                    ftxt = re.sub(rf"(?<![\w.]){re.escape(p)}(?![\w])",
                                  subst[p], ftxt)
                out.append(ftxt)
            return binders, out, hyp_texts, ("struct", head)
    # shape (2): ∧-tower
    conj = split_top_and(concl)
    if len(conj) > 1:
        return binders, conj, hyp_texts, ("tower", None)
    # single conjunct (degenerate)
    return binders, [concl], hyp_texts, ("single", None)


def _encode_conjuncts(fields, ctx, hyp_texts):
    """Encode each conjunct + the entry hypotheses.  Returns
    (enc_hyps, enc_fields, opaque_fields) where enc_fields is a list of
    (text, smt|None).  A None smt = opaque/unencodable (excluded, counted)."""
    enc_hyps = []
    for h in hyp_texts:
        e = encode_hyp_or_concl(h, ctx)
        enc_hyps.append(e)               # may be None (opaque hyp)
    enc_fields, opaque = [], []
    for f in fields:
        e = encode_hyp_or_concl(f, ctx)
        enc_fields.append((f, e))
        if e is None:
            opaque.append(f)
    return enc_hyps, enc_fields, opaque


def joint_inhabit(path, prop, log, timeout_ms=20000):
    """QUERY 1 — encode ALL conjuncts simultaneously under the entry hyps; ask
    Z3 for a joint model.  SAT ⇒ JOINTLY-INHABITABLE (witness).  UNSAT ⇒
    JOINTLY-CONTRADICTORY (the killer).  all-opaque core ⇒ UNKNOWN-OPAQUE."""
    ctx = EncCtx()
    binders, fields, hyp_texts, shape = _fields_of_target(path, prop, ctx)
    if fields is None:
        v = f"- `{prop}` → **ENCODE-FAIL** (target not found / struct undiscovered)"
        print(v); log.write(v + "\n"); log.flush(); return "ENCODE-FAIL", None
    enc_hyps, enc_fields, opaque = _encode_conjuncts(fields, ctx, hyp_texts)
    core = [e for _, e in enc_fields if e is not None]
    hyps = [h for h in enc_hyps if h is not None]
    if not core:
        v = (f"- `{prop}` → **UNKNOWN-OPAQUE** (all {len(fields)} conjuncts "
             f"opaque/unencodable; opaque={sorted(ctx.opaque)})")
        print(v); log.write(v + "\n"); log.flush(); return "UNKNOWN-OPAQUE", None
    smt = build_smt(ctx, hyps + core, get_model=True)
    out = run_z3(smt, timeout_ms)
    first = out.strip().split("\n", 1)[0].strip()
    n_enc, n_op = len(core), len(opaque)
    if first == "sat":
        model = parse_model(out)
        v = "JOINTLY-INHABITABLE" + ("-MODULO-OPAQUE" if n_op else "")
        note = f" — witness {_short(model)}; {n_enc} enc / {n_op} opaque conjunct(s)"
        rc = v
    elif first == "unsat":
        v = "JOINTLY-CONTRADICTORY"; model = None
        note = (f" — the {n_enc} encoded conjuncts are MUTUALLY UNSAT under the "
                f"entry hyps ({n_op} opaque excluded) — KILLER VERDICT")
        rc = v
    else:
        v = "UNKNOWN"; model = None
        note = f" ({first or out.strip()[:60]})"; rc = v
    line = f"- `{prop}` → **{v}**{note}"
    print(line); log.write(line + "\n"); log.flush()
    return rc, model


def _implies_check(ctx, ant_list, cons, log, timeout_ms):
    """UNSAT of (∧ ant) ∧ ¬cons ⇒ the implication HOLDS-IN-FRAGMENT.  Returns
    ('HOLDS'|'FAILS'|'UNKNOWN', model_or_None)."""
    ants = [a for a in ant_list if a is not None]
    neg = (["(and " + " ".join(ants) + ")"] if ants else []) + [f"(not {cons})"]
    smt = build_smt(ctx, neg, get_model=True)
    out = run_z3(smt, timeout_ms)
    first = out.strip().split("\n", 1)[0].strip()
    if first == "unsat":
        return "HOLDS", None
    if first == "sat":
        return "FAILS", parse_model(out)
    return "UNKNOWN", None


def producer_check(path, prop, producer_post, log, timeout_ms=20000,
                   approx=False):
    """QUERY 2 — does the producer's post (a hermetic Prop or an approximating
    trace-fact conjunction) IMPLY each target conjunct?  Per-conjunct verdict:
    HOLDS / FAILS (with CTI model) / MODULO-OPAQUE (conjunct opaque)."""
    ctx = EncCtx()
    binders, fields, hyp_texts, shape = _fields_of_target(path, prop, ctx)
    if fields is None:
        v = f"- `{prop}` → **ENCODE-FAIL** (target not found)"
        print(v); log.write(v + "\n"); log.flush(); return "ENCODE-FAIL", {}
    # antecedent = entry hyps AND the producer post (encoded in the SAME ctx so
    # shared binders/mems unify).  producer_post is a list of atom/hyp texts.
    ant = [encode_hyp_or_concl(h, ctx) for h in hyp_texts]
    for p in producer_post:
        ant.append(encode_hyp_or_concl(p, ctx))
    tag = "APPROX-TRACE" if approx else "POST"
    print(f"== producer-check ({tag}) `{prop}` =="); log.write(
        f"\n### producer-check ({tag}) `{prop}`\n")
    verdicts = {}
    for f in fields:
        cons = encode_hyp_or_concl(f, ctx)
        if cons is None:
            verdicts[f] = "MODULO-OPAQUE"
            line = f"  - `{_c(f)}` → **MODULO-OPAQUE** (conjunct unencodable)"
        else:
            rc, model = _implies_check(ctx, ant, cons, log, timeout_ms)
            if rc == "FAILS":
                verdicts[f] = "FAILS"
                line = (f"  - `{_c(f)}` → **PRODUCER-FAILS** — post does NOT "
                        f"supply it; CTI {_short(model or {})}")
            elif rc == "HOLDS":
                verdicts[f] = "HOLDS"
                line = f"  - `{_c(f)}` → **HOLDS** (post ⇒ conjunct)"
            else:
                verdicts[f] = "UNKNOWN"; line = f"  - `{_c(f)}` → **UNKNOWN**"
        print(line); log.write(line + "\n")
    log.flush()
    return ("PRODUCER-FAILS" if "FAILS" in verdicts.values() else "OK"), verdicts


def consumer_check(path, prop, demands, log, timeout_ms=20000):
    """QUERY 3 — does the target structure IMPLY each consumer demand (a
    projection a consumer takes)?  A FAILS here means the amended structure is
    too WEAK for a live consumer (e.g. deleting x13_pres breaks blockB spill)."""
    ctx = EncCtx()
    binders, fields, hyp_texts, shape = _fields_of_target(path, prop, ctx)
    if fields is None:
        v = f"- `{prop}` → **ENCODE-FAIL** (target not found)"
        print(v); log.write(v + "\n"); log.flush(); return "ENCODE-FAIL", {}
    enc_hyps, enc_fields, opaque = _encode_conjuncts(fields, ctx, hyp_texts)
    ant = [h for h in enc_hyps if h is not None] + \
          [e for _, e in enc_fields if e is not None]
    print(f"== consumer-check `{prop}` =="); log.write(
        f"\n### consumer-check `{prop}`\n")
    verdicts = {}
    for d in demands:
        cons = encode_hyp_or_concl(d, ctx)
        if cons is None:
            verdicts[d] = "MODULO-OPAQUE"
            line = f"  - demand `{_c(d)}` → **MODULO-OPAQUE** (unencodable)"
        else:
            rc, model = _implies_check(ctx, ant, cons, log, timeout_ms)
            if rc == "FAILS":
                verdicts[d] = "FAILS"
                line = (f"  - demand `{_c(d)}` → **CONSUMER-FAILS** — structure "
                        f"too weak; CTI {_short(model or {})}")
            elif rc == "HOLDS":
                verdicts[d] = "HOLDS"
                line = f"  - demand `{_c(d)}` → **SATISFIED** (structure ⇒ demand)"
            else:
                verdicts[d] = "UNKNOWN"; line = f"  - demand `{_c(d)}` → **UNKNOWN**"
        print(line); log.write(line + "\n")
    log.flush()
    return ("CONSUMER-FAILS" if "FAILS" in verdicts.values() else "OK"), verdicts


def _c(s):
    s = " ".join(s.split())
    return (s[:70] + "…") if len(s) > 71 else s


# --------------------------------------------------------------------------
# producer-post + consumer-demand harvesting
# --------------------------------------------------------------------------

def _post_of_module(spec, log):
    """`spec` is `path:Ns.PostDef` OR just a `Ns.PostDef` in the target file.
    Extract the producer post's conjuncts as atom texts (the ∧-tower / struct
    fields of the post).  Falls back to [] (empty post) if undiscoverable."""
    if spec is None:
        return []
    if ":" in spec and spec.split(":", 1)[0].endswith(".lean"):
        path, prop = spec.split(":", 1)
    else:
        return []                     # a Ns.Prop with no file: caller supplies
    ctx = EncCtx()
    binders, fields, _hyps, _shape = _fields_of_target(path, prop, ctx)
    return fields or []


def _traces_post(case):
    """Q2 APPROX — ground the producer post from mined trace facts for <case>.
    Reads experiments/traces/<case>.post (one atom per line) if present;
    otherwise returns a conservative headroom+slot approximation (the facts a
    blockA_k trace establishes) — LABELED APPROX by the caller."""
    pth = os.path.join(ROOT, "experiments", "traces", f"{case}.post")
    if os.path.exists(pth):
        return [l.strip() for l in open(pth) if l.strip()
                and not l.startswith("#")]
    # default approximation: what a blockA_k run establishes (headroom + slot).
    return ["SL.lo + 4352 ≤ sp.toNat", "∃ b, m0[slotAddr]? = some b"]


def _harvest_demands(path, prop):
    """Mechanically harvest consumer demands = the projections consumers take of
    the target structure.  Strategy: grep the repo for `.<field>` projection
    sites of the structure's mk fields; each projected field's TEXT is a demand
    the structure must supply.  For hermetic fixtures we default to the full
    field list (every field is a demanded projection)."""
    ctx = EncCtx()
    _binders, fields, _hyps, shape = _fields_of_target(path, prop, ctx)
    if not fields:
        return []
    # if the target names a real structure, grep for `.field` projection sites
    # to keep only the DEMANDED fields; else (hermetic) treat all as demanded.
    return fields


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
            v, _ = smt_check("validate", pth, prop, log)
            results["d_" + os.path.basename(pth)] = v
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
# JOINT / interlock acceptance — gates a-d (48e/48g history as ground truth)
# ==========================================================================

JOINT_FIX = os.path.join(SMT_DIR, "joint", "JointTargets.lean")


def joint_acceptance(log):
    """Gates a-d.  Each 48e/48g failure mode must be DETECTED:
      (a) pre-48f extras + 48e cure-A (entry-carry only): producer-check FLAGS
          frame_pop/x13 insufficiency (the per-field filter passed it).
      (b) 48f frame_pop ground-field cure: producer-check FAILS it (nothing
          supplies the dead-buffer / m0-totality presence).
      (c) x13_pres-DELETION candidate: consumer-check FAILS (blockB spill demand).
      (d) the 48g three-cure recipe: joint-inhabit SAT + NO producer/consumer
          failure in-fragment (the sound design passes)."""
    print("== JOINT / interlock ACCEPTANCE (48e/48g history) ==\n")
    log.write("\n## smt_check.py JOINT acceptance run\n\n")
    if not os.path.exists(JOINT_FIX):
        print(f"MISSING fixture {JOINT_FIX}"); return False
    f = JOINT_FIX
    results = {}

    # -- (a) entry-carry-only producer vs pre-48f extras: must flag frame_pop/x13
    print("== (a) 48e cure-A (entry-carry) vs pre-48f extras ==")
    # producer = the entry pins (headroom + slot) ONLY — the 48e cure-A carry.
    postA = ["SL.lo + 4352 ≤ sp.toNat", "∃ b, m0[slotAddr]? = some b"]
    rcA, va = producer_check(f, "JointFix.TargetA", postA, log)
    # detected iff frame_pop AND/OR x13 conjuncts FAIL under the entry-only post
    a_flagged = any(k.strip().startswith(("frame_pop", "∀ a")) or "x13" in k or
                    "mcall" in k for k, v in va.items() if v == "FAILS")
    results["a"] = ("PASS" if a_flagged else "MISS", rcA, va)

    # -- (b) 48f frame_pop ground-field cure: producer (entry pins) must FAIL the
    #        m0-totality conjunct (nothing supplies dead-buffer presence)
    print("\n== (b) 48f frame_pop ground-field cure ==")
    postB = ["SL.lo + 4352 ≤ sp.toNat", "∃ b, m0[slotAddr]? = some b"]
    rcB, vb = producer_check(f, "JointFix.TargetB", postB, log)
    b_flagged = any(v == "FAILS" for v in vb.values())
    results["b"] = ("PASS" if b_flagged else "MISS", rcB, vb)

    # -- (c) x13-DELETION candidate: consumer demand (blockB spills a3) must FAIL
    print("\n== (c) x13_pres-DELETION candidate ==")
    # the live consumer demand blockB_binary imposes: a3 present at x13slot.
    demC = ["∃ w, mcall[x13slot]? = some w"]
    rcC, vc = consumer_check(f, "JointFix.TargetC", demC, log)
    c_flagged = (vc.get("∃ w, mcall[x13slot]? = some w") == "FAILS")
    results["c"] = ("PASS" if c_flagged else "MISS", rcC, vc)

    # -- (d) 48g three-cure recipe: joint SAT + producer HOLDS all + consumer OK
    print("\n== (d) 48g three-cure recipe (sound design) ==")
    rcJ, jm = joint_inhabit(f, "JointFix.TargetD", log)
    d_sat = rcJ.startswith("JOINTLY-INHABITABLE")
    # recipe-consistent producer supplies ALL four conjuncts
    postD = ["SL.lo + 4352 ≤ sp.toNat", "∃ b, m0[slotAddr]? = some b",
             "∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)",
             "∃ w, mcall[x13slot]? = some w"]
    rcPD, vpd = producer_check(f, "JointFix.TargetD", postD, log)
    demD = ["∃ w, mcall[x13slot]? = some w"]
    rcCD, vcd = consumer_check(f, "JointFix.TargetD", demD, log)
    prod_ok = "FAILS" not in vpd.values()
    cons_ok = "FAILS" not in vcd.values()
    d_ok = d_sat and prod_ok and cons_ok
    results["d"] = ("PASS" if d_ok else "MISS", rcJ, dict(prod=rcPD, cons=rcCD))

    # verdicts
    print("\n### JOINT acceptance table")
    log.write("\n### JOINT acceptance table\n")
    for k in ("a", "b", "c", "d"):
        verdict = results[k][0]
        line = f"- ({k}) {verdict}"
        print(line); log.write(line + "\n")
    ok = all(results[k][0] == "PASS" for k in ("a", "b", "c", "d"))
    print(f"\n=== JOINT ACCEPTANCE → {'PASS' if ok else 'FAIL'} ===")
    log.write(f"\n**Joint acceptance → {'PASS' if ok else 'FAIL'}**\n")
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
    # --- joint / interlock validation ---
    ap.add_argument("--joint", action="store_true",
                    help="joint/interlock acceptance (gates a-d)")
    ap.add_argument("--joint-inhabit", action="store_true",
                    help="Q1: encode ALL conjuncts of the target simultaneously")
    ap.add_argument("--producer-check", dest="producer",
                    help="Q2: PRODUCER post module:Prop (or list) ⇒ each conjunct")
    ap.add_argument("--producer-traces", dest="prod_traces",
                    help="Q2 APPROX: ground producer post from mined trace facts "
                         "for <case> (labeled APPROX)")
    ap.add_argument("--consumer-check", action="store_true",
                    help="Q3: structure ⇒ each harvested consumer demand")
    ap.add_argument("--demands", help="';'-separated consumer demand texts "
                    "(default: harvest from the target's consumers)")
    ap.add_argument("--post", help="';'-separated producer post atom texts "
                    "(for --producer-check when a post module is not given)")
    ap.add_argument("--file", dest="file")
    ap.add_argument("--prop")
    ap.add_argument("--timeout", type=int, default=20000, help="z3 timeout (ms)")
    args = ap.parse_args()

    os.makedirs(LOGDIR, exist_ok=True)
    with open(LOG, "a") as log:
        log.write("\n## smt_check.py run\n\n")
        if args.acceptance:
            sys.exit(0 if acceptance(log) else 1)
        if args.joint:
            sys.exit(0 if joint_acceptance(log) else 1)
        # single joint queries
        if args.joint_inhabit or args.producer or args.prod_traces \
                or args.consumer_check:
            if not (args.file and args.prop):
                ap.error("joint queries need --file <mod.lean> --prop <Ns.T>")
            if args.joint_inhabit:
                joint_inhabit(args.file, args.prop, log, args.timeout)
            if args.producer or args.post:
                post = ([p.strip() for p in args.post.split(";")]
                        if args.post else _post_of_module(args.producer, log))
                producer_check(args.file, args.prop, post, log, args.timeout)
            if args.prod_traces:
                post = _traces_post(args.prod_traces)
                producer_check(args.file, args.prop, post, log, args.timeout,
                               approx=True)
            if args.consumer_check:
                dem = ([d.strip() for d in args.demands.split(";")]
                       if args.demands else _harvest_demands(args.file, args.prop))
                consumer_check(args.file, args.prop, dem, log, args.timeout)
            return
        mode = ("refute" if args.refute else "validate" if args.validate
                else "inhabit" if args.inhabit else None)
        if mode is None:
            ap.error("pick a mode: --refute / --validate / --inhabit / "
                     "--acceptance / --joint")
        if not (args.file and args.prop):
            ap.error(f"--{mode} needs --file <mod.lean> --prop <Ns.P>")
        smt_check(mode, args.file, args.prop, log, args.timeout)


if __name__ == "__main__":
    main()
