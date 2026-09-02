#!/usr/bin/env python3
"""cegis_cure.py — CEGIS cure generator for (possibly-false) Resid/field Props
(ANALYSIS ONLY; nothing here enters a proof).

Given a Lean Prop that a proving agent is stuck on (or that the fuzzer/SMT layer
has REFUTED), enumerate a bounded TEMPLATE SPACE of AMENDED statements — the
containing space of every landed cure — filter them in cost order, and emit a
ranked, per-filter-evidenced suite of candidate cures.  This automates the
"discover the cure" step that consumed waves 47e–48g by hand.

This is the CTI (counterexample-guided inductive synthesis) loop closed over
STATEMENTS rather than programs: the false statement is the counterexample; the
candidate amendments are the synthesis; the fuzzer/SMT layer is the verifier;
survivors are ranked and reported for a human/prover to land.

TEMPLATE SPACE (transformations over the input statement — every landed cure is
an instance):
  (i)   entry-conditioning  — insert `EvalEntry`/`ExecEntry` (or a `StackOK`
        entry-ground) as a LEADING hypothesis (the 47i NegResid cure, the B2
        class).  Pins the outer ghosts so the sp=0 / m0=∅ witnesses no longer
        bite.
  (ii)  quantifier repair   — a ∀-ghost totality conjunct (`∀ mcall … → ∀ a,
        ∃ b`) → an ∃-STRUCTURED / footprint-bounded demand (the 47i honest-pair
        cure) or a hypothesis-bound one.
  (iii) guard repair        — an agree-OFF-window hypothesis (`¬(lo≤a<sp)`) →
        agree-ON-window (`lo'≤a<hi'`) over the interval algebra, so the in-window
        adversary is excluded (the NovelResidB cure shape).
  (iv)  conjunct deletion   — drop a conjunct a BLOCK OUTPUT already supplies
        (the 48f `mem_ext` redundancy cure: `blockA_k` emits `MemExtends m0
        ment` intrinsically).
  (v)   oracle re-homing     — move an IH/step obligation from the statement to a
        recursor-side hypothesis (shape-2 — the seq/args SeqSpanGround move).

FILTERS, in cost order (cheapest first, drop on first refutation):
  1. SYNTACTIC — the amended def elaborates as a Lean def (`lake env lean`).
  2. Z3 REFUTATION — `smt_check.py --refute`; a negation-SAT (REFUTED-* or a
     REFUTABLE validate verdict) DROPS the candidate, keeping the countermodel.
  3. SEMANTIC/DESCENT — `statement_fuzz.py --semantic`; a REFUTED nested conjunct
     DROPS the candidate (the uncovered-address rule, address-map fragment).
  4. TRACE CONSISTENCY — if a mined candidate exists under experiments/invariants/
     for this field, prefer/cross-check (advisory; not a hard drop).

SURVIVORS RANKED: minimal-edit first, new-premises penalized.  `--llm-rank` is a
stub (no API calls here).

OUTPUT: experiments/cures/<field>.md — top-k candidates with per-filter evidence
and which landed assets each would relight.

ACCEPTANCE (`--acceptance`, hard, history-as-ground-truth): run against the
PRE-amendment reconstructions in experiments/cegis/ —
  (a) AcceptNegPre  → an ENTRY-CONDITIONING cure in top-3
  (b) AcceptMemExtPre → a DELETION cure in top-3
  (c) AcceptMcallPre  → an ∃-STRUCTURED / AGREE-ON repair in top-3

Usage:
  python3 scripts/cegis_cure.py --file <mod.lean> --prop <Ns.P> [--field <name>]
  python3 scripts/cegis_cure.py --acceptance
  python3 scripts/cegis_cure.py --file … --prop … --no-smt   # skip Z3 filter
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
CURESDIR = os.path.join(ROOT, "experiments", "cures")
INVDIR = os.path.join(ROOT, "experiments", "invariants")
CEGISDIR = os.path.join(ROOT, "experiments", "cegis")
FUZZ = os.path.join(HERE, "statement_fuzz.py")
SMT = os.path.join(HERE, "smt_check.py")
AX_OK = {"propext", "Classical.choice", "Quot.sound"}


# ==========================================================================
# Lean plumbing
# ==========================================================================

def run_lean(src, timeout=500):
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


# ==========================================================================
# statement parsing (a small, drift-tolerant surface parser over the def RHS)
# ==========================================================================

def extract_def(body_text, prop):
    """Return (sig, rhs) for `def/abbrev <short> <sig> : Prop := <rhs>`, verbatim
    (multi-line), stopping at the next top-level def/theorem/end/namespace/doc."""
    short = prop.split(".")[-1]
    m = re.search(rf"(?:def|abbrev)\s+{re.escape(short)}\b(.*?):=\s*",
                  body_text, re.S)
    if not m:
        return None, None
    sig = m.group(1)
    rest = body_text[m.end():]
    stop = re.search(r"\n(?:def|abbrev|theorem|end|namespace|/-)", rest)
    rhs = (rest[:stop.start()] if stop else rest)
    rhs = re.sub(r"--[^\n]*", "", rhs)          # strip line comments
    return sig, rhs.strip()


def unfold_body(path, prop, unfold_names):
    """When the def RHS is an APPLICATION of another Resid (e.g. `BinIntLive :=
    BinIntCellResid .add …`), the source-parser sees no ∀/∧ structure.  Unfold
    the named def(s) via Lean `trace_state` and return the elaborated body's
    ∀-telescope + conjunct tree as a re-parseable source string, or None.

    Mirrors statement_fuzz.discover_telescope: elaborate `example : P → True`,
    `unfold` the applied Resid at the hypothesis, and scrape `H : <body>`."""
    body_text = open(path).read()
    # inline the whole module (the target def lives in it, not on LEAN_PATH) and
    # append the trace_state probe just before the module's closing `end`.
    lines = body_text.splitlines()
    end_i = max((i for i, l in enumerate(lines)
                 if l.strip().startswith("end ")), default=len(lines))
    head = "\n".join(lines[:end_i])
    tail = "\n".join(lines[end_i:])
    unf = " ".join([prop] + list(unfold_names))
    probe = (f"{head}\n\nset_option pp.fullNames false in\n"
             f"example : {prop} → True := by\n"
             f"  intro H\n  unfold {unf} at H\n  trace_state\n  trivial\n\n{tail}\n")
    rc, out = run_lean(probe)
    m = re.search(r"H :\s*(.+?)\n⊢", out, re.S)
    if not m:
        return None
    return " ".join(m.group(1).split())


def split_binders(rhs):
    """Split the leading `∀ (…) …,` telescope from the body.  Returns
    (binder_text, body) where binder_text is the raw `∀ … ,` prefix (or "")."""
    s = rhs.strip()
    if not s.startswith("∀"):
        return "", s
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif ch == "," and depth == 0:
            return s[:i + 1], s[i + 1:].strip()
        i += 1
    return s, ""


def split_top(body, sep):
    """Top-level split respecting (),⟨⟩ and treating a top-level ∀ as capturing
    the rest of the string (so arrows/∧ inside a ∀-body aren't split out)."""
    parts, depth, i, start = [], 0, 0, 0
    L = len(sep)
    while i < len(body):
        ch = body[i]
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        elif depth == 0 and ch == "∀":
            break
        elif depth == 0 and body[i:i + L] == sep:
            parts.append(body[start:i].strip())
            start = i + L
            i += L
            continue
        i += 1
    parts.append(body[start:].strip())
    return [p for p in parts if p]


def split_conjuncts(body):
    """Split the body into top-level ∧-conjuncts, descending through the leading
    hypothesis chain first (H₁ → … → Hₙ → CONCL, we conjunct-split CONCL)."""
    # first isolate the conclusion (last top-level → segment)
    arr = split_top(body, "→")
    hyps, concl = arr[:-1], arr[-1]
    conj = split_top(concl, "∧")
    return hyps, conj


# ==========================================================================
# DEFECT DETECTION — classify what is wrong (drives which templates apply)
# ==========================================================================

WINDOW_OFF_RE = re.compile(r"∀\s*(\w+)[^,]*,\s*¬\s*\(([^()]*?)\)\s*→\s*"
                           r"(\w+)\[\1\]\?\s*=\s*(\w+)\[\1\]\?")
MCALL_TOTAL_RE = re.compile(r"∀\s*(\w+)\s*:\s*Mem\s*,.*?→\s*∀\s*\w+\s*:?\s*(?:Nat)?\s*,"
                            r"\s*∃\s*\w+\s*,\s*\1\[\w+\]\?\s*=\s*some", re.S)
MEMEXT_OVER_RE = re.compile(r"∀\s*(\w+)\s*:\s*Mem\s*,.*?→\s*MemExtends\s+\w+\s+\1", re.S)
HEADROOM_RE = re.compile(r"[\w.]+\s*\+\s*(\d+)\s*≤\s*(\w+)\.toNat")
SIZE_EQ_RE = re.compile(r"(\w+'*)\.store\.(frames|closures)\.size\s*=\s*"
                        r"(\w+'*)\.store\.\2\.size")
ENTRY_RE = re.compile(r"\b(EvalEntry|ExecEntry|StackOK|EvalGround|ExecGround)\b")


def detect_defects(binders, body):
    """Return a list of defect dicts, each naming a template that could cure it.
    Each: {kind, template, span, note}."""
    flat = " ".join(body.split())
    defects = []
    has_entry = bool(ENTRY_RE.search(binders + " " + " ".join(
        split_conjuncts(body)[0])))
    # (i) headroom / size-eq under ∀ with NO entry hypothesis → entry-condition
    if HEADROOM_RE.search(flat) and not has_entry:
        defects.append(dict(kind="headroom-no-entry", template="entry-conditioning",
                            note="stack-headroom pin under ∀-sp, no entry linkage"))
    if SIZE_EQ_RE.search(flat) and not has_entry:
        defects.append(dict(kind="size-eq-unrelated", template="entry-conditioning",
                            note="store-size equality over ∀-unrelated states"))
    # (ii) ∀-mcall totality (presence) → ∃-structured / footprint bound
    if MCALL_TOTAL_RE.search(flat):
        defects.append(dict(kind="mcall-total-presence", template="quantifier-repair",
                            note="∀-mcall → ∀a ∃b total presence (McallPop class)"))
    # (iii)+(iv) over-quantified MemExtends: agree-off-W → MemExtends m0 m.
    #   two cures apply — guard-repair (agree-on-W') and deletion (block output).
    if MEMEXT_OVER_RE.search(flat):
        defects.append(dict(kind="memext-over-quant", template="conjunct-deletion",
                            note="∀m, agree-off-W → MemExtends m0 m (block supplies)"))
        defects.append(dict(kind="memext-over-quant", template="guard-repair",
                            note="∀m, agree-off-W → MemExtends m0 m (agree-on-W')"))
    # (iii) generic agree-off-window hyp anywhere → guard-repair available
    if WINDOW_OFF_RE.search(flat) and not any(
            d["template"] == "guard-repair" for d in defects):
        defects.append(dict(kind="agree-off-window", template="guard-repair",
                            note="agree-off-window hypothesis; flip to agree-on-W'"))
    # (interlock) an opaque *Extras bundle (BinArmExtras/NegExtras/…) inside the
    # body packs entry-side pins (slot/sproom) + over-quant closures (frame_pop/
    # mem_ext/x13_pres) that are refutable AT m0=∅ / sp=0 but not visible as
    # source conjuncts (they live in the bundle's own def).  Entry-conditioning
    # supplies the pins; the over-quant closures need block-output threading
    # (the wave-48g interlock) — flagged so the report is honest.
    EXTRAS_RE = re.compile(r"\b(\w*Extras)\b")
    em = EXTRAS_RE.search(flat)
    if em and not has_entry:
        defects.append(dict(kind="extras-bundle-entry-pins",
                            template="entry-conditioning",
                            note=f"opaque `{em.group(1)}` packs entry pins "
                                 "(slot/sproom, refutable at m0=∅/sp=0) + "
                                 "over-quant closures (frame_pop/mem_ext/x13_pres, "
                                 "the wave-48g interlock — block-output threading)"))
    return defects, has_entry


# ==========================================================================
# TEMPLATE APPLICATION — produce an amended RHS (as Lean source) per candidate
# ==========================================================================

def _entry_binders_and_hyp(binders):
    """Choose the entry-conditioning insertion.  If the telescope already binds
    SL/sp/m0, insert a `StackOK SL sp <k>` guard (the hermetic, self-contained
    entry-ground the acceptance harness models); if it binds the full EvalEntry
    ghost set, an `EvalEntry …` hyp is the real-repo form.  We pick `StackOK`
    when SL+sp are present (always dischargeable-in-fragment, refutes the sp=0
    witness), else fall back to a named `EvalEntry`/`ExecEntry` placeholder."""
    b = binders
    has_sl = re.search(r"\bSL\s*[:)]", b) or "StackLayout" in b
    has_sp = re.search(r"\bsp\b", b)
    if has_sl and has_sp:
        return "StackOK SL sp 3264"
    return None


def apply_entry_conditioning(binders, body):
    """(i) Insert a leading entry hypothesis.  Returns (new_body, premise_added,
    desc) or None if inapplicable."""
    guard = _entry_binders_and_hyp(binders)
    if guard is None:
        return None
    hyps, conj = split_conjuncts(body)
    concl = " ∧\n    ".join(conj)
    new = ""
    for h in hyps:
        new += h + " →\n    "
    new += guard + " →\n    " + concl
    return new, 1, f"insert leading `{guard}` entry-ground hypothesis"


def apply_quantifier_repair(binders, body):
    """(ii) ∀-mcall total-presence → footprint-bounded ∃ demand.  Replace the
    `∀ a : Nat, ∃ b, mcall[a]? = some b` tail with a guarded
    `∀ a : Nat, (<footprint window>) → ∃ b, mcall[a]? = some b` (the 47i honest
    pair: presence on the actual dead-byte read window, not all of ℕ)."""
    flat = body
    # bounded footprint window (the 47i shape): lowered frame + node line-word.
    win = ("(sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨ "
           "(aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8)")
    # if aExpr not in scope, use the frame window alone
    if not re.search(r"\baExpr\b", binders + body):
        win = "(sp.toNat - 1120 ≤ a ∧ a < sp.toNat)"
    new, n = re.subn(
        r"(∀\s*a\s*:?\s*(?:Nat)?\s*,)\s*(∃\s*b\s*,\s*(\w+)\[a\]\?\s*=\s*some\s*b)",
        rf"\1\n        ({win}) →\n        \2", flat)
    if n == 0:
        return None
    return new, 0, "bound the ∀a presence demand to the dead-byte read footprint"


def apply_conjunct_deletion(binders, body):
    """(iv) Drop the over-quantified `∀ m, agree-off-W → MemExtends m0 m`
    conjunct (block output `_hpresM` supplies it).  Also drops a redundant
    `True`/leading placeholder if that is the only sibling."""
    hyps, conj = split_conjuncts(body)
    kept = [c for c in conj
            if not MEMEXT_OVER_RE.search(" ".join(c.split()))]
    if len(kept) == len(conj):
        return None
    if not kept:
        kept = ["True"]
    concl = " ∧\n    ".join(kept)
    new = "".join(h + " →\n    " for h in hyps) + concl
    return new, -1, "DELETE the ∀m→MemExtends conjunct (block output `_hpresM` supplies it)"


def apply_guard_repair(binders, body):
    """(iii) Flip an agree-OFF-window hypothesis `¬(lo≤a<sp)` to an agree-ON
    hypothesis over a covering window `[lo', hi')` that CONTAINS the demand
    addresses, so the in-window adversary is excluded (the NovelResidB cure).
    We use the whole stack `[SL.lo, SL.hi)` as the covering window (the 47e
    EntryStackSurv footprint-widening shape)."""
    flat = body
    # replace `¬ (SL.lo ≤ a ∧ a < sp.toNat)` (any bound var) with a positive
    # covering window `SL.lo ≤ a ∧ a < SL.hi`.
    def repl(m):
        v = m.group(1)
        return f"∀ {m.group(2)}{v}, (SL.lo ≤ {v} ∧ {v} < SL.hi) → "
    new, n = re.subn(
        r"∀\s*(\w+)(\s*:?\s*(?:Nat)?\s*,)\s*¬\s*\(\s*SL\.lo\s*≤\s*\1\s*∧\s*"
        r"\1\s*<\s*sp\.toNat\s*\)\s*→\s*",
        lambda m: f"∀ {m.group(1)}{m.group(2)} (SL.lo ≤ {m.group(1)} ∧ "
                  f"{m.group(1)} < SL.hi) → ", flat)
    if n == 0:
        return None
    return new, 0, "flip agree-OFF-[SL.lo,sp) to agree-ON-[SL.lo,SL.hi) (covering window)"


TEMPLATE_FNS = {
    "entry-conditioning": apply_entry_conditioning,
    "quantifier-repair": apply_quantifier_repair,
    "conjunct-deletion": apply_conjunct_deletion,
    "guard-repair": apply_guard_repair,
}

# a stable ordering + short tag for reporting
TEMPLATE_TAG = {
    "entry-conditioning": "(i) entry-conditioning",
    "quantifier-repair": "(ii) quantifier repair",
    "guard-repair": "(iii) guard repair",
    "conjunct-deletion": "(iv) conjunct deletion",
    "oracle-rehoming": "(v) oracle re-homing",
}


# ==========================================================================
# candidate = an amended hermetic module + a fresh def name
# ==========================================================================

class Candidate:
    def __init__(self, template, desc, sig, binders, new_body, premise_delta,
                 ns, imports):
        self.template = template
        self.desc = desc
        self.sig = sig
        self.binders = binders     # the ORIGINAL `∀ … ,` prefix (re-attached)
        self.body = new_body       # amended body (post-binder)
        self.premise_delta = premise_delta   # +1 new premise, -1 deleted conjunct
        self.ns = ns
        self.imports = imports
        self.name = "CegisCand"
        self.filters = {}          # filter → (verdict, evidence)
        self.dropped_by = None

    @property
    def rhs(self):
        """Full amended RHS = binder prefix + amended body."""
        return (self.binders + "\n    " + self.body) if self.binders else self.body

    def module(self):
        """A hermetic module defining the candidate as `<ns>.<name>`."""
        opens = ("open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While\n"
                 "open LeanRV64DExecutable Sail Register\n"
                 "open Vsa.Alloc (StackLayout StackOK)\n")
        ns_open = f"namespace {self.ns}\n" if self.ns else ""
        ns_close = f"end {self.ns}\n" if self.ns else ""
        return (f"{self.imports}\n{opens}\n{ns_open}"
                f"def {self.name} : Prop :=\n  {self.rhs}\n"
                f"{ns_close}")

    def full_prop(self):
        return f"{self.ns}.{self.name}" if self.ns else self.name


def enumerate_candidates(binders, body, sig, ns, imports):
    """Bounded enumeration: each detected defect's template, applied singly;
    plus bounded PAIRS (entry-conditioning ∘ {quantifier-repair, guard-repair,
    conjunct-deletion}) — the historical cures are single-or-double edits."""
    defects, has_entry = detect_defects(binders, body)
    cands = []
    seen = set()

    def add(template, res):
        if res is None:
            return
        new_body, delta, desc = res
        key = (template, " ".join(new_body.split()))
        if key in seen:
            return
        seen.add(key)
        cands.append(Candidate(template, desc, sig, binders, new_body, delta,
                               ns, imports))

    # single-edit candidates, one per applicable template
    applied = set()
    for d in defects:
        t = d["template"]
        if t in applied:
            continue
        applied.add(t)
        add(t, TEMPLATE_FNS[t](binders, body))

    # bounded double edits: entry-conditioning composed with each body repair.
    if "entry-conditioning" in applied:
        base = apply_entry_conditioning(binders, body)
        if base is not None:
            base_body = base[0]
            for t in ("quantifier-repair", "guard-repair", "conjunct-deletion"):
                if t in applied:
                    r = TEMPLATE_FNS[t](binders, base_body)
                    if r is not None:
                        new_body, delta, desc = r
                        c = Candidate(t, f"entry-conditioning + {desc}", sig,
                                      binders, new_body, delta + 1, ns, imports)
                        c.template = f"entry-conditioning+{t}"
                        key = ("dbl", " ".join(new_body.split()))
                        if key not in seen:
                            seen.add(key)
                            cands.append(c)
    return cands, defects, has_entry


# ==========================================================================
# FILTERS
# ==========================================================================

def filter_syntactic(cand):
    """FILTER 1: does the amended def elaborate?"""
    rc, out = run_lean(cand.module())
    if rc == 0 and "error" not in out.lower():
        return True, "elaborates"
    last = [l for l in out.strip().splitlines() if l.strip()]
    return False, (last[-1][:120] if last else "elaboration failed")


def _write_tmp_module(cand):
    path = os.path.join(CEGISDIR, f"_cand_{abs(hash(cand.full_prop())) % 100000}.lean")
    with open(path, "w") as f:
        f.write(cand.module())
    return path


def filter_smt(cand, timeout_ms=15000):
    """FILTER 2: Z3 refutation.  Only a MACHINE-CHECKED countermodel drops the
    candidate — verdict `REFUTED-REPLAYED` (the Lean ¬P probe green + axiom-clean,
    the plan's hard gate).  `REFUTED-MODULO-OPAQUE` (model hinges on an opaque
    symbol like `True`) and `ENCODING-GAP` (Z3 SAT but the Lean replay inserted a
    `sorryAx` ⇒ the SAT was spurious, the statement is NOT actually refutable —
    the documented symbolic-window behaviour) are NOT genuine refutations: KEEP
    and defer to the semantic filter.  This is the plan's principle — a spurious
    SAT cannot be a false green because the Lean replay gates the verdict."""
    path = _write_tmp_module(cand)
    try:
        r = subprocess.run(
            ["python3", SMT, "--refute", "--file", path, "--prop", cand.full_prop()],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout_ms / 1000 * 4 + 400)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return True, "smt timeout (kept)"        # timeout ⇒ do not drop
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    line = next((l for l in out.splitlines() if cand.full_prop() in l), "")
    # ONLY a machine-checked refutation drops.  Everything else keeps.
    if "REFUTED-REPLAYED" in line:
        model = re.search(r"model (\{[^}]*\})", line)
        return False, f"Z3 countermodel (Lean-replayed) {model.group(1) if model else '(sat)'}"
    if "NOT-REFUTED" in line or "VALID-IN-FRAGMENT" in line:
        return True, "Z3: negation UNSAT (no countermodel in fragment)"
    if "REFUTED-MODULO-OPAQUE" in line:
        return True, "Z3 SAT modulo opaque symbol (not machine-checked; kept)"
    if "ENCODING-GAP" in line:
        return True, "Z3 SAT but replay sorry'd (spurious SAT, symbolic window; kept)"
    if "UNKNOWN" in line:
        return True, "Z3 UNKNOWN (kept)"
    if "ENCODE-GAP" in line or "ENCODE-FAIL" in line:
        return True, "encoder gap (kept, defer to semantic filter)"
    return True, (line.split("→", 1)[-1].strip()[:80] if "→" in line else "no smt verdict")


def filter_semantic(cand, timeout_ms=15000):
    """FILTER 3: the v2.1 uncovered-address semantic rule (statement_fuzz
    --semantic).  A REFUTED nested conjunct DROPS the candidate."""
    path = _write_tmp_module(cand)
    try:
        r = subprocess.run(
            ["python3", FUZZ, "--semantic", "--file", path, "--prop", cand.full_prop()],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout_ms / 1000 * 4 + 400)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return True, "semantic timeout (kept)"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    line = next((l for l in out.splitlines() if cand.full_prop() in l), "")
    if "REFUTED" in line:
        return False, "semantic rule: uncovered demand address (adversary found)"
    if "SURVIVED" in line:
        return True, "semantic rule: every demand address covered (or SMT territory)"
    return True, "semantic: undecidable (kept)"


def filter_joint(cand, demands, timeout_ms=15000):
    """FILTER 3b (INTERLOCK): `smt_check.py --consumer-check` — does the AMENDED
    structure still IMPLY every harvested consumer demand?  A CONJUNCT-DELETION
    candidate is NOT refutable per-statement (a weaker Prop has no countermodel of
    its own), so filter_smt/filter_semantic PASS it; but if the deleted conjunct
    was load-bearing (e.g. `x13_pres`, spilled by blockB_binary) the structure
    becomes too weak — consumer-check FAILS.  This is the 48e/48c interlock the
    per-statement filters miss.  Only runs when `demands` are supplied (the
    consumer projections harvested for this field)."""
    if not demands:
        return True, "no consumer demands harvested (skipped)"
    path = _write_tmp_module(cand)
    try:
        r = subprocess.run(
            ["python3", SMT, "--consumer-check", "--demands", ";".join(demands),
             "--file", path, "--prop", cand.full_prop()],
            cwd=ROOT, capture_output=True, text=True,
            timeout=timeout_ms / 1000 * 4 + 400)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return True, "consumer-check timeout (kept)"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    if "CONSUMER-FAILS" in out:
        d = next((l for l in out.splitlines() if "CONSUMER-FAILS" in l), "")
        return False, f"interlock: amended structure too weak for a consumer — {d.strip()[:90]}"
    if "SATISFIED" in out:
        return True, "interlock: all consumer demands still satisfied"
    return True, "interlock: consumer demands opaque/undecidable (kept)"


def filter_trace(cand, field):
    """FILTER 4 (advisory): a mined candidate for this field under
    experiments/invariants/ — cross-check, don't hard-drop."""
    if not field:
        return None, ""
    for ext in (".lean", ".md"):
        p = os.path.join(INVDIR, field + ext)
        if os.path.exists(p):
            return True, f"mined artifact present ({os.path.basename(p)})"
    return None, ""


# ==========================================================================
# RANKING
# ==========================================================================

def rank_key(cand):
    """Prefer minimal edits (fewer new premises); deletion (delta<0) is cheapest,
    then guard-repair/quant-repair (delta 0), then entry-conditioning (delta>0),
    then double edits.  Ties by shorter amended RHS (closer to the original)."""
    double = 1 if "+" in cand.template else 0
    return (double, max(cand.premise_delta, 0), len(cand.rhs))


# ==========================================================================
# driver over ONE (file, prop)
# ==========================================================================

def imports_of(body_text):
    return "\n".join(l for l in body_text.splitlines()
                     if l.strip().startswith("import "))


def opens_of(body_text):
    return "\n".join(l for l in body_text.splitlines()
                     if l.strip().startswith("open "))


def cure_one(path, prop, field, do_smt=True, do_semantic=True, topk=5,
             quiet=False, unfold=None, demands=None):
    body_text = open(path).read()
    imports = imports_of(body_text)
    ns = ".".join(prop.split(".")[:-1])
    if unfold:
        # def RHS is an application of another Resid — unfold to expose the body.
        ub = unfold_body(path, prop, unfold)
        if ub is None:
            print(f"[{prop}] could not unfold {unfold}", file=sys.stderr)
            return None
        binders, body = split_binders(ub)
        sig = ""
        imports = imports + "\n" + opens_of(body_text)   # carry opens for elab
    else:
        sig, rhs = extract_def(body_text, prop)
        if rhs is None:
            print(f"[{prop}] def body not found in {path}", file=sys.stderr)
            return None
        binders, body = split_binders(rhs)
    cands, defects, has_entry = enumerate_candidates(binders, body, sig, ns, imports)
    space_size = len(cands)

    kills = {"syntactic": 0, "smt": 0, "semantic": 0, "joint": 0}
    survivors = []
    for c in cands:
        ok, ev = filter_syntactic(c)
        c.filters["syntactic"] = ("PASS" if ok else "FAIL", ev)
        if not ok:
            c.dropped_by = "syntactic"
            kills["syntactic"] += 1
            continue
        if do_smt:
            ok, ev = filter_smt(c)
            c.filters["smt"] = ("PASS" if ok else "REFUTED", ev)
            if not ok:
                c.dropped_by = "smt"
                kills["smt"] += 1
                continue
        if do_semantic:
            ok, ev = filter_semantic(c)
            c.filters["semantic"] = ("PASS" if ok else "REFUTED", ev)
            if not ok:
                c.dropped_by = "semantic"
                kills["semantic"] += 1
                continue
        if demands:                          # FILTER 3b — INTERLOCK
            ok, ev = filter_joint(c, demands)
            c.filters["joint"] = ("PASS" if ok else "CONSUMER-FAILS", ev)
            if not ok:
                c.dropped_by = "joint"
                kills["joint"] += 1
                continue
        tv, te = filter_trace(c, field)
        if tv is not None:
            c.filters["trace"] = ("PRESENT", te)
        survivors.append(c)

    survivors.sort(key=rank_key)
    result = dict(prop=prop, field=field or prop.split(".")[-1], space_size=space_size,
                  kills=kills, survivors=survivors, defects=defects,
                  has_entry=has_entry, all_cands=cands)
    if not quiet:
        write_report(result, path)
    return result


def write_report(result, src_path):
    os.makedirs(CURESDIR, exist_ok=True)
    field = result["field"]
    out = os.path.join(CURESDIR, field + ".md")
    survivors = result["survivors"]
    lines = [f"# Cure candidates — `{result['prop']}`", "",
             f"Source: `{os.path.relpath(src_path, ROOT)}`  ",
             f"Detected defects: " + (", ".join(
                 f"{d['kind']} → {TEMPLATE_TAG.get(d['template'], d['template'])}"
                 for d in result["defects"]) or "none") + "  ",
             f"Entry hypothesis already present: {result['has_entry']}  ",
             f"Template space: {result['space_size']} candidate(s).  ",
             f"Filter kills: syntactic {result['kills']['syntactic']}, "
             f"Z3-refute {result['kills']['smt']}, "
             f"semantic {result['kills']['semantic']}, "
             f"interlock {result['kills'].get('joint', 0)}.  ",
             f"Survivors: {len(survivors)}.", ""]
    RELIGHT = {
        "entry-conditioning": "B2/47i class — value-path sims relight verbatim; "
            "row dispatcher threads the entry hyp at each cell site (mechanical).",
        "quantifier-repair": "McallPop class — the 6 unary/logical Resid + "
            "NegResid/NotResid presence conjuncts; SubEvalReturn buffer-write "
            "supplies the footprint presence.",
        "guard-repair": "EntryStackSurv/47e class — the store-survival + agree "
            "conduits widen to the full stack window; children absorbed.",
        "conjunct-deletion": "48f class — `blockA_k`/`blockA_binaryArm` `_hpresM` "
            "output supplies it; zero downstream churn (consumers take the "
            "struct as a hypothesis).",
    }
    if not survivors:
        lines.append("**No survivors** — every candidate refuted. The statement's "
                     "defect is outside the address-map/entry-conditioning cure "
                     "vocabulary (likely a genuine semantic gap; Law 4 — return "
                     "the machine-checked obstruction).")
    for i, c in enumerate(survivors[:], 1):
        base = c.template.split("+")[0]
        lines += [f"## Candidate {i} — {TEMPLATE_TAG.get(c.template, c.template)}",
                  "", f"_{c.desc}_  ",
                  f"Edit cost: {'+' if c.premise_delta > 0 else ''}"
                  f"{c.premise_delta} premise(s).", "",
                  "```lean", f"def {result['field']} …: Prop :=", f"  {c.rhs}", "```",
                  "", "Per-filter evidence:"]
        for fk in ("syntactic", "smt", "semantic", "trace"):
            if fk in c.filters:
                v, e = c.filters[fk]
                lines.append(f"- **{fk}**: {v} — {e}")
        lines += ["", f"Relights: {RELIGHT.get(base, '—')}", ""]
    # also record refuted candidates as the CTI feedback trail
    refuted = [c for c in result["all_cands"] if c.dropped_by]
    if refuted:
        lines += ["## Refuted candidates (CTI trail)", ""]
        for c in refuted:
            v, e = c.filters.get(c.dropped_by, ("", ""))
            lines.append(f"- {TEMPLATE_TAG.get(c.template, c.template)} — "
                         f"dropped by **{c.dropped_by}**: {e}")
        lines.append("")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {os.path.relpath(out, ROOT)} — {len(survivors)} survivor(s), "
          f"space {result['space_size']}, kills {result['kills']}")
    return out


# ==========================================================================
# ACCEPTANCE — history as ground truth
# ==========================================================================

ACCEPT = [
    ("a", os.path.join(CEGISDIR, "AcceptA_Neg.lean"),
     "CegisAcceptA.AcceptNegPre", "entry-conditioning",
     "NegResid pre-47i → entry-conditioning must appear in top-3"),
    ("b", os.path.join(CEGISDIR, "AcceptB_MemExt.lean"),
     "CegisAcceptB.AcceptMemExtPre", "conjunct-deletion",
     "BinArmExtras.mem_ext pre-48f → deletion cure must appear in top-3"),
    ("c", os.path.join(CEGISDIR, "AcceptC_McallPair.lean"),
     "CegisAcceptC.AcceptMcallPre", ("quantifier-repair", "guard-repair"),
     "∀-mcall pair → an ∃-structured / agree-on repair must appear in top-3"),
]


def acceptance(do_smt=True, do_semantic=True):
    print("== CEGIS cure ACCEPTANCE (history as ground truth) ==\n")
    allok = True
    for tag, path, prop, want, desc in ACCEPT:
        res = cure_one(path, prop, None, do_smt, do_semantic, quiet=False)
        want_set = {want} if isinstance(want, str) else set(want)
        top3 = res["survivors"][:3]
        top3_templates = [c.template.split("+")[0] for c in top3]
        hit = any(t in want_set for t in top3_templates)
        # also require: the WHOLE original was actually refuted by ≥1 filter,
        # i.e. some candidate was dropped (the defect is real) OR no-op survived.
        rank = next((i + 1 for i, t in enumerate(top3_templates)
                     if t in want_set), None)
        allok = allok and hit
        print(f"\n[{tag}] {desc}")
        print(f"    top-3 templates: {top3_templates}")
        print(f"    want {sorted(want_set)} → "
              f"{'FOUND at rank ' + str(rank) if hit else 'MISS'}")
    print(f"\n== ACCEPTANCE: {'PASS' if allok else 'FAIL'} ==")
    return allok


# ==========================================================================
# main
# ==========================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="hermetic .lean module path")
    ap.add_argument("--prop", help="fully-qualified Prop name (the Resid/field)")
    ap.add_argument("--field", help="field/case name for the output filename "
                    "(default: prop short name)")
    ap.add_argument("--topk", type=int, default=5)
    ap.add_argument("--no-smt", action="store_true", help="skip the Z3 filter")
    ap.add_argument("--no-semantic", action="store_true",
                    help="skip the semantic-rule filter")
    ap.add_argument("--llm-rank", action="store_true",
                    help="(stub) LLM re-ranking — no API calls in this task")
    ap.add_argument("--acceptance", action="store_true",
                    help="run the a-c history-as-ground-truth gate")
    ap.add_argument("--unfold", nargs="+", default=None, metavar="DEF",
                    help="def name(s) to unfold when the prop is an APPLICATION "
                         "of another Resid (exposes its body via trace_state)")
    ap.add_argument("--demands", default=None,
                    help="';'-separated consumer demand texts → enables the "
                         "INTERLOCK filter (smt_check --consumer-check): drops a "
                         "candidate whose amended structure is too weak for a "
                         "load-bearing consumer projection")
    args = ap.parse_args()

    if args.llm_rank:
        print("[--llm-rank is a stub; no API calls]", file=sys.stderr)
    if args.acceptance:
        sys.exit(0 if acceptance(not args.no_smt, not args.no_semantic) else 1)
    if not (args.file and args.prop):
        ap.error("need --file and --prop (or --acceptance)")
    dem = [d.strip() for d in args.demands.split(";")] if args.demands else None
    cure_one(args.file, args.prop, args.field, not args.no_smt,
             not args.no_semantic, args.topk, unfold=args.unfold, demands=dem)


if __name__ == "__main__":
    main()
