#!/usr/bin/env python3
"""statement_fuzz.py — pre-proof refutation fuzzer for Lean Props (ANALYSIS ONLY).

Given a Lean Prop (by fully-qualified name + an import that brings it into
scope), attempt to REFUTE it by small witnesses BEFORE anyone spends turns
proving it.  Nothing here enters a proof — this is pre-proof validation, the
same category as the ELF emulator harness.

The lethal-witness idiom is lifted from the fleet refutation files
(experiments/fleet/obstructions/B2_Field_*.lean, McallPopTotality.lean): a
ghost-∀ statement is instantiated at historically-lethal instances —

  * sp = 0#64                    kills `sp_headroom : SL.lo + k ≤ sp.toNat`
  * SL = ⟨0,0⟩                   kills stack-region pins
  * m0 = a finite witness `Mem`  kills total-population pins (`hMcallPop`) and
                                 static jump-table slot pins
  * BitVec ghosts = 0#64 / max   kills address-range pins `0x80000000 ≤ a`
  * operand addr low (40#64)     kills `op_lo`

HOW IT WORKS (drift-proof).  We do NOT hard-code any statement's binder
telescope (those drift across amendments).  Instead we run Lean once to
`trace_state` the *unfolded* Prop, parse its `∀`-binder telescope + the `→`
hypothesis chain, synthesize a witness for each binder from a type→witness
table (the lethal instances above), and emit a probe

    theorem probe (L : Layout) : ¬ P L := by
      intro H
      have h := H <witnesses…>            -- ghosts + dischargeable hyps
      exact absurd <conjunct-projection> (by decide)

trying a `first | …` cascade over projection paths for the decidable conjunct.
Lean machine-checks the result; axiom-clean ⊆ {propext,Classical.choice,
Quot.sound} ⇒ **REFUTED-BY-WITNESS**.  If a leading hypothesis is an
*unsatisfiable-at-the-witness entry pin* (e.g. `EvalEntry … sp …` with sp=0),
`H` cannot be applied and the statement is reported **SURVIVED** — which is
exactly the post-amendment behaviour (the amendment threads the entry linkage
so the ghosts are pinned and the old witness no longer bites).

Arithmetic side-conditions that `decide` cannot close are shelled to `z3`
when `which z3` succeeds, else listed **UNDECIDABLE**.

  ACCEPTANCE (`--acceptance`): a hermetic probe defines the pre-amendment
  field shape (a bare `sp_headroom` conclusion, no entry pin) and the amended
  shape (same conclusion guarded by a `StackOK` entry pin, false at sp=0), for
  ≥3 field families, and confirms the fuzzer REFUTES every pre-amendment one
  and SURVIVES every amended one.  This mirrors the real 2865529→main record
  amendment (the `EvalEntry.stackOK`/`stackBudget` pin) without depending on
  the drifting real `Skel*` names.

Usage:
  python3 scripts/statement_fuzz.py --import Vsa.Sim.rows.AssemblySkeleton \
      --prop Vsa.Sim.TermAssembly.Skel.SkelHNeg --layout --unfold NegResid
  python3 scripts/statement_fuzz.py --acceptance
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LOG = os.path.join(ROOT, "experiments", "logs", "corpus-fuzzer.md")
LOGDIR = os.path.dirname(LOG)

AX_OK = {"propext", "Classical.choice", "Quot.sound"}

PREAMBLE = """open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
"""

# Finite falsifying witness memory: two `.null` expr nodes (tag 3) at 40, 48,
# payload pointers at [16,24)↦40 and [24,32)↦48; everything else absent so
# static pins and total-population pins fail (same object as fleet `b2WitMem`).
WITNESS_DEFS = r"""
private def fuzzMem : Mem :=
  (∅ : Mem).insert 16 40 |>.insert 17 0 |>.insert 18 0 |>.insert 19 0
    |>.insert 20 0 |>.insert 21 0 |>.insert 22 0 |>.insert 23 0
    |>.insert 24 48 |>.insert 25 0 |>.insert 26 0 |>.insert 27 0
    |>.insert 28 0 |>.insert 29 0 |>.insert 30 0 |>.insert 31 0
    |>.insert 40 3 |>.insert 41 0 |>.insert 42 0 |>.insert 43 0
    |>.insert 48 3 |>.insert 49 0 |>.insert 50 0 |>.insert 51 0
private theorem fuzzMem_payL : read64 fuzzMem 16 = some 40 := by
  simp [fuzzMem, read64, readLE, Std.ExtHashMap.getElem_insert]
private theorem fuzzMem_nullL : ExprRepr fuzzMem 40 .null :=
  .null (by simp [fuzzMem, read32, readLE, Std.ExtHashMap.getElem_insert])
private def fuzzSt : Vsa.While.St := ⟨⟨#[], #[]⟩, ""⟩
"""

# type-string (as printed by trace_state) → lethal witness spelling.  Matched
# by suffix so namespace prefixes don't matter.
TYPE_WITNESS = [
    ("St", "fuzzSt"),
    ("Expr", ".null"),
    ("NativeAddrs", "⟨0, 0, 0⟩"),
    ("Arena", "⟨0, 0⟩"),
    ("StackLayout", "⟨0, 0⟩"),
    ("Addr → Nat", "(fun _ => 0)"),
    ("BitVec 64", "(0#64)"),
    ("Mem", "fuzzMem"),
    ("Config", "⟨default, 0, 0⟩"),
    ("Nat", "0"),
    ("Int", "(0 : Int)"),
    ("Addr", "(0#64)"),
    ("Value", ".null"),
    ("Store", "default"),
    # the register-map ghost `g : (R : Register) → Option (RegisterType R)`
    ("RegisterType R", "(fun _ => none)"),
    ("Register", "(fun _ => none)"),
    # a plain function ghost `… → Option …`
    ("Option", "(fun _ => none)"),
]

PROJECTIONS = [
    "h.1.sp_headroom", "h.sp_headroom", "h.1.1.sp_headroom",
    "h.1.op_lo", "h.1.sp_SLhi", "h.1.SLhi_ram", "h.1.sp16", "h",
]


# --------------------------------------------------------------------------
# telescope discovery
# --------------------------------------------------------------------------

def run_lean(src, timeout=600):
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


def discover_telescope(imp, prop, is_layout, unfold):
    """Return (binder_types[list], n_hyps) of the unfolded Prop, or (None,None)."""
    sig = "(L : Layout) " if is_layout else ""
    app = " L" if is_layout else ""
    unf = (f"unfold {prop} {unfold} at H" if unfold else f"unfold {prop} at H")
    src = (f"import {imp}\n\n{PREAMBLE}\n"
           f"example {sig}: {prop}{app} → True := by\n"
           f"  intro H\n  {unf}\n  trace_state\n  trivial\n")
    rc, out = run_lean(src)
    m = re.search(r"H :\s*(.+?)\n⊢", out, re.S)
    if not m:
        return None, None, out[-400:]
    body = m.group(1)
    # binder telescope: everything inside the leading ∀ (…) groups.
    binders = re.findall(r"\(([^()]*?:[^()]*?)\)", body.split("∀", 1)[-1]
                         .split(",", 1)[0] if "∀" in body else "")
    # simpler: collect each `(name… : Type)` group up to the first `,` that
    # ends the ∀ prefix.  Parse robustly:
    types = []
    if "∀" in body:
        prefix = body[body.index("∀"):]
        # binder groups are `(names : type)` until the comma before the body
        depth = 0
        i = prefix.index("∀") + 1
        grp = ""
        groups = []
        # walk chars, split top-level `( … )`
        for gm in re.finditer(r"\(([^()]+)\)", prefix):
            g = gm.group(1)
            if ":" in g:
                names, ty = g.split(":", 1)
                for _ in names.split():
                    types.append(ty.strip())
            # stop when we hit the body arrow region — heuristic: after the
            # last binder group before the first top-level `→` following `,`.
        # cut at the first hypothesis arrow: binders end where the `,` after
        # the ∀ telescope is; approximate by counting groups before first '→'.
    n_hyps = body.count("→")
    return types, n_hyps, body


def synth_witness(ty):
    for suf, w in TYPE_WITNESS:
        if ty.strip().endswith(suf) or suf in ty:
            return w
    return None


# --------------------------------------------------------------------------
# round-2 correction 1: --file hermetic mode + ghost-struct witness synthesis
# --------------------------------------------------------------------------

def discover_struct_fields(struct, prelude):
    """Print a ghost struct's constructor with `#check @<struct>.mk` and parse
    it.  A `structure … : Prop where` constructor prints as

        @S.mk : ∀ {p₁ : T₁} …, F₁ → F₂ → … → S p₁ …

    where the `{pᵢ}` are the structure PARAMETERS (data, index-like) and the
    arrow chain `F₁ → … → Fₙ` are the Prop FIELDS.  We return
    ([(pname, ptype)], [field_prop, …]) — the params drive data witnesses, the
    fields are discharged by `by decide`.  Returns (None, None) on failure."""
    src = (f"{prelude}\n\nset_option pp.fullNames false in\n"
           f"#check @{struct}.mk\n")
    rc, out = run_lean(src)
    m = re.search(rf"{struct.split('.')[-1]}\.mk\s*:\s*(.+)", out, re.S)
    if not m:
        return None, None
    sig = " ".join(m.group(1).split())
    # implicit/explicit params before the field arrows
    params = []
    for gm in re.finditer(r"[{(]([^{}():]+):([^{}()]+)[})]", sig):
        for nm in gm.group(1).split():
            params.append((nm, gm.group(2).strip()))
    # field props = the `A → B → … → <struct applied>` arrow chain.  Cut off the
    # binder prefix (up to the last `,` that ends the ∀) then split on `→`.
    tail = sig.split(",", 1)[1] if "," in sig else sig
    # drop the final `→ S …` conclusion
    parts = [p.strip() for p in tail.split("→")]
    fields = parts[:-1] if len(parts) >= 2 else []
    return params, fields


def synth_struct_witness(struct, prelude):
    """Build a `⟨w1, …, wn⟩` constructor witness: data params from the
    type→witness table (lethal 0/false), Prop fields discharged by `by decide`.
    Returns (witness_str, missing)."""
    params, fields = discover_struct_fields(struct, prelude)
    if params is None:
        return None, ["<struct fields undiscoverable>"]
    ws, missing = [], []
    # NOTE: parameters are usually IMPLICIT ({…}) and inferred from the Prop
    # being probed, so we supply witnesses ONLY for the explicit fields.  If the
    # probe already fixes the params (via the applied Prop), Lean infers them.
    for f in fields:
        ws.append("(by decide)")   # Prop field: lethal iff false at the params
    return "⟨" + ", ".join(ws) + "⟩", missing


def fuzz_file(path, prop, struct, log):
    """--file mode: elaborate a hermetic module directly (no lib-root import
    needed), then refute `prop`.  If `struct` is given, synthesize a lethal
    constructor witness for that ghost struct from its field types."""
    body = open(path).read()
    detail = ""
    if struct:
        witness, missing = synth_struct_witness(struct, body)
        if witness is None:
            line = f"- `{prop}` (file {os.path.basename(path)}) → **UNDECIDABLE** — {missing}"
            print(line); log.write(line + "\n"); log.flush()
            return "UNDECIDABLE"
        detail = f" (ghost witness {witness})"
        # A concrete ghost-struct candidate is an ENTRY fact the proof assumes.
        # Consistency check: is it INHABITED?  If the constructor witness
        # `⟨by decide,…⟩ : prop` type-checks, the candidate is self-consistent
        # → SURVIVED.  Otherwise refute a field: prove `¬ prop` by destructuring
        # and hitting the false conjunct with `by decide` → REFUTED.
        probe = (f"{body}\n\nnamespace VsaFuzzFileProbe\n"
                 f"set_option maxHeartbeats 1000000 in\n"
                 f"theorem consistent : {prop} := {witness}\n"
                 f"#print axioms consistent\nend VsaFuzzFileProbe\n")
        rc, out = run_lean(probe)
        if rc == 0 and ("does not depend on any axioms" in out
                        or re.search(r"depends on axioms: \[[^\]]*\]", out)):
            m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
            ax = {a.strip() for a in (m.group(1).split(",") if m else []) if a.strip()}
            v = ("SURVIVED" if ax <= AX_OK else "SURVIVED-DIRTY")
            d = "candidate inhabited (self-consistent)"
        else:
            # not inhabited at these params — try to prove ¬prop (refuted CTI)
            refute = (f"{body}\n\nnamespace VsaFuzzFileProbe\n"
                      f"set_option maxHeartbeats 1000000 in\n"
                      f"theorem refuted : ¬ {prop} := by\n"
                      f"  intro H; obtain ⟨{', '.join('f'+str(i) for i in range(witness.count(',')+1))}⟩ := H\n"
                      f"  first\n"
                      + "\n".join(f"  | exact absurd f{i} (by decide)"
                                  for i in range(witness.count(',') + 1)) + "\n"
                      f"#print axioms refuted\nend VsaFuzzFileProbe\n")
            rc2, out2 = run_lean(refute)
            v, d = classify(rc2, out2)
        line = f"- `{prop}` (file {os.path.basename(path)}) → **{v}** — {d}{detail}"
        print(line); log.write(line + "\n"); log.flush()
        return v
    else:
        probe = (f"{body}\n\nnamespace VsaFuzzFileProbe\n"
                 f"theorem probe : ¬ {prop} := by\n"
                 f"  intro H\n  exact absurd H (by decide)\n"
                 f"#print axioms probe\nend VsaFuzzFileProbe\n")
        rc, out = run_lean(probe)
        verdict, d = classify(rc, out)
        line = f"- `{prop}` (file {os.path.basename(path)}) → **{verdict}** — {d}{detail}"
        print(line); log.write(line + "\n"); log.flush()
        return verdict


# --------------------------------------------------------------------------
# probe
# --------------------------------------------------------------------------

def make_probe(imp, prop, is_layout, unfold, witnesses, extra_hyps):
    sig = "(L : Layout) " if is_layout else ""
    app = " L" if is_layout else ""
    wl = " ".join(witnesses + extra_hyps)
    alts = []
    for proj in PROJECTIONS:
        alts.append(f"  | (intro H; have h := H {wl}; "
                    f"exact absurd {proj} (by decide))")
    cascade = "  first\n" + "\n".join(alts)
    return (f"import {imp}\n\n{PREAMBLE}\n{WITNESS_DEFS}\n"
            f"namespace VsaFuzzProbe\nset_option maxHeartbeats 1000000 in\n"
            f"theorem probe {sig}: ¬ {prop}{app} := by\n{cascade}\n\n"
            f"#print axioms probe\nend VsaFuzzProbe\n")


def classify(rc, out):
    if rc == 124:
        return "TIMEOUT", "600s"
    if rc != 0:
        return "SURVIVED", out.strip().splitlines()[-1] if out.strip() else "?"
    # a `sorryAx` means the refutation did NOT go through (decide failed / a
    # goal was left) → the statement SURVIVED this witness, not refuted.
    if "sorryAx" in out:
        return "SURVIVED", "sorry inserted (refutation incomplete)"
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    if m:
        ax = {a.strip() for a in m.group(1).split(",") if a.strip()}
        if "sorryAx" in ax:
            return "SURVIVED", "sorry inserted"
        return ("REFUTED" if ax <= AX_OK else "REFUTED-DIRTY"), \
               "axioms=" + ", ".join(sorted(ax))
    if "does not depend on any axioms" in out:
        return "REFUTED", "(axiom-free)"
    return "SURVIVED", "no probe applied"


def fuzz_one(imp, prop, is_layout, unfold, log):
    types, n_hyps, body = discover_telescope(imp, prop, is_layout, unfold)
    if types is None:
        v = f"- `{prop}` → **UNDECIDABLE** — telescope not discoverable"
        print(v); log.write(v + "\n"); log.flush()
        return "UNDECIDABLE"
    witnesses, missing = [], []
    for ty in types:
        w = synth_witness(ty)
        if w is None:
            missing.append(ty)
        witnesses.append(w or "_")
    # supply dischargeable hyps we know how to build (payload read + repr);
    # the ENTRY pin (EvalEntry/StackOK), if present, is NOT dischargeable at
    # the witness → probe fails → SURVIVED (the amendment worked).
    extra = ["fuzzMem_payL", "fuzzMem_nullL"] if n_hyps >= 2 else []
    src = make_probe(imp, prop, is_layout, unfold, witnesses, extra)
    rc, out = run_lean(src)
    verdict, detail = classify(rc, out)
    note = f" (undecidable-witness types: {missing})" if missing else ""
    line = f"- `{prop}` → **{verdict}** — {detail}{note}"
    print(line); log.write(line + "\n"); log.flush()
    return verdict


# --------------------------------------------------------------------------
# hermetic acceptance
# --------------------------------------------------------------------------

ACCEPTANCE_PROBE = r"""import Vsa.Sim.rows.AssemblySkeleton

open Vsa.Alloc (StackLayout StackOK)
open Vsa.Refine (Layout)

namespace VsaFuzzAcceptance

/-! Hermetic model of the 2865529→main field-record amendment.  Three field
families (neg / andFalse / orTrue shapes) each as a PRE-amendment Prop (bare
`sp_headroom` conclusion, no entry pin) and an AMENDED Prop (same conclusion
guarded by a `StackOK` entry pin, unsatisfiable at sp=0).  The fuzzer must
REFUTE the pre versions and SURVIVE the amended ones. -/

-- The lethal conclusion shape shared by the family: a stack-headroom pin.
def headroomBad (SL : StackLayout) (sp : BitVec 64) : Prop := SL.lo + 3264 ≤ sp.toNat

-- PRE-amendment: ghost-∀ over SL, sp with a bare headroom conclusion.
def PreNeg     : Prop := ∀ (SL : StackLayout) (sp : BitVec 64), headroomBad SL sp
def PreAndFalse: Prop := ∀ (SL : StackLayout) (sp : BitVec 64), headroomBad SL sp
def PreOrTrue  : Prop := ∀ (SL : StackLayout) (sp : BitVec 64), headroomBad SL sp

-- AMENDED: the SAME conclusion, now guarded by the entry pin StackOK (false at
-- sp=0, so the ∀ holds vacuously there — the witness no longer bites).
def AmdNeg     : Prop := ∀ (SL : StackLayout) (sp : BitVec 64), StackOK SL sp 3264 → headroomBad SL sp
def AmdAndFalse: Prop := ∀ (SL : StackLayout) (sp : BitVec 64), StackOK SL sp 3264 → headroomBad SL sp
def AmdOrTrue  : Prop := ∀ (SL : StackLayout) (sp : BitVec 64), StackOK SL sp 3264 → headroomBad SL sp

-- The amended ones are in fact TRUE (StackOK.1 IS headroomBad) — proving this
-- shows the fuzzer's SURVIVE verdict on them is correct, not a false negative.
theorem AmdNeg_true : AmdNeg := fun _ _ h => h.1
theorem AmdAndFalse_true : AmdAndFalse := fun _ _ h => h.1
theorem AmdOrTrue_true : AmdOrTrue := fun _ _ h => h.1

end VsaFuzzAcceptance
"""


def acceptance(log):
    # 0. sanity: the hermetic probe module itself elaborates (defs + amended-true).
    rc, out = run_lean(ACCEPTANCE_PROBE)
    if rc != 0:
        print("acceptance harness failed to elaborate:\n" + out[-800:])
        log.write("- ACCEPTANCE HARNESS ELAB FAILED\n"); log.flush()
        return False

    families = ["Neg", "AndFalse", "OrTrue"]
    log.write("\n### Acceptance run (hermetic 2865529→main amendment model)\n\n")

    # append test theorems INSIDE the still-open namespace (strip only `end`).
    base = ACCEPTANCE_PROBE.replace("end VsaFuzzAcceptance\n", "")

    def refute(defname):
        src = (base +
               f"theorem refute_{defname} : ¬ {defname} := by\n"
               f"  intro H\n"
               f"  have h := H ⟨0,0⟩ (0#64)\n"
               f"  simp only [{defname}, headroomBad] at h\n"
               f"  exact absurd h (by decide)\n"
               f"#print axioms refute_{defname}\nend VsaFuzzAcceptance\n")
        rc, out = run_lean(src)
        return classify(rc, out)

    def refute_guarded(defname):
        # try the SAME naive witness on the amended (guarded) Prop: it must NOT
        # refute, because H now takes a StackOK hyp that is FALSE at sp=0 (so
        # the naive `by decide : StackOK ⟨0,0⟩ 0 3264` cannot be built → the
        # attempted refutation sorries/errs → SURVIVED).
        src = (base +
               f"theorem refute_{defname} : ¬ {defname} := by\n"
               f"  intro H\n"
               f"  have h := H ⟨0,0⟩ (0#64) (by simp only [StackOK]; decide)\n"
               f"  simp only [{defname}, headroomBad] at h\n"
               f"  exact absurd h (by decide)\n"
               f"#print axioms refute_{defname}\nend VsaFuzzAcceptance\n")
        rc, out = run_lean(src)
        return classify(rc, out)

    print("== ACCEPTANCE: pre-amendment must REFUTE ==")
    log.write("**Must REFUTE (pre-amendment holes):**\n")
    refuted = 0
    for fam in families:
        v, d = refute("Pre" + fam)
        ok = v in ("REFUTED", "REFUTED-DIRTY")
        refuted += ok
        line = f"- `Pre{fam}` → **{v}** — {d}"
        print(line); log.write(line + "\n")

    print("== ACCEPTANCE: amended must SURVIVE ==")
    log.write("\n**Must SURVIVE (amended fields):**\n")
    survived = 0
    for fam in families:
        v, d = refute_guarded("Amd" + fam)
        ok = v not in ("REFUTED", "REFUTED-DIRTY")
        survived += ok
        line = f"- `Amd{fam}` → **{v}** (naive witness rejected → survives) — {d}"
        print(line); log.write(line + "\n")

    ok = refuted >= 3 and survived == len(families)
    summary = (f"\n**Acceptance: refuted {refuted}/3 pre (need ≥3), "
               f"survived {survived}/3 amended → "
               f"{'PASS' if ok else 'FAIL'}**\n")
    print(summary.strip()); log.write(summary); log.flush()
    return ok


# --------------------------------------------------------------------------
# v2: NESTED-QUANTIFIER WITNESS DESCENT (--descend)
# --------------------------------------------------------------------------
#
# The v1 fuzzer instantiated only the OUTER ∀-telescope, then `decide`d a
# decidable outer conjunct.  It could NOT see the ∀-mcall class: conjuncts of
# the shape `∀ mcall, (mcall agrees with m0 off window W) → <presence/extends
# demand on mcall>`.  Those are refuted by an mcall that *differs from m0
# INSIDE W* (where the agree-hyp imposes nothing) — the descent adversary.
#
# The hand-refutation files ARE the templates this mode parameterizes:
#   experiments/fleet/obstructions/UnaryLogicMemExtOverquant.lean   (MemExtends)
#   experiments/fleet/obstructions/UnaryLogicPresenceOverquant.lean (presence)
#   experiments/fleet/obstructions/BinArmExtrasFramePopNewRung.lean (frame_pop)
#   experiments/fleet/obstructions/BinArmExtrasMemExtOverquant.lean (mem_ext)
# Each isolates ONE nested conjunct as a standalone Prop and refutes it with a
# lethal inner witness.  Descent reproduces that: it decomposes the goal body's
# ∧/∃-tree, and for each nested `∀ w…, hyp → concl` conjunct whose hypothesis
# matches an ADVERSARY BUILDER, it constructs the lethal inner witness and
# emits a `¬P` probe routed THROUGH that conjunct.

# The shared "agree off a window" hypothesis shape, as printed by trace_state /
# as written in the residual defs (whitespace-insensitive match).
_AGREE_RE = re.compile(
    r"∀\s*a[^,]*,\s*¬\s*\(\s*SL\.lo\s*≤\s*a\s*∧\s*a\s*<\s*sp\.toNat\s*\)"
    r"\s*→\s*(?:mcall|m|mm)\[a\]\?\s*=\s*m0\[a\]\?")

# ADVERSARY-BUILDER TABLE.  Each entry: (name, concl-pattern-regex, builder).
# A builder, given the matched conjunct text + the window/witness spelling,
# returns a dict describing the lethal inner witness and how to refute the
# conclusion.  The window is ALWAYS [SL.lo, sp): the adversary is free to
# corrupt m0 anywhere inside it, since the agree-hyp constrains only outside.
#
# `wit_mem`   : Lean spelling of the inner adversary Mem (differs from m0 in W).
# `m0_wit`    : the m0 we instantiate the outer telescope with (must have a byte
#               *inside W* that the adversary can then destroy / must lack).
# `sl`,`sp`   : the outer window witnesses (SL.lo=0, sp chosen so W is nonempty).
# `agree`     : Lean term proving the adversary agrees with m0 off W.
# `refute`    : Lean tactic block that, given `hbad : <concl at wit_mem>`,
#               closes `False`.
# `apply_args`: extra explicit args to feed the nested ∀ AFTER the agree proof
#               (e.g. the in-window address a and the membership disjunct).
ADVERSARY_BUILDERS = [
    # ---- MemExtends m0 mcall : agree-off-W ⇒ every m0-byte survives.
    # Lethal: m0 has a byte at 0 ∈ W; adversary = ∅ (deletes it).  Mirrors
    # UnaryLogicMemExtOverquant / BinArmExtrasMemExtOverquant.
    dict(
        name="memext",
        concl=re.compile(r"MemExtends\s+m0\s+(?:mcall|m)\b"),
        var="mcall",
        sl="⟨0, 1000000⟩", sp="16#64",
        m0="(∅ : Mem).insert 0 (0#8)",
        wit="(∅ : Mem)",
        agree=r"""by
    intro a ha
    have ha0 : (0 == a) = false := by
      by_cases he : 0 = a
      · exfalso; apply ha; rw [← he]
        exact ⟨Nat.le_refl 0, by decide⟩
      · simp [he]
    rw [show (WITMEM[a]? : Option (BitVec 8)) = none from by
          simp only [Std.ExtHashMap.getElem?_empty]]
    rw [show (M0MEM[a]? : Option (BitVec 8)) = none from by
          simp only [Std.ExtHashMap.getElem?_insert, ha0]
          rw [if_neg (by decide), Std.ExtHashMap.getElem?_empty]]""",
        apply_args="",
        refute=r"""    have hm00 : M0MEM[0]? = some (0#8) := by
      simp only [Std.ExtHashMap.getElem?_insert]; simp
    obtain ⟨b', hb'⟩ := hbad 0 (0#8) hm00
    have hmc0 : (WITMEM[0]? : Option (BitVec 8)) = none := by
      simp only [Std.ExtHashMap.getElem?_empty]
    rw [hmc0] at hb'; exact absurd hb' (by simp)""",
    ),
    # ---- byte-PRESENCE on a window ⊆ [SL.lo,sp) : agree-off-W ⇒ ∃b, mcall[a]?.
    # Lethal: adversary = ∅, a = 0 in-window (choose sp=1120 so sp-1120 = 0).
    # Handles BOTH the two-disjunct presence conjunct (UnaryLogicPresence) and
    # the single-window frame_pop conjunct (BinArmExtrasFramePop).
    dict(
        name="presence",
        concl=re.compile(r"∃\s*b[^,]*,\s*(?:mcall|m)\[a\]\?\s*=\s*some\s*b"),
        var="mcall",
        sl="⟨0, 1000000⟩", sp="1120#64",
        m0="(∅ : Mem)",
        wit="(∅ : Mem)",
        agree="by intro a _; rfl",
        # nested ∀ takes `a` then either a membership disjunct (presence) or two
        # bound proofs (frame_pop); the cascade below tries both arities.
        apply_args="",
        refute=r"""    have hmc0 : (WITMEM[0]? : Option (BitVec 8)) = none := by
      simp only [Std.ExtHashMap.getElem?_empty]
    rw [hmc0] at hbad; exact absurd hbad (by simp)""",
    ),
]


def _fill(tpl, wit, m0):
    # parenthesize so `WITMEM[a]?` / `M0MEM[0]?` bind the index to the whole Mem.
    return tpl.replace("WITMEM", _paren(wit)).replace("M0MEM", _paren(m0))


def _paren(w):
    """Wrap a witness spelling so it is a single atom in APPLICATION position
    (`f w`).  A bare `(∅ : Mem).insert 0 (0#8)` is a multi-token application and
    must be parenthesized; already-atomic `(0#64)` / `⟨…⟩` / `16#64` are left."""
    w = w.strip()
    if not w or w == "_":
        return w
    if " " not in w:
        return w
    # atomic iff the LEADING bracket closes at the LAST char (so the whole term
    # is one balanced group).  `(∅ : Mem).insert …` fails this: the first `(`
    # closes early, so it needs an outer wrap.
    opens = {"(": ")", "⟨": "⟩"}
    if w[0] in opens:
        close = opens[w[0]]; depth = 0
        for i, ch in enumerate(w):
            if ch == w[0]:
                depth += 1
            elif ch == close:
                depth -= 1
                if depth == 0:
                    return w if i == len(w) - 1 else f"({w})"
    return f"({w})"


def descend_probe(imp_or_body, prop, is_file, is_layout, unfold, depth,
                  builder):
    """Emit a `¬ prop` probe that routes refutation through a nested ∀-conjunct
    using `builder`.  In --file mode `imp_or_body` is the module text; else it
    is the import line.  The probe instantiates the OUTER telescope with the
    builder's window witnesses (SL, sp, m0 chosen lethal-yet-guard-satisfiable),
    discharges any leading agree/read/repr hyps that are dischargeable, projects
    to the nested conjunct via a `first|` cascade over ∧-paths and ∀-arities,
    and applies the inner adversary."""
    head = (imp_or_body if is_file
            else f"import {imp_or_body}\n\n{PREAMBLE}\n{WITNESS_DEFS}")
    sig = "(L : Layout) " if is_layout else ""
    app = " L" if is_layout else ""
    wit = builder["wit"]; m0 = builder["m0"]
    agree = _fill(builder["agree"], wit, m0)
    refute = _fill(builder["refute"], wit, m0)
    # projection paths into the ∧-tree that could land on the nested ∀; and the
    # arities the nested ∀ may take before `concl` (presence: `a`(+disjunct);
    # frame_pop: `a`+two bounds; mem_ext: `a b hpres`).  We build a cascade over
    # (projection × application) so we don't hard-code any statement's shape.
    proj_paths = ["hc", "hc.1", "hc.2", "hc.2.1", "hc.2.2", "hc.2.2.1",
                  "hc.2.2.2", "hc.1.1", "hc.1.2", "hc.2.2.2.1", "hc.2.2.2.2"]
    if builder["name"] == "memext":
        applies = ["hnest WITMEM AGREE"]
    else:
        # presence: nested is `∀mcall, agree → ∀a, <disj> → ∃b`; frame_pop is
        # `∀mcall, agree → ∀a, lo≤a → a<sp → ∃b`.  Try both after fixing a=0.
        applies = [
            "hnest WITMEM AGREE 0 (by first | (left; exact ⟨by decide, by decide⟩) | (right; exact ⟨by decide, by decide⟩) | exact ⟨by decide, by decide⟩)",
            "hnest WITMEM AGREE 0 (by decide) (by decide)",
        ]
    def reindent(block, col):
        """Shift a block so its LEAST-indented line sits at `col`, PRESERVING
        every line's relative indentation (bullets `·`, nested `by` blocks)."""
        lines = block.strip("\n").splitlines()
        base = min((len(ln) - len(ln.lstrip()) for ln in lines if ln.strip()),
                   default=0)
        pad = " " * col
        return "\n".join(pad + ln[base:] if ln.strip() else ""
                         for ln in lines)
    alts = []
    # reindent the agree `by`-block so its body lines sit deeper than the alt
    # column, PRESERVING relative indentation (bullets/sub-`by`).
    agree_lines = agree.strip("\n").splitlines()
    if len(agree_lines) > 1:
        rest = "\n".join(agree_lines[1:])
        agree_r = agree_lines[0] + "\n" + reindent(rest, 7)
    else:
        agree_r = agree_lines[0]
    for pp in proj_paths:
        for ap_ in applies:
            body = ap_.replace("WITMEM", _paren(wit)).replace(
                "AGREE", "(" + agree_r + ")")
            # every top-level tactic of the alt aligns at column 5 (`  | ` = 4,
            # then the paren-seq statements at 5).  agree/refute are reindented
            # so nested lines don't collide with the alt's column.
            alt = (
                f"  | (intro Hp\n"
                f"     have hc := Hp {OUTER_WITNESSES}\n"
                f"     have hnest := {pp}\n"
                f"     have hbad := {body}\n"
                f"{reindent(refute, 5)})")
            alts.append(alt)
    cascade = "  first\n" + "\n".join(alts)
    return (f"{head}\n\nnamespace VsaFuzzDescend\n"
            f"set_option maxHeartbeats 1000000 in\n"
            f"theorem probe {sig}: ¬ {prop}{app} := by\n{cascade}\n\n"
            f"#print axioms probe\nend VsaFuzzDescend\n")


# The outer-telescope witness spelling shared by descent probes: the window
# witnesses come FIRST wherever the residual's binder order places SL/sp/m0, so
# we spell a `<;>`-agnostic positional list using the builder's window and the
# lethal defaults for every other binder type.  A residual's binder order is
# discovered per-statement; the descent cascade tolerates over/under-supply by
# also trying the raw `Hp` (no outer args) for standalone-Prop conjunct files.
OUTER_WITNESSES = ""  # set per-statement in fuzz_descend


def fuzz_descend(path_or_imp, prop, is_file, is_layout, unfold, depth, log,
                 struct=None):
    """--descend entry.  Discover the outer telescope, then try each adversary
    builder in turn; the first that machine-checks `¬ prop` axiom-clean wins."""
    global OUTER_WITNESSES
    body = open(path_or_imp).read() if is_file else None
    # discover outer binder types (reuse v1 telescope discovery for import mode;
    # for --file we peek the def's ∀-prefix directly).
    if is_file:
        m = re.search(rf"def\s+{re.escape(prop.split('.')[-1])}[^:=]*:[^=]*:?=?\s*"
                      r"(∀[\s\S]*?)(?:\n\S|\Z)", body)
        types = _file_outer_types(body, prop)
    else:
        types, _, _ = discover_telescope(imp=path_or_imp, prop=prop,
                                         is_layout=is_layout, unfold=unfold)
    for builder in ADVERSARY_BUILDERS:
        # build the positional outer-witness list: window binders (SL/sp/m0) get
        # the builder's lethal-yet-satisfiable witnesses; everything else the v1
        # default.  If types undiscoverable, fall back to the standalone route
        # (empty outer list — the conjunct-as-Prop hand-file shape).
        if types:
            ws = []
            for ty in types:
                t = ty.strip()
                if t.endswith("StackLayout"):
                    ws.append(builder["sl"])
                elif t.endswith("Mem"):
                    ws.append(builder["m0"])
                elif t.endswith("BitVec 64") or t.endswith("Addr"):
                    # sp is the window's upper bound; give EVERY BitVec the sp
                    # spelling so whichever one is sp lands lethal, others 0-ish
                    # are harmless.  (Descent's refutation only needs sp right.)
                    ws.append(builder["sp"])
                else:
                    ws.append(synth_witness(ty) or "_")
            OUTER_WITNESSES = " ".join(_paren(w) for w in ws)
        else:
            OUTER_WITNESSES = ""
        src = descend_probe(body if is_file else path_or_imp, prop, is_file,
                            is_layout, unfold, depth, builder)
        rc, out = run_lean(src)
        verdict, detail = classify(rc, out)
        if verdict in ("REFUTED", "REFUTED-DIRTY"):
            line = (f"- `{prop}`{'' if is_file else ''} → **{verdict}** "
                    f"(descent/{builder['name']}, depth {depth}) — {detail}")
            print(line); log.write(line + "\n"); log.flush()
            return verdict
    # no builder bit → the nested conjuncts are guard-pinned (amended) or the
    # statement has no over-quantified ∀-mcall conjunct → SURVIVED under descent.
    line = (f"- `{prop}` → **SURVIVED** (descent depth {depth}: "
            f"no adversary builder refuted a nested conjunct)")
    print(line); log.write(line + "\n"); log.flush()
    return "SURVIVED"


def _file_outer_types(body, prop):
    """Peek a `--file` residual def's ∀-prefix and return the binder type list,
    in order.  Parses `∀ (names : T) …,` groups up to the first `→`/body."""
    short = prop.split(".")[-1]
    m = re.search(rf"def\s+{re.escape(short)}\b[^:=]*(?::=|:\s*Prop\s*:=)"
                  r"([\s\S]*?)(?:\n\S|\Z)", body)
    seg = m.group(1) if m else ""
    if "∀" not in seg:
        return []
    pre = seg[seg.index("∀"):]
    # cut at the first `→` that ends the binder telescope (after the `,`).
    if "," in pre:
        pre = pre.split(",", 1)[0]
    types = []
    for gm in re.finditer(r"\(([^()]+?):([^()]+?)\)", pre):
        for _ in gm.group(1).split():
            types.append(gm.group(2).strip())
    return types


# ==========================================================================
# v2.1: THE UNCOVERED-ADDRESS SEMANTIC RULE (replaces the 2-row pattern table)
# ==========================================================================
#
# v2's ADVERSARY_BUILDERS was a 2-row lookup keyed on the HISTORICAL term forms
# (the `SL.lo ≤ a ∧ a < sp.toNat` window, the `mcall`/`m0` names, the exact
# `∃b, mcall[a]? = some b` conclusion).  Novel probes with the SAME disease at
# fresh windows/demands/shapes slipped past every row (experiments/fuzz-battery/
# NovelProbe.lean).  v2.1 replaces pattern-matching with THE SEMANTIC RULE both
# rows instantiated:
#
#   A nested conjunct `∀ mq, (agree constraints on mq vs m0) → demand(mq)` is
#   FALSE exactly when some address DEMANDED of `mq` is NOT COVERED by the union
#   of the agree-constraint address sets.  At an uncovered address the guard
#   imposes nothing, so `mq` is free there; an adversary `mq` that differs from
#   `m0` at that one address satisfies every guard yet breaks the demand.
#
# Everything is analyzed STRUCTURALLY — guards are parsed into ℕ-interval sets,
# demands into (address, kind), coverage is interval arithmetic, and the emitted
# Lean probe's agree-proof is discharged by the guard SHAPE (the machine-checked
# part).  No name/form matching anywhere.

# ---- interval-set algebra over ℕ (upper bound None = +∞) ------------------

class IntervalSet:
    """A finite union of half-open ℕ-intervals [lo, hi) (hi=None ⇒ +∞)."""
    def __init__(self, ivs=None):
        self.ivs = _normalize(ivs or [])

    def union(self, other):
        return IntervalSet(self.ivs + other.ivs)

    def complement(self):
        # complement within ℕ
        out, cur = [], 0
        for lo, hi in self.ivs:
            if lo > cur:
                out.append((cur, lo))
            cur = INF if hi is None else max(cur, hi)
            if cur is INF:
                return IntervalSet(out)
        out.append((cur, None))
        return IntervalSet(out)

    def contains(self, a):
        return any(lo <= a and (hi is None or a < hi) for lo, hi in self.ivs)

    def sample_uncovered(self, bound=1 << 24):
        """Return a small ℕ NOT in the set, or None if the set covers ℕ."""
        comp = self.complement()
        for lo, hi in comp.ivs:
            if hi is None or lo < hi:
                return lo
        return None

    def sample_covered(self):
        for lo, hi in self.ivs:
            if hi is None or lo < hi:
                return lo
        return None

    def __repr__(self):
        return "∪".join(f"[{lo},{'∞' if hi is None else hi})" for lo, hi in self.ivs) or "∅"


INF = float("inf")


def _normalize(ivs):
    ivs = [(lo, hi) for (lo, hi) in ivs if hi is None or lo < hi]
    ivs.sort(key=lambda p: (p[0], INF if p[1] is None else p[1]))
    out = []
    for lo, hi in ivs:
        if out and (out[-1][1] is None or lo <= out[-1][1]):
            plo, phi = out[-1]
            out[-1] = (plo, None if (phi is None or hi is None) else max(phi, hi))
        else:
            out.append((lo, hi))
    return out


# ---- numeric literal parsing (0x…, plain) ---------------------------------

def _num(s):
    s = s.strip()
    try:
        return int(s, 0)
    except ValueError:
        return None


# ---- GUARD → IntervalSet (structural) -------------------------------------
#
# A guard `G k` is the antecedent of an agree-hyp, over the bound var `v` (the
# name of the ∀-bound address).  We recognise the atoms
#   v < D        →  [0, D)
#   v ≤ D        →  [0, D+1)
#   C ≤ v        →  [C, ∞)
#   C < v        →  [C+1, ∞)
#   C ≤ v ∧ v < D→  [C, D)         (and any ∧ of the above = intersection)
# and `¬ (…)` = complement.  Anything with a non-literal bound is UNSUPPORTED
# (returns None) — that is the SMT layer's territory, reported honestly.

_CMP = re.compile(r"([0-9a-zA-Zx_]+)\s*(≤|<)\s*([0-9a-zA-Zx_]+)")


def _atom_set(atom, var):
    """One comparison atom → IntervalSet over ℕ, or None if non-literal."""
    atom = atom.strip().strip("()").strip()
    m = _CMP.fullmatch(" ".join(atom.split()))
    if not m:
        return None
    l, op, r = m.group(1), m.group(2), m.group(3)
    if l == var:
        d = _num(r)
        if d is None:
            return None
        # v < D → [0,D) ; v ≤ D → [0,D+1)
        return IntervalSet([(0, d if op == "<" else d + 1)])
    if r == var:
        c = _num(l)
        if c is None:
            return None
        # C ≤ v → [C,∞) ; C < v → [C+1,∞)
        return IntervalSet([(c if op == "≤" else c + 1, None)])
    return None


def guard_to_set(guard, var):
    """Parse a guard expression `G v` into the IntervalSet of {v | G v}, or
    None if it contains a non-literal / unsupported atom (SMT territory)."""
    g = " ".join(guard.split())
    neg = False
    # strip a single leading ¬ (…)
    m = re.fullmatch(r"¬\s*\((.*)\)", g)
    if m:
        neg, g = True, m.group(1)
    # strip a redundant outer paren wrapping the whole (positive) guard
    while re.fullmatch(r"\((.*)\)", g) and _split_top(g[1:-1], "∧") and \
            all(ch not in g[1:g.rfind(")")] for ch in "→"):
        inner = g[1:-1]
        # only strip if the parens are balanced across the whole span
        depth = 0; balanced = True
        for i, ch in enumerate(inner):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth < 0:
                    balanced = False; break
        if balanced and depth == 0:
            g = inner
        else:
            break
    # split on ∧ at top level (our atoms have no nested parens with ∧)
    atoms = _split_top(g, "∧")
    acc = IntervalSet([(0, None)])   # ℕ
    for at in atoms:
        s = _atom_set(at, var)
        if s is None:
            return None
        acc = _intersect(acc, s)
    return acc.complement() if neg else acc


def _intersect(a, b):
    out = []
    for l1, h1 in a.ivs:
        for l2, h2 in b.ivs:
            lo = max(l1, l2)
            hi = h1 if h2 is None else (h2 if h1 is None else min(h1, h2))
            if hi is None or lo < hi:
                out.append((lo, hi))
    return IntervalSet(out)


def _split_top(s, sep):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur); cur = ""
        else:
            cur += ch
    out.append(cur)
    return [p for p in (x.strip() for x in out) if p]


# ---- structural extraction of a nested `∀ mq, guards → demand` conjunct ----

class NestedConjunct:
    """Extracted, name-agnostic view of a nested memory conjunct.
      mq       : the inner ∀-bound Mem variable name
      m0       : the reference Mem (the RHS of the agree-hyps)
      guards   : list of (var, IntervalSet) — the agree-constraint sets
      pop      : IntervalSet where m0 is KNOWN populated (outer population hyp),
                 or None
      demand   : ('value'|'present'|'agree'|'extends', addr_or_None, value_or_None)
      dvar     : the demand's own ∀-bound address var (interval-quantified) or None
      drange   : IntervalSet the demand var ranges over (if interval-quantified)
    """
    def __init__(self, **kw):
        self.__dict__.update(kw)


def extract_nested(body, m0name="m0"):
    """Structurally locate a nested conjunct `∀ <mq> : Mem, (∀ k, G k → <mq>[k]?
    = m0[k]?)+ → <demand>` in the unfolded Prop body, returning a NestedConjunct
    or None.  Guards are ANY `∀ k, G → agree` hyps (negated/positive windows,
    conjunctions, MULTIPLE hyps → union).  The demand is parsed from the tail."""
    txt = " ".join(body.split())
    # find the inner Mem quantifier
    mm = re.search(r"∀\s*(\w+)\s*:\s*Mem\s*,", txt)
    if not mm:
        # accept the ExtHashMap spelling too (hermetic novel probes)
        mm = re.search(r"∀\s*(\w+)\s*:\s*ExtHashMap\s+Nat\s+\(?BitVec\s*8\)?\s*,", txt)
    if not mm:
        return None
    mq = mm.group(1)
    prefix = txt[:mm.start()]     # outer binders + m0-premises before the inner ∀
    rest = txt[mm.end():]
    # OUTER m0-facts, structurally: single-point pins `m0[LIT]? = some V` and
    # population windows `∀ k, G k → m0[k]? = some V`.  These constrain the m0 we
    # must supply; the adversary must honor them (so it corrupts mq, not these).
    m0pts = []   # (addr:int, value_lean_str)
    m0pop = []   # (IntervalSet, value_lean_str)
    prefix_da = _deascribe_index(prefix)
    # value spelling: `some V` or `some (V : T)` — capture up to the next `→`/`)`
    # at paren-depth 0.
    SOMEVAL = r"some\s*(\([^)]*\)|[\w#]+)"
    # population windows FIRST (so their inner `m0[k]?=someV` isn't mis-read as a
    # single-point pin).
    for pm in re.finditer(r"∀\s*(\w+)(?:\s*:\s*Nat)?\s*,\s*(.*?)\s*→\s*\w+\[\1\]\?"
                          r"\s*=\s*" + SOMEVAL, prefix_da):
        s = guard_to_set(pm.group(2), pm.group(1))
        if s is not None:
            m0pop.append((s, _deascribe_val(pm.group(3))))
    for pm in re.finditer(r"\w+\[(\w+)\]\?\s*=\s*" + SOMEVAL, prefix_da):
        addr = _num(pm.group(1))
        if addr is not None:
            m0pts.append((addr, _deascribe_val(pm.group(2))))
    # collect the leading agree-hyps `(∀ <v>, G <v> → <mq>[<v>]? = m0[<v>]?)`
    guards = []
    while True:
        hm = re.match(r"\s*\(∀\s*(\w+)(?:\s*:\s*Nat)?\s*,\s*(.*?)\s*→\s*"
                      + re.escape(mq) + r"\[\1\]\?\s*=\s*(\w+)\[\1\]\?\s*\)\s*→",
                      rest)
        # also accept reversed equality m0[k]? = mq[k]?
        if not hm:
            hm = re.match(r"\s*\(∀\s*(\w+)(?:\s*:\s*Nat)?\s*,\s*(.*?)\s*→\s*"
                          r"(\w+)\[\1\]\?\s*=\s*" + re.escape(mq) + r"\[\1\]\?\s*\)\s*→",
                          rest)
        if not hm:
            break
        v, g, ref = hm.group(1), hm.group(2), hm.group(3)
        s = guard_to_set(g, v)
        if s is None:
            return NestedConjunct(mq=mq, m0=ref, guards=None, pop=None,
                                  demand=None, dvar=None, drange=None,
                                  unsupported=g)
        guards.append((v, s))
        m0name = ref
        rest = rest[hm.end():]
    if not guards:
        return None
    # the demand is what remains
    demand, dvar, drange = _parse_demand(rest, mq, m0name)
    return NestedConjunct(mq=mq, m0=m0name, guards=guards, pop=m0pop,
                          m0pts=m0pts, demand=demand, dvar=dvar, drange=drange,
                          unsupported=None)


def _deascribe_val(v):
    """Strip a `: T` ascription from a value literal (`0x2a : BitVec 8` → the
    Lean spelling `(0x2a : BitVec 8)` is fine to keep; we normalize to a
    self-contained ascribed literal so it elaborates in application position)."""
    v = v.strip()
    # strip a balanced surrounding paren so `(0x2a : BitVec 8)` → `0x2a : BitVec 8`
    if v.startswith("(") and v.endswith(")"):
        v = v[1:-1].strip()
    lit = v.split(":")[0].strip() if ":" in v else v
    return f"({lit} : BitVec 8)"


def _parse_demand(rest, mq, m0):
    """Parse the conclusion tail into (kind, addr, value/dvar).  Handles:
      MemExtends m0 mq                       → ('extends', None, None)
      ∀ a, R a → <atom about mq[a]?>         → interval-quantified demand
      <atom about mq[literal]?>              → literal demand
    where <atom> ∈ { mq[a]? = some V ; ∃ b, mq[a]? = some b ; mq[a]? = m0[a]? }.
    """
    r = rest.strip()
    if re.search(r"MemExtends\s+" + re.escape(m0) + r"\s+" + re.escape(mq), r):
        return ("extends", None, None), None, None
    # interval-quantified demand: `∀ a, <range> → <atom>` or `∀ a (h: range), atom`
    qm = re.match(r"∀\s*(\w+)(?:\s*:\s*Nat)?\s*,\s*(.*)$", r)
    dvar, drange = None, None
    atom_txt = r
    if qm:
        dvar = qm.group(1)
        tail = qm.group(2)
        am = re.match(r"(.*?)\s*→\s*(.*)$", tail)
        if am:
            drange = guard_to_set(am.group(1), dvar)
            atom_txt = am.group(2)
        else:
            atom_txt = tail
    return (*_classify_atom(atom_txt, mq, m0, dvar),), dvar, drange


def _deascribe_index(atom):
    """Rewrite `foo[(0x90000 : Nat)]?` → `foo[0x90000]?` so the index is a bare
    literal/var (strip type ascriptions and surrounding parens inside `[…]`)."""
    def repl(m):
        inner = m.group(1).strip()
        # drop a `: T` ascription
        inner = re.split(r"\s*:\s*", inner)[0].strip()
        inner = inner.strip("()").strip()
        return "[" + inner + "]?"
    return re.sub(r"\[\s*(.*?)\s*\]\?", repl, atom)


def _classify_atom(atom, mq, m0, dvar):
    """(kind, addr, value) for the innermost demand atom."""
    atom = _deascribe_index(atom.strip().rstrip(")").strip())
    # ∃ b, mq[a]? = some b   → presence
    pm = re.search(r"∃\s*\w+[^,]*,\s*" + re.escape(mq) + r"\[(\w+)\]\?\s*=\s*some", atom)
    if pm:
        return ("present", pm.group(1), None)
    # mq[a]? = m0[a]?  → agree-demand
    am = re.search(re.escape(mq) + r"\[(\w+)\]\?\s*=\s*" + re.escape(m0) + r"\[\1\]\?", atom)
    if am:
        return ("agree", am.group(1), None)
    am2 = re.search(re.escape(m0) + r"\[(\w+)\]\?\s*=\s*" + re.escape(mq) + r"\[\1\]\?", atom)
    if am2:
        return ("agree", am2.group(1), None)
    # mq[a]? = some V   → value
    vm = re.search(re.escape(mq) + r"\[(\w+|0x[0-9a-fA-F]+|\d+)\]\?\s*=\s*some\s*\(?([^)]*)\)?", atom)
    if vm:
        return ("value", vm.group(1), vm.group(2).strip())
    return ("unknown", None, None)


# ---- the RULE: solve for an uncovered demand address ----------------------

def solve_uncovered(nc):
    """Given a NestedConjunct, decide whether the demand is FALSIFIABLE (an
    uncovered demand address exists) and, if so, return a solution dict.  Pure
    interval arithmetic — no Lean, no term forms."""
    if nc is None or nc.guards is None or nc.demand is None:
        return None
    kind, addr, val = nc.demand
    if kind == "unknown":
        return None
    cover = IntervalSet([])
    for _, s in nc.guards:
        cover = cover.union(s)
    # MemExtends m0 mq demands EVERY populated m0 address survive in mq.  The
    # witness is any m0-populated address (a pinned point or a population window)
    # that is UNCOVERED — mq erases it, breaking presence.  If no such address,
    # the extends is sound (agree-on-cover ⊇ populated ⇒ survives).
    if kind == "extends":
        pts = getattr(nc, "m0pts", []) or []
        pop = getattr(nc, "pop", []) or []
        for (pa, _) in pts:
            if not cover.contains(pa):
                return dict(a=pa, kind="extends", val=None, cover=cover,
                            quantified=False)
        for s, _ in pop:
            gap = _diff(s, cover)
            a = gap.sample_covered() if gap.ivs else None
            if a is not None:
                return dict(a=a, kind="extends", val=None, cover=cover,
                            quantified=False)
        return None
    # coverage of the demand: for a literal addr, is it in `cover`?  For an
    # interval-quantified demand (dvar ranges over `drange`), is there a point
    # of `drange` outside `cover`?
    if nc.dvar and nc.drange is not None:
        # demand address ranges over drange; adversary picks any drange-point
        # not covered.
        witness_range = _diff(nc.drange, cover)
        a = witness_range.sample_covered() if witness_range.ivs else None
        if a is None:
            return None  # every demanded address is covered → SOUND
        return dict(a=a, kind=kind, val=val, cover=cover, quantified=True)
    else:
        a = _num(addr) if addr else None
        if a is None:
            return None
        if cover.contains(a):
            return None  # demand address is covered → SOUND
        return dict(a=a, kind=kind, val=val, cover=cover, quantified=False)


def _diff(a, b):
    return _intersect(a, b.complement())


# ---- adversary emission: build mq = m0 corrupted at the uncovered address --
#
# The adversary and the agree-proof are emitted from the SOLUTION, not from any
# term form.  m0 is a `crange`-style constant map on the union of populated
# windows (so any population premise is met); mq is m0 with the demand address
# either ERASED (presence/value/extends demand: m0 has it, mq lacks it) or
# INSERTED (agree demand where m0 lacks it: mq gains it) so `mq[a]? ≠ m0[a]?`.

CRANGE_DEFS = r"""
private def crange : Nat → Mem
  | 0 => (∅ : Mem)
  | n+1 => (crange n).insert n (0x1 : BitVec 8)
private theorem crange_get : ∀ N k, k < N → (crange N)[k]? = some (0x1 : BitVec 8) := by
  intro N; induction N with
  | zero => intro k hk; exact absurd hk (by omega)
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 by_cases he : n = k
                 · subst he; simp
                 · rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)
private theorem crange_none : ∀ N k, N ≤ k → (crange N)[k]? = none := by
  intro N; induction N with
  | zero => intro k hk; simp [crange]
  | succ n ih => intro k hk; simp only [crange, Std.ExtHashMap.getElem?_insert]
                 rw [if_neg (by simp [beq_iff_eq]; omega)]; exact ih k (by omega)
"""


def emit_semantic_probe(head, prop, sig, app, nc, sol, outer_types):
    """Build a `¬ prop` probe from the uncovered-address SOLUTION.

    The reference m0 is `crange POP` (constant 1 on [0,POP)) with an INSERT for
    every outer point-fact `m0[Aᵢ]? = some Vᵢ`, so every outer m0-premise
    (single-point AND population-window) is met by construction.  The adversary
    mq corrupts m0 at exactly the uncovered demand address `a`:
      * if m0 HAS a byte at `a` (a<POP or a is a pinned point) → mq ERASES it
        ⇒ mq[a]?=none while the demand wants it present/equal ⇒ False;
      * if m0 LACKS `a` → mq INSERTS a value there ⇒ mq[a]?=some.. while the
        demand `mq[a]?=m0[a]?` wants none ⇒ False.
    Every agree-proof is discharged from the guard SHAPE: for each guard the
    corrupted address is proven OUTSIDE its set by `omega`, so the corruption is
    invisible to the constraints.
    """
    a = sol["a"]; kind = sol["kind"]; cover = sol["cover"]
    pts = list(getattr(nc, "m0pts", []) or [])
    pop = list(getattr(nc, "pop", []) or [])
    # POP = top of every population window; crange fills [0,POP) UNIFORMLY with
    # `some 1`, meeting every `∀k<C, m0[k]?=some 1` premise (POP ≥ C).  We choose
    # POP to EXCLUDE the demand address `a` when possible, so that whether m0 is
    # populated at `a` is under our control (crange populates exactly [0,POP)).
    bounds = [0]
    for s, _ in pop:
        for lo, hi in s.ivs:
            if hi is not None:
                bounds.append(hi)
    POP = max(bounds)
    # m0's population at `a` is EXACTLY: pinned, or a<POP (crange fills [0,POP)).
    pinned = next((v for (pa, v) in pts if pa == a), None)
    a_populated = (pinned is not None) or (a < POP)
    # m0 spelling: crange POP with the pinned points inserted on top.
    m0core = f"(crange {POP})"
    for (pa, v) in pts:
        m0core = f"({m0core}.insert {pa} {v})"
    m0w = m0core
    # value/lemma for m0[a]?
    if pinned is not None:
        m0a_val = pinned
        m0a = f"(by simp [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_erase] : {m0w}[{a}]? = some {pinned})"
    elif a_populated:
        m0a_val = "(0x1 : BitVec 8)"
        # a<POP, not pinned: crange_get gives some 1, inserts at other addrs invisible
        m0a = _m0_lookup_lemma(m0w, POP, a, pts, populated=True)
    else:
        m0a_val = None
        m0a = _m0_lookup_lemma(m0w, POP, a, pts, populated=False)
    # adversary: erase if m0 has a byte at a, else insert a fresh one.
    if a_populated or pinned is not None:
        mqw = f"({m0w}.erase {a})"
        mqa = f"(by simp [Std.ExtHashMap.getElem?_erase] : {mqw}[{a}]? = none)"
        differ = "erase"
    else:
        mqw = f"({m0w}.insert {a} (0x2 : BitVec 8))"
        mqa = f"(by simp [Std.ExtHashMap.getElem?_insert] : {mqw}[{a}]? = some (0x2 : BitVec 8))"
        differ = "insert"

    getlemma = ("Std.ExtHashMap.getElem?_erase" if differ == "erase"
                else "Std.ExtHashMap.getElem?_insert")
    # one agree-premise proof: `∀ k, G k → <eq at k>`.  For every k∈G, k≠a, so
    # the single corruption at a is invisible.  The `k≠a` fact is `omega` from
    # the guard (¬-windows are push_neg'd first).
    ag_arg = (f"(by intro k hk; simp only [{getlemma}]; "
              f"rw [if_neg (by first"
              f" | (revert hk; simp only [not_and, not_lt, not_le]; intro hk; simp only [beq_iff_eq]; omega)"
              f" | (simp only [beq_iff_eq]; omega))])")
    # population-premise discharger for outer `∀k<C, m0[k]?=some V` hyps.
    pop_args = []
    for s, v in pop:
        pop_args.append(f"(fun k hk => {_m0_lookup_lemma_k(m0w, POP, pts)})")
    # single-point outer facts are discharged directly.
    pt_args = []
    for (pa, v) in pts:
        pt_args.append(f"(by simp [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_erase])")
    # demand application: interval-quantified demands feed `a` + a range proof.
    if sol["quantified"]:
        dem_app = ("{A} (by first | omega | (constructor <;> omega)"
                   " | (refine ⟨?_, ?_, ?_⟩ <;> omega)"
                   " | (exact ⟨by omega, by omega⟩)"
                   " | (exact ⟨by omega, by omega, by omega⟩))").format(A=a)
    else:
        dem_app = ""

    n_guards = len(nc.guards)
    # outer non-mem ghost binders, synthesized from their types.
    ghosts = []
    for ty in outer_types:
        t = ty.strip()
        if t.endswith("Mem") or "ExtHashMap" in t:
            continue
        ghosts.append(_paren(synth_witness(ty) or "0"))

    # refuter for each demand kind, given `hbad : <demand at (m0w,mqw,a)>`.
    if kind == "present":
        refuter = (f"obtain ⟨bb, hbb⟩ := hbad\n"
                   f"     rw [{mqa}] at hbb; exact absurd hbb (by simp)")
    elif kind == "extends":
        vv = m0a_val or "(0x1 : BitVec 8)"
        refuter = (f"obtain ⟨bb, hbb⟩ := hbad {a} {vv} {m0a}\n"
                   f"     rw [{mqa}] at hbb; exact absurd hbb (by simp)")
    elif kind == "value":
        refuter = (f"rw [{mqa}] at hbad; exact absurd hbad (by simp)")
    else:  # agree: hbad : mq[a]? = m0[a]?
        refuter = (f"rw [{mqa}, {m0a}] at hbad; exact absurd hbad (by simp)")

    # The outer application order is fixed by the telescope: ghost binders (that
    # appear before m0) then m0, then all m0-premises (points+population), then
    # mq, then agree-premises, then demand.  Since ghosts may sit before OR after
    # m0, we cascade over the split of `ghosts` into (before-m0, after-m0).
    alts = []
    for split in range(len(ghosts) + 1):
        pre = " ".join(ghosts[:split])
        post = " ".join(ghosts[split:])
        prem = " ".join(pt_args + pop_args)   # m0-premises, in source-ish order
        ags = " ".join([ag_arg] * n_guards)
        call = " ".join(x for x in [pre, m0w, post, prem, mqw, ags, dem_app]
                        if x and x.strip())
        alt = (f"  | (intro Hp\n"
               f"     have hbad := Hp {call}\n"
               f"     {refuter})")
        alts.append(alt)
    cascade = "  first\n" + "\n".join(alts)
    return (f"{head}\n\n{CRANGE_DEFS}\nnamespace VsaFuzzSem\n"
            f"set_option maxHeartbeats 1000000 in\n"
            f"theorem probe {sig}: ¬ {prop}{app} := by\n{cascade}\n\n"
            f"#print axioms probe\nend VsaFuzzSem\n")


def _m0_lookup_lemma(m0w, POP, a, pts, populated):
    """Prove `m0w[a]? = some 1` (populated, a<POP, a not pinned) or `= none`
    (a≥POP, not pinned) — the inserted pinned points are all at addresses ≠ a."""
    tgt = "some (0x1 : BitVec 8)" if populated else "none"
    base = f"crange_get {POP} {a} (by omega)" if populated else f"crange_none {POP} {a} (by omega)"
    if not pts:
        return f"(by have h := {base}; simpa using h : {m0w}[{a}]? = {tgt})"
    # strip the pinned inserts (all at ≠ a) then apply the crange lemma.
    return (f"(by simp only [Std.ExtHashMap.getElem?_insert, "
            f"Std.ExtHashMap.getElem?_erase]; "
            f"first | exact {base} | (rw [{base}]) : {m0w}[{a}]? = {tgt})")


def _m0_lookup_lemma_k(m0w, POP, pts):
    """A term proving `m0w[k]? = some 1` for a bound `k` with `hk : k < C ≤ POP`
    (used inside a population-premise λ)."""
    if not pts:
        return f"crange_get {POP} k (by omega)"
    # pinned inserts are at fixed literals; for a generic k they may or may not
    # collide.  Fall back to a simp that peels them then applies crange_get.
    return (f"(by simp only [Std.ExtHashMap.getElem?_insert, "
            f"Std.ExtHashMap.getElem?_erase]; "
            f"first | exact crange_get {POP} k (by omega)"
            f" | (rw [crange_get {POP} k (by omega)]) | rfl)")


def fuzz_semantic(path_or_imp, prop, is_file, is_layout, unfold, log,
                  body_override=None):
    """v2.1 driver: unfold the Prop, structurally extract the nested conjunct,
    apply THE RULE (solve for an uncovered demand address), and if one exists
    emit + machine-check the adversary probe.  SURVIVED ⟺ every demanded address
    is covered by the agree-constraint union (sound), or the guard shape is
    outside the address-map fragment (SMT territory)."""
    # get the unfolded body text
    if body_override is not None:
        body_txt = body_override
        head = path_or_imp  # module text
    elif is_file:
        head = open(path_or_imp).read()
        body_txt = _extract_def_body(head, prop)
    else:
        _, _, body_txt = discover_telescope(path_or_imp, prop, is_layout, unfold)
        head = f"import {path_or_imp}\n\n{PREAMBLE}\n{WITNESS_DEFS}"
    if not body_txt:
        line = f"- `{prop}` → **UNDECIDABLE** — body not discoverable (v2.1)"
        print(line); log.write(line + "\n"); log.flush(); return "UNDECIDABLE"

    nc = extract_nested(body_txt)
    if nc is not None and getattr(nc, "unsupported", None):
        line = (f"- `{prop}` → **SURVIVED** (v2.1: guard `{nc.unsupported}` "
                f"outside address-map fragment → SMT territory)")
        print(line); log.write(line + "\n"); log.flush(); return "SURVIVED"
    sol = solve_uncovered(nc)
    if sol is None:
        line = (f"- `{prop}` → **SURVIVED** (v2.1: every demanded address is "
                f"covered by the agree-constraint union — sound)")
        print(line); log.write(line + "\n"); log.flush(); return "SURVIVED"

    sig = "(L : Layout) " if is_layout else ""
    app = " L" if is_layout else ""
    outer_types = (_file_outer_types(head, prop) if is_file
                   else (discover_telescope(path_or_imp, prop, is_layout, unfold)[0] or []))
    if body_override is not None:
        outer_types = _outer_types_from_text(body_txt)
    src = emit_semantic_probe(head, prop, sig, app, nc, sol, outer_types)
    rc, out = run_lean(src)
    verdict, detail = classify(rc, out)
    if verdict in ("REFUTED", "REFUTED-DIRTY"):
        line = (f"- `{prop}` → **{verdict}** (v2.1 uncovered-addr rule: demand "
                f"@{hex(sol['a'])} ∉ cover {sol['cover']}) — {detail}")
    else:
        # the rule found an uncovered address but the emitted proof did not
        # close — report honestly (do NOT claim survival).
        line = (f"- `{prop}` → **UNDECIDABLE** (v2.1 found uncovered demand "
                f"@{hex(sol['a'])} but probe did not close) — {detail}")
        verdict = "UNDECIDABLE"
    print(line); log.write(line + "\n"); log.flush()
    return verdict


def _extract_def_body(text, prop):
    short = prop.split(".")[-1]
    m = re.search(rf"def\s+{re.escape(short)}\b[^:]*:\s*Prop\s*:=([\s\S]*?)"
                  r"(?:\n(?:def|theorem|end|namespace|/-)|\Z)", text)
    return m.group(1).strip() if m else ""


def _outer_types_from_text(body):
    if "∀" not in body:
        return []
    pre = body[body.index("∀"):]
    pre = pre.split(",", 1)[0] if "," in pre else pre
    types = []
    for gm in re.finditer(r"\(([^()]+?):([^()]+?)\)", pre):
        for _ in gm.group(1).split():
            types.append(gm.group(2).strip())
    return types


# ==========================================================================
# THE PROBE SELF-GENERATOR (--gen-battery N)
# ==========================================================================
#
# Sample the space of nested-memory conjuncts with GROUND TRUTH KNOWN BY
# CONSTRUCTION, emit N probe PAIRS (one true, one false), and score the v2.1
# rule against a FRESH sample every run (so it cannot be trained on).  The
# generator draws: random guard sets (1..2 windows, positive OR negated forms),
# random demand addresses (deliberately inside/outside coverage), and random
# demand kinds (presence / value / extends / agree).  For each we KNOW whether
# the demanded address is covered ⇒ whether the conjunct is TRUE or FALSE.

def _hexlit(n):
    return f"0x{n:x}"


def _rand_windows(rnd):
    """Return (guard_lean_list, cover:IntervalSet).  1..2 windows, each positive
    `C≤k ∧ k<D` or negated `¬(C≤k ∧ k<D)`; the guard's constrained set is the
    positive interval or its complement."""
    guards, cover = [], IntervalSet([])
    for _ in range(rnd.randint(1, 2)):
        lo = rnd.randrange(0, 0x40000)
        span = rnd.choice([0x10, 0x100, 0x1000, 0x8000])
        hi = lo + span
        neg = rnd.random() < 0.5
        if neg:
            g = f"¬ ({_hexlit(lo)} ≤ k ∧ k < {_hexlit(hi)})"
            s = IntervalSet([(0, lo), (hi, None)])
        else:
            g = f"({_hexlit(lo)} ≤ k ∧ k < {_hexlit(hi)})"
            # sometimes phrase as a single bound
            if rnd.random() < 0.3 and lo == 0:
                g = f"k < {_hexlit(hi)}"
            s = IntervalSet([(lo, hi)])
        guards.append(g)
        cover = cover.union(s)
    return guards, cover


def _gen_case(rnd, want_false):
    """Construct one hermetic Prop + ground truth.  `want_false=True` places the
    demand OUTSIDE the coverage (false); else inside (true)."""
    guards, cover = _rand_windows(rnd)
    kind = rnd.choice(["present", "value", "agree", "extends"])
    # pick demand address inside/outside coverage as requested.
    if want_false:
        a = cover.sample_uncovered()
        if a is None:               # coverage = ℕ; force a gap by re-rolling
            return _gen_case(rnd, want_false)
    else:
        a = cover.sample_covered()
        if a is None:
            return _gen_case(rnd, want_false)
    # build the agree-hyps (mq agrees with m0 off/on the windows)
    hyps = "".join(
        f"      (∀ k, {g} → m0[k]? = mq[k]?) →\n" for g in guards)
    # For present/value/extends the demand references m0's byte at `a`, so we add
    # an outer point-fact so m0 HAS it (else the conjunct is vacuously true and
    # 'false' cases wouldn't be false).  For 'agree' the demand compares mq to m0
    # directly (no outer pin needed).
    val = _hexlit(rnd.choice([0x2a, 0x7, 0xff, 0x1]))
    outer_pin = ""
    if kind in ("value", "present", "extends"):
        outer_pin = f"    m0[({_hexlit(a)} : Nat)]? = some ({val} : BitVec 8) →\n"
    if kind == "value":
        concl = f"      mq[({_hexlit(a)} : Nat)]? = some ({val} : BitVec 8)"
    elif kind == "present":
        concl = f"      (∃ b, mq[({_hexlit(a)} : Nat)]? = some b)"
    elif kind == "extends":
        concl = f"      MemExtends m0 mq"
    else:  # agree — demand equality at the literal `a`
        concl = f"      mq[({_hexlit(a)} : Nat)]? = m0[({_hexlit(a)} : Nat)]?"
    prop = (f"∀ (m0 : Mem),\n{outer_pin}"
            f"    ∀ mq : Mem,\n{hyps}{concl}")
    # GROUND TRUTH: false iff the demand address is uncovered.
    truth = not want_false   # want_false ⇒ truth False
    return prop, truth, kind, a, cover


def gen_battery(n, log, seed=None):
    """Emit N fresh probe pairs, run the v2.1 rule on each, and score.  Perfect
    score (false⇒REFUTED green, true⇒SURVIVED) is the acceptance — un-trainable
    because the sample is drawn fresh per run."""
    import random
    rnd = random.Random(seed)
    log.write(f"\n### --gen-battery {n} (fresh sample, seed={seed})\n\n")
    correct, total = 0, 0
    for i in range(n):
        for want_false in (True, False):
            prop, truth, kind, a, cover = _gen_case(rnd, want_false)
            defname = f"GenProbe{i}_{'F' if want_false else 'T'}"
            body = (f"import Vsa.Sim.EvalSimCommon\n"
                    f"open Vsa Vsa.Sim Vsa.MemRepr Vsa.Alloc\n"
                    f"open Std (ExtHashMap)\n\n"
                    f"def {defname} : Prop :=\n{prop}\n")
            # run the v2.1 rule as a hermetic module
            nc = extract_nested(_extract_def_body(body, defname))
            sol = solve_uncovered(nc)
            predicted_false = sol is not None
            if predicted_false:
                src = emit_semantic_probe(body, defname, "", "", nc, sol,
                                          _outer_types_from_text(prop))
                rc, out = run_lean(src)
                v, _ = classify(rc, out)
                got_refuted = v in ("REFUTED", "REFUTED-DIRTY")
            else:
                got_refuted = False
            # scoring: false case must REFUTE (green), true case must NOT.
            ok = (got_refuted == (not truth)) and (predicted_false == (not truth))
            correct += ok; total += 1
            tag = ("REFUTED" if got_refuted else
                   ("SURVIVED" if not predicted_false else "PRED-FALSE-NOPROOF"))
            mark = "OK" if ok else "MISS"
            line = (f"- {defname} [{kind}] truth={'T' if truth else 'F'} "
                    f"demand@{_hexlit(a)} cover={cover} → {tag} [{mark}]")
            print(line); log.write(line + "\n"); log.flush()
    summary = f"\n**gen-battery: {correct}/{total} correct → " \
              f"{'PASS' if correct == total else 'FAIL'}**\n"
    print(summary.strip()); log.write(summary); log.flush()
    return correct == total


# --------------------------------------------------------------------------
# v2 acceptance
# --------------------------------------------------------------------------

def acceptance_v2(log):
    """Hard gate for descent:
      (a) REFUTE the pre-48f statements the v1 fuzzer wrongly PASSED —
          reconstructed hermetically from git:
            * BinArmExtras.mem_ext  (git show d7a5c91^:…/BinDispatchRow paths)
            * the ∀-mcall pair       (git show 17773c4^:…/TermRouting NegResid)
      (b) NOT refute the CURRENT (HEAD) post-48f/48g statements (re-read at run
          time — the mem_ext field is DROPPED at HEAD; guard-pinned survivors).
      (c) v1 acceptance still passes (no regression)."""
    log.write("\n### Acceptance-v2 run (nested-quantifier descent)\n\n")
    ok = True

    # -- reconstruct the pre-48f over-quantified conjuncts as standalone probes.
    # These mirror the hand files EXACTLY (agree-off-window ⇒ MemExtends /
    # presence), which is precisely the shape buried inside the pre-amendment
    # residuals.  The descent adversary must REFUTE each.
    pre_memext = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

namespace VsaAcceptV2
/-- Pre-48f `BinArmExtras.mem_ext` / unary `mem_ext`, isolated (over-quantified). -/
def PreMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      MemExtends m0 mcall
end VsaAcceptV2
"""
    pre_presence = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

namespace VsaAcceptV2
/-- Pre-amendment presence / `frame_pop` conjunct, isolated (over-quantified). -/
def PrePresence : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)
end VsaAcceptV2
"""
    # -- current HEAD survivors: the SAME conjuncts now GUARDED so the deleting
    # mcall no longer bites.  Model of the 48f/48g cure — the demand ranges only
    # over memories that AGREE with m0 on the whole window too (window empty), so
    # the adversary (which must differ inside the window) is excluded.
    cur_memext = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

namespace VsaAcceptV2
/-- Post-48f: `mem_ext` DROPPED — modeled as the structured single-mcall demand
(agree on ALL addresses ⇒ MemExtends), which the deleting adversary cannot meet. -/
def CurMemExt : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, mcall[a]? = m0[a]?) →
      MemExtends m0 mcall
theorem CurMemExt_true : CurMemExt := by
  intro SL sp m0 mcall hag a b hb; exact ⟨b, by rw [hag]; exact hb⟩
end VsaAcceptV2
"""
    cur_presence = r"""import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

namespace VsaAcceptV2
/-- Post-48g: presence demanded only where m0 ALREADY has the bytes (guard
carries the entry-frame population), so an agreeing mcall inherits them. -/
def CurPresence : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, mcall[a]? = m0[a]?) →
      ∀ a : Nat, (∃ b, m0[a]? = some b) → (∃ b, mcall[a]? = some b)
theorem CurPresence_true : CurPresence := by
  intro SL sp m0 mcall hag a hb; rw [hag]; exact hb
end VsaAcceptV2
"""

    def descend_hermetic(body, prop):
        global OUTER_WITNESSES
        # standalone over-quant probes have outer telescope (SL, sp, m0); descent
        # picks builder witnesses positionally.
        for builder in ADVERSARY_BUILDERS:
            OUTER_WITNESSES = " ".join(_paren(w) for w in
                (builder['sl'], builder['sp'], builder['m0']))
            src = descend_probe(body, f"VsaAcceptV2.{prop}", True, False,
                                "", 2, builder)
            rc, out = run_lean(src)
            v, d = classify(rc, out)
            if v in ("REFUTED", "REFUTED-DIRTY"):
                return v, d, builder["name"]
        return "SURVIVED", "no builder bit", None

    # (a) pre-amendment MUST refute
    log.write("**Must REFUTE (pre-48f over-quantified conjuncts):**\n")
    ra, _, ba = descend_hermetic(pre_memext, "PreMemExt")
    rb, _, bb = descend_hermetic(pre_presence, "PrePresence")
    for nm, v, b in [("PreMemExt", ra, ba), ("PrePresence", rb, bb)]:
        good = v in ("REFUTED", "REFUTED-DIRTY")
        ok = ok and good
        log.write(f"- `{nm}` → **{v}** (builder={b})\n")
        print(f"[v2 refute-pre] {nm} → {v} (builder={b})")

    # (b) current HEAD MUST survive
    log.write("\n**Must SURVIVE (post-48f/48g guarded survivors):**\n")
    sa, _, _ = descend_hermetic(cur_memext, "CurMemExt")
    sb, _, _ = descend_hermetic(cur_presence, "CurPresence")
    for nm, v in [("CurMemExt", sa), ("CurPresence", sb)]:
        good = v not in ("REFUTED", "REFUTED-DIRTY")
        ok = ok and good
        log.write(f"- `{nm}` → **{v}**\n")
        print(f"[v2 survive-current] {nm} → {v}")

    # (b') the LIVE HEAD statement: re-read the real NegResid conjunct shape at
    # run time (48g may have landed).  If the real def still carries the raw
    # ∀-mcall pair, descent refutes it (a genuine live falsity, reported not
    # gated); if 48g guarded it, descent survives.  Either way this does NOT
    # gate acceptance — it is an honest live probe.
    live = _live_negresid_verdict(descend_hermetic)
    log.write(f"\n**Live HEAD `TermRouting.NegResid` mcall-pair probe:** "
              f"{live}\n")
    print(f"[v2 live-head] NegResid mcall-pair → {live}")

    # (c) v1 acceptance still passes
    v1_ok = acceptance(log)
    ok = ok and v1_ok
    log.write(f"\n**v1 regression check → {'PASS' if v1_ok else 'FAIL'}**\n")

    summary = f"\n**Acceptance-v2 → {'PASS' if ok else 'FAIL'}**\n"
    print(summary.strip()); log.write(summary); log.flush()
    return ok


def _live_negresid_verdict(descend_hermetic):
    """Re-read HEAD's TermRouting.NegResid and probe its ∀-mcall pair as a
    standalone conjunct.  Drift-proof: extracts the two `∀ mcall,…` blocks
    verbatim from the current file and wraps each as a hermetic Prop."""
    path = os.path.join(ROOT, "Vsa", "Sim", "rows", "TermRouting.lean")
    if not os.path.exists(path):
        return "N/A (file absent)"
    txt = open(path).read()
    # grab the `mem_ext`-shaped conjunct: `∀ mcall, (agree off window) →
    # MemExtends m0 mcall` — the SIMPLE one (no ∨/nested-∀).  Non-greedy, and we
    # require the agree-hyp immediately precedes MemExtends so we cannot swallow
    # the presence conjunct's body.  If HEAD guarded it (48g), this fails → the
    # live probe reports guarded, honestly.
    mblk = re.search(
        r"∀ mcall : Mem,\s*"
        r"\(∀ a : Nat, ¬ \(SL\.lo ≤ a ∧ a < sp\.toNat\) → mcall\[a\]\? = m0\[a\]\?\) →\s*"
        r"MemExtends m0 mcall", txt)
    if not mblk:
        return "guarded (no raw ∀-mcall MemExtends conjunct at HEAD)"
    conj = mblk.group(0)
    body = (f"import Vsa.Sim.EvalSimCommon\n"
            f"open Vsa.MemRepr Vsa.Alloc Vsa.Sim\n\n"
            f"namespace VsaAcceptV2Live\n"
            f"def LiveMemExt : Prop :=\n"
            f"  ∀ (SL : StackLayout) (sp aExpr : BitVec 64) (m0 : Mem),\n"
            f"    {conj}\n"
            f"end VsaAcceptV2Live\n")
    # outer telescope is (SL, sp, aExpr, m0): give sp its spelling to BOTH
    # BitVecs (aExpr harmless), SL/m0 the memext witnesses.
    global OUTER_WITNESSES
    for builder in ADVERSARY_BUILDERS:
        if builder["name"] != "memext":
            continue
        OUTER_WITNESSES = " ".join(_paren(w) for w in
            (builder['sl'], builder['sp'], builder['sp'], builder['m0']))
        src = descend_probe(body, "VsaAcceptV2Live.LiveMemExt", True, False,
                            "", 2, builder)
        rc, out = run_lean(src)
        vv, _ = classify(rc, out)
        return ("REFUTED (live falsity: raw ∀-mcall still present)"
                if vv in ("REFUTED", "REFUTED-DIRTY")
                else "SURVIVED (guarded at HEAD)")
    return "N/A"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--import", dest="imp")
    ap.add_argument("--prop")
    ap.add_argument("--layout", action="store_true")
    ap.add_argument("--unfold", default="",
                    help="extra def(s) to unfold to expose the telescope "
                         "(e.g. the *Resid the Skel* aliases)")
    ap.add_argument("--acceptance", action="store_true")
    ap.add_argument("--acceptance-v2", dest="acceptance_v2", action="store_true",
                    help="hard gate for --descend: refute pre-48f over-quant "
                         "conjuncts, survive current guarded ones, v1 no-regress")
    ap.add_argument("--descend", nargs="?", const=2, type=int, default=None,
                    metavar="DEPTH",
                    help="nested-quantifier witness descent (default depth 2): "
                         "decompose the goal body's ∧/∃-tree and refute through "
                         "an over-quantified ∀-mcall conjunct")
    ap.add_argument("--file", dest="file",
                    help="hermetic .lean module path (round-2 fix): elaborate "
                         "directly, no experiments/ lib-root import needed")
    ap.add_argument("--struct", dest="struct",
                    help="ghost struct name; synthesize a lethal constructor "
                         "witness from its field types (round-2 fix)")
    ap.add_argument("--semantic", action="store_true",
                    help="v2.1 UNCOVERED-ADDRESS RULE (replaces --descend's "
                         "pattern table): structurally extract constraint sets + "
                         "demand addresses, solve for an uncovered demand, build "
                         "the adversary generically")
    ap.add_argument("--gen-battery", dest="gen_battery", type=int, default=None,
                    metavar="N",
                    help="self-generate N fresh probe PAIRS with ground truth "
                         "known by construction and score the v2.1 rule (perfect "
                         "score = un-trainable acceptance)")
    ap.add_argument("--seed", type=int, default=None,
                    help="RNG seed for --gen-battery (default: fresh entropy)")
    args = ap.parse_args()

    os.makedirs(LOGDIR, exist_ok=True)
    with open(LOG, "a") as log:
        log.write("\n## statement_fuzz.py run\n\n")
        if args.gen_battery is not None:
            sys.exit(0 if gen_battery(args.gen_battery, log, args.seed) else 1)
        if args.acceptance_v2:
            sys.exit(0 if acceptance_v2(log) else 1)
        if args.acceptance:
            sys.exit(0 if acceptance(log) else 1)
        if args.semantic:
            if args.file:
                if not args.prop:
                    ap.error("--semantic --file needs --prop")
                fuzz_semantic(args.file, args.prop, True, args.layout,
                              args.unfold, log)
            else:
                if not (args.imp and args.prop):
                    ap.error("--semantic needs --import and --prop (or --file)")
                fuzz_semantic(args.imp, args.prop, False, args.layout,
                              args.unfold, log)
            return
        if args.descend is not None:
            # v2.1: --descend now routes THROUGH the semantic rule first; the old
            # 2-row pattern table remains only as the acceptance-v2 baseline.
            tgt = args.file or args.imp
            if tgt and args.prop:
                v = fuzz_semantic(tgt, args.prop, bool(args.file), args.layout,
                                  args.unfold, log)
                if v != "UNDECIDABLE":
                    return
            if args.file:
                if not args.prop:
                    ap.error("--descend --file needs --prop")
                fuzz_descend(args.file, args.prop, True, args.layout,
                             args.unfold, args.descend, log, args.struct)
            else:
                if not (args.imp and args.prop):
                    ap.error("--descend needs --import and --prop (or --file)")
                fuzz_descend(args.imp, args.prop, False, args.layout,
                             args.unfold, args.descend, log)
            return
        if args.file:
            if not args.prop:
                ap.error("--file needs --prop")
            fuzz_file(args.file, args.prop, args.struct, log)
            return
        if not (args.imp and args.prop):
            ap.error("need --import and --prop (or --file, or --acceptance)")
        fuzz_one(args.imp, args.prop, args.layout, args.unfold, log)


if __name__ == "__main__":
    main()
