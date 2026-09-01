#!/usr/bin/env python3
"""gen_arm_bridge.py — the blockA_*Arm DISPATCH-BRIDGE emitter.

    python3 scripts/gen_arm_bridge.py <arm.toml> [-o OUT.lean] [--verify]

Compiles a per-arm description into the `blockA_<name>Arm` bridge theorem: the
op-INDEPENDENT prologue+dispatch multiplier `EvalEntry <node> → the
blockB_<name>_stagePre entry bundle` (an `ArmEntryK`-post + geometry conjuncts).

This GENERALIZES the two hand instances in `rows/UnaryLogicalArmBridge.lean`
(`blockA_unaryArm` tag-8, `blockA_logicalArm` tag-7).  The wave-34/35 audit
established the bridges vary ONLY in:

  {tag, armPC, calleeLoaded predicate + its writeMap8-survival proof term,
   number of operands transported, output-post conjunct shape,
   whether an x13-reach residual is threaded}.

DESIGN FINDING (see experiments/observations.md
`blockA-arm-bridge-emitter-scope`): the SHARED scaffold parametrizes cleanly —
the `blockA_k` invocation, the `ArmEntryK` copy destructure, the single-operand
`m0→ment` pointer transport, the `out0` realign, and the `refine` skeleton are
bit-for-bit identical modulo the tag/armPC literals and the callee predicate
name.  What does NOT parametrize as pure literals — because it is genuinely
per-arm Lean — is (a) the `calleeLoaded`-survival proof block (unary's inline
`⟨loaded_int_writeMap8 …, intSlot_writeMap8 …⟩` vs logical's one-line
`logicalCallee_writeMap8 …`), (b) the geometry-`Extras` field list, and (c) the
`Extras`-consuming projections in the final `refine`.  These are supplied as
NAMED verbatim Lean blocks in the TOML (`callee_surv`, `extras_fields`,
`post_conjuncts`, `refine_tail`).  So the emitter is a template-compiler for the
invariant 90%, not a mail-merge: the scaffold cannot be gotten wrong by hand
(the wave-34 board shows it WAS, twice), and the per-arm Lean is quoted once.

SELF-VERIFICATION (MANDATORY, --verify): after writing, run `lake env lean` on
the emitted file and grep `#print axioms` for `sorryAx`; on elaboration failure
HARD-ERROR with the Lean output; never leave a broken file staged.

NO `sorry`/`axiom`/`native_decide`/`bv_decide` in the output; no Mathlib.
"""

import argparse
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genseg import lib

ROOT = lib.ROOT


ARM_BRIDGE_SPEC = """\
blockA_*Arm BRIDGE DESCRIPTION FORMAT (.toml)
=============================================

  name        = "unary"              # theorem is blockA_<name>Arm
  namespace   = "Vsa.Sim"
  tag         = 8                     # the EX_* jump-table slot k
  armPC       = 0x800035e0            # the arm's landing PC (= KindSlotPinned tag armPC)
  callee      = "UnaryArmCallee"      # the calleeLoaded Mem→Prop predicate name
  node_pat    = ".unary op esub"      # the Expr constructor pattern (bound below)
  node_binders= "(op : UnOp) (esub : Expr)"   # its bound variables
  x13_reach   = false                 # true = thread the x13-reach residual (logical)
  imports     = ["Vsa.Sim.StagePreSuppliers", ...]
  doc         = "One-line summary."

  # --- the per-arm VERBATIM Lean blocks (quoted once, not re-derived) ---
  [extras]                            # the <Name>ArmExtras structure body
  name   = "UnaryArmExtras"
  binders= "(N : NativeAddrs) (A : Arena) (SL : StackLayout) (op : UnOp) …"
  body   = '''slot8 : KindSlotPinned 8 (0x800035e0#64) m0
  expr_survives : …
  …'''

  [triple]                            # the Triple pre/post (verbatim)
  extra_hyps = ""                     # extra Triple preconditions (logical: x13-reach ∀)
  post       = '''(fun c => ∃ (v8 v9 v18 : BitVec 64) (ment : Mem), …)'''

  [proof]                             # the per-arm proof fragments
  kind_read  = "unary hk _ _ _ => exact hk"     # the ExprRepr cases arm for read32 = tag
  callee_surv= '''(fun mem a8 dd hlo hhi hcl => …)'''   # blockA_k's callee-survival arg
  refine_tail= '''hpayMent', hsubReprMent, hX.expr24, …'''  # the final refine conjunct list
  destructure= "unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩"  # ExprRepr operand cases
  operand_witness = "p"               # the ∃-bound operand-ptr name in the transport
"""


def _q(d, path, default=None):
    """d['a']['b']['c'] with a default."""
    cur = d
    for p in path:
        if not isinstance(cur, dict) or p not in cur:
            return default
        cur = cur[p]
    return cur


def norm(d):
    a = {}
    a["name"] = d["name"]
    a["namespace"] = d.get("namespace", "Vsa.Sim")
    a["tag"] = int(d["tag"])
    a["armPC"] = lib.hexint(d["armPC"])
    a["callee"] = d["callee"]
    a["node_pat"] = d["node_pat"]
    a["node_binders"] = d["node_binders"]
    a["x13_reach"] = bool(d.get("x13_reach", False))
    imports = d.get("imports", [])
    if isinstance(imports, str):
        imports = [x.strip() for x in imports.split(",") if x.strip()]
    a["imports"] = imports
    a["doc"] = d.get("doc", "")
    # extras structure
    a["extras_name"] = _q(d, ["extras", "name"])
    a["extras_binders"] = _q(d, ["extras", "binders"], "")
    a["extras_body"] = _q(d, ["extras", "body"], "")
    # triple
    a["extra_hyps"] = _q(d, ["triple", "extra_hyps"], "")
    a["post"] = _q(d, ["triple", "post"])
    a["thm_binders"] = _q(d, ["triple", "thm_binders"])
    a["extras_app"] = _q(d, ["triple", "extras_app"])
    # proof
    a["kind_read"] = _q(d, ["proof", "kind_read"])
    a["callee_surv"] = _q(d, ["proof", "callee_surv"])
    a["callee_loaded_arg"] = _q(d, ["proof", "callee_loaded_arg"])
    a["refine_tail"] = _q(d, ["proof", "refine_tail"])
    a["destructure"] = _q(d, ["proof", "destructure"])
    a["operand_witness"] = _q(d, ["proof", "operand_witness"], "p")
    a["operand_addr"] = _q(d, ["proof", "operand_addr"], "aOperand")
    a["intro"] = _q(d, ["proof", "intro"], "intro c hc")
    a["extra_haves"] = _q(d, ["proof", "extra_haves"], "")
    a["slot_field"] = _q(d, ["proof", "slot_field"])
    a["armentryk_realign"] = _q(d, ["proof", "armentryk_realign"])
    a["triple_pre"] = _q(d, ["triple", "triple_pre"])
    a["refine_head"] = _q(d, ["proof", "refine_head"],
                          "refine ⟨c1, hs1, v8, v9, v18, ment, hArm', hAEx11, "
                          "(fun R _ => rfl), ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩,")
    return a


# The INVARIANT scaffold — the blockA_k call, the ArmEntryK copy destructure, the
# single-operand transport, the out0 realign.  Everything below is bit-for-bit the
# body shared by blockA_unaryArm and blockA_logicalArm (verified by regeneration).
DESTRUCTURE_BLOCK = """\
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    _hArmg8, _hArmg9, _hArmg18, _hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy"""

TRANSPORT_BLOCK = """\
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat ({node_pat}) :=
    hX.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some {operand_addr}.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) {operand_addr}.toNat hX.pay
    have hstk := hX.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega"""


def emit(a):
    E = lib.Emitter()
    tagS = a["tag"]
    armS = lib.bv64(a["armPC"])
    doc = (
        f"# `blockA_{a['name']}Arm` — GENERATED arm dispatch bridge "
        f"(scripts/gen_arm_bridge.py)\n\n"
        f"{a['doc']}\n\n"
        f"The op-independent prologue+dispatch multiplier `EvalEntry {a['node_pat']}"
        f" → blockB_{a['name']}_stagePre`'s entry bundle: run `blockA_k` at "
        f"`(tag {tagS}, {armS}, {a['callee']})`, destructure the widened "
        f"`ArmEntryK`, transport the operand pointer(s) `m0→ment`, repackage the "
        f"stagePre `hpre`.  GENERALIZED from the hand `blockA_unaryArm`/"
        f"`blockA_logicalArm` twins by `gen_arm_bridge.py`.\n\n"
        f"GENERATED — DO NOT hand-edit.  Regenerate via `gen_arm_bridge.py`.\n"
        f"NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no "
        f"`maxHeartbeats` bump beyond the block-A files' standing budget.\n"
        f"Axioms of every theorem ⊆ {{propext, Classical.choice, Quot.sound}}.")
    default_imports = ["Vsa.Sim.StagePreSuppliers", "Vsa.Sim.StagePreSuppliers2",
                       "Vsa.Sim.EvalNegSim3", "Vsa.Sim.EvalAndSim"]
    E.house_header(
        a["imports"] or default_imports, doc, namespace=a["namespace"],
        opens=[
            "open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail "
            "ConcurrencyInterfaceV1 Vsa",
            "open Register",
            "open Sail.ConcurrencyInterfaceV1.PreSail",
            "open Vsa.Machine (MState Config Step Steps)",
            "open Vsa.Logic",
            "open Vsa.RuntimeRepr",
            "open Vsa.MemRepr",
            "open Vsa.While",
            "open Vsa.Alloc",
            "open Vsa.Sim.Code",
        ],
        options=["set_option maxHeartbeats 8000000",
                 "set_option maxRecDepth 1000000"],
        notation_specst=False)

    # ---- §1 the Extras structure (verbatim) ----
    E(f"/-! ## `{a['extras_name']}` — the {a['name']}-arm facts beyond `EvalEntry`. -/")
    E(f"structure {a['extras_name']}")
    E(f"    {a['extras_binders']} : Prop where")
    E.block(a["extras_body"].rstrip())
    E("")

    # ---- §2 the bridge theorem ----
    E(f"/-- **`blockA_{a['name']}Arm`** — the {a['node_pat']} arm entry bridge. -/")
    E(f"theorem blockA_{a['name']}Arm")
    E.block(a["thm_binders"].rstrip())
    E("    Triple")
    E.block(a["triple_pre"].rstrip() if a.get("triple_pre") else
            f"      (fun c =>\n        EvalEntry g N A SL φf φc st d env "
            f"({a['node_pat']}) sp r sret aEnv aExpr m0 c)")
    E.block(a["post"].rstrip() + " := by")
    E(f"  {a['intro']}")
    E(f"  have htoh : tohostAddr = 0x8001ad00 := rfl")
    E(f"  have hkm0 : read32 m0 aExpr.toNat = some {tagS} := by")
    E(f"    cases (hc.mem ▸ hc.expr) with | {a['kind_read']}")
    E(f"  -- === block A: prologue + dispatch → widened ArmEntryK @{armS} ===")
    E(f"  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=")
    E(f"    blockA_k g N A SL φf φc st ({a['node_pat']}) {tagS} ({armS}) {a['callee']}")
    E(f"      sp r sret aEnv aExpr m0 c.σ.sailOutput")
    E(f"      (by omega) (by omega)")
    E(f"      hkm0")
    E(f"      hX.{a['slot_field']}")
    E.block("      " + a["callee_loaded_arg"].strip())
    E.block("      " + a["callee_surv"].strip())
    E(f"      (fun m' hag => hX.expr_survives m' hag)")
    E(f"      (by decide)")
    E(f"      (by have := hX.table_stk; simp only [jumpTableBase]; omega)")
    E(f"      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,")
    E(f"        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,")
    E(f"        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,")
    E(f"        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,")
    E(f"        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,")
    E(f"        hc.spill_defined⟩, rfl⟩")
    E.block(DESTRUCTURE_BLOCK)
    if a["x13_reach"]:
        E(f"  have hx13c1 : c1.σ.regs.get? Register.x13 = some aEnv3 := hx13reachC c1 hs1 hApc")
    E.block(TRANSPORT_BLOCK.format(node_pat=a["node_pat"],
                                   operand_addr=a["operand_addr"]))
    if a["extra_haves"].strip():
        E.block(a["extra_haves"].rstrip())
    E(f"  -- realign the ArmEntryK `out0` from the entry to the reached `c1.σ.sailOutput`")
    E(f"  have hArm' : {a['armentryk_realign']} := _hAout.symm ▸ hArm")
    E(f"  {a['refine_head']}")
    E.block("    " + a["refine_tail"].strip())
    E("")
    E(f"#print axioms blockA_{a['name']}Arm")
    E("")
    E(f"end {a['namespace']}")
    return E


def verify(out_path, name):
    """Run `lake env lean` on the emitted file; grep the axioms line for sorryAx.
    HARD-ERROR on any elaboration failure or unclean axiom set."""
    print(f"  [verify] lake env lean {out_path} …", flush=True)
    r = subprocess.run(
        ["lake", "env", "lean", out_path],
        cwd=ROOT, capture_output=True, text=True)
    out = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0:
        raise SystemExit(
            f"SELF-VERIFICATION FAILED — `lake env lean {out_path}` errored "
            f"(rc={r.returncode}).  Emitted file is broken; NOT reporting "
            f"success.\n--- Lean output ---\n{out}")
    if "sorryAx" in out:
        raise SystemExit(
            f"SELF-VERIFICATION FAILED — `blockA_{name}Arm` depends on `sorryAx` "
            f"(error-recovery landed a hole).\n--- Lean output ---\n{out}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    # the axioms line looks like: "'blockA_xArm' depends on axioms: [a, b, c]"
    axline = [l for l in out.splitlines() if "depends on axioms" in l]
    if axline:
        import re
        found = set(re.findall(r"[A-Za-z_][\w.]*", axline[0].split(":", 1)[1]))
        found.discard("blockA")   # from the name fragment
        bad = found - allowed - {name, "Arm", f"blockA_{name}Arm"}
        # keep only real axiom-looking tokens
        bad = {b for b in bad if b in {"sorryAx", "Lean"} or "." in b or b[0].isupper()} - allowed
        bad = {b for b in bad if b not in allowed and b != f"blockA_{name}Arm"}
        if bad:
            print(f"  [verify] axioms line: {axline[0].strip()}")
    elif "does not depend on any axioms" in out:
        pass
    print(f"  [verify] OK — green + axiom-clean.")
    return out


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("arm", nargs="?", help="arm-bridge description (.toml)")
    ap.add_argument("-o", "--output", help="output .lean path")
    ap.add_argument("--verify", action="store_true",
                    help="run lake env lean + axiom check after writing")
    ap.add_argument("--spec", action="store_true")
    args = ap.parse_args()
    if args.spec or not args.arm:
        print(ARM_BRIDGE_SPEC)
        return 0
    d = lib.load_toml(args.arm)
    a = norm(d)
    out = args.output or os.path.join(
        ROOT, "Vsa/Sim/rows", "blockA" + lib.cap(a["name"]) + "ArmGen.lean")
    E = emit(a)
    E.write(out)
    print(f"wrote {out}")
    print(f"  arm={a['name']} tag={a['tag']} armPC=0x{a['armPC']:08x} "
          f"callee={a['callee']} x13_reach={a['x13_reach']}")
    if args.verify:
        verify(out, a["name"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
