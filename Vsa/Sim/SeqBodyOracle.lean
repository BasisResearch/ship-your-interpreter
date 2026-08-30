import Vsa.Sim.ReprStackSurvival
import Vsa.Sim.ExecBlock2

/-!
# Layer-4 — the seq loop-body oracle's AST-repr seam (the shared-gap application)

`execBlockStep` (`ExecBlock2.lean`) is CONDITIONAL on `hbody` — the compiled
do-while body chain `setup ≫ jal exec_stmt [ExecIH] ≫ status-dispatch ≫
back-edge`. The FIRST step of that chain (`execBlockIter`) runs the seven setup
instructions ending in `sd i, 8(sp)` (the loop counter spill) and then invokes
`armExec_rec` (`ExecBlock.lean:185`) for the recursive `jal exec_stmt`.

`armExec_rec`'s precondition (`ExecBlock.lean:224`) demands
`StmtRepr mcall aStmtSub.toNat sSub` — the current statement's AST representation
in the CALL memory `mcall`, which is the loop-head memory `m0` AFTER the `sd i`
spill. The spill lands at `sp - 168 ∈ [SL.lo, sp)` (inside the stack window), so
the AST — living in the read-only script region, disjoint from the stack — must
SURVIVE the spill. That transport is the SINGLE gap the loop-fan-out flagged as
gating all four body oracles (seq/while/for/args), stated abstractly as the
recurring `exprRepr_agreeP`/`stmtRepr_agreeP` residual.

This file closes it for the SEQ shape (the exemplar): `blockIter_stmtRepr_ready`
applies `ReprStackSurvival.stmtRepr_survives_spill` to `ExecStepGeom`'s pinned
`StmtRepr m0` + the caller's deep footprint-disjointness (`hfpDisj`, the
"AST lives in the script region" fact `ExecStepGeom` does not itself carry — it
pins only the tag-node disjointness, exactly as `ExecDispatch.execPrologue`
pushes the deep `hfpDisj` to its caller) + the in-window spill slot, delivering
the `StmtRepr mcall …` conjunct `armExec_rec` needs. With that conjunct
supplied, `hbody`'s residual is PURELY the register-threading decode of the
seven setup sites + `armExec_rec`'s IH-seam + the branch-control sites — no
AST-repr transport remains.

`spillSlot`/`spillWrite` name the concrete `sd i, 8(sp - 176)` write so the
statement of the seam matches the site lemma `ExecBlockSites.site_800041c0_es`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc (StackLayout)
open Vsa.RuntimeRepr (Arena)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- The block do-while counter-spill target: `8(sp - 176)` = `sp - 168`, where
the iteration index `i` is spilled (`sd x16, 0x8(x2)` at `0x800041c0`, `x2 =
sp - 176`). Inside the stack window `[SL.lo, sp)` by the loop's stack geometry
(`SL.lo + 2352 ≤ sp`). -/
def blockSpillSlot (sp : Nat) : Nat := sp - 168

/-- The spill target lies in the stack window `[SL.lo, sp)` whenever the loop's
recursion-headroom geometry holds (`SL.lo + 2352 ≤ sp ≤ SL.hi`). This is the
`hin` premise `stmtRepr_survives_spill` consumes, discharged from the same stack
bounds `ExecStepGeom` already carries. -/
theorem blockSpillSlot_in_window {SL : StackLayout} {sp : Nat}
    (hlo : SL.lo + 2352 ≤ sp) :
    SL.lo ≤ blockSpillSlot sp ∧ blockSpillSlot sp + 8 ≤ sp := by
  unfold blockSpillSlot; omega

/-- **The seq body oracle's AST-repr seam** (the shared-gap application).

From the loop-head statement representation `StmtRepr m0 aStmtSub s` (pinned by
`ExecStepGeom`), the loop's stack-headroom geometry (giving the spill slot
in-window), and the caller's deep footprint-disjointness `hfpDisj` (the AST node
and its whole recursive subtree live in the script region, disjoint from the
stack window — the same fact `ExecDispatch.execPrologue` requires of `exec_stmt`
entry), the statement's representation SURVIVES the `sd i, 8(sp-176)` spill:
`StmtRepr (writeMap8 m0 (sp-168) d) aStmtSub s`. This is the exact
`StmtRepr mcall …` conjunct `armExec_rec` (`ExecBlock.lean:224`) demands, with
`mcall = writeMap8 m0 (sp-168) (sdData_val i)`.

Fanned to while/for/args verbatim (their body spill is the identical
`sd counter, k(sp)` at their own slot, and `exprRepr_survives_spill` covers the
condition/arg-expression `ExprRepr` twin). -/
theorem blockIter_stmtRepr_ready
    {SL : StackLayout} {sp : Nat} {m0 : Mem}
    {aStmtSub : Nat} {s : Stmt} (d : BitVec (8 * 8))
    (hheadroom : SL.lo + 2352 ≤ sp)
    (hfpDisj : ∀ addr, StmtFp m0 aStmtSub s addr → ¬ (SL.lo ≤ addr ∧ addr < sp))
    (hstmt : StmtRepr m0 aStmtSub s) :
    StmtRepr (writeMap8 m0 (blockSpillSlot sp) d) aStmtSub s :=
  stmtRepr_survives_spill (SL := SL) (sp := sp) (blockSpillSlot sp) d
    (blockSpillSlot_in_window hheadroom) hfpDisj hstmt

end Vsa.Sim
