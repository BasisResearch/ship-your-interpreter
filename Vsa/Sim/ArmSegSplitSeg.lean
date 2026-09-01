import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.InductionScaffold
import Vsa.Sim.StepCount

/-!
# `ArmSegSplitSeg` — the `jal`→child-`SegEntry` marshalling variant (Task #76, Half A.2)

`ArmSegSplit.evalEntry_of_jalPrefix` / `ArmSegSplitExec.execEntry_of_jalPrefix` are
the RICH-entry marshalling twins (eval / exec).  The remaining non-eval-child arm
classes of `ApproxArmResid` land at interior control points that have NO dedicated
rich struct — the EX_CALL arg loop (`AEntryC`), the callee-inline body head at
depth `d+1` (`CEntryC`), the for-loop re-entry (`FEntryC`).  `ApproxArmReseat`
anchors those on `SegEntry` at a ghost interior PC.

`SegEntry` (`InductionScaffold.lean`) is a LIGHT entry — PC + `StoreRepr` + `OutRepr`
+ ghost frame + two SKELETON budgets (`depth_budget`/`arena_budget`).  So the jal→
`SegEntry` marshalling is much lighter than the rich twins: the jal step supplies
`good`/`tick`/`pc`/`mem`, and the store/out/budget facts are carried straight
through as premises (nothing frame-lowering-specific is projected — `SegEntry` has
no `stackOK`/`aExpr`/`spill_defined`).

`segEntry_of_jalPrefix` is the ONE shared fact; `AEntryC`/`CEntryC`/`FEntryC`
instantiate it at their own ghost `entryPC` (`argLoopPC`/`calleeBodyPC`/`forCondPC`),
supplying the depth/arena budgets that the interior control point respects.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.Scaffold (SegEntry)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- **The shared jal→child-`SegEntry` marshalling fact.**

From an arm config `c` at a recursive `jal <interior>` PC `callPC` targeting the
interior control point `entryPC` (arg loop / callee body / for-cond), one `jal` step
reaches a config satisfying `SegEntry` at `entryPC`.  The light `SegEntry` fields
(`store`/`out`/`frame` + the two skeleton budgets) are carried through as premises;
the jal supplies control (`good`/`tick`/`pc`/`mem`).

Delivered as `LandedN 1 c (SegEntry … entryPC …)` — the divergence-fold shape.
The sub-ghosts are the post-`jal` register file and `m0_sub := mcall`. -/
theorem segEntry_of_jalPrefix
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (entryPC : Nat)
    (callPC : BitVec 64) (jalImm : BitVec 21)
    (mcall : Mem)
    (c : Config)
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 entryPC)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.mem = mcall ∧
        Exec_stmtLoaded mcall ∧
        StoreRepr mcall N A φf φc st.store ∧
        Machine.output c.σ = st.out ∧
        d + dLeft = Vsa.While.maxCallDepth ∧
        A.lo + aLeft ≤ A.hi) :
    LandedN 1 c (fun c' =>
      SegEntry (fun R => c'.σ.regs.get? R) N A SL φf φc st d dLeft aLeft entryPC
        mcall c') := by
  obtain ⟨hG, htick, hpc, ⟨vmi, hmi⟩, hmemc, hcodeS, hstore, hout, hdepth, harena⟩ := hpre
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcodeS) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 entryPC) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hout0 : σ1.sailOutput = c.σ.sailOutput := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]
  refine ⟨1, ⟨σ1, i1, c.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · exact
      { good := hG1
        tick := hi1
        pc := hpc1
        store := by show StoreRepr σ1.mem N A φf φc st.store; rw [hmem1e]; exact hstore
        out := by
          show Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout0]
          simpa only [Vsa.Machine.output] using hout
        mem := hmem1e
        frame := fun _ _ => rfl
        depth_budget := hdepth
        arena_budget := harena }

#print axioms segEntry_of_jalPrefix

end Vsa.Sim
