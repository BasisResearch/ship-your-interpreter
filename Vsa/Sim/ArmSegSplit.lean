import Vsa.Sim.EvalRecCommon
import Vsa.Sim.StepCount

/-!
# `ArmSegSplit` — the shared jal→child-entry marshalling fact (Task #75)

The divergence fold in `ApproxDispatchSuppliers.ApproxArmResid` needs, per arm
class, the **PRE-JAL PREFIX** of the arm: from the arm head, ≥1 machine step,
landing AT the child's rich entry (`EvalEntry` for a sub-expression, control at
the recursive `jal eval_expr` target, child NOT yet returned).  Every *landed*
M4 arm Triple (`armTail_rec`, `blockB_unary`, …) instead consumes the child as a
RETURNING IH: it builds the child `EvalEntry`, applies `hIH : EvalIH`, and lands
at `SubEvalReturn` (post-return).  The child `EvalEntry` is therefore reached
mid-chain but never exposed.

This file EXTRACTS that reach as ONE shared marshalling fact,
`evalEntry_of_jalPrefix`: the `armTail_rec` Triple pre (arm state with the
sub-call arguments already staged, at the `jal eval_expr` PC) advances exactly
one machine step to a config satisfying the child's `EvalEntry`.  This is
`armTail_rec` truncated *before* the IH application — lines 311–401 of
`EvalRecCommon.armTail_rec`, verbatim, minus the `hIH` call — packaged as a
`LandedN 1`.

## What the jal-step config supplies vs. what must be premises (the finding)

`EvalEntry` (`Vsa/Sim/InterpEntry.lean`) is a ~40-field structure.  Reading which
fields the post-`jal` config *supplies for free* from the marshalling vs. which
must be carried as premises of the arm-head bundle:

* **Supplied by the jal step itself** (from `sigmaPost_jal`): `good`, `tick`,
  `pc` (= `evalExprEntry`, via `hjaltgt`), `a0`/`a1`/`a2` (the staged
  sret/interp/operand registers, transported by `obs_jalT_other`), `ra` (= the
  link `retPC`, via `hlink`), `spReg` (= the lowered `sp - 1088`), `minstret`,
  `mem` (= `mcall`, unchanged by jal), `out`, `frame` (the sub-ghosts are the
  post-jal register file, so `frame` is `rfl`), `spill_defined`.
* **Must be premises of the arm-head bundle** (NOT derivable from a PC-only or
  even a returning-IH-shaped entry): the sub-call GEOMETRY at the *lowered*
  frame — `stackOK` for `sp - 1088` (needs `SL.lo + 3264 ≤ sp`, one extra frame
  of headroom), the operand node's `ExprRepr`/alignment/RAM/disjointness at the
  lowered `sp`, the sub-result buffer geometry, `StoreRepr` + its survival
  clause, and the code/table/arena disjointness re-checked against `sp - 1088`.
  These are exactly the "recursive-case extras" `blockB_unary` takes beyond its
  `ArmEntryK` (the `ArmEntryK` widening residual), and they are why the split
  `EEntryC (.unary op e) → LandedN 1 (EEntryC e)` is NOT closable from `EEntryC`
  alone (see `armSegSplit-*` in `experiments/observations.md`).

So `evalEntry_of_jalPrefix` is the ONE reusable seam (analogous to
`jalStep_of_obs` for the CALL seam); every arm class instantiates it after its
own arm-head staging span establishes the bundle.

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

namespace Vsa.Sim

/-- **The shared jal→child-`EvalEntry` marshalling fact.**

From the `armTail_rec` Triple pre — a config `c` at the recursive `jal eval_expr`
PC `callPC`, with the sub-call arguments staged (`a0 = subsret`, `a1 = aIn`,
`a2 = aOperand`, `sp` lowered to `sp - 1088`) and the full lowered-frame geometry
bundle — one `jal` step reaches a config satisfying the child's `EvalEntry` at
node `esub`, sub-frame `sp - 1088`, link `retPC`, buffer `subsret`.

Delivered as `LandedN 1 c (fun c' => EvalEntry … esub … c')`: the exact
divergence-fold shape (one machine step ≥, control AT the child entry, child NOT
returned).  The sub-ghosts are chosen as the post-`jal` register file
(`fun R => σ1.regs.get? R`), `sp_sub := sp - 1088`, `m0_sub := mcall`, exactly
`armTail_rec`'s choice.

This is `armTail_rec` truncated before its `hIH` call; a class instantiates it
after staging the bundle from its arm-head span. -/
theorem evalEntry_of_jalPrefix
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (c : Config)
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    (hpre :
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧
        c.σ.regs.get? Register.x9 = some sret ∧
        c.σ.regs.get? Register.x11 = some aIn ∧
        c.σ.regs.get? Register.x12 = some aOperand ∧
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w)) ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        aOperand.toNat % 8 = 0 ∧
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: the child expression's recursion-sound budget at the
        -- lowered `sp - 1088`, its `.fn`-bodies bound, and the store-bodies
        -- invariant (eval_expr does NOT bump `d`, so the child is at depth `d`).
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget) :
    LandedN 1 c (fun c' =>
      EvalEntry (fun R => c'.σ.regs.get? R) N A SL φf φc st d env esub
        (sp - 1088#64) retPC subsret aIn aOperand mcall c') := by
  obtain ⟨hG, htick, hpc, ha0, hs1, hx11, hx12, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmemc,
    hcode, hviCode, hslot, hsubexpr, hstore, hstoreSurv, hframe, ⟨⟨w8, hw8⟩, ⟨w18, hw18⟩⟩,
    hslotRa, hslotS0, hslotS1, hslotS2,
    hopAl, hopLo, hopHi, hopWin, hopStk,
    hssAl, hssLo, hssHi,
    hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,
    hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
    hstackBudget, hexprBodies, hstoreBodies⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  -- ============ callPC: jal eval_expr → PC := evalExprEntry, x1 := retPC ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmemc ▸ hcode) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = mcall := by rw [hmem1]; exact hmemc
  have hpc1 : σ1.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some retPC := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some subsret := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_jalT_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11
  have hx12_1 : σ1.regs.get? Register.x12 = some aOperand := obs_jalT_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some w8 := by
    have hc8 : c.σ.regs.get? Register.x8 = some w8 := (hframe Register.x8 (by decide)).trans hw8
    exact obs_jalT_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc8
  have hx18_1 : σ1.regs.get? Register.x18 = some w18 := by
    have hc18 : c.σ.regs.get? Register.x18 = some w18 := (hframe Register.x18 (by decide)).trans hw18
    exact obs_jalT_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc18
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by
    rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- ============ the sub-call's EvalEntry at ⟨σ1, i1, steps+1⟩ ============
  -- `LandedN 1 c P = ∃ m c', 1 ≤ m ∧ StepsN m c c' ∧ P c'`: reached in exactly
  -- one machine step (the `jal`), landing at the child `EvalEntry`.
  refine ⟨1, ⟨σ1, i1, c.steps + 1⟩, Nat.le_refl _,
    StepsN.succ hstep1 (StepsN.zero _), ?_⟩
  · -- the LandedN post: EvalEntry at the reached config ⟨σ1,i1,steps+1⟩, whose
    -- register file is `fun R => σ1.regs.get? R` definitionally.
    exact
      { good := hG1
        tick := hi1
        pc := hpc1
        a0 := ha0_1
        a1 := hx11_1
        a2 := hx12_1
        ra := hlink1
        ra_align := hretAl
        spReg := hsp_1
        stackOK := ⟨by rw [hspsub]; omega, by rw [hspsub]; omega, by rw [hspsub]; omega⟩
        stackBudget := hstackBudget
        expr_bodies := hexprBodies
        store_bodies := hstoreBodies
        minstret := ⟨vmi1, hmi1⟩
        mem := hmem1e
        code := by show Eval_exprLoaded σ1.mem; rw [hmem1e]; exact hcode
        expr := by rw [hmem1e]; exact hsubexpr
        store := by rw [hmem1e]; exact hstore
        store_survives := by
          intro m' hag
          refine hstoreSurv m' (fun k hk1 _ => ?_)
          have hk1' : ¬ (SL.lo ≤ k ∧ k < (sp - 1088#64).toNat) := by
            rw [hspsub]; intro ⟨ha, hb⟩; exact hk1 ⟨ha, by omega⟩
          have hk2' : ¬ (subsret.toNat ≤ k ∧ k < subsret.toNat + 24) := by
            intro ⟨ha, hb⟩; exact hk1 ⟨by omega, by omega⟩
          have := hag k hk1' hk2'
          rwa [hmem1e] at this
        out := by
          show Vsa.Machine.output σ1 = st.out
          simp only [Vsa.Machine.output]; rw [hout1]; exact houtStr
        frame := fun _ _ => rfl
        code_stack_disjoint := by
          rcases hcodeStk with h | h
          · left; rw [hspsub]; omega
          · right; exact h
        expr_stack_disjoint := by
          rcases hopStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        expr_align := hopAl
        expr_ram := ⟨hopLo, hopHi⟩
        expr_win := hopWin
        sret_align := hssAl
        sret_ram := ⟨by omega, by omega⟩
        sret_win := by omega
        sret_vicode_disjoint := by
          rcases hviStk with h | h
          · right; omega
          · left; omega
        sret_stack_disjoint := by right; rw [hspsub]; omega
        sret_evalcode_disjoint := by
          rcases hcodeStk with h | h
          · left; omega
          · right; omega
        vicode_stack_disjoint := by
          rcases hviStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        stack_ram := ⟨hSLlo, hSLhiRam⟩
        stack_win := hSLwin
        value_int_code := by rw [hmem1e]; exact hviCode
        int_slot := by rw [hmem1e]; exact hslot
        table_stack_disjoint := by
          rcases htableStk with h | h
          · left; exact h
          · right; rw [hspsub]; omega
        spill_defined := ⟨⟨w8, hx8_1⟩, ⟨sret, hs1_1⟩, ⟨w18, hx18_1⟩⟩ }

#print axioms evalEntry_of_jalPrefix

end Vsa.Sim
