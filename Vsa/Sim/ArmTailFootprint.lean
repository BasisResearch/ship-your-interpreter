import Vsa.Sim.ExitFootprint

/-!
# `ArmTailFootprint` — `armTail_rec` for `sp`/`m0`-aware child facts

`armTail_rec_gen` (`EvalRecCommon.lean`) is the `jal eval_expr ≫ child ⇒
SubEvalReturn` glue for ANY fact `Q` retained at the child's actual return.
This file instantiates it at the `sp`/`m0`-aware child contracts of
`ExitFootprint.lean`:

* `armTail_rec_withM` — at `EvalIHWithM Extra`;
* `armTail_rec_footprint` — at `EvalIHF F`: the child's return memory has the
  footprint `F SL A (sp - 1088) subsret` relative to the call memory `mcall`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `armTail_rec_with` for an `sp`/`m0`-aware extra. -/
theorem armTail_rec_withM
    {Extra : EvalExtraM}
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (vsub : Value)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    -- target arithmetic, fixed by the arm (`decide`-able concretely):
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (henvValid : EnvValid st env)
    -- the per-arm `jal eval_expr` site step:
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    -- the induction hypothesis for the sub-derivation:
    (hIH : EvalIHWithM Extra st d env esub st' vsub) :
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some callPC ∧
        c.σ.regs.get? Register.x10 = some subsret ∧          -- a0 = sub-sret
        c.σ.regs.get? Register.x9 = some sret ∧              -- s1 = outer sret
        c.σ.regs.get? Register.x11 = some aIn ∧              -- a1 = interp*
        c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
        c.σ.regs.get? Register.x12 = some aOperand ∧         -- a2 = operand node
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧    -- sp lowered
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        String.join out0.toList = st.out ∧
        c.σ.mem = mcall ∧
        ValueWordsTotal mcall subsret.toNat ∧
        Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        NBSPins mcall ∧
        -- WAVE 47i: the child's entry-ground bundle (transported+projected
        -- from the parent `EvalEntry.ground` by the supplier).
        EvalGround mcall SL A (sp - 1088#64) subsret aOperand.toNat esub ∧
        ExprRepr mcall aOperand.toNat esub ∧
        StoreRepr mcall N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            mcall[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
          (∃ w, gpre Register.x19 = some w) ∧ (∃ w, gpre Register.x20 = some w) ∧
          (∃ w, gpre Register.x21 = some w)) ∧
        read64 mcall (sp.toNat - 8) = some r.toNat ∧
        read64 mcall (sp.toNat - 16) = some v8.toNat ∧
        read64 mcall (sp.toNat - 24) = some v9.toNat ∧
        read64 mcall (sp.toNat - 32) = some v18.toNat ∧
        -- operand-node geometry (the sub-call's `aExpr`):
        0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aOperand.toNat ∧
        (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
        -- sub-result buffer geometry: inside the lowered frame, below the spill slots:
        subsret.toNat % 8 = 0 ∧
        sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
        -- stack geometry: recursive headroom (one extra frame), 16-alignment:
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        sp.toNat ≤ 0x100000000 ∧
        0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
        -- code/table/arena region disjointness:
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        -- ITEM ZERO B1: child budget at the lowered `sp - 1088`, `.fn`-bodies
        -- bound, store-bodies invariant (eval_expr keeps depth `d`).
        StackOK SL (sp - 1088#64)
          (esub.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget esub = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget)
      (ReturnedWith
        (SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' vsub sp r sret subsret retPC v8 v9 v18 mcall)
        (Extra N A SL φf φc (sp - 1088#64) subsret mcall)) :=
  armTail_rec_gen (Extra N A SL φf φc (sp - 1088#64) subsret mcall) gpre N A SL φf φc st st' d env esub vsub callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall hjaltgt hlink hretAl henvValid hjalSite
    (fun g_sub => hIH.run g_sub N A SL φf φc (sp - 1088#64) retPC subsret aIn aOperand mcall)

/-- `armTail_rec` at a footprint-carrying child (`armTail_rec_withM` at `footExtra F`):
the same precondition as `armTail_rec_with`, and the post
`ReturnedWith (SubEvalReturn …) (footExtra F N A SL φf φc (sp - 1088#64) subsret mcall)`, whose
extra unfolds to `MemFootprint (F SL A (sp - 1088#64).toNat subsret.toNat) mcall c.σ.mem`. -/
def armTail_rec_footprint (F : FootFam)
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (vsub : Value)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    -- target arithmetic, fixed by the arm (`decide`-able concretely):
    (hjaltgt : (callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry)
    (hlink : (BitVec.addInt callPC 4) = retPC)
    (hretAl : retPC.toNat % 4 = 0)
    (henvValid : EnvValid st env)
    -- the per-arm `jal eval_expr` site step:
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4)))
    -- the footprint-carrying induction hypothesis for the sub-derivation:
    (hIH : EvalIHF F st d env esub st' vsub) :=
  armTail_rec_withM (Extra := footExtra F) gpre N A SL φf φc st st' d env esub vsub callPC
    retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall hjaltgt hlink hretAl
    henvValid hjalSite hIH

#print axioms armTail_rec_withM
#print axioms armTail_rec_footprint

end Vsa.Sim
