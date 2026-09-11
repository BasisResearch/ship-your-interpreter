import Vsa.Sim.ArmSegSplit

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) Existing fixed-witness call bundle, moved below the divergence fold without changing its definition.
def JalPreCore (e : Expr) (c' : Config) (st : Vsa.While.St) (d : Nat)
    (env : Addr)
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem) : Prop :=
    EnvValid st env ∧
    ((callPC + sign_extend (m := 64) jalImm) = BitVec.ofNat 64 evalExprEntry) ∧
    ((BitVec.addInt callPC 4) = retPC) ∧ retPC.toNat % 4 = 0 ∧
    (∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some callPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ callPC vmi jalImm Register.x1 (BitVec.addInt callPC 4))) ∧
    GoodState c'.σ ∧ c'.tick < 2 ∧
    c'.σ.regs.get? Register.PC = some callPC ∧
    c'.σ.regs.get? Register.x10 = some subsret ∧
    c'.σ.regs.get? Register.x9 = some sret ∧
    c'.σ.regs.get? Register.x11 = some aIn ∧
    c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) ∧
    c'.σ.regs.get? Register.x12 = some aOperand ∧
    c'.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
    (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
    c'.σ.sailOutput = out0 ∧
    String.join out0.toList = st.out ∧
    c'.σ.mem = mcall ∧
    ValueWordsTotal mcall subsret.toNat ∧
    Eval_exprLoaded mcall ∧ Value_intLoaded mcall ∧ IntSlotPinned mcall ∧ NBSPins mcall ∧
    -- WAVE 47i: the child's entry-ground bundle.
    EvalGround mcall SL A (sp - 1088#64) subsret aOperand.toNat e ∧
    ExprRepr mcall aOperand.toNat e ∧
    StoreRepr mcall N A φf φc st.store ∧
    (∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store) ∧
    (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
    ((∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
      (∃ w, gpre Register.x19 = some w) ∧ (∃ w, gpre Register.x20 = some w) ∧
      (∃ w, gpre Register.x21 = some w)) ∧
    read64 mcall (sp.toNat - 8) = some r.toNat ∧
    read64 mcall (sp.toNat - 16) = some v8.toNat ∧
    read64 mcall (sp.toNat - 24) = some v9.toNat ∧
    read64 mcall (sp.toNat - 32) = some v18.toNat ∧
    0x80000000 ≤ aOperand.toNat ∧ aOperand.toNat + 16 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ aOperand.toNat ∧
    (aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat) ∧
    subsret.toNat % 8 = 0 ∧
    sp.toNat - 1088 ≤ subsret.toNat ∧ subsret.toNat + 24 ≤ sp.toNat - 32 ∧
    SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
    sp.toNat ≤ 0x100000000 ∧
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 ∧ tohostAddr + 16 ≤ SL.lo ∧
    (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
    ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
    ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
    (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
    (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
    -- ITEM ZERO B1: the operand's recursion-sound budget at `sp - 1088`, its
    -- `.fn`-bodies bound, and the store-bodies invariant.
    StackOK SL (sp - 1088#64)
      (e.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
    Expr.bodiesBound Vsa.While.perCallBudget e = true ∧
    Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

end Vsa.Sim
