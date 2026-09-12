import EvalVarLookupTail
import Vsa.Sim.DeriveMetaTowers
import Vsa.Sim.EvalReturn

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Owned store bytes lie outside the caller's entire stack region. -/
theorem LookupData.stack_survives
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name : BitVec 64} {m : Mem}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    ∀ m', AgreeP (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) m m' →
      StoreRepr m' N A phiF phiC s := by
  intro m' hag
  apply D.owned.repr_transport D.repr hag
  · intro role p n hp k hk hin
    have hb := (D.ledger.arena.1 _ (D.ledger.live role p n hp)).2
    change A.lo ≤ p ∧ p + n ≤ A.hi at hb
    change p ≤ k ∧ k < p + n at hk
    omega
  · intro k hk hin
    have := D.geometry.stack k hk
    omega

theorem var_abi_cases : ∀ R : Register, AbiPreservedNoise R →
    R = .x2 ∨ R = .x8 ∨ R = .x9 ∨ R = .x18 ∨
    R = .x19 ∨ R = .x20 ∨ R = .x21 ∨ kept R = true := by
  intro R
  cases R <;> simp [AbiPreservedNoise, AbiPreserved, kept]

theorem kept_arm_registers : ∀ R : Register, kept R = true →
    AbiPreservedNoise R ∧ (Register.x8 == R) = false ∧
    (Register.x9 == R) = false ∧ (Register.x18 == R) = false ∧
    (Register.x2 == R) = false := by
  intro R
  cases R <;> simp [AbiPreservedNoise, AbiPreserved, kept]

/-- The lookup windows fit below the evaluator's original stack pointer. -/
theorem var_lookup_windows {SL : StackLayout} {sp : BitVec 64}
    (hroom : SL.lo + 1152 ≤ sp.toNat) :
    ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      EnvGetFootprint ((sp - 1088#64) + 240#64) (sp - 1088#64) k := by
  have h1088 : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have := sp.isLt
    change ((2^64 - 1088) + sp.toNat) % 2^64 = sp.toNat - 1088
    omega
  have h1152 : ((sp - 1088#64) - 64#64).toNat = sp.toNat - 1152 := by
    rw [BitVec.toNat_sub, h1088]
    have := sp.isLt
    change ((2^64 - 64) + (sp.toNat - 1088)) % 2^64 = sp.toNat - 1152
    omega
  have hout : ((sp - 1088#64) + 240#64).toNat = sp.toNat - 848 := by
    rw [BitVec.toNat_add, h1088]
    have := sp.isLt
    change (sp.toNat - 1088 + 240) % 2^64 = sp.toNat - 848
    omega
  intro k hk
  unfold EnvGetFootprint
  rw [hout, h1152]
  omega

/-- Construct the coherent evaluator exit from the actual arm and return.
The returned ownership uses the same maps as the value and store. -/
theorem VarReturnResult.at_arm
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value}
    {name sp dst ret r8 r9 r18 r19 r20 r21 aExpr aEnv armPC : BitVec 64}
    {callee : Mem → Prop} {e : Vsa.While.Expr} {out0 : Array String}
    {m0 ment : Mem} {before after : Config}
    (h : VarReturnResult N A SL phiF phiC alloc exts shared st.store query v
      name (sp - 1088#64) dst ret r8 r9 r18 r19 r20 r21 before after)
    (entry : ArmEntryK g N A SL phiF phiC st armPC callee e
      sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment before)
    (presence : MemExtends m0 before.σ.mem)
    (h19 : before.σ.regs.get? Register.x19 = some r19)
    (h20 : before.σ.regs.get? Register.x20 = some r20)
    (h21 : before.σ.regs.get? Register.x21 = some r21)
    (hroom : SL.lo + 1152 ≤ sp.toNat)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    EvalReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp ret dst m0
      (fun f c m => StoreOwned m f c alloc shared st.store ∧ ValueOwned m shared dst.toNat v)
      after := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st armPC callee e
    sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment before entry
  obtain ⟨hra, hsp, h8, h9, h18, ha0, hr19, hr20, hr21, _⟩ := h.regs
  have frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = g R := by
    intro R hR
    rcases var_abi_cases R hR with h2 | h08 | h09 | h018 | h019 | h020 | h021 | hk
    · subst R
      have hs : after.σ.regs.get? Register.x2 = some sp := by
        simpa only [gprGet, BitVec.sub_add_cancel] using hsp
      exact hs.trans p.savedSp.symm
    · subst R; exact h8.trans p.saved8.symm
    · subst R; exact h9.trans p.saved9.symm
    · subst R; exact h18.trans p.saved18.symm
    · subst R
      exact hr19.trans (h19.symm.trans (p.frame _ hR (by decide) (by decide) (by decide) (by decide)))
    · subst R
      exact hr20.trans (h20.symm.trans (p.frame _ hR (by decide) (by decide) (by decide) (by decide)))
    · subst R
      exact hr21.trans (h21.symm.trans (p.frame _ hR (by decide) (by decide) (by decide) (by decide)))
    · obtain ⟨_, h08, h09, h018, h02⟩ := kept_arm_registers R hk
      exact (h.kept_frame R hk).trans (p.frame R hR h08 h09 h018 h02)
  have he : EvalExit g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp ret dst m0 after :=
    { good := h.good, tick := h.tick
      pc := by rw [ret_tgt ret p.retAlign]; exact h.pc
      a0 := ha0, ra := hra
      spReg := by simpa only [gprGet, BitVec.sub_add_cancel] using hsp
      minstret := h.good.minstret
      result := ⟨phiC, PhiExtends.refl _ _, h.value.repr⟩
      store := ⟨phiF, phiC, PhiExtends.refl _ _, PhiExtends.refl _ _, h.data.repr⟩
      out := by
        change String.join after.σ.sailOutput.toList = st.out
        rw [h.output, p.out]
        exact p.outStr
      frame := frame
      memFrame := by
        intro k hk _
        by_cases hd : dst.toNat ≤ k ∧ k < dst.toNat + 24
        · exact Or.inl hd
        · exact Or.inr ((h.outside k (var_lookup_windows hroom k hk) hd).trans
            (by rw [p.mem]; exact p.memFrame k hk)) }
  have hd : EvalExitD g N A SL phiF phiC st.store.frames.size st.store.closures.size
      st v sp ret dst m0 after :=
    ⟨he, presence.trans h.extendsMemory, h.value.raw,
      phiF, phiC, PhiExtends.refl _ _, PhiExtends.refl _ _, h.data.stack_survives arena⟩
  exact hd.withReturnRepr
    { frames := PhiExtends.refl _ _, closures := PhiExtends.refl _ _
      values := fun a w haw => by
        have heq : (a, w) = (dst.toNat, v) := List.mem_singleton.mp haw
        cases heq
        exact h.value.repr
      owned := ⟨h.data.owned, h.owned⟩
      survives := h.data.stack_survives arena }

#print axioms LookupData.stack_survives
#print axioms var_abi_cases
#print axioms kept_arm_registers
#print axioms var_lookup_windows
#print axioms VarReturnResult.at_arm

end Vsa.Sim.EnvGetReflected
