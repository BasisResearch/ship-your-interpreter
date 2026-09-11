import Vsa.Sim.SeqInterpAllocatorExit

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Saved interpreter words and the owned suffix at a reached statement call. -/
structure SeqInterpContinueCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (phiF : Addr → Nat) (shared : Nat → Prop)
    (d env : Nat) (sp aRet cursor finish interp : BitVec 64) (ss : List Stmt)
    (m0 mCall : Mem) : Prop
    extends SeqInterpCaller g gExec A SL sp aRet cursor finish m0 mCall where
  retSlot : aRet = sp + 88#64
  remaining : finish.toNat = cursor.toNat + 8 * (1 + ss.length)
  nonempty : ss ≠ []
  stackLo : SL.lo ≤ sp.toNat
  arenaBelow : A.hi ≤ SL.lo
  savedOffRet : sp.toNat + 16 ≤ aRet.toNat
  interpAbove : sp.toNat ≤ interp.toNat
  interpHi : interp.toNat + 8 ≤ 0x100000000
  interpOffRet : interp.toNat + 8 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ interp.toNat
  savedInterp : read64 mCall sp.toNat = some interp.toNat
  script : read64 mCall (sp.toNat + 8) = some 0
  environment : read64 mCall interp.toNat = some (phiF env)
  spill21 : ∃ v, gExec .x21 = some v
  suffix : SeqSuffixOwned mCall shared SL A sp aRet d (cursor.toNat + 8) ss

/-- Values of the three protected words in the actual child-return memory. -/
structure SeqInterpReadback (m : Mem) (sp interp : BitVec 64) (environment : Nat) : Prop where
  savedInterp : read64 m sp.toNat = some interp.toNat
  script : read64 m (sp.toNat + 8) = some 0
  environment : read64 m interp.toNat = some environment

/-- The child frame preserves saved arguments and the interpreter's environment word. -/
theorem SeqInterpContinueCarrier.readback
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {shared : Nat → Prop}
    {d env nf nc : Nat} {final : Vsa.While.St} {status : Status}
    {sp aRet cursor finish interp : BitVec 64} {ss : List Stmt} {m0 mCall : Mem} {cfg : Config}
    (h : SeqInterpContinueCarrier g gExec A SL phiF shared d env
      sp aRet cursor finish interp ss m0 mCall)
    (child : ExecExitD gExec N A SL phiF phiC nf nc final status
      sp 0x80004478#64 aRet mCall cfg) :
    SeqInterpReadback cfg.σ.mem sp interp (phiF env) := by
  have word (a : Nat) (above : sp.toNat ≤ a)
      (offRet : a + 8 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ a) :
      read64 cfg.σ.mem a = read64 mCall a := by
    have agreement : AgreeP (fun k => a ≤ k ∧ k < a + 8) mCall cfg.σ.mem := by
      intro k hk
      have hlo := h.stackLo
      have hA := h.arenaBelow
      exact ((child.1.memFrame k (by omega) (by omega)).resolve_left (by omega)).symm
    exact (read64_agreeP agreement (fun k hk => ⟨by omega, by omega⟩)).symm
  exact
    { savedInterp := (word _ (by omega) (Or.inl (by have := h.savedOffRet; omega))).trans h.savedInterp
      script := (word _ (by omega) (Or.inl h.savedOffRet)).trans h.script
      environment := (word _ h.interpAbove h.interpOffRet).trans h.environment }

#print axioms SeqInterpContinueCarrier.readback

end Vsa.Sim
