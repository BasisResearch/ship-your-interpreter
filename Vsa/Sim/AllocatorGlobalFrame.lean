import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.ReprSurvival

namespace Vsa.Sim.AllocatorGlobalFrame

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The current arena/stack frame preserves the allocator's top-pointer slot.
The layout premises put all eight bytes outside both permitted write regions. -/
theorem top_unchanged {A : Arena} {SL : StackLayout} {sp : BitVec 64} {m m' : Mem}
    (frame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) →
      ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m'[k]? = m[k]?)
    (arena : 0x8001ad28 ≤ A.lo)
    (stack : 0x8001ad28 ≤ SL.lo ∨ sp.toNat ≤ 0x8001ad20) :
    read64 m' 0x8001ad20 = read64 m 0x8001ad20 := by
  apply read64_agreeP (P := fun k => 0x8001ad20 ≤ k ∧ k < 0x8001ad28)
  · intro k hk
    apply frame k
    · intro ha; omega
    · intro hs
      rcases stack with below | above <;> omega
  · intro k hk; omega

/-- Apply the framing consequence to the exact current env_new return type. -/
theorem env_new_top_unchanged
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {sp r : BitVec 64} {m : Mem}
    {out : Array String} {cfg : Config}
    (returned : EnvNewReturnState g N A SL phiF phiC st env sp r m out cfg)
    (arena : 0x8001ad28 ≤ A.lo)
    (stack : 0x8001ad28 ≤ SL.lo ∨ sp.toNat ≤ 0x8001ad20) :
    read64 cfg.σ.mem 0x8001ad20 = read64 m 0x8001ad20 :=
  top_unchanged returned.mem_frame arena stack

/-- Any endpoint that changes the top pointer violates this return contract.
This theorem does not establish that a particular allocator execution changes it. -/
theorem rejects_top_change
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {sp r : BitVec 64} {m : Mem}
    {out : Array String} {cfg : Config}
    (arena : 0x8001ad28 ≤ A.lo)
    (stack : 0x8001ad28 ≤ SL.lo ∨ sp.toNat ≤ 0x8001ad20)
    (changed : read64 cfg.σ.mem 0x8001ad20 ≠ read64 m 0x8001ad20) :
    ¬ EnvNewReturnState g N A SL phiF phiC st env sp r m out cfg :=
  fun returned => changed (env_new_top_unchanged returned arena stack)

#print axioms top_unchanged
#print axioms env_new_top_unchanged
#print axioms rejects_top_change

end Vsa.Sim.AllocatorGlobalFrame
