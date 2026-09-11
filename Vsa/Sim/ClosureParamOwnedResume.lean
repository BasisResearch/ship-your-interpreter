import Vsa.Sim.ClosureParamResume
import Vsa.Sim.EnvDefineBindingRuntime

namespace Vsa.Sim.ClosureParamResume

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The back edge or body entry retains the helper's selected owned runtime. -/
structure OwnedPost
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (N : NativeAddrs) (phiF phiC : Addr → Nat)
    (shared : Nat → Prop) (credits : Nat) (store : Store) (m : Mem)
    (sp savedS6 : BitVec 64) (index count : Nat) (more : Bool) (before after : Config) : Prop extends
    Post sp savedS6 index count more before after where
  result : AllocatorResult M N shared credits store [] m phiF phiC after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv

/-- Execute the actual fold branch while retaining the newly installed binding and reserve. -/
theorem run_owned
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {param : String} {value : Value} {sp savedS6 : BitVec 64} {index count : Nat} {more : Bool}
    {m : Mem} {out : Array String} {returned : Config}
    (h : EnvDefineOwnedReturn g N M phiF phiC shared credits st env param value
      sp 0x80003314#64 m out returned)
    (geometry : ClosureEnvNewResume.Geometry sp)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (arenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (bound : g Register.x22 = some (BitVec.ofNat 64 (8 * count)))
    (indexRead : read64 m sp.toNat = some (8 * index))
    (savedRead : read64 m (sp.toNat + 1024) = some savedS6.toNat)
    (indexLt : index < count) (countBound : count < 2^31)
    (branch : decide (index + 1 < count) = more)
    (support : EvalCallSupport m SL A sp) :
    ∃ after, Steps returned after ∧
      OwnedPost M N phiF phiC shared credits (st.store.define env param value) m
        sp savedS6 index count more returned after := by
  have pre := Pre.of_return h.exit geometry stackLo stackHi arenaStack bound indexRead savedRead
    indexLt countBound branch support
  obtain ⟨after, steps, post⟩ := run pre
  exact ⟨after, steps,
    { toPost := post, result := by rw [post.memory]; exact h.result
      gp := (post.frame .x3 (by decide)).trans h.gp }⟩

#print axioms run_owned

end Vsa.Sim.ClosureParamResume
