import Vsa.Sim.EnvDefineScanAllocator
import Vsa.Sim.EnvDefineHitGeometry

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Finish a reached scan hit using owned array geometry and the framed update tail. -/
theorem EnvDefineScanAllocatorPost.hit_return
    {saved gm : (R : Register) → Option (RegisterType R)}
    {env namePtr pv count pn sp : BitVec 64} {m : Mem} {out : Array String}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {valid : target < store.frames.size} {name : String} {v : Value}
    {idx : Nat} {hi : idx < store.frames[target].vars.length} {cmp : BitVec 64} {before : Config}
    (h : EnvDefineScanAllocatorPost saved gm env namePtr pv count pn sp m out N M
      phiF phiC alloc exts shared credits store target valid name v before)
    (hit : EnvDefineScanHitExit M exts out saved gm env namePtr pv count pn sp
      store.frames[target] name m idx hi cmp before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (envAddr : env.toNat = phiF target) (source : RetSlotGeom SL sp pv)
    (frameHi : sp.toNat + 64 ≤ SL.hi)
    (unique : FrameUnique store.frames[target]) (bounded : ValueClosuresBounded store.closures.size v) :
    ∃ after dst, Steps before after ∧
      EnvDefineHitKeptPost
        (EnvDefineHitAllocatorPost saved sp dst m N M phiF phiC alloc exts shared credits
          store target name v) (fun R => before.σ.regs.get? R) out after := by
  have entry : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m := by
    rw [← h.memory]; exact h.allocator
  obtain ⟨vals, dst, geometry⟩ := entry.defineHitGeometry L valid hi envAddr source
  have stackLo := hit.frame.stack
  have arenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo := by
    rcases L.arena_stack with left | right
    · left; obtain ⟨lo, _, _⟩ := stackLo; omega
    · right; omega
  obtain ⟨after, steps, post⟩ := envDefineHitAllocator_run_kept
    (g := fun R => before.σ.regs.get? R) ⟨fun _ _ => rfl, hit.frame.out⟩ L entry
    ⟨cmp, hit.live, hit.savedFrame⟩ hit.frame.gp valid hi hit.nameEq unique envAddr
    geometry.values geometry.slot
    (by rw [← h.memory]; exact h.owned) (by rw [← h.memory]; exact h.word)
    bounded (by rw [← h.memory]; exact h.support.image.text.Env_defineLoaded)
    geometry.geometry geometry.arena arenaStack
    (h.support.image.arena_disjoint (by decide) (by decide))
  exact ⟨after, dst, steps, post⟩

#print axioms EnvDefineScanAllocatorPost.hit_return

end Vsa.Sim
