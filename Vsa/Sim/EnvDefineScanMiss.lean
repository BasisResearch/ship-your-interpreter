import Vsa.Sim.EnvDefineScanAllocator

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- An owned exhausted scan reaches the append or grow branch with unchanged data. -/
structure EnvDefineCapacityAllocatorPost
    (saved gm : (R : Register) → Option (RegisterType R))
    (env namePtr pv count pn sp : BitVec 64) (m : Mem) (out : Array String)
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (store : Store)
    (target : Addr) (valid : target < store.frames.size) (name : String) (v : Value) (cap : Nat)
    (after : Config) : Prop where
  capacity : EnvDefineCapacityExit M exts out saved gm env count pn sp store.frames[target] m cap after
  missing : ∀ j (hj : j < store.frames[target].vars.length), store.frames[target].vars[j].1 ≠ name
  namesRead : read64 after.σ.mem (phiF target + 8) = some pn.toNat
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store after.σ.mem
  word : ValueWordRepr after.σ.mem N phiC pv.toNat v
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared namePtr.toNat name
  support : EvalCallSupport after.σ.mem SL A sp

/-- Execute the capacity test after the owned scan's miss, using the represented capacity. -/
theorem EnvDefineScanAllocatorPost.miss_capacity
    {saved gm : (R : Register) → Option (RegisterType R)}
    {env namePtr pv count pn sp : BitVec 64} {m : Mem} {out : Array String}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {valid : target < store.frames.size} {name : String} {v : Value}
    {idx : Nat} {cmp : BitVec 64} {before : Config}
    (h : EnvDefineScanAllocatorPost saved gm env namePtr pv count pn sp m out N M
      phiF phiC alloc exts shared credits store target valid name v before)
    (miss : EnvDefineScanMissExit M exts out saved gm env namePtr pv count pn sp
      store.frames[target] name m idx cmp before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (envAddr : env.toNat = phiF target) (countEq : count.toNat = store.frames[target].vars.length) :
    ∃ after cap, Steps before after ∧
      EnvDefineCapacityAllocatorPost saved gm env namePtr pv count pn sp m out N M
        phiF phiC alloc exts shared credits store target valid name v cap after := by
  have entry : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m := by
    rw [← h.memory]; exact h.allocator
  have frame := entry.heap.store.frames target valid
  obtain ⟨arrays, fields⟩ := frame.arrays
  have signed := frame.capSigned entry.heap.ledger fields.capRead L.arena_ram.2
  obtain ⟨arena, align⟩ := entry.repr.frames_arena target valid
  have stable : ∀ (a b : MState), a.regs.get? Register.x3 = b.regs.get? Register.x3 →
      (∀ k, a.mem[k]? = b.mem[k]?) → M.AInv a exts → M.AInv b exts :=
    fun a b gp memory => L.ainv_private exts a b gp (fun k _ => memory k)
  obtain ⟨after, steps, dispatched⟩ := envDefineMissCapDispatch M exts out saved gm
    env namePtr pv count pn sp store.frames[target] name m arrays.cap
    (by rw [envAddr]; exact fields.capRead) signed fields.bound
    ⟨L.arena_ram.1, L.arena_ram.2, Or.inr (by have := L.arena_htif; omega)⟩
    (by rw [envAddr]; exact arena) (by rw [envAddr]; exact align) countEq stable before
    ⟨miss.missing, idx, miss.lastIndex, cmp, miss.live, miss.savedFrame, miss.frame⟩
  apply dispatched.resolve
  intro cap capacity
  refine ⟨after, cap, steps,
    { capacity := capacity, missing := miss.missing
      namesRead := ?_, allocator := ?_, word := ?_, owned := ?_, nameOwned := ?_, support := ?_ }⟩
  all_goals rw [capacity.memory, ← h.memory]
  · exact h.namesRead
  · exact h.allocator
  · exact h.word
  · exact h.owned
  · exact h.nameOwned
  · exact h.support

#print axioms EnvDefineScanAllocatorPost.miss_capacity

end Vsa.Sim
