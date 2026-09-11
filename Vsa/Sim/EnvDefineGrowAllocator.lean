import Vsa.Sim.rows.EnvDefineGrowLane
import Vsa.Sim.RuntimeArraysGrow
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.InterpEntry

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The append entry carries the same shared domain and its remaining allocation reserve. -/
structure EnvDefineAppendAllocatorPost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (name : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits cap : Nat) (after : Config) : Prop where
  head : EnvDefineAppendHead g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
    exts after.σ.mem cap after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits st.store after.σ.mem
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared aName.toNat name
  support : EvalCallSupport after.σ.mem SL A esp

/-- Retain readiness and debit the two actual array reallocations. -/
theorem EnvDefineGrowHeapPost.allocator
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m mA : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    {alloc : Allocations} {shared : Nat → Prop} {credits pn pvals cap : Nat}
    {before after : Config} {exts' : List Extent} {cap' pn' pvals' : Nat}
    (h : EnvDefineGrowHeapPost g N A SL phiF phiC st env name v esp aEnv aName pv r m mA out M
      exts alloc shared InitialReadableByte (InitialWriteByte SL)
      pn pvals cap credits before after exts' cap' pn' pvals')
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 2) st.store mA)
    (capRead : read32 mA (phiF env + 4) = some cap)
    (valuesRead : read64 mA (phiF env + 16) = some pvals) :
    RuntimeAllocatorState M N phiF phiC
      ((alloc.insert (.names env) pn' (8 * cap')).insert (.values env) pvals' (24 * cap'))
      exts' shared credits st.store after.σ.mem := by
  have valid := h.head.facts.env_lt
  obtain ⟨arrays, fields⟩ := (entry.heap.store.frames env valid).arrays
  have capEq := Option.some.inj (fields.capRead.symm.trans capRead)
  have bound : st.store.frames[env].vars.length ≤ cap := by rw [← capEq]; exact fields.bound
  let P : Nat → Prop := fun k => mA[k]? = after.σ.mem[k]?
  have agreement : AgreeP P mA after.σ.mem := fun _ hk => hk
  have ready := entry.arrays.replaceArrays entry.heap.store valid valuesRead
    h.core.namesRead h.core.valsRead (by have := h.namesAligned; omega)
    (by have := h.valuesAligned; omega) agreement
    (fun role q n h1 h2 h3 allocated k hk => (h.off.other role q n h1 h2 h3 allocated k hk).symm)
    (fun k hk => (h.off.sharedOff k hk).symm)
    (fun i hi k hk => h.core.values i (by omega) k hk)
  refine
    { heap := h.heap, repr := h.head.facts.store, arrays := ready
      geometry := entry.geometry, parents := entry.parents
      ainv := L.ainvAt_of_state h.head.regs.gp h.head.regs.ainv
      budget := h.budget
      reserve := h.reserve }

/-- Execute grow or initial allocation at the caller's actual value slot. -/
theorem envDefineGrowAllocator_run
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (name : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) (mA : Mem)
    (alloc : Allocations) (shared : Nat → Prop) (credits cap pn pvals : Nat) (before : Config)
    (geometry : EnvDefineGrowGeometry A SL esp pv)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (F : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m exts mA cap)
    (R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M exts mA F.env_lt before)
    (entry : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 2) st.store mA)
    (owned : ValueOwned mA shared pv.toNat v)
    (nameOwned : SharedCString mA shared aName.toNat name)
    (support : EvalCallSupport mA SL A esp)
    (full : (st.store.frames[env]'F.env_lt).vars.length = cap)
    (namesRead : read64 mA (phiF env + 8) = some pn)
    (valuesRead : read64 mA (phiF env + 16) = some pvals)
    (request : 48 * cap ≤ maxReq) (kind : EnvDefineGrowKind cap before)
    (namesReg : before.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn)) :
    ∃ after exts' cap' pn' pvals', Steps before after ∧
      EnvDefineAppendAllocatorPost g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        ((alloc.insert (.names env) pn' (8 * cap')).insert (.values env) pvals' (24 * cap'))
        exts' shared credits cap' after ∧ AgreeP shared mA after.σ.mem := by
  obtain ⟨after, exts', cap', pn', pvals', post⟩ :=
    envDefineGrowLaneOwnedAt g N A SL phiF phiC st env name v esp aEnv aName pv r m out M exts
      mA cap pn pvals before geometry L F R full namesRead valuesRead request kind namesReg entry.budget entry.reserve
      alloc shared InitialReadableByte (InitialWriteByte SL) entry.heap
      (fun k lo hi => Or.inr ⟨lo, hi⟩) owned nameOwned
  have sharedAgreement : AgreeP shared mA after.σ.mem := fun k hk => (post.off.sharedOff k hk).symm
  let P : Nat → Prop := fun k => mA[k]? = after.σ.mem[k]?
  have agreement : AgreeP P mA after.σ.mem := fun _ hk => hk
  refine ⟨after, exts', cap', pn', pvals', post.steps,
    { head := post.head, allocator := post.allocator L entry F.cap_read valuesRead
      owned := owned.transport agreement (fun k hk => (post.off.slot k hk).symm) sharedAgreement
      nameOwned := nameOwned.transport sharedAgreement
      support := ?_ }, sharedAgreement⟩
  apply support.transport
  intro k hk
  exact post.off.offArena k (support.outsideArena hk)
    (fun bad => support.outsideStack hk ⟨bad.1, by have := geometry.stack.2.1; omega⟩)

#print axioms EnvDefineGrowHeapPost.allocator
#print axioms envDefineGrowAllocator_run

end Vsa.Sim
