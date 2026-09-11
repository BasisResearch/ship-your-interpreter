import Vsa.Sim.EnvDefineAppendComplete
import Vsa.Sim.BindingArena
import Vsa.Sim.AllocatorResult

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Install the copied name in the runtime ledger and retain the remaining reserve. -/
theorem EnvDefineNameAppended.allocator
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {name : String} {v : Value}
    {esp env namePtr src r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap p names vals : Nat} {before after : Config}
    (h : EnvDefineNameCopied g N A SL phiF phiC st target name v esp env namePtr src r m out M
      alloc exts shared credits cap p before)
    (post : EnvDefineNameAppended g N A SL phiF phiC st target h.facts.env_lt name v esp env src r M
      exts shared cap p names vals before after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (placement : BindingArena A SL) (geometry : EnvDefineGrowGeometry A SL esp src)
    (bounded : ValueClosuresBounded st.store.closures.size v)
    (room : (st.store.frames[target]'h.facts.env_lt).vars.length < cap) :
    RuntimeAllocatorState M N phiF phiC
      (alloc.insert (.binding target (st.store.frames[target]'h.facts.env_lt).vars.length) p (name.length + 1))
      ((p, name.length + 1) :: exts) (BindingShared shared p (name.length + 1)) credits
      (st.store.define target name v) after.σ.mem := by
  have F := h.facts
  have ptrNat := h.block.toNat L.arena_hi
  have arena : A.contains (BitVec.ofNat 64 p).toNat (name.length + 1) := by
    rw [ptrNat]; exact h.block.arena
  have fresh : ∀ e ∈ exts, ExtDisjoint ((BitVec.ofNat 64 p).toNat, name.length + 1) e := by
    rw [ptrNat]; exact h.block.fresh
  have readableNew : ∀ k, ExtentByte ((BitVec.ofNat 64 p).toNat, name.length + 1) k → InitialReadableByte k := by
    intro k hk
    obtain ⟨lo, hi⟩ := arena
    obtain ⟨lower, upper⟩ := hk
    have ram := L.arena_ram
    exact ⟨by omega, by omega⟩
  have heap := post.returned.toEnvDefineAppendMemory.heap_owned h.baseHeap F.env_addr F.cap_read
    post.namesRead post.valuesRead room F.miss h.owned bounded arena fresh readableNew
    (fun _ hk => placement.outsideWrites arena hk)
  have gp : after.σ.regs.get? Register.x3 = some gpv :=
    (post.returned.rest .x3 (by decide) (by decide) (by decide)).trans h.regs.gp
  have frame := h.allocator.heap.store.frames target F.env_lt
  obtain ⟨a, fields⟩ := frame.arrays
  have capEq := Option.some.inj (fields.capRead.symm.trans F.cap_read)
  have namesEq := Option.some.inj (fields.namesRead.symm.trans post.namesRead)
  have valuesEq := Option.some.inj (fields.valuesRead.symm.trans post.valuesRead)
  have namesAllocated : Allocated alloc (.names target) names (8 * cap) := by
    simpa only [capEq, namesEq] using fields.names.nonempty (by omega : 0 < a.cap)
  have valuesAllocated : Allocated alloc (.values target) vals (24 * cap) := by
    simpa only [capEq, valuesEq] using fields.values.nonempty (by omega : 0 < a.cap)
  have reserve : AllocationReserve A after.σ.mem ((p, name.length + 1) :: exts) maxReq credits := by
    apply h.allocator.reserve.after_live ?_
      (fun e he => (h.allocator.heap.ledger.arena.1 e he).2) L.arena_globals
    intro k off
    apply post.returned.toEnvDefineAppendMemory.agreement k
    rw [F.env_addr]
    have namesOff := off (names, 8 * cap)
      (h.allocator.heap.ledger.live _ _ _ namesAllocated)
    have valuesOff := off (vals, 24 * cap)
      (h.allocator.heap.ledger.live _ _ _ valuesAllocated)
    have recordOff := off (phiF target, 32)
      (h.allocator.heap.ledger.live _ _ _ frame.record)
    unfold AppendUntouched
    exact ⟨by omega, by omega, by omega⟩
  exact
    { heap := by simpa only [ptrNat] using heap
      repr := post.store, arrays := post.arrays
      geometry := placement.extend geometry.stack geometry.stack_ram.2 h.allocator.geometry h.block.arena
      parents := StoreParents.define st.store target name v h.allocator.parents
      ainv := L.ainvAt_of_state gp post.ainv
      budget := h.allocator.budget, reserve := reserve }

/-- A helper return keeps one selected runtime and the original shared-byte frame. -/
structure EnvDefineOwnedReturn
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (entryShared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (target : Addr)
    (name : String) (v : Value) (sp r : BitVec 64) (m : Mem) (out : Array String) (after : Config) : Prop where
  exit : EnvDefineReturnState g N A SL phiF phiC st target name v sp r m out after
  result : AllocatorResult M N entryShared credits (st.store.define target name v) [] m phiF phiC after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv

/-- The existing-name return selects its unchanged shared domain in the same result type. -/
theorem EnvDefineAllocatorReturn.ownedReturn
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {st : Vsa.While.St} {target : Addr} {name : String} {v : Value}
    {sp r : BitVec 64} {m : Mem} {out : Array String} {after : Config}
    (h : EnvDefineAllocatorReturn g N M phiF phiC alloc exts shared credits st target name v sp r m out after)
    (gp : after.σ.regs.get? Register.x3 = some gpv) :
    EnvDefineOwnedReturn g N M phiF phiC shared credits st target name v sp r m out after :=
  { exit := h.exit, gp := gp
    result := ⟨alloc, exts, shared,
      { allocator := h.allocator, includes := fun _ hk => hk
        values := fun _ _ member => False.elim (List.not_mem_nil member), agreement := h.agreement }⟩ }

/-- Execute allocation, full copy, append, and return with the enlarged owned runtime. -/
theorem EnvDefineAppendAllocatorPost.return_append_owned
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {name : String} {v : Value}
    {esp env namePtr src r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap : Nat} {before : Config}
    (h : EnvDefineAppendAllocatorPost g N A SL phiF phiC st target name v esp env namePtr src r m out M
      alloc exts shared (credits + 1) cap before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (placement : BindingArena A SL) (geometry : EnvDefineGrowGeometry A SL esp src)
    (sourceAlign : src.toNat % 8 = 0) (request : name.length + 1 ≤ maxReq)
    (present : EnvDefineSavedPresent g)
    (bounded : ValueClosuresBounded st.store.closures.size v)
    (entryAgreement : AgreeP shared m before.σ.mem) :
    ∃ after, Steps before after ∧
      EnvDefineOwnedReturn g N M phiF phiC shared credits st target name v esp r m out after := by
  obtain ⟨called, p, prepareSteps, prepared⟩ := h.prepareCopy L geometry request
  obtain ⟨copied, copySteps, copy, copyAgreement⟩ := prepared.copy_return L geometry
  obtain ⟨after, names, vals, appendSteps, appended⟩ := copy.append L geometry sourceAlign h.head.room
  have allocator := appended.allocator copy L placement geometry bounded h.head.room
  refine ⟨after, prepareSteps.trans (copySteps.trans appendSteps),
    { exit := appended.toReturn copy L present bounded h.head.room
      gp := (appended.returned.rest .x3 (by decide) (by decide) (by decide)).trans copy.regs.gp
      result := ⟨alloc.insert (.binding target (st.store.frames[target]'copy.facts.env_lt).vars.length)
        p (name.length + 1), ((p, name.length + 1) :: exts), BindingShared shared p (name.length + 1), ?_⟩ }⟩
  exact
    { allocator := allocator, includes := fun _ hk => Or.inl hk
      values := fun _ _ member => False.elim (List.not_mem_nil member)
      agreement := fun k hk => (entryAgreement k hk).trans
        ((copyAgreement k hk).trans (appended.agreement k hk)) }

#print axioms EnvDefineNameAppended.allocator
#print axioms EnvDefineAllocatorReturn.ownedReturn
#print axioms EnvDefineAppendAllocatorPost.return_append_owned

end Vsa.Sim
