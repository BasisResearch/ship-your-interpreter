import Vsa.Sim.EnvDefineNameAppend

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The installed binding survives subsequent caller-stack writes. -/
theorem EnvDefineNameAppended.toReturn
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
    (present : EnvDefineSavedPresent g)
    (bounded : ValueClosuresBounded st.store.closures.size v)
    (room : (st.store.frames[target]'h.facts.env_lt).vars.length < cap) :
    EnvDefineReturnState g N A SL phiF phiC st target name v esp r m out after := by
  have F := h.facts
  have ptrNat := h.block.toNat L.arena_hi
  have memory := post.returned.toEnvDefineAppendMemory
  have namesRead := post.namesRead
  have valuesRead := post.valuesRead
  let writes : Nat → Prop := fun k => SL.lo ≤ k ∧ k < SL.hi
  have oldHeap : HeapOwned A exts before.σ.mem phiF phiC alloc shared InitialReadableByte writes st.store :=
    { h.baseHeap with immutable :=
      { h.baseHeap.immutable with outsideWrites := fun k hk hw => h.baseHeap.immutable.outsideWrites k hk (Or.inr hw) } }
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
  have outsideWrites : ∀ k, ExtentByte ((BitVec.ofNat 64 p).toNat, name.length + 1) k → ¬ writes k := by
    intro k hk hw
    obtain ⟨lo, hi⟩ := arena
    obtain ⟨lower, upper⟩ := hk
    have separate := L.arena_stack
    change SL.lo ≤ k ∧ k < SL.hi at hw
    omega
  have heap := memory.heap_owned oldHeap F.env_addr F.cap_read namesRead valuesRead room F.miss
    h.owned bounded arena fresh readableNew outsideWrites
  have survives : ∀ m', (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A phiF phiC (st.store.define target name v) := by
    intro m' agree
    apply heap.store.repr_transport post.store agree
    · intro role q n allocated k within
      have bounds := (heap.ledger.arena.1 _ (heap.ledger.live role q n allocated)).2
      have separate := L.arena_stack
      change A.lo ≤ q ∧ q + n ≤ A.hi at bounds
      change q ≤ k ∧ k < q + n at within
      omega
    · exact heap.immutable.outsideWrites
  have returned := post.returned.returned
  have core : EnvDefineReturnCore g N A SL phiF phiC st target name v esp r m after :=
    { good := returned.good, tick := returned.tick
      pc := by rw [returned.pc, envDefineSaved_x1, Option.getD_some, bitvec_update_self r F.ra_align]
      ra := by rw [returned.ra, envDefineSaved_x1]; rfl
      sp := by rw [returned.spReg, BitVec.sub_add_cancel]
      minstret := returned.good.minstret, restored := returned.restored present
      store := post.store, store_survives := survives
      mem_frame := fun k ha hs => (memory.outsideArena k ha).symm.trans (F.mem_agree k ha hs)
      mem_extends := F.mem_extends.trans memory.presence }
  exact core.toReturn F.g_sp
    { out := post.returned.output.trans h.regs.out, a0 := post.returned.resultReg
      rest := fun R abi unrestored notSp =>
        (post.returned.rest R abi unrestored notSp).trans (h.regs.rest R abi unrestored notSp) }

/-- Execute strlen, allocation, the complete memcpy, append, and caller return. -/
theorem EnvDefineAppendAllocatorPost.return_append
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
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (sourceAlign : src.toNat % 8 = 0) (request : name.length + 1 ≤ maxReq)
    (present : EnvDefineSavedPresent g)
    (bounded : ValueClosuresBounded st.store.closures.size v) :
    ∃ after, Steps before after ∧
      EnvDefineReturnState g N A SL phiF phiC st target name v esp r m out after ∧
      AgreeP shared before.σ.mem after.σ.mem := by
  obtain ⟨called, p, prepareSteps, prepared⟩ := h.prepareCopy L geometry request
  obtain ⟨copied, copySteps, copy, copyAgreement⟩ := prepared.copy_return L geometry
  obtain ⟨after, names, vals, appendSteps, appended⟩ := copy.append L geometry sourceAlign h.head.room
  exact ⟨after, prepareSteps.trans (copySteps.trans appendSteps),
    appended.toReturn copy L present bounded h.head.room,
    fun k hk => (copyAgreement k hk).trans (appended.agreement k hk)⟩

#print axioms EnvDefineNameAppended.toReturn
#print axioms EnvDefineAppendAllocatorPost.return_append

end Vsa.Sim
