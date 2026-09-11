import Vsa.Sim.EnvDefineNameCopyInput
import Vsa.Sim.MemcpyCopyRun

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The copied name and caller ownership at the actual append-store entry. -/
structure EnvDefineNameCopied
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (name : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits cap p : Nat)
    (after : Config) : Prop where
  facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
    exts after.σ.mem cap
  regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
    ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after
  pc : after.σ.regs.get? Register.PC = some 0x80002b44#64
  savedCopyReg : after.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 p)
  copiedName : CString after.σ.mem p name
  block : MallocBlock A exts (name.length + 1) p
  allocator : RuntimeAllocatorState M N phiF phiC alloc ((p, name.length + 1) :: exts)
    shared credits st.store after.σ.mem
  baseHeap : HeapOwned A exts after.σ.mem phiF phiC alloc shared
    InitialReadableByte (InitialWriteByte SL) st.store
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared aName.toNat name
  support : EvalCallSupport after.σ.mem SL A esp

/-- Execute the complete name copy and retain the caller's owned append input. -/
theorem EnvDefineNameCopyReady.copy_return
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap p : Nat} {origin before : Config}
    (h : EnvDefineNameCopyReady g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      alloc exts shared credits cap p origin before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp pv) :
    ∃ after, Steps before after ∧
      EnvDefineNameCopied g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        alloc exts shared credits cap p after ∧ AgreeP shared origin.σ.mem after.σ.mem := by
  obtain ⟨bs, source, input⟩ := h.copyInput L
  have ptrNat := h.block.toNat L.arena_hi
  have align : (BitVec.ofNat 64 p).toNat % 8 = 0 := by
    rw [ptrNat]
    have := h.block.align
    omega
  obtain ⟨after, steps, C⟩ := MemcpyCopy.run input align (by decide)
  have copiedName : CString after.σ.mem p name := by
    simpa only [ptrNat] using C.state.nameString h.nameOwned.repr source
  let P : Nat → Prop := fun k => ¬ ExtentByte (p, name.length + 1) k
  have agreement : AgreeP P before.σ.mem after.σ.mem := by
    intro k hk
    apply Eq.symm (C.state.meminv.outside k ?_)
    rw [ptrNat]
    change ¬ (p ≤ k ∧ k < p + (name.length + 1)) at hk
    omega
  have allocatedOff : ∀ role q n, Allocated alloc role q n → ∀ k, ExtentByte (q, n) k → P k := by
    intro role q n allocated k within freshByte
    have separate := h.block.fresh (q, n) (h.baseHeap.ledger.live role q n allocated)
    change p + (name.length + 1) ≤ q ∨ q + n ≤ p at separate
    change q ≤ k ∧ k < q + n at within
    change p ≤ k ∧ k < p + (name.length + 1) at freshByte
    omega
  have sharedOff : ∀ k, shared k → P k :=
    h.baseHeap.reserved.outsideFresh h.block.arena h.block.fresh
  have arena := h.block.arena
  change A.lo ≤ p ∧ p + (name.length + 1) ≤ A.hi at arena
  have arenaOff : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → P k := by
    intro k off within
    change p ≤ k ∧ k < p + (name.length + 1) at within
    exact off ⟨by omega, by omega⟩
  have stackOff : ∀ k, SL.lo ≤ k → k < SL.hi → P k := by
    intro k lo hi
    apply arenaOff k
    have := L.arena_stack
    omega
  have slotOff : ∀ k, valHeader pv.toNat k → P k := by
    intro k hk
    unfold valHeader at hk
    have := geometry.slot_above
    have := geometry.slot_in_stack
    have := geometry.stack.1
    apply stackOff k <;> omega
  have sharedAgreement : AgreeP shared before.σ.mem after.σ.mem :=
    fun k hk => agreement k (sharedOff k hk)
  have value := h.owned.transport agreement slotOff sharedOff
  have nameAfter := h.nameOwned.transport sharedAgreement
  have baseHeap := h.baseHeap.transport agreement allocatedOff sharedOff
  have store := h.baseHeap.store.repr_transport h.facts.store agreement allocatedOff sharedOff
  have arrays := h.allocator.arrays.transport h.baseHeap.store agreement allocatedOff sharedOff
  have privateOff : ∀ k, M.privFoot k → P k := by
    intro k privateByte within
    change p ≤ k ∧ k < p + (name.length + 1) at within
    have forbidden := M.privFoot_disjoint before.σ _ h.regs.ainv
      (p, name.length + 1) List.mem_cons_self (k - p) (by omega)
    rw [show p + (k - p) = k by omega] at forbidden
    exact forbidden privateByte
  have runtime : RuntimeAllocatorState M N phiF phiC alloc ((p, name.length + 1) :: exts)
      shared credits st.store after.σ.mem :=
    { h.allocator with
      heap := h.allocator.heap.transport agreement allocatedOff sharedOff
      repr := store, arrays := arrays
      ainv := L.ainvAt_transport h.allocator.ainv (fun k hk => agreement k (privateOff k hk))
      reserve := h.allocator.reserve.after_live
        (fun k off => agreement k (off (p, name.length + 1) List.mem_cons_self))
        (fun e he => (h.allocator.heap.ledger.arena.1 e he).2) L.arena_globals }
  have support : EvalCallSupport after.σ.mem SL A esp :=
    h.support.transport (fun k hk => (agreement k (arenaOff k (h.support.outsideArena hk))).symm)
  have word : ValueWordRepr after.σ.mem N phiC pv.toNat v :=
    ⟨valueRepr_agreeP agreement slotOff (h.owned.covered sharedOff) h.facts.word.repr,
      valueWordsTotal_transport h.facts.word.words agreement slotOff⟩
  have record := h.baseHeap.store.frameFootprint allocatedOff sharedOff h.facts.env_lt
  have capEq := (extent_covers record.header (by decide : 4 + 4 ≤ 32)).read32_eq agreement
  have facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
      exts after.σ.mem cap :=
    { h.facts with text := support.image.text, store := store
                   owned := ⟨alloc, shared, InitialReadableByte, InitialWriteByte SL, baseHeap,
                     fun _ lo hi => Or.inr ⟨lo, hi⟩, value, nameAfter⟩
                   word := word, cap_read := capEq.symm.trans h.facts.cap_read
                   names_align := arrays.namesAligned env h.facts.env_lt
                   vals_align := arrays.valuesAligned env h.facts.env_lt
                   mem_agree := fun k ha hs =>
                     (agreement k (arenaOff k ha)).symm.trans (h.facts.mem_agree k ha hs)
                   mem_extends := h.facts.mem_extends.trans C.presence }
  have stackLo := geometry.stack.1
  have stackHi := geometry.stack.2.1
  have sp64 := sp_sub64_toNat esp (by omega)
  have saved := h.regs.saved.of_interval_agree
    (fun k lo hi => by
      apply Eq.symm (agreement k (arenaOff k ?_))
      have := geometry.arena_image
      omega)
    (fun k lo hi => by
      apply Eq.symm (agreement k (stackOff k ?_ ?_)) <;> rw [sp64] at lo hi <;> omega)
  have regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
      ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after :=
    { good := C.state.good, tick := C.state.tick, mem := rfl
      out := C.output.trans h.regs.out, minstret := C.state.good.minstret
      sp := (C.frame _ (by decide)).trans h.regs.sp
      gp := (C.frame _ (by decide)).trans h.regs.gp
      s2 := (C.frame _ (by decide)).trans h.regs.s2
      s3 := (C.frame _ (by decide)).trans h.regs.s3
      s4 := (C.frame _ (by decide)).trans h.regs.s4
      s5 := (C.frame _ (by decide)).trans h.regs.s5
      rest := fun reg abi restored notSp => (C.frame reg abi).trans (h.regs.rest reg abi restored notSp)
      saved := saved, stack := h.regs.stack
      ainv := AllocLedger.ainvAt_at_state runtime.ainv ((C.frame _ (by decide)).trans h.regs.gp) rfl }
  exact ⟨after, steps,
    { facts := facts, regs := regs, pc := C.state.pc
      savedCopyReg := (C.frame _ (by decide)).trans h.savedCopyReg
      copiedName := copiedName, block := h.block, allocator := runtime, baseHeap := baseHeap
      owned := value, nameOwned := nameAfter, support := support },
    fun k hk => (h.agreement k hk).trans (sharedAgreement k hk)⟩

#print axioms EnvDefineNameCopyReady.copy_return

end Vsa.Sim
