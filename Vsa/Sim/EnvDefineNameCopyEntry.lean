import Vsa.Sim.EnvDefineNameAllocate

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual copy call carries the fresh destination and owned source bytes. -/
structure EnvDefineNameCopyReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (name : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits cap p : Nat)
    (before after : Config) : Prop where
  facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
    exts after.σ.mem cap
  regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
    ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after
  pc : after.σ.regs.get? Register.PC = some 0x80006bc8#64
  copyReg : after.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  sourceReg : after.σ.regs.get? Register.x11 = some aName
  lengthReg : after.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 (name.length + 1))
  savedCopyReg : after.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 p)
  returnReg : after.σ.regs.get? Register.x1 = some 0x80002b44#64
  sourceGeometry : StrlenReadRegions aName name.length
  disjoint : p + (name.length + 1) ≤ aName.toNat ∨ aName.toNat + (name.length + 1) ≤ p
  block : MallocBlock A exts (name.length + 1) p
  allocator : RuntimeAllocatorState M N phiF phiC alloc ((p, name.length + 1) :: exts)
    shared credits st.store after.σ.mem
  baseHeap : HeapOwned A exts after.σ.mem phiF phiC alloc shared
    InitialReadableByte (InitialWriteByte SL) st.store
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared aName.toNat name
  support : EvalCallSupport after.σ.mem SL A esp
  agreement : AgreeP shared before.σ.mem after.σ.mem
  outside : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < (esp - 64#64).toNat) →
    after.σ.mem[k]? = before.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem

/-- Stage memcpy from the successful name allocation without changing memory. -/
theorem EnvDefineNameAllocated.copy_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap p : Nat} {origin before : Config}
    (h : EnvDefineNameAllocated g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      alloc exts shared credits cap p origin before)
    (L : AllocLedger A SL gpv headroom maxReq M) :
    ∃ after, Steps before after ∧
      EnvDefineNameCopyReady g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        alloc exts shared credits cap p origin after := by
  have ptrNat := h.block.toNat L.arena_hi
  have nonzero : BitVec.ofNat 64 p ≠ 0#64 := by
    intro zero
    have := congrArg BitVec.toNat zero
    rw [ptrNat] at this
    exact h.block.nonzero this
  obtain ⟨after, call⟩ := envDefineMemcpyParked_of (BitVec.ofNat 64 p)
    (BitVec.ofNat 64 (name.length + 1)) aName before nonzero h.regs.good h.pc h.copyReg
    h.sizeReg h.regs.s2 h.facts.text.Env_defineLoaded h.regs.tick
  have facts : EnvDefineMissFacts g N A SL phiF phiC st env name v esp aEnv aName pv r m
      exts after.σ.mem cap := by rw [call.mem]; exact h.facts
  have regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M
      ((p, name.length + 1) :: exts) after.σ.mem facts.env_lt after :=
    { good := call.good, tick := call.tick, mem := rfl, out := call.out.trans h.regs.out
      minstret := call.minstret
      sp := (call.abi _ (by decide)).trans h.regs.sp
      gp := (call.abi _ (by decide)).trans h.regs.gp
      s2 := (call.abi _ (by decide)).trans h.regs.s2
      s3 := (call.abi _ (by decide)).trans h.regs.s3
      s4 := (call.abi _ (by decide)).trans h.regs.s4
      s5 := (call.abi _ (by decide)).trans h.regs.s5
      rest := by
        intro reg abi restored notSp
        obtain ⟨_, _, _, notS1, _⟩ := envDefineRest_facts reg abi restored notSp
        have kept : AbiExceptS1 reg = true := by simp [AbiExceptS1, abi, notS1]
        exact (call.abi reg kept).trans (h.regs.rest reg abi restored notSp)
      saved := h.regs.saved.of_mem_eq call.mem, stack := h.regs.stack
      ainv := AllocLedger.ainvAt_at_state h.allocator.ainv
        ((call.abi _ (by decide)).trans h.regs.gp) call.mem }
  have sourceOutside : ∀ k, k < name.length + 1 →
      ¬ ExtentByte (p, name.length + 1) (aName.toNat + k) := by
    intro k hk
    exact h.baseHeap.reserved.outsideFresh h.block.arena h.block.fresh _
      (h.nameOwned.bytes k (by omega))
  exact ⟨after, call.steps,
    { facts := facts, regs := regs, pc := call.pc, copyReg := call.a0
      sourceReg := call.a1, lengthReg := call.a2, savedCopyReg := call.s1, returnReg := call.ra
      sourceGeometry := h.allocator.geometry.strlenRegions h.nameOwned
      disjoint := windows_disjoint_of_off (by omega) sourceOutside
      block := h.block
      allocator := by rw [call.mem]; exact h.allocator
      baseHeap := by rw [call.mem]; exact h.baseHeap
      owned := by rw [call.mem]; exact h.owned
      nameOwned := by rw [call.mem]; exact h.nameOwned
      support := by rw [call.mem]; exact h.support
      agreement := by intro k hk; rw [call.mem]; exact h.agreement k hk
      outside := by intro k hp hs; rw [call.mem]; exact h.outside k hp hs
      presence := by rw [call.mem]; exact h.presence }⟩

/-- Execute the append prefix through the actual memcpy call entry. -/
theorem EnvDefineAppendAllocatorPost.prepareCopy
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {name : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits cap : Nat} {before : Config}
    (h : EnvDefineAppendAllocatorPost g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
      alloc exts shared (credits + 1) cap before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp pv) (request : name.length + 1 ≤ maxReq) :
    ∃ after p, Steps before after ∧
      EnvDefineNameCopyReady g N A SL phiF phiC st env name v esp aEnv aName pv r m out M
        alloc exts shared credits cap p before after := by
  obtain ⟨allocated, p, allocationSteps, allocation⟩ := h.allocateName L geometry request
  obtain ⟨after, callSteps, ready⟩ := allocation.copy_entry L
  exact ⟨after, p, allocationSteps.trans callSteps, ready⟩

#print axioms EnvDefineAppendAllocatorPost.prepareCopy

#print axioms EnvDefineNameAllocated.copy_entry

end Vsa.Sim
