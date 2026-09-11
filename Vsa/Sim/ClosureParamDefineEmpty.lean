import Vsa.Sim.ClosureParamPrologue
import Vsa.Sim.EnvDefineEmptyAllocator

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The first binding reaches append after allocating the empty frame's arrays. -/
theorem OwnedPost.define_empty_grow
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 2) st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (valid : target < st.store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R))
    (emptyCapacity : read32 called.σ.mem (phiF target + 4) = some 0) :
    ∃ after exts' cap' pn' pvals', Steps called after ∧
      EnvDefineAppendAllocatorPost (fun R => called.σ.regs.get? R) N A SL phiF phiC
        st target param value sp scope name (sp + 64#64) 0x80003314#64
        called.σ.mem called.σ.sailOutput M
        ((alloc.insert (.names target) pn' (8 * cap')).insert (.values target) pvals' (24 * cap'))
        exts' shared credits cap' after ∧ AgreeP shared called.σ.mem after.σ.mem := by
  obtain ⟨ready, prologueSteps, prologue⟩ := h.run_prologue L valid scopeAddr stack
    stackRam stackWin bufferHi support present
  have slot : (sp + 64#64).toNat = sp.toNat + 64 := by
    have ramHi := stackRam.2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 64 < 2^64), Nat.mod_eq_of_lt (by omega)]
  have geometry : EnvDefineGrowGeometry A SL sp (sp + 64#64) :=
    { stack := stack, stack_ram := stackRam, stack_win := stackWin
      slot_above := by rw [slot]; omega
      slot_in_stack := by rw [slot]; exact bufferHi
      arena_image := support.image.arena }
  have ghostSp : called.σ.regs.get? Register.x2 = some sp := by
    show gprGet called.σ 2 = some sp
    exact gholds_lookup _ h.call.regs (by rfl)
  have capacity : read32 ready.σ.mem (phiF target + 4) = some 0 := by
    have copy : ∀ k, k < 4 → ready.σ.mem[phiF target + 4 + k]? =
        called.σ.mem[phiF target + 4 + k]? := by
      intro k hk
      have off := (h.allocator.runtime L).allocated_off_stack
        (h.allocator.heap.store.frames target valid).record
        (k := phiF target + 4 + k) (by change phiF target ≤ _ ∧ _ < phiF target + 32; omega)
      exact (prologue.outside _ (by have := stack.1; have := stack.2.1; omega)).symm
    exact (read32_shift copy).trans emptyCapacity
  obtain ⟨after, exts', cap', pn', pvals', steps, post, agreement⟩ :=
    prologue.empty_grow L geometry scopeAddr ghostSp (by decide) capacity
  exact ⟨after, exts', cap', pn', pvals', prologueSteps.trans steps, post, agreement⟩

#print axioms OwnedPost.define_empty_grow

end Vsa.Sim.ClosureParam
