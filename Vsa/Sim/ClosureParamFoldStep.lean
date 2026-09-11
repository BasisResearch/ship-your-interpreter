import Vsa.Sim.ClosureParamFoldReturn

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The current prefix store, owned argument array, and live parameter-loop registers. -/
structure FoldStepInput
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (N : NativeAddrs) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (target : Addr) (sp scope closure names savedS6 : BitVec 64)
    (params : List String) (values : List Value) (index : Nat) (before : Config) : Prop where
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 3) st.store before.σ.mem
  data : FoldData before.σ.mem N phiC shared sp closure names params values
  indexLt : index < values.length
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x800032dc#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (callClosureFoldStageL sp
    (BitVec.ofNat 64 (sp.toNat + 240 + 24 * index)) (BitVec.ofNat 64 (8 * index)) scope closure)
  bound : before.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 (8 * values.length))
  savedRead : read64 before.σ.mem (sp.toNat + 1024) = some savedS6.toNat
  gp : before.σ.regs.get? Register.x3 = some gpv
  present : EnvDefineSavedPresent (fun R => before.σ.regs.get? R)
  support : EvalCallSupport before.σ.mem SL A sp
  stack : StackOK SL sp 1088
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stackWin : tohostAddr + 16 ≤ SL.lo
  stackHi : sp.toNat + 1032 ≤ SL.hi
  valid : target < st.store.frames.size
  scopeAddr : scope.toNat = phiF target
  unique : FrameUnique st.store.frames[target]
  bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i]
  emptyCapacity : st.store.frames[target].vars.length = 0 →
    read32 before.σ.mem (phiF target + 4) = some 0
  nameRequest : ∀ param ∈ params, param.length + 1 ≤ maxReq
  growRequest : 48 * st.store.frames[target].vars.length ≤ maxReq

/-- Execute one parameter from its array cell through the actual loop branch. -/
theorem FoldStepInput.run
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St}
    {sp scope closure names savedS6 : BitVec 64} {before : Config} {target index : Nat}
    {params : List String} {values : List Value}
    (h : FoldStepInput M N phiF phiC alloc exts shared credits st target
      sp scope closure names savedS6 params values index before)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL) :
    ∃ after returned alloc' exts' shared', Steps before after ∧
      FoldReturnAt M N phiF phiC shared credits
        (st.store.define target (params[index]'(by have := h.data.arity; have := h.indexLt; omega))
          (values[index]'h.indexLt)) alloc' exts' shared'
        sp (BitVec.ofNat 64 (sp.toNat + 240 + 24 * index)) scope closure names savedS6 params values
        index (decide (index + 1 < values.length)) before returned after := by
  have stackLo : SL.lo ≤ sp.toNat := by have := h.stack.1; omega
  have valid := h.valid
  have geometry : ClosureEnvNewResume.Geometry sp :=
    { lo := by have := h.stack.1; have := h.stackRam.1; omega
      hi := by have := h.stackHi; have := h.stackRam.2; omega
      htif := by have := h.stack.1; have := h.stackWin; omega
      align := by have := h.stack.2.2; omega }
  have bufferHi : sp.toNat + 88 ≤ SL.hi := by have := h.stackHi; omega
  obtain ⟨name, selected⟩ := h.data.select h.allocator.heap.immutable geometry stackLo h.stackHi
    (by have := h.support.code_stack; have := h.stack.1; omega) index h.indexLt
    h.good h.tick h.pc h.minstret h.regs h.support.image.text.Eval_exprLoaded
  obtain ⟨called, stageSteps, staged⟩ := ClosureParam.run selected.pre
  have owned := staged.owned L h.allocator selected.argument selected.owned selected.name
    stackLo bufferHi h.gp
  have present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have reg : gprGet called.σ 8 = some (BitVec.ofNat 64 (sp.toNat + 240 + 24 * index) + 24#64) :=
        gholds_lookup _ staged.regs (by rfl)
      change (gprGet called.σ 8).isSome = true
      rw [reg]; rfl
    · rw [staged.frame .x9 (by decide) (by decide) (by decide)]; exact h.present.s1
    · rw [staged.frame .x18 (by decide) (by decide) (by decide)]; exact h.present.s2
    · have reg : gprGet called.σ 19 = some scope := gholds_lookup _ staged.regs (by rfl)
      change (gprGet called.σ 19).isSome = true
      rw [reg]; rfl
    · rw [staged.frame .x20 (by decide) (by decide) (by decide)]; exact h.present.s4
    · have reg : gprGet called.σ 21 = some closure := gholds_lookup _ staged.regs (by rfl)
      change (gprGet called.σ 21).isSome = true
      rw [reg]; rfl
    · rw [staged.frame .x22 (by decide) (by decide) (by decide)]; exact h.present.s6
  have emptyCapacity : st.store.frames[target].vars.length = 0 →
      read32 called.σ.mem (phiF target + 4) = some 0 := by
    intro empty
    have arena := (h.allocator.repr.frames_arena target h.valid).1
    have agreement : AgreeP (fun k => A.lo ≤ k ∧ k < A.hi) before.σ.mem called.σ.mem := by
      intro k hk
      exact owned.stackFrame k (by have := L.arena_stack; omega)
    have read := read32_agreeP agreement (a := phiF target + 4) (by
      intro k hk
      rcases arena with ⟨lo, hi⟩
      omega)
    exact read.symm.trans (h.emptyCapacity empty)
  obtain ⟨returned, defineSteps, exit⟩ := owned.define_next_owned L placement h.valid h.scopeAddr
    h.stack h.stackRam h.stackWin bufferHi h.support present h.unique
    (h.bounded index h.indexLt) emptyCapacity
    (h.nameRequest _ (List.getElem_mem _)) h.growRequest
  obtain ⟨after, alloc', exts', shared', resumeSteps, result⟩ := owned.resume_fold h.data exit geometry
    stackLo h.stackHi L.arena_stack h.bound h.savedRead h.indexLt h.support
  exact ⟨after, returned, alloc', exts', shared', stageSteps.trans (defineSteps.trans resumeSteps), result⟩

end Vsa.Sim.ClosureParam
