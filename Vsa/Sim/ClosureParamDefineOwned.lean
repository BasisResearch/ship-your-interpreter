import Vsa.Sim.ClosureParamDefineEmpty
import Vsa.Sim.ClosureParamDefineHit
import Vsa.Sim.EnvDefineMissOwnedReturn

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The first parameter executes env_define through its actual return to the fold. -/
theorem OwnedPost.define_empty_owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 3) st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (placement : BindingArena A SL)
    (valid : target < st.store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R))
    (emptyCapacity : read32 called.σ.mem (phiF target + 4) = some 0)
    (request : param.length + 1 ≤ maxReq)
    (bounded : ValueClosuresBounded st.store.closures.size value) :
    ∃ after, Steps called after ∧
      EnvDefineOwnedReturn (fun R => called.σ.regs.get? R) N M phiF phiC shared credits st target param value
        sp 0x80003314#64 called.σ.mem called.σ.sailOutput after := by
  obtain ⟨ready, exts', cap', pn', pvals', growSteps, grown, growAgreement⟩ :=
    h.define_empty_grow L valid scopeAddr stack stackRam stackWin bufferHi support present emptyCapacity
  have slot : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 64 < 2^64), Nat.mod_eq_of_lt (by have := stackRam.2; omega)]
  have geometry : EnvDefineGrowGeometry A SL sp (sp + 64#64) :=
    { stack := stack, stack_ram := stackRam, stack_win := stackWin
      slot_above := by rw [slot]; omega
      slot_in_stack := by rw [slot]; exact bufferHi
      arena_image := support.image.arena }
  have align : (sp + 64#64).toNat % 8 = 0 := by
    rw [slot]; have := stack.2.2; omega
  obtain ⟨after, appendSteps, returned⟩ :=
    grown.return_append_owned L placement geometry align request present bounded growAgreement
  exact ⟨after, growSteps.trans appendSteps, returned⟩


/-- A new parameter in a nonempty scope executes scan, optional grow, append, and return. -/
theorem OwnedPost.define_miss_owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 3) st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (placement : BindingArena A SL)
    (valid : target < st.store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R))
    (bounded : ValueClosuresBounded st.store.closures.size value)
    (positive : 0 < (st.store.frames[target]'valid).vars.length)
    (missing : ∀ i (hi : i < (st.store.frames[target]'valid).vars.length),
      ((st.store.frames[target]'valid).vars[i]'hi).1 ≠ param)
    (nameRequest : param.length + 1 ≤ maxReq)
    (growRequest : 48 * (st.store.frames[target]'valid).vars.length ≤ maxReq) :
    ∃ after, Steps called after ∧
      EnvDefineOwnedReturn (fun R => called.σ.regs.get? R) N M phiF phiC shared credits st target param value
        sp 0x80003314#64 called.σ.mem called.σ.sailOutput after := by
  obtain ⟨ready, prologueSteps, prologue⟩ := h.run_prologue L valid scopeAddr stack
    stackRam stackWin bufferHi support present
  have slot : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 64 < 2^64), Nat.mod_eq_of_lt (by have := stackRam.2; omega)]
  have geometry : EnvDefineGrowGeometry A SL sp (sp + 64#64) :=
    { stack := stack, stack_ram := stackRam, stack_win := stackWin
      slot_above := by rw [slot]; omega
      slot_in_stack := by rw [slot]; exact bufferHi
      arena_image := support.image.arena }
  have align : (sp + 64#64).toNat % 8 = 0 := by
    rw [slot]; have := stack.2.2; omega
  have ghostSp : called.σ.regs.get? Register.x2 = some sp := by
    show gprGet called.σ 2 = some sp
    exact gholds_lookup _ h.call.regs (by rfl)
  obtain ⟨after, returnSteps, returned⟩ := prologue.return_miss_owned L placement geometry scopeAddr ghostSp
    (by decide) align present bounded positive missing nameRequest growRequest
  exact ⟨after, prologueSteps.trans returnSteps, returned⟩


/-- Execute an existing parameter binding from the actual sp+64 call through its return. -/
theorem OwnedPost.define_hit_owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (valid : target < st.store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R))
    (unique : FrameUnique st.store.frames[target])
    (bounded : ValueClosuresBounded st.store.closures.size value)
    (hasName : ∃ i, ∃ hi : i < st.store.frames[target].vars.length,
      st.store.frames[target].vars[i].1 = param) :
    ∃ after, Steps called after ∧
      EnvDefineOwnedReturn (fun R => called.σ.regs.get? R) N M phiF phiC shared credits
        st target param value sp 0x80003314#64 called.σ.mem called.σ.sailOutput after := by
  obtain ⟨after, steps, returned⟩ := h.define_hit L valid scopeAddr stack stackRam stackWin
    bufferHi support present unique bounded hasName
  exact ⟨after, steps, returned.ownedReturn ((returned.exit.frame .x3 (by decide)).trans h.gp)⟩

#print axioms OwnedPost.define_hit_owned

#print axioms OwnedPost.define_empty_owned
#print axioms OwnedPost.define_miss_owned

end Vsa.Sim.ClosureParam
