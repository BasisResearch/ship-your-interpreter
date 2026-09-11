import Vsa.Sim.ClosureParamPrologue
import Vsa.Sim.EnvDefineAllocatorReturn

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Execute an existing parameter binding from the actual sp+64 call through its return. -/
theorem OwnedPost.define_hit
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
      EnvDefineAllocatorReturn (fun R => called.σ.regs.get? R) N M phiF phiC alloc exts shared credits
        st target param value sp 0x80003314#64 called.σ.mem called.σ.sailOutput after := by
  obtain ⟨ready, prologueSteps, prologue⟩ := h.run_prologue L valid scopeAddr stack
    stackRam stackWin bufferHi support present
  have slot : (sp + 64#64).toNat = sp.toNat + 64 := by
    have ramHi := stackRam.2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 64 < 2^64), Nat.mod_eq_of_lt (by omega)]
  have source : RetSlotGeom SL (sp - 64#64) (sp + 64#64) := by
    obtain ⟨lo, top, align⟩ := stack
    obtain ⟨ramLo, ramHi⟩ := stackRam
    have spNat := sp_sub64_toNat sp (by omega : 64 ≤ sp.toNat)
    refine
      { align := ?_, ram := ?_, win := ?_, scribble_disjoint := ?_, inSL := ?_ }
    all_goals rw [slot]
    · omega
    · constructor <;> omega
    · omega
    · right; rw [spNat]; omega
    · constructor <;> omega
  have ghostSp : called.σ.regs.get? Register.x2 = some sp := by
    show gprGet called.σ 2 = some sp
    exact gholds_lookup _ h.call.regs (by rfl)
  obtain ⟨after, returnSteps, returned⟩ := prologue.return_hit L scopeAddr stack source
    present ghostSp (by decide) unique bounded hasName
  exact ⟨after, prologueSteps.trans returnSteps, returned⟩

#print axioms OwnedPost.define_hit

end Vsa.Sim.ClosureParam
