import Vsa.Sim.ClosureParamDefineEmpty
import Vsa.Sim.EnvDefineAppendComplete

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The first parameter executes env_define through its actual return to the fold. -/
theorem OwnedPost.define_empty_return
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared (credits + 3) st.store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
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
      EnvDefineReturnState (fun R => called.σ.regs.get? R) N A SL phiF phiC st target param value
        sp 0x80003314#64 called.σ.mem called.σ.sailOutput after ∧
      AgreeP shared called.σ.mem after.σ.mem := by
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
  obtain ⟨after, appendSteps, returned, appendAgreement⟩ :=
    grown.return_append L geometry align request present bounded
  exact ⟨after, growSteps.trans appendSteps, returned,
    fun k hk => (growAgreement k hk).trans (appendAgreement k hk)⟩

#print axioms OwnedPost.define_empty_return

end Vsa.Sim.ClosureParam
