import Vsa.Sim.ClosureParamStage
import Vsa.Sim.EnvDefinePrologueAllocator

namespace Vsa.Sim.ClosureParam

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Enter env_define from the actual closure staging result and its sp+64 value. -/
theorem OwnedPost.run_prologue
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store} {value : Value} {param : String}
    {sp cursor index scope closure name : BitVec 64} {before called : Config} {target : Addr}
    (h : OwnedPost N M phiF phiC alloc exts shared credits store value param
      sp cursor index scope closure name before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (valid : target < store.frames.size) (scopeAddr : scope.toNat = phiF target)
    (stack : StackOK SL sp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo) (bufferHi : sp.toNat + 88 ≤ SL.hi)
    (support : EvalCallSupport before.σ.mem SL A sp)
    (present : EnvDefineSavedPresent (fun R => called.σ.regs.get? R)) :
    ∃ after, Steps called after ∧
      EnvDefinePrologueAllocatorPost (fun R => called.σ.regs.get? R)
        sp scope name (sp + 64#64) 0x80003314#64 called.σ.mem called.σ.sailOutput N M
        phiF phiC alloc exts shared credits store target valid param value after := by
  have slot : (sp + 64#64).toNat = sp.toNat + 64 := by
    have ramHi := stackRam.2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 64 < 2^64), Nat.mod_eq_of_lt (by omega)]
  have regs : GHolds called.σ [(2, sp), (10, scope), (11, name), (12, sp + 64#64)] :=
    gholds_selected (by repeat' constructor) h.call.regs
  obtain ⟨spReg, envReg, nameReg, valueReg, _⟩ := regs
  have entry : EnvDefineProloguePre (fun R => called.σ.regs.get? R)
      sp scope name (sp + 64#64) 0x80003314#64 called.σ.mem called.σ.sailOutput called :=
    { good := h.call.good, tick := h.call.tick, pc := h.call.pc
      mem := rfl, out := rfl, sp := spReg, a0 := envReg, a1 := nameReg, a2 := valueReg
      ra := h.call.ra, frame := fun _ _ => rfl }
  exact envDefinePrologueAllocator_run L entry h.allocator valid scopeAddr
    (by rw [slot]; exact h.word) (by rw [slot]; exact h.owned) h.name
    (by rw [slot]; omega) stack stackRam stackWin
    (support.transport_stack (fun k hk => (h.stackFrame k hk).symm)) present h.gp (by decide)

#print axioms OwnedPost.run_prologue

end Vsa.Sim.ClosureParam
