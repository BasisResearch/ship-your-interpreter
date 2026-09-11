import Vsa.Sim.CallArgRun
import Vsa.Sim.CallArgReturnOwned
import Vsa.Sim.AllocatorResultBind

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- One completed argument iteration retains all values at the child's selected maps. -/
structure Advanced (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (entryF entryC : Addr → Nat) (nf nc : Nat)
    (entryShared : Nat → Prop) (reserve : Nat) (st : Vsa.While.St)
    (prior : List (Nat × Value)) (value : Value) (node sp interp env : BitVec 64)
    (index count : Nat) (more : Bool) (m0 : Mem) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (CallArgReturn.nextPC more)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(2, sp), (8, node), (18, interp), (13, env),
    (15, BitVec.ofNat 64 count), (16, BitVec.ofNat 64 (index + 1))]
  more_iff : more = true ↔ index + 1 < count
  selected : ∃ resultF resultC,
    ReturnRepr N A entryF entryC resultF resultC nf nc st.store (prior ++ [(CallArgReturn.slot sp index, value)])
      (AllocatorResult M N entryShared reserve st.store (prior ++ [(CallArgReturn.slot sp index, value)]) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv
  support : EvalCallSupport after.σ.mem SL A sp
  presence : MemExtends before.σ.mem after.σ.mem
  frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R
  memoryFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat + 32) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    ¬ ((sp + 64#64).toNat ≤ k ∧ k < (sp + 64#64).toNat + 24) →
    ¬ (CallArgReturn.slot sp index ≤ k ∧ k < CallArgReturn.slot sp index + 24) →
      before.σ.mem[k]? = after.σ.mem[k]?
  out : OutRepr after.σ st

/-- Execute staging, owned child evaluation, value copy, and the loop back edge. -/
theorem Input.iterate
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {entryF entryC middleF middleC : Addr → Nat}
    {nf nc : Nat} {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {cost request reserve : Nat} {st final : Vsa.While.St} {d env : Nat} {e : Expr} {value : Value}
    {prior : List (Nat × Value)} {m0 : Mem} {node sp interp base child : BitVec 64}
    {index count : Nat} {before : Config}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop} {firstWrites : Nat → Prop}
    (I : Input SL A middleF st d env e node sp interp base child index count before)
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (window : BinaryPrefix.Window SL sp)
    (data : AllocatorResultAt M N entryShared (cost + reserve) st.store prior m0
      middleF middleC alloc exts shared before.σ.mem)
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc st.store prior FirstOwned firstWrites before.σ.mem)
    (sizeF : nf ≤ st.store.frames.size) (sizeC : nc ≤ st.store.closures.size)
    (priorBound : ∀ a v, (a, v) ∈ prior → ValueClosuresBounded st.store.closures.size v)
    (priorWindow : ∀ a v, (a, v) ∈ prior → sp.toNat + 96 ≤ a ∧ a + 24 ≤ sp.toNat + 1056)
    (priorOff : ∀ a v, (a, v) ∈ prior → a + 24 ≤ CallArgReturn.slot sp index ∨ CallArgReturn.slot sp index + 24 ≤ a)
    (ast : ExprReprWithin before.σ.mem shared child.toNat e)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (ih : EvalAllocatorAt N st d env e final value cost request) :
    ∃ after more, Steps before after ∧ Advanced N M entryF entryC nf nc entryShared reserve final prior value
      node sp interp (BitVec.ofNat 64 (middleF env)) index count more m0 before after := by
  obtain ⟨returned, childSteps, evaluated⟩ := I.evaluate L requestBound data.allocator ast gp ih
  obtain ⟨resultF, resultC, second⟩ := evaluated.selected
  have buffer : (sp + 64#64).toNat = sp.toNat + 64 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := I.geometry.caller.stackHi; change sp.toNat + 64 < 2^64; omega)]
    rfl
  have headers : ∀ a v, (a, v) ∈ prior → ∀ k, valHeader a k → before.σ.mem[k]? = returned.σ.mem[k]? := by
    intro a v member k hk
    have bounds := priorWindow a v member
    change a ≤ k ∧ k < a + 24 at hk
    apply evaluated.memoryFrame k (by omega)
    · have := L.arena_stack; have := window.lo; have := window.hi; omega
    · rw [buffer]; omega
  have combined := data.bind_return first second sizeF sizeC priorBound childSteps headers
  obtain ⟨after, more, copySteps, copied⟩ := CallArgReturn.run
    { good := evaluated.good, tick := evaluated.tick, pc := evaluated.pc, spReg := evaluated.spReg
      geometry := I.geometry, saved := evaluated.saved, code := evaluated.support.image.text.Eval_exprLoaded }
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → returned.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply copied.outside k
    unfold CallArgReturn.slot
    have := window.lo; have := window.hi; have := I.geometry.indexBound; have := I.geometry.countBound
    omega
  have abi : ∀ R, AbiPreservedNoise R → AbiPreserved R = true := by intro R; cases R <;> decide
  have frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R :=
    fun R hr => (copied.frame R (abi R hr)).trans (evaluated.frame R hr)
  obtain ⟨_, nodeReg, _, _, interpReg, _, _⟩ := I.regs
  obtain ⟨spReg, envReg, indexReg, countReg, _⟩ := copied.regs
  refine ⟨after, more, childSteps.trans copySteps,
    { good := copied.good, tick := copied.tick, pc := copied.pc, minstret := copied.minstret
      regs := ⟨spReg, (frame .x8 (by decide)).trans nodeReg, (frame .x18 (by decide)).trans interpReg,
        envReg, countReg, indexReg, trivial⟩
      more_iff := copied.more_iff
      selected := ⟨resultF, resultC, copied.owned I.geometry L window priorOff combined⟩
      gp := (copied.frame .x3 (by decide)).trans evaluated.gp
      support := evaluated.support.transport_stack (fun k hk => (stackFrame k hk).symm)
      presence := evaluated.presence.trans (by rw [copied.memory]; exact memExtends_writeLog _ _)
      frame := frame
      memoryFrame := fun k hs ha hb hc => (evaluated.memoryFrame k hs ha hb).trans (copied.outside k hc)
      out := by simpa [OutRepr, output, copied.output] using evaluated.out }⟩

end Vsa.Sim.CallArgStage
