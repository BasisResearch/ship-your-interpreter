import Vsa.Sim.CallArgLoopState

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Recursive child contracts in the source argument evaluation order. -/
inductive Arguments (N : NativeAddrs) (d env request : Nat) :
    Vsa.While.St → List Expr → Vsa.While.St → List Value → Nat → Prop where
  | nil (st : Vsa.While.St) : Arguments N d env request st [] st [] 0
  | cons {st middle final : Vsa.While.St} {e : Expr} {es : List Expr} {value : Value} {values : List Value}
      {cost tailCost : Nat} :
      EvalE st d env e middle value → EvalAllocatorAt N st d env e middle value cost request →
      Arguments N d env request middle es final values tailCost →
      Arguments N d env request st (e :: es) final (value :: values) (cost + tailCost)

/-- The physical destination for every returned argument, in source order. -/
def argumentSlots (sp : BitVec 64) : Nat → List Value → List (Nat × Value)
  | _, [] => []
  | index, value :: values => (CallArgReturn.slot sp index, value) :: argumentSlots sp (index + 1) values

theorem LoopFrame.refl (SL : StackLayout) (A : Arena) (sp : BitVec 64) (cfg : Config) :
    LoopFrame SL A sp cfg cfg := ⟨fun _ b h => ⟨b, h⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem LoopFrame.trans {SL : StackLayout} {A : Arena} {sp : BitVec 64} {before middle after : Config}
    (first : LoopFrame SL A sp before middle) (second : LoopFrame SL A sp middle after) :
    LoopFrame SL A sp before after :=
  ⟨first.presence.trans second.presence, fun R h => (second.regs R h).trans (first.regs R h),
    fun k hs ha => (first.memory k hs ha).trans (second.memory k hs ha)⟩

/-- Run the complete remaining argument list and reach closure dispatch with every owned value. -/
theorem Arguments.run
    {N : NativeAddrs} {d env request : Nat} {st final : Vsa.While.St}
    {es : List Expr} {values : List Value} {cost : Nat}
    (children : Arguments N d env request st es final values cost)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {entryF entryC : Addr → Nat} {nf nc : Nat}
    {shared : Nat → Prop} {reserve : Nat} {callee : Expr} {args : List Expr}
    {node sp interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq) :
    ∀ (doneExprs : List Expr) (prior : List (Nat × Value)) (before : Config), args = doneExprs ++ es →
      LoopState N M entryF entryC nf nc shared (cost + reserve) st prior
        d env callee args node sp interp doneExprs.length m0 before →
      ∃ after, Steps before after ∧
        LoopState N M entryF entryC nf nc shared reserve final
          (prior ++ argumentSlots sp doneExprs.length values)
          d env callee args node sp interp args.length m0 after ∧ LoopFrame SL A sp before after := by
  induction children with
  | nil st =>
    intro doneExprs prior before remaining h
    have length : doneExprs.length = args.length := by simpa using congrArg List.length remaining.symm
    refine ⟨before, Steps.refl before, ?_, LoopFrame.refl SL A sp before⟩
    simpa only [argumentSlots, List.append_nil, Nat.zero_add, length] using h
  | @cons st middle final e es value values cost tailCost source child tail ih =>
    intro doneExprs prior before remaining h
    have more : doneExprs.length < args.length := by rw [remaining, List.length_append, List.length_cons]; omega
    have selected : args[doneExprs.length] = e := by
      subst args
      simp
    have source' : EvalE st d env args[doneExprs.length] middle value := by rw [selected]; exact source
    have child' : EvalAllocatorAt N st d env args[doneExprs.length] middle value cost request := by rw [selected]; exact child
    have ready : LoopState N M entryF entryC nf nc shared (cost + (tailCost + reserve)) st prior
        d env callee args node sp interp doneExprs.length m0 before := by
      simpa only [Nat.add_assoc] using h
    obtain ⟨next, step, advanced, frame⟩ := ready.advance L requestBound more source' child'
    obtain ⟨after, rest, finished, tailFrame⟩ := ih (doneExprs ++ [e])
      (prior ++ [(CallArgReturn.slot sp doneExprs.length, value)]) next
      (by simpa only [List.append_assoc, List.singleton_append] using remaining)
      (by simpa only [List.length_append, List.length_singleton] using advanced)
    refine ⟨after, step.trans rest, ?_, frame.trans tailFrame⟩
    simpa only [argumentSlots, List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] using finished

end Vsa.Sim.CallArgStage
