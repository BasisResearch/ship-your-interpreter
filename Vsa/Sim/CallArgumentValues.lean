import Vsa.Sim.CallArgumentsComplete
import Vsa.Sim.ClosureCallData

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

theorem Arguments.length {N : NativeAddrs} {d env request : Nat} {st final : Vsa.While.St}
    {es : List Expr} {values : List Value} {cost : Nat}
    (h : Arguments N d env request st es final values cost) : values.length = es.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem Arguments.source {N : NativeAddrs} {d env request : Nat} {st final : Vsa.While.St}
    {es : List Expr} {values : List Value} {cost : Nat}
    (h : Arguments N d env request st es final values cost) : EvalArgs st d env es final values := by
  induction h with
  | nil => exact .nil ..
  | cons source _ _ ih => exact .cons _ _ _ _ _ _ _ _ _ source ih

/-- Indexed source values occur at their actual copied machine slots. -/
theorem argumentSlots_member (sp : BitVec 64) (start : Nat) (values : List Value)
    (index : Nat) (bound : index < values.length) :
    (CallArgReturn.slot sp (start + index), values[index]) ∈ argumentSlots sp start values := by
  induction values generalizing start index with
  | nil => simp at bound
  | cons value values ih =>
    cases index with
    | zero => simp [argumentSlots]
    | succ index =>
      apply List.mem_cons_of_mem
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.getElem_cons_succ] using
        ih (start + 1) index (by simpa using bound)

end Vsa.Sim.CallArgStage

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The selected allocator supplies the represented closure and complete binding data. -/
structure ClosureDataAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (entryF entryC resultF resultC : Addr → Nat)
    (nf nc : Nat) (alloc : Allocations) (exts : List Extent) (entryShared shared : Nat → Prop)
    (credits : Nat) (store : Store) (ca : Addr) (cd : ClosureData) (values : List Value)
    (sp : BitVec 64) (fn names body : Nat) (m0 m : Mem) : Prop where
  allocator : RuntimeAllocatorState M N resultF resultC alloc exts shared credits store m
  frames : PhiExtends entryF resultF nf
  closures : PhiExtends entryC resultC nc
  includes : ∀ k, entryShared k → shared k
  agreement : AgreeP entryShared m0 m
  callee : ValueRepr m N resultC (sp.toNat + 96) (.closure ca)
  object : ClosureObjectReads m resultF resultC shared ca fn names body cd
  fold : ClosureParam.FoldData m N resultC shared sp (BitVec.ofNat 64 fn) (BitVec.ofNat 64 names) cd.params values
  bounded : ∀ i (hi : i < values.length), ValueClosuresBounded store.closures.size values[i]

/-- Extract closure fields and each copied argument from the actual selected return maps. -/
theorem ArgumentsReady.closure_data
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {calleeCost argsCost reserve : Nat} {st middle final : Vsa.While.St} {d env : Nat}
    {callee : Expr} {args : List Expr} {ca : Addr} {values : List Value} {cd : ClosureData}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {after : Config}
    (h : ArgumentsReady g N M phiF phiC alloc exts shared calleeCost argsCost reserve
      st middle final d env callee args (.closure ca) values sp ret dst node interp saved7 m0 after)
    (source : final.store.closures[ca]? = some cd) (arity : values.length = cd.params.length)
    (length : values.length = args.length) :
    ∃ resultF resultC resultAlloc resultExts resultShared fn names body,
      ClosureDataAt N M phiF phiC resultF resultC st.store.frames.size st.store.closures.size
        resultAlloc resultExts shared resultShared reserve final.store ca cd values (sp - 1088#64)
        fn names body m0 after.σ.mem := by
  obtain ⟨resultF, resultC, repr⟩ := h.loop.selected
  obtain ⟨resultAlloc, resultExts, resultShared, data⟩ := repr.owned.selected
  obtain ⟨fn, names, body, object⟩ := data.allocator.closure_reads source
  have callee := repr.values _ _ (List.mem_cons_self ..)
  have buffer : ((sp - 1088#64) + 96#64).toNat = (sp - 1088#64).toNat + 96 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.loop.caller.stackHi; change (sp - 1088#64).toNat + 96 < 2^64; omega)]
    rfl
  rw [buffer] at callee
  have member (i : Nat) (hi : i < values.length) :
      (CallArgReturn.slot (sp - 1088#64) i, values[i]) ∈
        ([(((sp - 1088#64) + 96#64).toNat, .closure ca)] ++ CallArgStage.argumentSlots (sp - 1088#64) 0 values) := by
    apply List.mem_append_right
    simpa only [Nat.zero_add] using CallArgStage.argumentSlots_member (sp - 1088#64) 0 values i hi
  exact ⟨resultF, resultC, resultAlloc, resultExts, resultShared, fn, names, body,
    { allocator := data.allocator, frames := repr.frames, closures := repr.closures
      includes := data.includes, agreement := data.agreement, callee := callee, object := object
      fold := object.node.fold_data (read64_lt_eg4 _ _ _ object.nodeRead) arity
        (by rw [length]; exact h.loop.countBound)
        (fun i hi => repr.values _ _ (member i hi)) (fun i hi => data.values _ _ (member i hi))
      bounded := fun i hi => h.loop.priorBound _ _ (member i hi) }⟩

end Vsa.Sim.CallCallee
