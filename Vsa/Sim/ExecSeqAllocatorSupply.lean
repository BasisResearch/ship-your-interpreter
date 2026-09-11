import Vsa.Sim.AllocatorSupply
import Vsa.Sim.ExecSeqAllocatorNil
import Vsa.Sim.SeqClosureAllocatorCases
import Vsa.Sim.SeqInterpAllocatorCases
import Vsa.Sim.SeqBlockAllocatorCases
import Vsa.Sim.rows.StoreWF

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Source sequence resources are chosen before machine entry. The selected
physical loop supports the requested status, as in the ordinary sequence contract. -/
structure ExecSeqAllocatorSupply (copy : ExecSeqCopy) (st : Vsa.While.St)
    (d env : Nat) (ss : List Stmt) (final : Vsa.While.St) (status : Status) : Prop where
  provide : copy.Supports status → ∀ (N : NativeAddrs),
    (∀ f h, N.addr f = N.addr h → f = h) → StoreClosuresBounded st.store →
    ∃ cost request, ExecSeqAllocatorAt N copy st d env ss final status cost request

/-- One source-selected ceiling covers the body and every parameter allocation. -/
structure ClosureBodyAllocation (N : NativeAddrs) (st : Vsa.While.St) (d : Nat)
    (cd : ClosureData) (values : List Value) (final : Vsa.While.St) (status : Status)
    (cost request : Nat) : Prop where
  body : ExecSeqAllocatorAt N .closureBody
    ⟨(cd.params.zip values).foldl
      (fun s binding => s.define st.store.frames.size binding.1 binding.2)
      (st.store.allocFrame (some cd.env)).1, st.out⟩
    (d + 1) st.store.frames.size cd.body final status cost request
  names : ∀ param ∈ cd.params, param.length + 1 ≤ request
  grow : 48 * values.length ≤ request

private theorem parameter_request_bound (params : List String) :
    ∀ param ∈ params,
      param.length + 1 ≤ params.foldr (fun p n => max (p.length + 1) n) 0 := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    intro param member
    rcases List.mem_cons.mp member with same | tail
    · subst param; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih param tail) (Nat.le_max_right _ _)

/-- Instantiate the exact closure-body IH and choose binding requests before machine entry. -/
theorem ExecSeqAllocatorSupply.closure_allocation
    {st final : Vsa.While.St} {d : Nat} {cd : ClosureData} {values : List Value}
    {store' : Store} {frame : Addr} {status : Status} {value : Value}
    (allocated : st.store.allocFrame (some cd.env) = (store', frame))
    (body : ExecSeqAllocatorSupply .closureBody
      ⟨(cd.params.zip values).foldl (fun s binding => s.define frame binding.1 binding.2) store', st.out⟩
      (d + 1) frame cd.body final status)
    (meaning : status = .normal ∧ value = .null ∨ status = .ret value)
    (N : NativeAddrs) (native : ∀ f h, N.addr f = N.addr h → f = h)
    (bounded : StoreClosuresBounded st.store)
    (valuesBounded : ∀ v ∈ values, ValueClosuresBounded st.store.closures.size v) :
    ∃ cost request, ClosureBodyAllocation N st d cd values final status cost request := by
  have storeEq : store' = (st.store.allocFrame (some cd.env)).1 :=
    (congrArg Prod.fst allocated).symm
  have frameEq : frame = st.store.frames.size := by
    simpa only [Store.allocFrame] using (congrArg Prod.snd allocated).symm
  subst store'; subst frame
  have supported : ExecSeqCopy.Supports .closureBody status := by
    rcases meaning with ⟨normal, _⟩ | returns
    · subst status; simp [ExecSeqCopy.Supports]
    · subst status; simp [ExecSeqCopy.Supports]
  have boundStore : StoreClosuresBounded
      ((cd.params.zip values).foldl
        (fun s binding => s.define st.store.frames.size binding.1 binding.2)
        (st.store.allocFrame (some cd.env)).1) := by
    apply StoreClosuresBounded.foldDefine (cd.params.zip values) (bounded.allocFrame rfl)
    intro pair member
    exact valuesBounded pair.2 (List.of_mem_zip member).2
  obtain ⟨cost, bodyRequest, run⟩ := body.provide supported N native boundStore
  let names := cd.params.foldr (fun p n => max (p.length + 1) n) 0
  let request := max bodyRequest (max names (48 * values.length))
  refine ⟨cost, request,
    { run := fun g A SL gpv headroom maxReq M L le =>
        run.run g A SL gpv headroom maxReq M L (Nat.le_trans (Nat.le_max_left _ _) le) }, ?_, ?_⟩
  · intro param member
    exact Nat.le_trans (parameter_request_bound cd.params param member)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- All physical copies supply the empty source constructor at zero cost. -/
theorem ExecSeqAllocatorSupply.nil (copy : ExecSeqCopy) (st : Vsa.While.St) (d env : Nat) :
    ExecSeqAllocatorSupply copy st d env [] st .normal where
  provide := fun _ N _ _ => ⟨0, 0, execSeqAllocatorAt_nil N copy st d env⟩

/-- The normal source constructor selects the final or continuing machine route. -/
theorem ExecSeqAllocatorSupply.closure_consNormal
    {st middle final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt}
    {status : Status}
    (headSource : ExecS st d env s middle .normal)
    (tailSource : ExecSeq middle d env ss final status)
    (head : ExecAllocatorSupply st d env s middle .normal)
    (tail : ExecSeqAllocatorSupply .closureBody middle d env ss final status) :
    ExecSeqAllocatorSupply .closureBody st d env (s :: ss) final status where
  provide := by
    intro supported N native bounded
    obtain ⟨headCost, headRequest, headRun⟩ := head.provide N native bounded
    cases ss with
    | nil =>
      cases tailSource
      exact ⟨headCost, headRequest, execSeqAllocatorAt_closure_singleton headRun⟩
    | cons next rest =>
      obtain ⟨tailCost, tailRequest, tailRun⟩ := tail.provide supported N native
        (execS_storeClosuresBounded headSource bounded)
      exact ⟨headCost + tailCost, max headRequest tailRequest,
        execSeqAllocatorAt_closure_consNormal headSource (by simp) headRun tailRun⟩

/-- The abrupt source constructor uses the closure loop's value-return route. -/
theorem ExecSeqAllocatorSupply.closure_consAbrupt
    {st final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt} {status : Status}
    (abrupt : status ≠ .normal)
    (head : ExecAllocatorSupply st d env s final status) :
    ExecSeqAllocatorSupply .closureBody st d env (s :: ss) final status where
  provide := by
    intro supported N native bounded
    cases status with
    | normal => exact False.elim (abrupt rfl)
    | brk => simp [ExecSeqCopy.Supports] at supported
    | cont => simp [ExecSeqCopy.Supports] at supported
    | ret v =>
      obtain ⟨cost, request, run⟩ := head.provide N native bounded
      exact ⟨cost, request, execSeqAllocatorAt_closure_consRet run⟩

/-- Fold the three checked closure constructors over the source sequence.
The mutual statement recursor supplies each statement's owned contract. -/
theorem execSeqAllocatorSupply_closure
    (head : ∀ (st final : Vsa.While.St) (d env : Nat) (s : Stmt) (status : Status),
      ExecS st d env s final status → ExecAllocatorSupply st d env s final status)
    {st final : Vsa.While.St} {d env : Nat} {ss : List Stmt} {status : Status}
    (source : ExecSeq st d env ss final status) :
    ExecSeqAllocatorSupply .closureBody st d env ss final status := by
  induction ss generalizing st final status with
  | nil =>
    cases source
    exact ExecSeqAllocatorSupply.nil .closureBody st d env
  | cons s ss ih =>
    cases source with
    | consNormal _ _ _ _ _ middle _ _ headSource tailSource =>
      exact ExecSeqAllocatorSupply.closure_consNormal headSource tailSource
        (head _ _ _ _ _ _ headSource) (ih tailSource)
    | consAbrupt _ _ _ _ _ _ _ headSource abrupt =>
      exact ExecSeqAllocatorSupply.closure_consAbrupt abrupt (head _ _ _ _ _ _ headSource)

/-- The interpreter's normal source constructor selects its last or continuing route. -/
theorem ExecSeqAllocatorSupply.interp_consNormal
    {st middle final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt}
    {status : Status}
    (headSource : ExecS st d env s middle .normal)
    (tailSource : ExecSeq middle d env ss final status)
    (head : ExecAllocatorSupply st d env s middle .normal)
    (tail : ExecSeqAllocatorSupply .interpRun middle d env ss final status) :
    ExecSeqAllocatorSupply .interpRun st d env (s :: ss) final status where
  provide := by
    intro supported N native bounded
    have normal : status = .normal := supported
    subst status
    obtain ⟨headCost, headRequest, headRun⟩ := head.provide N native bounded
    cases ss with
    | nil =>
      cases tailSource
      exact ⟨headCost, headRequest, execSeqAllocatorAt_interp_singleton headRun⟩
    | cons next rest =>
      obtain ⟨tailCost, tailRequest, tailRun⟩ := tail.provide rfl N native
        (execS_storeClosuresBounded headSource bounded)
      exact ⟨headCost + tailCost, max headRequest tailRequest,
        execSeqAllocatorAt_interp_consNormal headSource (by simp) headRun tailRun⟩

/-- Interpreter sequences expose normal exits, so their supported source case is normal. -/
theorem ExecSeqAllocatorSupply.interp_consAbrupt
    {st final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt} {status : Status}
    (abrupt : status ≠ .normal) :
    ExecSeqAllocatorSupply .interpRun st d env (s :: ss) final status where
  provide := fun supported => False.elim (abrupt supported)

/-- The block's normal constructor selects the last or continuing owned route. -/
theorem ExecSeqAllocatorSupply.block_consNormal
    {st middle final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt}
    {status : Status}
    (headSource : ExecS st d env s middle .normal)
    (tailSource : ExecSeq middle d env ss final status)
    (head : ExecAllocatorSupply st d env s middle .normal)
    (tail : ExecSeqAllocatorSupply .blockBody middle d env ss final status) :
    ExecSeqAllocatorSupply .blockBody st d env (s :: ss) final status where
  provide := by
    intro _ N native bounded
    obtain ⟨headCost, headRequest, headRun⟩ := head.provide N native bounded
    cases ss with
    | nil =>
      cases tailSource
      exact ⟨headCost, headRequest, execSeqAllocatorAt_block_singleton headRun⟩
    | cons next rest =>
      obtain ⟨tailCost, tailRequest, tailRun⟩ := tail.provide trivial N native
        (execS_storeClosuresBounded headSource bounded)
      exact ⟨headCost + tailCost, max headRequest tailRequest,
        execSeqAllocatorAt_block_consNormal headSource (by simp) headRun tailRun⟩

/-- An abrupt first statement supplies the whole block sequence's result. -/
theorem ExecSeqAllocatorSupply.block_consAbrupt
    {st final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt} {status : Status}
    (abrupt : status ≠ .normal)
    (head : ExecAllocatorSupply st d env s final status) :
    ExecSeqAllocatorSupply .blockBody st d env (s :: ss) final status where
  provide := by
    intro _ N native bounded
    obtain ⟨cost, request, run⟩ := head.provide N native bounded
    exact ⟨cost, request, execSeqAllocatorAt_block_consAbrupt run abrupt⟩

#print axioms ExecSeqAllocatorSupply.block_consNormal
#print axioms ExecSeqAllocatorSupply.block_consAbrupt
#print axioms ExecSeqAllocatorSupply.interp_consNormal
#print axioms ExecSeqAllocatorSupply.interp_consAbrupt
#print axioms ExecSeqAllocatorSupply.nil
#print axioms ExecSeqAllocatorSupply.closure_allocation
#print axioms ExecSeqAllocatorSupply.closure_consNormal
#print axioms ExecSeqAllocatorSupply.closure_consAbrupt
#print axioms execSeqAllocatorSupply_closure

end Vsa.Sim
