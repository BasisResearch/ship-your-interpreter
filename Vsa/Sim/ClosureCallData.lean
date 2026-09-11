import Vsa.Sim.ClosureParamFoldData
import Vsa.Sim.AstFootprintTransport

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The represented parameter-array count is the source list length. -/
private theorem params_length {m : Mem} {a n : Nat} {params : List String}
    (h : ParamsRepr m a n params) : n = params.length := by
  induction params generalizing a n with
  | nil => cases h; rfl
  | cons name rest ih =>
    cases h with
    | cons read string tail => exact congrArg Nat.succ (ih tail)

/-- The closure's existing footprint owns every parameter cell and name. -/
private theorem params_owned {m : Mem} {a n : Nat} {params : List String}
    {shared : Nat → Prop} (h : ParamsRepr m a n params)
    (covered : ∀ k, ParamsFp m a n params k → shared k) :
    ParamsReprWithin m shared a n params := by
  induction params generalizing a n with
  | nil => cases h; exact .nil
  | cons name rest ih =>
    cases h with
    | cons read string tail =>
      exact .cons read (fun i hi => covered _ (.slot hi))
        ⟨string, fun i hi => covered _ (.str read hi)⟩
        (ih tail (fun k hk => covered k (.tail hk)))

/-- Actual fields of the closure's function node and its owned parameter names. -/
structure ClosureFnReads (m : Mem) (shared : Nat → Prop) (fn names body : Nat)
    (cd : ClosureData) : Prop where
  namesRead : read64 m (fn + 16) = some names
  namesCovered : Covers shared (fn + 16) 8
  countRead : read32 m (fn + 24) = some cd.params.length
  countCovered : Covers shared (fn + 24) 4
  params : ParamsReprWithin m shared names cd.params.length cd.params
  bodyRead : read64 m (fn + 32) = some body
  bodyCovered : Covers shared (fn + 32) 8
  bodyRepr : StmtRepr m body (.block cd.body)
  bodyFootprint : ∀ k, StmtFp m body (.block cd.body) k → shared k

/-- Extract the same node fields from either named or anonymous closure syntax. -/
theorem closureFnReads_of_repr {m : Mem} {shared : Nat → Prop} {fn : Nat} {cd : ClosureData}
    (repr : ExprRepr m fn (.fn cd.name cd.params cd.body))
    (covered : ∀ k, ExprFp m fn (.fn cd.name cd.params cd.body) k → shared k) :
    ∃ names body, ClosureFnReads m shared fn names body cd := by
  rcases cd with ⟨env, name, params, body⟩
  cases name with
  | some x =>
    cases repr with
    | fnNamed tag nameRead nonzero string namesRead countRead params bodyRead bodyRepr =>
      have count := params_length params
      refine ⟨_, _,
        { namesRead := namesRead, namesCovered := fun i hi => covered _ (.off16 hi)
          countRead := by simpa only [count] using countRead
          countCovered := fun i hi => covered _ (.off24 (by omega))
          params := ?_, bodyRead := bodyRead, bodyCovered := fun i hi => covered _ (.off32 hi)
          bodyRepr := bodyRepr, bodyFootprint := fun k hk => covered k (.body32 (.fn _ _ _) bodyRead hk) }⟩
      simpa only [count] using params_owned params
        (fun k hk => covered k (.paramsArr (.fn _ _ _) namesRead hk))
  | none =>
    cases repr with
    | fnAnon tag anonymous namesRead countRead params bodyRead bodyRepr =>
      have count := params_length params
      refine ⟨_, _,
        { namesRead := namesRead, namesCovered := fun i hi => covered _ (.off16 hi)
          countRead := by simpa only [count] using countRead
          countCovered := fun i hi => covered _ (.off24 (by omega))
          params := ?_, bodyRead := bodyRead, bodyCovered := fun i hi => covered _ (.off32 hi)
          bodyRepr := bodyRepr, bodyFootprint := fun k hk => covered k (.body32 (.fn _ _ _) bodyRead hk) }⟩
      simpa only [count] using params_owned params
        (fun k hk => covered k (.paramsArr (.fn _ _ _) namesRead hk))

/-- The closure object and its function node refer to the same source closure. -/
structure ClosureObjectReads (m : Mem) (phiF phiC : Addr → Nat) (shared : Nat → Prop)
    (ca fn names body : Nat) (cd : ClosureData) : Prop where
  nodeRead : read64 m (phiC ca) = some fn
  envRead : read64 m (phiC ca + 8) = some (phiF cd.env)
  envNonzero : phiF cd.env ≠ 0
  node : ClosureFnReads m shared fn names body cd

/-- The current owned store supplies the closure object, names, and body reads. -/
theorem RuntimeAllocatorState.closure_reads
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop} {credits : Nat}
    {store : Store} {m : Mem} {ca : Nat} {cd : ClosureData}
    (h : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m)
    (source : store.closures[ca]? = some cd) :
    ∃ fn names body, ClosureObjectReads m phiF phiC shared ca fn names body cd := by
  have valid : ca < store.closures.size := by
    exact Array.getElem?_eq_some_iff.mp source |>.1
  have actual : store.closures[ca] = cd :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans source)
  obtain ⟨⟨fn, nodeRead, nodeRepr⟩, envRead, nonzero⟩ := h.repr.closures ca valid
  have footprint := h.heap.store.closureAsts ca valid fn nodeRead
  rw [actual] at nodeRepr envRead nonzero footprint
  obtain ⟨names, body, node⟩ := closureFnReads_of_repr nodeRepr footprint
  exact ⟨fn, names, body, ⟨nodeRead, envRead, nonzero, node⟩⟩

/-- The extracted names combine with the actual argument slots used by the fold. -/
theorem ClosureFnReads.fold_data
    {m : Mem} {shared : Nat → Prop} {fn names body : Nat} {cd : ClosureData}
    (h : ClosureFnReads m shared fn names body cd)
    {N : NativeAddrs} {phiC : Addr → Nat} {sp : BitVec 64} {values : List Value}
    (fnBound : fn < 2^64) (arity : values.length = cd.params.length) (bound : values.length ≤ 32)
    (arguments : ∀ i (hi : i < values.length), ValueRepr m N phiC (sp.toNat + 240 + 24 * i) values[i])
    (owned : ∀ i (hi : i < values.length), ValueOwned m shared (sp.toNat + 240 + 24 * i) values[i]) :
    ClosureParam.FoldData m N phiC shared sp (BitVec.ofNat 64 fn) (BitVec.ofNat 64 names) cd.params values := by
  have fnNat : (BitVec.ofNat 64 fn).toNat = fn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fnBound]
  have namesNat : (BitVec.ofNat 64 names).toNat = names := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ h.namesRead)]
  exact
    { arity := arity, bound := bound
      namesRead := by rw [fnNat, namesNat]; exact h.namesRead
      namesCovered := by rw [fnNat]; exact h.namesCovered
      paramsOwned := by rw [namesNat]; exact h.params
      arguments := arguments, owned := owned }

end Vsa.Sim
