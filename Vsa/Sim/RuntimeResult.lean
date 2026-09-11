import Vsa.Sim.RuntimeOwnershipDataTransport
import Vsa.Sim.CoherentReturn

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

namespace Vsa.Sim
open RuntimeOwnership

/-- Runtime data and owned results at the producer's selected allocation state. -/
structure RuntimeResultAt (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (entryShared : Nat → Prop) (store : Store) (results : List (Nat × Value))
    (m0 : Mem) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (m : Mem) : Prop where
  runtime : StoreRuntimeData N A SL phiF phiC alloc exts shared store m
  includes : ∀ k, entryShared k → shared k
  values : ∀ a v, (a, v) ∈ results → ValueOwned m shared a v
  agreement : AgreeP entryShared m0 m

/-- Allocation and shared-domain witnesses belong to the actual return memory. -/
structure RuntimeResult (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (entryShared : Nat → Prop) (store : Store) (results : List (Nat × Value))
    (m0 : Mem) (phiF phiC : Addr → Nat) (m : Mem) : Prop where
  selected : ∃ alloc exts shared,
    RuntimeResultAt N A SL entryShared store results m0 phiF phiC alloc exts shared m

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
  {entryShared shared : Nat → Prop} {store : Store} {results results' : List (Nat × Value)}
  {m0 m1 m : Mem} {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}

/-- Retain any subset of the results and compose the caller's preceding shared frame. -/
theorem RuntimeResult.rebase
    (h : RuntimeResult N A SL entryShared store results m0 phiF phiC m)
    (subset : ∀ av, av ∈ results' → av ∈ results)
    (before : AgreeP entryShared m1 m0) :
    RuntimeResult N A SL entryShared store results' m1 phiF phiC m := by
  obtain ⟨alloc, exts, shared, data⟩ := h.selected
  exact ⟨alloc, exts, shared,
    { runtime := data.runtime
      includes := data.includes
      values := fun a v hv => data.values a v (subset (a, v) hv)
      agreement := fun k hk => (before k hk).trans (data.agreement k hk) }⟩

theorem RuntimeResult.shared_agree
    (h : RuntimeResult N A SL entryShared store results m0 phiF phiC m) :
    AgreeP entryShared m0 m := by
  obtain ⟨_, _, _, data⟩ := h.selected
  exact data.agreement

/-- Hereditary expression reads survive in the returned shared domain. -/
theorem RuntimeResultAt.expr
    (h : RuntimeResultAt N A SL entryShared store results m0 phiF phiC alloc exts shared m)
    {a : Nat} {e : Expr} (ast : ExprReprWithin m0 entryShared a e) :
    ExprReprWithin m shared a e :=
  (ast.transport h.agreement).mono h.includes

/-- Hereditary statement reads survive in the returned shared domain. -/
theorem RuntimeResultAt.stmt
    (h : RuntimeResultAt N A SL entryShared store results m0 phiF phiC alloc exts shared m)
    {a : Nat} {s : Stmt} (ast : StmtReprWithin m0 entryShared a s) :
    StmtReprWithin m shared a s :=
  (ast.transport h.agreement).mono h.includes

/-- The reached runtime supplies coherent store survival at its selected maps. -/
theorem RuntimeResultAt.coherent
    (h : RuntimeResultAt N A SL entryShared store results m0 phiF phiC alloc exts shared m)
    {entryF entryC : Addr → Nat} {nf nc : Nat}
    (hf : PhiExtends entryF phiF nf) (hc : PhiExtends entryC phiC nc)
    (hv : ∀ a v, (a, v) ∈ results → ValueRepr m N phiC a v) :
    ReturnRepr N A entryF entryC phiF phiC nf nc store results
      (RuntimeResult N A SL entryShared store results m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) m where
  frames := hf
  closures := hc
  values := hv
  owned := ⟨alloc, exts, shared, h⟩
  survives := fun _ hag => (h.runtime.after_stack hag).repr

#print axioms RuntimeResult.rebase
#print axioms RuntimeResult.shared_agree
#print axioms RuntimeResultAt.expr
#print axioms RuntimeResultAt.stmt
#print axioms RuntimeResultAt.coherent

end Vsa.Sim
