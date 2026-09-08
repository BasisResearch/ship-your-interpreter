import Vsa.Sim.ExitFootprint
import Vsa.Sim.RuntimeOwnershipAllocation

/-!
# `IHClauseGenericAlloc` — the allocating arms' footprint premises (IH tower, Level 2)

The `Footprint` clause at `noArenaFoot` is FALSE for the arms that allocate:
`fn` (closure record + closure-array push), `call` of a closure (`env_new`,
argument binding, the body's own allocations), and string concatenation (the
concatenated payload; `value_str` itself only boxes a pointer —
`value_str_spec_full_exact` — so the string leaf is non-allocating).  Their footprint
includes fresh arena extents and allocator-private bytes.  This file states,
as doc-commented named premises, the exact fact each arm needs from the
allocator/ownership layer (`MallocContract`, `MallocRun`, `HeapOwned`,
`Reserved`; `PROOF_CLOSURE_PLAN.md`, task 2).  No step is proved here.

The footprint of an allocating call is `allocFoot`: the stack window, the result
slot, the allocator-private set `M.privFoot`, and the fresh extents (arena
blocks disjoint from every live extent of the entry ledger).  The clause extra
is stated over the entry ledger `exts` through `HeapOwned … m0 …`, the
memory-only characterisation of the live ledger the `EvalExtraM` world can
see (`EvalEntry` carries no ledger).
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (ExtentByte HeapOwned Reserved Allocations)

namespace Vsa.Sim

/-- Fresh extents relative to the entry ledger: inside the arena and disjoint
from every live extent (`MallocContract.spec`'s fresh-block clause, per block). -/
def FreshExtents (A : Arena) (exts fresh : List Extent) : Prop :=
  ∀ e ∈ fresh, A.contains e.1 e.2 ∧ ∀ e' ∈ exts, ExtDisjoint e e'

/-- The footprint of an allocating call: the non-allocating footprint, the
allocator-private bytes `priv` (`MallocContract.privFoot`), and the fresh extents. -/
def allocFoot (priv : Nat → Prop) (fresh : List Extent) : FootFam :=
  fun SL A sp sret k => noArenaFoot SL A sp sret k ∨ priv k ∨ ∃ e ∈ fresh, ExtentByte e k

/-- The allocating clause extra at a child's actual return: for every live
ledger the entry memory owns, the exit memory differs from the entry memory
only inside `allocFoot` at some fresh extents.  Shared bytes reserved by the
ledger are untouched (`Reserved.outsideFresh` + `MallocContract.privFoot_disjoint`). -/
def allocExtra (priv : Nat → Prop) (s : Store) : EvalExtraM :=
  fun _ A SL φf φc sp sret m0 c =>
    ∀ (exts : List Extent) (alloc : Allocations)
      (shared readable writes : Nat → Prop),
      HeapOwned A exts m0 φf φc alloc shared readable writes s →
      ∃ fresh, FreshExtents A exts fresh ∧
        MemFootprint (allocFoot priv fresh SL A sp.toNat sret.toNat) m0 c.σ.mem

/-- The allocating child contract (the `Footprint` clause's family for
allocating arms), at the allocator-private set `priv`. -/
abbrev EvalIHAlloc (priv : Nat → Prop)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (allocExtra priv st.store) st d env e st' v

/-- **NAMED PREMISE — the closure-literal arm (`hFn`).**  The `fn` arm allocates
the closure record (`malloc`) and pushes it on the store's closure array
(`realloc` on growth): its footprint is `allocFoot` at the two fresh blocks
(plus the reused array block when no growth occurs, which is a LIVE extent the
store owns — the write lands inside the store's own mutable array, not the
shared set).  Supplier: `MallocRun M` (the fresh block and `mem_frame`),
`HeapOwned.pushClosure` (`RuntimeOwnershipAllocation`/`PROOF_CLOSURE_PLAN.md`
task 2), and `Reserved.outsideFresh` for the shared bytes. -/
structure FnArmFootprint {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq) : Prop where
  run : ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr),
    st.store.allocClosure { env := env, name := name, params := params, body := body } =
      (store', a) →
    EvalIHAlloc M.privFoot st d env (.fn name params body) { store := store', out := st.out }
      (.closure a)

/-- **NAMED PREMISE — the closure call (`hCall` at `Call.closure`).**  The call
arm allocates the callee frame (`env_new`: frame record + name/value arrays)
and binds the arguments (`env_define`: copied keys, array growth), then runs
the body; its footprint is `allocFoot` at the frame's fresh blocks together
with the body's own allocating footprint (the `ExecSeq` clause) — the children
(`f`, the arguments) contribute theirs.  Supplier: `EnvNewContract`
(`rows/EnvNewContractSupply.lean`: `envNewContract_of_ledger` over `MallocRun`),
`EnvDefineContract` (`HelperCallEnvDefine.lean`), and the `ExecSeq`/`ExecS`
clause motives (`L3-generator.md`, `motives` column). -/
structure CallArmFootprint {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq) : Prop where
  run : ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : Vsa.While.St) (fv : Value) (vs : List Value) (v : Value),
    EvalE st d env f st' fv → args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs → Call st'' d fv vs st''' v →
    EvalIHAlloc M.privFoot st d env f st' fv →
    EvalIHAlloc M.privFoot st d env (f.call args) st''' v

/-- **NAMED PREMISE — string concatenation (`hBinary` at `.add` with a string
operand).**  Both concatenation cells allocate the result payload
(`value_str` → `malloc(len + 1)` + `memcpy`); their footprint is `allocFoot` at
that one fresh block, beyond the two children's.  Supplier: `MallocRun M`, the
`value_str` payload copy (`valueRepr_copy_total`), and `Reserved.outsideFresh`
for the operands' shared payloads. -/
structure StrAddFootprint {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq) : Prop where
  left : ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
      (st' st'' : Vsa.While.St) (sl : String) (rv : Value),
    EvalE st d env el st' (.str sl) → EvalE st' d env er st'' rv →
    EvalIHAlloc M.privFoot st d env el st' (.str sl) → EvalIHAlloc M.privFoot st' d env er st'' rv →
    EvalIHAlloc M.privFoot st d env (.binary .add el er) st''
      (.str ((Value.str sl).catDisplay st''.store ++ rv.catDisplay st''.store))
  right : ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
      (st' st'' : Vsa.While.St) (lv : Value) (sr : String),
    EvalE st d env el st' lv → EvalE st' d env er st'' (.str sr) →
    EvalIHAlloc M.privFoot st d env el st' lv → EvalIHAlloc M.privFoot st' d env er st'' (.str sr) →
    EvalIHAlloc M.privFoot st d env (.binary .add el er) st''
      (.str (lv.catDisplay st''.store ++ (Value.str sr).catDisplay st''.store))

/-- A non-allocating child satisfies the allocating clause with no fresh extents. -/
theorem EvalIHF.toAlloc (priv : Nat → Prop)
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    (h : EvalIHF noArenaFoot st d env e st' v) : EvalIHAlloc priv st d env e st' v :=
  EvalIHWithM.mono
    (fun _ _ _ _ _ _ _ _ _ hf _ _ _ _ _ _ =>
      ⟨[], (fun _ h => nomatch h),
        hf.mono (fun _ hk => Or.inl hk)⟩) h

#print axioms EvalIHF.toAlloc

end Vsa.Sim
