import Vsa.Sim.rows.EnvDefineReallocArraySuccess
import Vsa.Sim.AllocRuns
import Vsa.Sim.RuntimeOwnershipArrays

/-!
# `EnvDefineReallocArray` — one owned array through `realloc`, uniformly

`env_define`'s grow path reallocates the frame's two arrays; on the empty
frame the arrays are `NULL` and the same instructions call `realloc(NULL, n)`.
`ReallocRun` distinguishes the two (`grow`/`null`); `reallocArray_run` runs
either from the array's ownership (`ArrayOwned`: empty or live) and lands ONE
named result, `ArrayReallocResult`, whose ledger form
`(pNew, nNew) :: exts.erase (pOld, nOld)` and public frame
`[(pOld, nOld), (pNew, nNew)]` are the grow forms with `(0, 0)` for the empty
array.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (Allocations Role ArrayOwned Allocated heapArena_erase_zero)

/-- The uniform outcome of reallocating one owned array (live or empty). -/
inductive ArrayReallocResult (A : Arena) (SL : StackLayout) (privFoot : Nat → Prop)
    (AInv : MState → List Extent → Prop) (exts : List Extent) (pOld nOld nNew : Nat)
    (sp : BitVec 64) (m0 : Mem) (σ : MState) : Prop where
  | intro (pNew : Nat)
      (ptr : σ.regs.get? Register.x10 = some (BitVec.ofNat 64 pNew))
      (nonzero : pNew ≠ 0) (align : pNew % 16 = 0) (arena : A.contains pNew nNew)
      (fresh : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e)
      (copies : ReallocCopies m0 σ.mem pOld pNew nOld)
      (ainv : AInv σ ((pNew, nNew) :: exts.erase (pOld, nOld)))
      (frame : HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 σ.mem)

/-- Execute the resource-bearing successful array contract from the run-global instance.
The selected result retains the unused reserve for the following call. -/
theorem reallocArray_run {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    (RI : ReallocInstance A SL gpv headroom maxReq AInv privFoot)
    {exts : List Extent} {alloc : Allocations} {role : Role} {pOld width cap nNew : Nat}
    (harena : HeapArena A exts)
    (hold : ArrayOwned alloc role pOld width cap)
    (hmem : 0 < cap → (pOld, width * cap) ∈ exts)
    (hnz : 0 < cap → pOld ≠ 0)
    (hgrow : width * cap < nNew)
    (g : (R : Register) → Option (RegisterType R)) (sp r : BitVec 64) (m0 : Mem)
    (out : Array String) (credits : Nat) :
    Triple
      (ReallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts pOld nNew sp r m0 out)
      (ReallocGrowSuccessExit A SL gpv maxReq credits AInv privFoot
        g exts pOld (width * cap) nNew sp r m0 out) :=
  reallocArraySuccess_run RI.success harena hold hmem hnz hgrow g sp r m0 out credits

/-- A live extent is never equal to an extent of a different role. -/
theorem ne_of_extDisjoint_pos {a b : Extent} (hd : ExtDisjoint a b) (hpos : 0 < a.2) :
    a ≠ b := by
  intro h
  subst h
  change a.1 + a.2 ≤ a.1 ∨ a.1 + a.2 ≤ a.1 at hd
  omega

#print axioms reallocArray_run
#print axioms ne_of_extDisjoint_pos

end Vsa.Sim
