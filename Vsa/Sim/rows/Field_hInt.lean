import Vsa.Sim.rows.AssemblySkeleton

/-!
# RUN-1 field `hInt` — DISCHARGED (wave 47e)

The first `TermResidualsCore` field to close.  Route (the re-seat verdict,
`experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean`, landed):

* **`EntryStackSurv`** — the `EvalEntry.store_survives` footprint amendment
  (`[SL.lo, sp)` → `[SL.lo, SL.hi)`, `InterpEntry.lean`), so the entry survival
  covers the caller strip `[sp, SL.hi)` the motive-fixed `EvalExitD` demands;
* **`LeafExitPin`** — the leaf sims re-landed at the PINNED exit
  (`evalIntSimP`: `EvalExit ∧ LeafMemPin`, the exit memory pinned to the leaf's
  own write chain), transported across the epilogue by `blockD_v`'s `Q`;
* the residual `IntLeafResid` re-stated at the pinned widener (`LeafWidenP`,
  `TermRouting.lean`), which `leafWidenP_of_entry` (`EvalLeafD.lean`)
  discharges from the amended entry alone.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows

local notation "SpecSt" => Vsa.While.St

/-- **`hInt` discharged**: the int-leaf residual holds outright — the pinned
widener is entry-derivable. -/
theorem field_hInt : ∀ (st : SpecSt) (n : Int), IntLeafResid st n :=
  fun _st _n _g _N _A _SL _φf _φc _d _env _sp _r _sret _aEnv _aExpr _m0 _c hc =>
    Vsa.Sim.leafWidenP_of_entry hc

/-- The skeleton-hole form (`assembly_skeleton.tsv` row `hInt`). -/
theorem skelHInt_discharged (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHInt L :=
  fun st n => field_hInt st n

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hInt
#print axioms Vsa.Sim.Rows.skelHInt_discharged
