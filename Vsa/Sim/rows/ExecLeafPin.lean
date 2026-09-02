import Vsa.Sim.rows.ExecLeafD
import Vsa.Sim.rows.ExecRouting
import Vsa.Sim.rows.EntryGroundRows
import Vsa.Sim.rows.AssemblySkeleton

/-!
# `ExecLeafPin` — the X3 exec-leaf re-seat, CLOSED (Wave 48d, X3-c)

The pinned re-seat of the register-only exec leaves (`brk`/`cont`) at
`ExecExitPinned`, the exec twin of the wave-47e eval re-seat
(`evalIntSimP`/`leafWidenP_of_entry`, `EvalLeafD.lean`).  Waves 48a/b/c landed the
pinned family (`ExecLeafMemPin`/`ExecExitPinned`/`ExecLeafWidenP`,
`execLeafWidenP_of_entry`) and the block-level `MemExtends m0 ment` exposure, and
reduced `field_hSBrk`/`field_hSCont` to ONE named premise `ExecArmMemExt` (the
pin recovered from a bare `ExecExit` — provably underivable, wave-48c obstruction).

## What wave 48d (X3-c) did — the presence transport, MIRRORING the eval precedent

The eval leaves closed this exact gap in wave 47e NOT by recovering the pin from a
bare `EvalExit`, but by CARRYING the presence through the shared epilogue: `blockD_v`
gained a `Q : Mem → Prop` post-parameter, threaded `Q mpre → Q c.σ.mem` across the
memory-pure epilogue, and `evalIntSimP` concluded `EvalExit ∧ LeafMemPin` directly.
Wave 48d transcribes that to exec:

* `execBlockD` (`ExecBrkCont.lean`) gained the `Q : Mem → Prop` parameter (post
  `ExecExit ∧ Q c.σ.mem`, pre `… ∧ Q mpre`), exec twin of `blockD_v`'s `Q`.
* `execBrkSim`/`execContSim` now CONCLUDE `ExecExitPinned` (the pin threaded as
  `Q := ExecLeafMemPin SL sp m0` for brk through `execBlockD`, inline for cont),
  supplying `pres` from the arm presence `MemExtends m0 ment` and `agree` from the
  arena-inclusive arm frame `hmemframe`.
* `ExecCaseGeom` (`ExecCaseGeom.lean`) now carries the PINNED widener
  `ExecLeafWidenP` (entry-derivable via `execLeafWidenP_of_entry`), and
  `execBrkSimD`/`execContSimD` re-point at `execExitD_of_pinnedExecExit`.

The upshot: `field_hSBrk`/`field_hSCont` are now PREMISE-FREE — the widener half of
`BrkResid`/`ContResid` follows from the entry alone (`execLeafWidenP_of_entry`), the
slot/table halves from `ExecEntry.ground` (wave 47i).  `ExecArmMemExt` is GONE.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows

local notation "SpecSt" => Vsa.While.St

/-! ## The field discharges — `BrkResid`/`ContResid` from `ExecEntry` alone

`BrkResid`/`ContResid` (`ExecRouting.lean`) demand the `ExecCaseGeom` bundle: the
jump-table slot pin + its stack-disjointness + the (now PINNED) `ExecLeafWidenP`
widener.  The slot/table halves come from `ExecEntry.ground`
(`execGround_caseGeom_brk`/`_cont`, wave 47i); the pinned widener from
`execLeafWidenP_of_entry` (`ExecCaseGeom.lean`), which follows from the
(47e-widened) `ExecEntry.store_survives` alone.  Wave 48d makes the leaf sims
conclude the pin, so no `ExecArmMemExt` premise is needed. -/

/-- **`field_hSBrk`** — `∀ st, BrkResid st`, outright (premise-free, wave 48d).
The slot pin + table disjunct come from `ExecEntry.ground`; the pinned widener
from `execLeafWidenP_of_entry`. -/
theorem field_hSBrk : ∀ st, BrkResid st :=
  fun st _g _N _A _SL _φf _φc _d _env _sp _r _aInterp _aStmt _aEnv _aRet _m0 _c hc =>
    ⟨hc.mem ▸ (Vsa.Sim.Rows.execGround_caseGeom_brk hc.ground).1,
     (Vsa.Sim.Rows.execGround_caseGeom_brk hc.ground).2,
     Vsa.Sim.execLeafWidenP_of_entry hc⟩

/-- **`field_hSCont`** — `∀ st, ContResid st`, outright (premise-free, wave 48d). -/
theorem field_hSCont : ∀ st, ContResid st :=
  fun st _g _N _A _SL _φf _φc _d _env _sp _r _aInterp _aStmt _aEnv _aRet _m0 _c hc =>
    ⟨hc.mem ▸ (Vsa.Sim.Rows.execGround_caseGeom_cont hc.ground).1,
     (Vsa.Sim.Rows.execGround_caseGeom_cont hc.ground).2,
     Vsa.Sim.execLeafWidenP_of_entry hc⟩

/-- The skeleton-hole form (`assembly_skeleton.tsv` row `hSBrk`). -/
theorem skelHSBrk (L : Vsa.Refine.Layout) :
    Vsa.Sim.TermAssembly.Skel.SkelHSBrk L :=
  field_hSBrk

/-- The skeleton-hole form for `hSCont`. -/
theorem skelHSCont (L : Vsa.Refine.Layout) :
    Vsa.Sim.TermAssembly.Skel.SkelHSCont L :=
  field_hSCont

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hSBrk
#print axioms Vsa.Sim.Rows.field_hSCont
#print axioms Vsa.Sim.Rows.skelHSBrk
#print axioms Vsa.Sim.Rows.skelHSCont
