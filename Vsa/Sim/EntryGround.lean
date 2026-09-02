import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.MemRegion

/-!
# `EntryGround` — the complete entry-need bundle (wave 47h interface, RELOCATED 47i)

Wave 47h landed the complete entry-suppliable bundle here as a standalone
interface (`experiments/entry-needs-audit.md` §C).  Wave 47i INSERTED the
bundles into the entries — `EvalEntry.ground : EvalGround …` and
`ExecEntry.ground : ExecGround …` — which requires the definitions BELOW the
entry structures, so everything moved (same names, same `Vsa.Sim` namespace,
zero consumer changes):

* `KindSlotPinned`, `KindTablePins`, `AstRegionSpec`/`AstRegionPins`,
  `EvalGround` (+ transports, `survive_stack`) → `Vsa/Sim/InterpEntry.lean`;
* `StmtTablePins`, `StmtRegionSpec`/`StmtRegionPins`, `RetSlotGeom`,
  `ExecGround` (+ transports, `survive_stack`) → `Vsa/Sim/ExecEntry.lean`.

This module remains as the import shim (`Vsa.lean` and
`rows/EntryGroundRows.lean` import it) and the design-doc anchor.

Suppliers: `LayoutJumpTableGen.groundSlot_0..10` /
`LayoutStmtTableGen.groundStmtSlot_0..8` ground the tables from the loaded
image at M6 (`rows/EntryGroundRows.lean`); the AST region is the M6
parse-arena Layout fact (47g verdict).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/
