# Lane S1: cost existence, stack admissibility, Room/Cost bridge

Design: `VsaIris/INTERP_DESIGN.md` §5 (§5.1b), §9 (S1), §10.4, "STATEMENT CHANGE".

## Done
1. **StackAdmissible (Q1).** `InterpRunReadyFacts.stack_admissible`
   (`Vsa/Sim/LayoutInstance.lean`: `ProgramStackFits`, `programStackFits`
   checker, `ProgramStackFits.execBudget`). `Refinement.lean` is unchanged, and
   `interpRunLayout' = interpRunLayout`.
   - Control witness: `NativeNameAudit.Control.readyFacts`.
   - `c/tests/*.wl` witnesses: `Vsa/Sim/StackAdmissibleWitness.lean` (kernel
     `decide`).
2. **Cost existence/soundness.** `Vsa/While/CostExists.lean`:
   `EvalECost.exists` … `ExecSeqCost.exists`, `BigStep.cost`, and
   `EvalECost.sound` … `ExecSeqCost.sound` (`CostExists`/`CostSound`).
3. **Room ↔ Cost bridge.** `VsaIris/Vsa/CostRoom.lean`:
   - byte-credit `costRoom` for `isHeapRoom`;
   - per-site `Covers` lemmas (`physSize n ≤ 2c`);
   - `CostTop.spend`/`.split`;
   - `costRoomAt` + `mallocCostSpec`, with obligation `MallocCostRun` (H4);
   - boundary `costRoom_of_bigStep`;
   - control witness `Control.costReserve`.

## In flight
None.

## Holes
None added. The `alloc.mallocRoomRun` row in HOLES.md now names its
byte-credit form `MallocCostRun`, which H4 owns.

## Next (for other lanes)
- A0 sets `heapRes (.counted k) := isHeapRoom vsaLayout costRoom H k` and
  starts it from `costRoom_of_bigStep`.
- H4 proves `MallocCostRun`, and the realloc analogue at `costRoomAt`.
