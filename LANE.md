# Lane A0: the boundary world — IN FLIGHT

Package A0 of `VsaIris/INTERP_DESIGN.md` §5.1/§9.

## Done
- Survey. Inputs: `InterpRunReadyFacts` (+ `stack_admissible`), `InitialOwned`,
  R's `Boundary.lean` carving, S1's `costRoom_of_bigStep`, F3's `stackScratch_boundary`.

## In flight
- `VsaIris/Interp/World.lean`: heap shape at a filled memory (`BlockHeapAt.extend`),
  `worldPre`, `world_of_boundary` (both regimes), control vacuity.

## Findings
- The boundary does not say frame 0's struct/names/values allocations each occupy
  their own dlmalloc chunk. §3's `world` requires the store's blocks to be members
  of the heap's live-block list (whole chunk payloads). Carried as the named premise
  `FrameChunks` (checked at the control program); see PROOF_CLOSURE_PLAN.md.
- The boundary does not assert presence of every arena byte, so the heap image is
  read at a filled memory (`BlockHeapAt.extend`).

## Holes
None added.
