# Wave 34 Task #82b — instantiate concatHeapCore seams + lift to StrConcatCBlockResid

## State on entry
- `concatHeapCore` (rows/ConcatHeapCore.lean) is LANDED, pure callSeg/Triple.seq algebra
  over abstract Config→Prop seams S1..S7 with 8 callee contracts + 7 seam bridges as
  NAMED hypotheses. Green + axiom-clean.
- Callee contracts landed: `MallocContract.spec` (malloc), `MallocContract.freeSpec` (free×2),
  `MallocContract.nonNull_of_bounded` (no-OOM prune), `strlen_spec_framed`,
  `memcpy_spec_framed_byte`, `StrcpyContractCpw`, `value_str_spec_full`.
- Staging segs landed (rows/ConcatCBlockStaging.lean): concatMallocArgRow / concatMemcpyArgRow
  / concatStrcpyArgRow — SegPre→...Post Triples parked at jal seams.
- CString glue landed (rows/CStringAppend.lean): cstring_append / concatReadback.

## Plan
1. Instantiate seam predicates concretely; produce `concatCBlockTriple_of` — concatHeapCore
   with malloc/free×2 plugged from `M`, no-OOM prune from `M.nonNull_of_bounded`, value_str
   seam readback from `concatReadback`. Remaining SegPre↔entry marshalling seams stay NAMED.
2. `binArmStrResid_of_cblock`: lift to StrConcatCBlockResid via
   blockA_binaryArm ≫ (two sub-EvalIH) ≫ concatHeapCore ≫ blockD_v_rec.

## Findings

## Result

### Step 1 — LANDED: `Vsa/Sim/rows/ConcatSeams.lean` (green + axiom-clean, discipline OK)
Seam/callee discharge status:
- DISCHARGED `malloc` slot   = `M.spec`  (`concatMallocSlot`)
- DISCHARGED `free1`/`free2`  = `M.freeSpec` (`concatFreeSlot`, both slots)
- DISCHARGED no-OOM prune @beqz = `M.nonNull_of_bounded` (`concatOOM_prune`, via `ConcatMallocPost.disj` named destructurer)
- DISCHARGED value_str readback = `concatReadback` (`concatValueStrSeam_readback`)
- `concatCBlockTriple_of` = concatHeapCore with those 3 callee slots pre-plugged;
  the 4 call-threaded callees (strlenL/strlenR/memcpy/strcpy/valueStr) + 7
  marshalling seams remain arguments (call data / straight-line residuals).
REMAIN (named, threaded — genuine call data or straight-line):
- strlenL/strlenR = strlen_spec_framed (per-call instantiation)
- memcpy = memcpy_spec_framed_byte; strcpy = StrcpyContractCpw; valueStr = value_str_spec_full
- seam0/seam1/seamSc/seamEnd/seamQ = SegPre↔entry `mv`-staging bridges (straight-line)
  (seamM/seamMc/seamF1/seamF2/seamV keyed to the concrete malloc/free pre/post now)

### Step 2 — BLOCKED (Law 3b, reported): `binArmStrResid_of_cblock` needs a
missing `blockC_concat` combinator. The plan's `blockA_binaryArm ≫ blockB_binary ≫
concatHeapCore ≫ blockD_v_rec` is NOT type-correct: blockB_binary's TwoSubReturn is
the arith path; the concat C-block is reached via operator-dispatch → STRINGIFY-arm
(two `stringify` calls, not the operand eval_expr calls). The middle span
`operator-token dispatch → two-stringify entry → concatHeapCore.P` has never been
built (~200-line bespoke = forbidden battery). Recorded in observations.md.

### Wiring (report-only, NOT applied)
- Vsa.lean: `import Vsa.Sim.rows.ConcatSeams` (after ConcatHeapCore + StrcpyContractInhab imports)
- check_all.sh axiom list: add
  Vsa.Sim.{concatMallocSlot, concatFreeSlot, concatOOM_prune, concatValueStrSeam_readback, concatCBlockTriple_of}
