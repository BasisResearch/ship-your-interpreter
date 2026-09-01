# InterpSim completion plan (updated 2026-09-01, wave 33)

`InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem; completion = discharging the four bundles.
check_all: OK, 622/622 axiom-audited (was 400 at the last plan revision — the
delta is waves 22–33). History: git waves `7813980`..`1e4f887`, the memory
files (`interpsim-completion-campaign.md`, `divergence-endgame.md`), the
observations sidechannel `experiments/observations.md`.

## Where the four bundles stand

- **herrFam** — CLOSED (`errFamilyClosed`); the M6-side `ErrShared`
  instantiation + per-arm `link_*` facts remain (task #54, mechanical — the
  19-PC-class family is fully templated, zero hand Lean per site).
- **htri** — UNCONDITIONAL (`trichotomy_unconditional`, premise-free).
- **hdivFam** — at its FINAL reduction: `divFamily_of_armStages` closes
  `DivFamily L` on `hEntry + hIter + ArmStages` (ApproxArmResidGapAssembly).
  The 29-field fold is proved (ApproxSeamFold — one strong induction on fuel
  across the 6-relation mutual family); all marshalling bridges are
  load-bearing; what remains is filling `ArmStages` (arm-head cuts, task
  #81) and `IterSeamResid`'s three providers — whose `hExecIH` field IS
  hterm's exec_stmt content (the two families' machine work has converged).
- **hterm** — the assembly capstone (`interpSim_of_residuals`) consumes
  `TermResiduals`, which SHRANK by 3 fields in wave 28 (the unsatisfiable
  scaffold `.some` motives amended to True). Remaining fields below.

## The wave-22..33 arc (what landed since the last revision)

- **Entry**: `driveToLoopHead_closed` — the whole prologue drive at the
  concrete layout (spill ≫ setjmp_spec ≫ bnez ≫ loop-setup ≫ loop head),
  coarse premises discharged from proved rows; honest residuals = hSpill,
  setjmp buffer geometry, span entry data, off-path `hFields`.
- **The step-counting layer** (`StepCount.lean`): `Step.steps_succ` →
  `segToTripleN` — every seg row upgrades to a counted `TripleN` for free
  (the machine's own `Config.steps` field carries the count);
  `Landed`/`LandedN` combinators. This killed the feared "divergence twin
  of the M4 sim layer": lower bounds need no posts.
- **The loop-head dispatch span** (`loopHeadDispatch_span`): built once,
  serves iterSeam + approxSeam + the hterm back-edge. Found an INTERIOR
  value_null call in the loop body (seg≫CALL≫seg≫jal — `callSpanSeg`
  combinator proposed).
- **The jal-split layer**: `evalEntry_of_jalPrefix` + exec/SegEntry twins
  (armTail_rec truncated BEFORE its IH — one jal step lands at the child's
  rich entry, child not returned) + 29/29 field splits + the
  `binaryR_midStagePre` MID-ARM COMBINATOR (the feared ~250-line-per-op
  threading factored once: the left-span entanglement is honest carried
  premises `SubEvalReturn` already establishes).
- **Str front**: stringify decoded (= Value.display); `Code/Stringify.lean`
  pins generated (105 sites); all three strdup-tail jal seams closed;
  `stringifyStrdupTailContract_closed` (modulo the entry supplier + 2 named
  memcpy-bridge infra gaps); `cstring_append`/`concatReadback` (the general
  C-string concat lemma — the concat C-block's post is now mechanical); the
  3 concat staging segs; ALL SEVEN callee contracts for the concat splice.
- **Contract layer**: `MallocContract.freeSpec` (exts-POPPING — dlmalloc
  reuses freed blocks, so frame-only would be uninhabitable);
  `AllocClosureContract` + `storeRepr_pushClosure` (the missing
  StoreRepr-grow lemma); `armEntry_widen` + `preEpilogueV_of_writeLog` (the
  two parametric arm lemmas serving every composite arm's front/back);
  `fnArmGeom_hArm_of_seam` (fn arm composes end-to-end modulo the
  AllocClosureContract inhabitant).
- **Statement falsities found + amended (Law 4), all with regression
  guards**: NullBridgeSeam.splice's contradictory entry (two PC pins →
  False); the scaffold `.some` motives (unsatisfiable AND dead plumbing —
  TermResiduals shrank); StrcpyContract's frame alias (the aligned word
  path clobbers a2/a3/a6 — `NotWrittenB` → `NotWrittenCpw`, sound
  inhabitant landed from the pre-existing `strcpy_full_spec`).
- **Gate hardening**: stage c joins Lean's wrapped axiom-report lines
  (long names were silently uncounted); measured discipline payoff:
  de-positionalizing one glue proof took its file from a 94s elab-budget
  WARN to zero.

## Discharge queue (the remaining board)

In flight (wave 34): **#81** ArmStages fan-out (exec-side stagings, head
cuts, logicalR value_truthy variant, SqEntry spans, the shared blockA_k
dispatch cut); **#82** str last pieces (segToTripleLds + the
`MallocContract.nonNull_of_bounded` field, then `concatHeapCore`).

Then, in leverage order:
1. **The two bespoke machine spans** — `evalAssignSim` (front covered by
   armEntry_widen; identity-φ HIT tail) and the CallClosure crux
   (callee-eval ⋈ arg-loop ⋈ dispatch at d+1). The largest single items.
2. **The AllocClosureContract inhabitant** — 3 named pieces over existing
   segs (arm-head a3 decode + malloc splice over fnArmMallocCallBridge +
   build write-log marshalling) → `fnArmGeom_closed` → evalFnSim.
3. **#49 native contracts** — print/println char loop (`loopFromBody`) +
   assertOk.
4. **#15 memcpy word route** — framed epilogue via FrameMeta (gates
   hRoutePrintln).
5. **#54 error links** — ErrShared instantiation + link_* facts
   (mechanical).
6. **#55 M6 close** — the geometry emitter (generate the concrete Layout
   decides from the linker script, like the decode table), Layout
   instantiation, thread `interpSim_of_residuals`, end-to-end theorem into
   check_all.

Non-blocking hygiene: #31 keys_evalBlocks, #32 de-towering, #45 stale-file
deletion, #11 legacy strlen re-seat, #57 PredIso adapter class. Harvest
`experiments/observations.md` every wave.

Estimate: **~3–5 waves** to the assembled close. Tail risks: the call crux
(depth-indexed recursion) and any further statement falsity (pattern so
far: found + amended within one wave).

## Execution notes (unchanged, still binding)

- Coordinator owns `Vsa.lean` + `scripts/check_all.sh`; agents return
  wiring lines. `scripts/abs_inventory.sh` before every dispatch; reuse by
  name. Agents log missing-general-facts + duplicate/mechanical work to
  `experiments/observations.md` AT THE MOMENT OF NOTICING.
- Elaboration-budget law: no heartbeat raises — a timeout means the
  construction is wrong. Landing bundles carrying a reached Config are
  `def : Prop := ∃ …`, never structures (Prop structures reject Config
  data fields; Type structures block Exists elimination).
- Verify agent files with `lake env lean` BEFORE wiring (stale IDE
  diagnostics lie both ways). Read gate TAILS before committing; never
  chain commit&&push behind an unread gate. check_all stage b scans
  untracked files — quiesce agent WIP for validating runs.
- ≤3 concurrent lean; `lake env lean` only, never `lake build`, never LSP.
  Dirty-tree olean cascades: rebuild serially with `lake env lean -o`.
