# InterpSim completion plan (updated 2026-09-01, wave 37)

`InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem; completion = discharging the four bundles.
check_all: OK, 691/691 axiom-audited (622 at wave 33 — the delta is waves
34–37). History: git waves `bb8eb8c`..`a47bbe0`, the memory files, the
observations sidechannel `experiments/observations.md`, per-wave agent logs
in `experiments/logs/`.

## Where the four bundles stand

- **herrFam** — CLOSED (`errFamilyClosed`); residual = the M6-side `ErrShared`
  instantiation + per-arm `link_*` facts (task #54, mechanical — fully
  templated/generated, zero hand Lean per site).
- **htri** — UNCONDITIONAL (premise-free).
- **hdivFam** — final reduction filling: 7/14 eval-child ArmStages fields
  machine-composed (unary/binaryL/binaryR/logicalL/logicalR/assignE/callF)
  + seqHead; remaining 7 eval (argsHead + 6 stmt*/flCond) + 11 non-eval +
  2 SqEntry + flStep are cut-shaped (task #19: gen_stagepre for the uniform
  3-step class, the argsHead arg-loop shape, the exec-frame class).
- **hterm** — the CALL CRUX IS COMPOSED (wave 37): depth step needed no new
  proof shape; falsities #5/#6 amended (BodyHandoff/emptyBypass); residual =
  the named spans in task #20. EX_FN reduces to 2 named seams (task #18).

## The wave-34..37 arc

- **Falsities #4–#6 found + amended** (s0-reseat frame ghost; the
  CallClosureGeom entryBase 4-way; entryFold independent-pcf). Pattern
  holds: found + amended within the wave, regression guards kept.
- **The CallSpec calling-convention layer** (wave 36, THE exponentiator):
  `CallSpec` (uniform callee record, explicit clobber sets — the
  frame/clobber falsity class is now unstatable), `rzSeamFrame_of_run`
  (ONE red-zone theorem replacing the per-splice hAInvStable*/hjalmem/
  spill-disjointness families), `spliceFold` (zero per-callee theorems at
  any arity). MEASURED: hEntry = 2 named seams + a one-line proof vs the
  strdup hand route's 28 premise lines.
- **Generators hardened + extended**: genseg static callee-saved guard
  (the false-decide→sorryAx mechanism found + fixed); gen_arm_bridge with
  mandatory self-verification (caught a real sorryAx and refused);
  abs_inventory refreshed (GENERATED section + dynamic all-segs index).
- **The concat/STR front CLOSED to plumbing**: blockC_concat_str_closed
  (κ-parametrized dispatch chain — zero proof edits; AbiExceptS2S3 framed
  staging; int tail through the landed snprintf interior).
- **EX_FN**: AllocClosureContract inhabited; hEntry spliced; the arm =
  staging + tail marshalling (task #18).

## Discharge queue (the remaining board, task numbers = session task list)

1. **#18** evalFnSim close: the staging + tail seams of hEntry.
2. **#20** CallClosure residual spans + the exec-motive stack-window
   clause (statement amendment, consumer-analysis-first).
3. **#19** gen_stagepre + the argsHead/exec-side cut classes → divergence
   board to 29/29.
4. **#7** (=old #49/#15) native contracts (print/println via loopFromBody,
   assertOk) + the memcpy word-route framed epilogue.
5. **#8** (=old #54/#55) ErrShared instantiation + link facts; then the M6
   geometry emitter (Layout decides from the linker script), thread
   `interpSim_of_residuals`, end-to-end theorem into check_all.

Estimate: ~2 waves to the assembled close. Tail risks: the exec-motive
stack-window amendment (statement surgery over the exec motive family) and
any 7th falsity.

## Execution notes (binding)

- Coordinator owns `Vsa.lean` + `scripts/check_all.sh`; agents return
  wiring lines. `scripts/abs_inventory.sh` before every dispatch (it now
  lists GENERATED segs + all #derive_case names — grep before deriving).
- Mixed fleet: Fable agents for statement surgery / novel composition;
  opus for template instantiation + crank. Agents log incrementally to
  `experiments/logs/wave<N>-<lane>.md` (stall recovery seed) and append
  observations AT THE MOMENT OF NOTICING.
- Generators MUST self-verify emitted files (`lake env lean` + grep
  sorryAx) — the genseg lesson.
- Elaboration law: no heartbeat raises; log-list rfl BEFORE writeLog
  reflection (the FnArmClosureBuild idiom). Reached-Config bundles are
  `def : Prop := ∃ …` (+ R7 allow when the gate trips on genuine ones).
- Verify with `lake env lean` only; ≤3 concurrent lean; oleans only into
  `.lake/build/lib/lean/`; regen top-level Vsa.olean after Vsa.lean edits
  (else #print axioms sees unknown constants); quiesce agent WIP before
  validating check_all runs.
