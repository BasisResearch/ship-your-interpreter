# InterpSim completion plan (2026-08-31)

`InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem; completion = discharging the four bundles.
The metaprogram layer (chain_facts, #derive_error_site, segToTriple,
loopFromBody, callSeg) and the row/reduction layer are both built: every bundle
is reduced to named typed residuals, none unscoped. check_all: OK, 400/400
axiom-audited. History lives in git (waves `7813980`..`34dbd7e`), the memory
file `interpsim-completion-campaign.md`, and the per-front ledgers in
`experiments/`.

## Where the four bundles stand

- **herrFam** — CLOSED (`errFamilyClosed`).
- **htri** — rests on `StmtDispatchD` + `hroot`
  (`trichotomy_of_stmtDispatchD`, `Vsa/While/Trichotomy.lean` §5). The
  within-statement-divergence spec bug is fixed (`SApprox` family +
  `Approx.head`; demo `loopP_diverges`).
- **hdivFam** — `DivCorrFamily`: supplied by the same forward-sim Triples as
  hterm (progress-only skeleton), nothing independent to build.
- **hterm** — ~26/50 recursor premises have slot-verified rows; the rest of the
  work is discharging the rows' named residuals plus the un-rowed ExecS
  dispatch/loop family, then the table assembly.

## The exponentiating layer (LANDED 2026-08-31) and its enforcement

Diagnosis: env_define's cost came from proving on the wrong layer — bespoke
per-site batteries (four near-identical prefix-runs beside a region that was
already 106/106 decode-tabled) and per-callee framed-post re-derivations. The
force multipliers are now LANDED; queue items below are consumed THROUGH this
layer, not beside it:

- **`FrameMeta`** (`abiFrame_of_wrChain`/`memFrame_of_chain`/
  `bblocks_sound_framed`): ABI + memory frames for any reflected chain by one
  `decide` each — framed callee variants are FREE (the block-reflection
  soundness lemmas already carried the clauses; these are thin corollaries).
- **`BridgeSeg.bridgeOfSeg`** + `jalStep_of_obs`: the Shape-A bridge shape
  factored once. Measured on capCompute: 350 hand lines / 6.8s → 72 lines /
  1.5s; each remaining bridge ≈ 35 lines. `MKind.slliw` added to the shared
  core (5-bit shamt; whole-struct `mkLine` rfl freezes for it — assert
  decoded fields individually). Model files: `EnvDefSeg.lean`.
- **Discipline gate** (`check_all` stage a4 = `scripts/check_discipline.py` +
  `scripts/discipline_rules.tsv`): hand site batteries, heartbeat raises,
  hand frame threading, framed re-derivations, stepObs-volume — FAIL for new
  files. 647 legacy files grandfathered (shrink-only). Extending: one TSV
  line per new rule; when a new abstraction lands, add it to CLAUDE.md's
  mandatory-use table AND add a rule catching its hand-rolled equivalent.
- **`CLAUDE.md`**: the standing laws + task-shape→tool table for every future
  session. **`experiments/observations.md`**: agents append missing-general-
  fact observations AT THE MOMENT OF NOTICING (survives stalls); coordinator
  harvests to the task board.

Legacy shrink (`experiments/legacy-elimination-plan.md`): NOT campaign
priority. Only its Tier-0 build-time experiment (the 512 generated DecodeTable
files' uniform 16M-heartbeat constant — DecodeTable dominates build CPU) is
worth a slot DURING the campaign, and only if the measurement shows a rebuild-
speed win that pays back in iteration rate. Everything else is post-campaign
hygiene under the ratchet.

## Discharge queue

Ordered by leverage and dependency; each item is scoped with reuse identified
(details in the session task board and ledgers).

1. **env_define bridges** (5 of 9 remain — namesToVals CLOSED via the
   `GrowEnvEntry` struct-pin seam): each remaining bridge = a `#derive_case`
   seg + `bridgeOfSeg` application (~35 lines; `capComputeSeg_run` is the
   model). bridgeStore additionally uses the landed `frameRepr_append` core;
   appendHead reuses the realloc `JalStep` shape; hUpdate's straight-line
   prefix via `bridgeOfSeg`, its scan via the env_get scan shape
   (`loopFromBody`); memcpy word-route framed epilogue via `FrameMeta` (no
   ghost re-run). Unblocks hAssign, hSVarInit/hSVarNull/hSBlock, and the
   Call.closure env-fold.
2. **ExecS dispatch/loop arms** (if/while/for/block/seq) — the largest
   un-rowed family; `execBlockA`/`execBlockD` + the loop shapes exist; each
   arm = seg chains (`#derive_case`/`chain_facts`) + `callSeg` seams +
   `ExecRecWiden`, frames free via `FrameMeta`.
3. **Call residuals** — native print char-loop body (`loopFromBody` +
   `NativeDispatchSpan`), `CallArmSpec`/`FnArmSpec` (unblocked by
   `blockD_v_phic`; entry via `blockA_binaryArm`-style bridges), retNull glue
   assembly (site batteries + `NullBridgeSeam` landed — the ld-step +
   splice compose via `callSeg`), `ArgsNilHop`, `ArgsBodyOracle`.
4. **hBinary str cells** — str-cmp arm chain (sign tails + callees landed;
   assemble via `cmpDispatch`-style segs + `callSeg` on `strcmp_full_spec`;
   `StrCmpOrderBridge` = String.lt ↔ strcmp sign is the one spec-layer gap)
   and the stringify/concat path (biggest single new development; give
   `stringify` its framed spec via `FrameMeta` over its reflected chain, not
   a ghost re-run).
5. **hVar last layer** — `VarPostRepack` + `EnvGetCallerGeom` discharge at the
   arm (`foundSt_of_storeRepr` marshalling + `env_get_found_framed` landed;
   the repack consumes the memory-frame post).
6. **Entry seams** — `StoreInitSeam` (env_new startup: seg the prologue via
   the tabled region + `setjmp_spec` `callSeg` splice) + `EpilogueFrame`
   (`restoreRetChain_run` reuse); closes hEntryHalts via `hEntryHalts_closed`.
7. **hCallClosure** — after (1): arity + depth guard + env_new +
   env_define-fold (`frameRepr_append` per slot) + body-ExecSeq at d+1, all
   `callSeg` seams.
8. **Error-judgment amendment** (3 rules: ExecSeqErr abrupt-head,
   CallErr.badClosure, for-init) — discharges the three named holes of the
   LANDED `trichotomy_closed`/`htri_closed`, making htri unconditional; audit
   the error-family consumers (routing generator absorbs new premises).
9. **Assembly + M6** — unify residuals into `TermShared`/`TermCallees`/
   `TermGuards`, fill the `@EvalE.rec` table, `termSimClosed`, hdivFam from
   the same Triples (the `DivStep` conjunction's two arms), Layout bundling
   into `Vsa.Refine.refinement`, final axiom audit, end-to-end theorem into
   check_all.

Non-blocking exponentiation refactors, do opportunistically (each also
retires grandfathered files): re-seat the strlen byte-tail + the four hand
prefix-runs on `bridgeOfSeg`/`FrameMeta` (retires the R3/R1 files); re-seat
`interpContSeg_of` on `restoreRetChain_run`; generic-`w` cmp fixup bridges
(serve int + str arms); `keys_evalBlocks` subset lemma (task #31 — drops
`bridgeOfSeg`'s per-seg key decides to zero); generator for the
thrice-duplicated 42-premise error-site list. Harvest
`experiments/observations.md` every wave for new candidates.

## Execution notes

- Coordinator owns `Vsa.lean` + `scripts/check_all.sh`; agents return wiring
  lines. Run `scripts/abs_inventory.sh` before every dispatch; reuse by name.
- Elaboration-budget law: no heartbeat/timeout raises — a timeout means the
  construction is wrong; fix with more abstraction (check ground literals
  first on whnf timeouts). Residuals are named typed premises, never sorry.
- ≤3 concurrent lean; agents use `lake env lean` only, never `lake build`,
  never LSP. Under API instability: single-agent regime, no check_all
  concurrent with agents, bake salvaged diagnoses into relaunches, do
  near-done or spec-layer items inline.
- check_all stage b scans untracked files — move agent WIP aside for
  validating runs; read the output tail, not just the exit code.
