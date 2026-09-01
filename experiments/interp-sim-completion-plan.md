# InterpSim completion plan (updated 2026-09-01, wave 40 — NEW-SESSION HANDOFF)

## The one-theorem view (READ THIS FIRST)

`Vsa/Sim/EndToEnd.lean`:

    theorem endToEnd (W : RemainingWork interpRunLayout) : InterpSim interpRunLayout
    theorem endToEnd_refinement …   -- full BigStep ↔ Halts correspondence

**The remaining project = the field list of `RemainingWork`** (= `TermResidualsCore`
+ `errWork : ErrWork`, defined in `Vsa/Sim/TermAssembly.lean` + `rows/ErrFamilyAssembly.lean`).
To know the live status, read that record's fields and grep each for its supplier.
Progress = removing fields (by supplying them inside the theorem) or shrinking a
field's own premises. The wave-39 M6 log (`experiments/logs/wave39-m6.md`) has the
last full field-by-field table.

State: HEAD `e991e3f` (wave 40). check_all: OK, **743/743** axiom-audited (622 at
wave 33). Seven statement falsities found + amended lifetime, every one within its
wave. History: waves 34–40 = commits `bb8eb8c..e991e3f`, one log per lane in
`experiments/logs/wave<N>-<lane>.md`, ledger in `experiments/observations.md`.

## The discharge queue (session task list #s; leverage order)

1. **#26 nativeArmSplice** (observation `native-call-segentry-wrapper`): factor the
   native dispatch/join wrapper ONCE (analogue of `callClosureSim`), +
   `nativeAddr_of_valueRepr` (jalr a6 resolution), + 3 fn-body Triples
   (assertOk = value_truthy ≫ value_null; print/println = `loopFromBody` char loop
   + `chain_out` OutRepr invariant). Per-site batteries already exist
   (NativeWrapperSites/NativeAssertSites). Then 3 native RemainingWork fields close.
2. **The exec mail-merge** (5 arms: stmtRet/stmtVarInit/stmtIfCond/stmtWhileCond/
   flCond): ride `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix`
   (`ArmSegSplitExecEval.lean`) exactly like the landed stmtExpr
   (`rows/StmtExprArmStagePre.lean` — the model; reuses landed `_es` sites).
   Extend `gen_stagepre.py` with the exec template if ≥3 heads are uniform
   (heads differ by instr order + optional beqz). → divergence board 13/14.
3. **argsHead** (the last eval-child field): the arg-loop-entry shape; consume
   `CallArgLoopInv` (rows/CallClosureSplice.lean) — do not duplicate.
4. **The crux marshalling residue** (wave-40 log `wave40-cruxfinal.md`, itemized):
   env_new_pre side-conditions at the dispatch seam; carrier re-assembly between
   rows (GHolds → CallParamFoldInv/BodyHandoff/SegExit); the env_define splice per
   fold param (`foundSt_of_storeRepr`/`frameRepr_append` class); the seq-row
   suppliers (stackWin k=168 + BodyStatusABI); 2 value_null splices; per-bridge
   ChainFacts/hjalSeam instantiations. All marshalling-class, no new theory.
5. **The fn bundle suppliers at the arm site** (AllocBuildStagingLink /
   AllocBuildTailFacts / AllocBuildReloadPost fields — `rows/FnArmSeams.lean` doc
   comments are the spec) + the 9 fn dispatch facts (Layout .rodata jump-table
   bytes at slot 10 — an M6 table item; consider extending `gen_layout.py` to
   emit jump-table slot pins for ALL tags at once: every arm needs its 9).
6. **The 11 NonEvalChildStages fields + SqEntry stmtBlock/callBody + flStep**:
   same `ExecJalPreBundle`/split machinery; suppliers exist
   (`armResidGap_nonEvalChildFields`, `callBody_split`, `stmtBlock_split`).
7. **Remaining TermResidualsCore oracles** (see the wave-39 table): hInitStore
   (drive premises: hSpill/setjmp geometry/span data), hDivCorr (= the ArmStages
   board, items 2/3/6), the leaf/cell `*Resid` oracles (StrCmpOrderBridge landed;
   stringify blocks conditional), var/assign rows, hEpilogueSpill, for-loop GAPs.
8. **ErrWork stragglers**: hBadClosure + hTopAbrupt (non-jal passthroughs), plus
   ErrSharedInputs' open segments (SnprintfContract / MainErrorSeg / Crt0ExitSeg
   — M6 decode class) and the 42 SpillArmPre/SetupArmPre arm linkages (M4).
9. **StoreClosuresBounded** (`rows/StoreReprPhicRebase.lean`): consider proving it
   as a global store-WF invariant of EvalE/ExecStmt (closures only made by
   allocClosure at in-bounds indices) instead of threading per-arm.

Estimate: 2–3 waves of the current cadence. Nothing left is research-shaped.

## Residual burn-down (coordinator-enforced, added wave 43)

- Ledger: `experiments/residuals.tsv` (id, class, status, created/closed wave,
  description). The COORDINATOR updates it per wave: every named residual an
  agent creates gets a row AT LANDING TIME; every closure flips its row.
  Dashboard: `tools/residual_dashboard/` (see its README; d3 burn-down +
  per-class open list, reads the TSV live).
- RULE (the ≥3 law, an instance of Law 3): no residual class with ≥3 open
  instances gets instantiated by hand. First land its combinator/generator,
  THEN a mail-merge lane. Current class targets: `arm-dispatch` (9 — the
  dispatch-bridge combinator consuming the LayoutJumpTableGen slot pins),
  `m4-linkage` (42 — the errSite generator + COW-clone fan-out precedent).
- "Waves left" = number of open classes without a landed combinator/generator
  + the one serial decode chain (native-serial + m6-decode: value_print/fputc,
  Snprintf/MainError/Crt0Exit). The serial chain is the critical path — start
  it early, run it beside the mechanical fan-outs; no abstraction removes it.

## The abstraction stack (REUSE BY NAME — this is what made waves cheap)

- **Call splices**: `CallSpec` (uniform callee record, explicit clobber sets) +
  `spliceFold`/`SpliceChain` (zero per-callee theorems) + `rzSeamFrame_of_run`
  (`LogInRZ` one-omega check ⇒ ABI frame + AInv + code pins + spill disjointness).
  Models: `rows/StrdupTailSpliceFold.lean`, `rows/AllocBuildEntrySplice.lean`,
  `rows/CallClosureSplice.lean`. NEVER thread hAInvStable*/hjalmem families by hand.
- **Divergence fields**: `evalChildField_of_blockA_stage` (eval) /
  `ExecJalPreBundle` + `execEvalEntry_of_jalPrefix` (exec) + the `_mk` builders
  (ArmStagesPartial) + the capstones (`divFamily_wave40`, ArmStagesWave34).
- **Generators** (ALL self-verifying — `lake env lean` + sorryAx grep, hard-error):
  `genseg.py` (segs/bridges; callee-saved-write guard; lds threading — never
  hand-roll a seg), `gen_arm_bridge.py` (blockA bridges), `gen_stagepre.py`
  (the eval 3-step cut class from a 5-tuple TOML), `gen_layout.py` (Layout↔ELF).
- **Motive tables** (signature-free statement extension pattern):
  `stackScratchTop`/`SegExit.stackWin` + `EntryImage` (InductionScaffold) —
  per-PC tables, vacuous when untabled. Use this pattern for any new motive need.
- **Write-log reflection**: log-list rfl FIRST, then offset-normalize, then cheap
  foldl rfl (`fnArmClosureBuild_log_eq` idiom). NEVER rfl writeLog vs an abstract map.
- The full inventory: `scripts/abs_inventory.sh` (run BEFORE every dispatch; has a
  GENERATED section + a dynamic all-segs index — grep it before any #derive_case).

## Fleet protocol (verified across ~20 dispatches this session)

- ≤3 concurrent agents, each ONE lean process. Mixed fleet: **Fable** for statement
  surgery / novel composition / falsity-risk items; **opus** for template
  instantiation, generators, marshalling.
- Every agent prompt: CLAUDE.md laws verbatim reminder; run abs_inventory + `ls
  rows/*Gen.lean`; WORK INCREMENTALLY with a log at
  `experiments/logs/wave<N>-<lane>.md` updated per landing (the stall-recovery
  seed — ~1/3 of dispatches stall on a stream watchdog; with the logs, ZERO work
  was lost across ~8 stalls); observations appended AT THE MOMENT OF NOTICING;
  named-field structures; reached-Config bundles `def : Prop := ∃…` (+ R7
  `-- discipline: allow(...)` when genuine); Law 4 for falsities (machine-checked
  obstruction, never a workaround — 7 precedents); do NOT touch Vsa.lean/
  check_all.sh (coordinator-owned; agents return wiring lines); disjoint file
  ownership per lane spelled out in the prompt; axioms ⊆ {propext,
  Classical.choice, Quot.sound}; `#print axioms` everything.
- On a stall: ground-truth the tree (`lake env lean` the touched files — editor
  diagnostics LIE both ways), read the lane log, respawn with the log as
  inheritance. Two stalls were "finished, died during cleanup" — check before
  redoing anything.
- Known gotchas (put in every proof-agent prompt): `mv`/`li` reflect
  `+ sign_extend imm` (hsext idiom); `gholds_lookup` concludes `gprGet` (use
  exact / rewrite-in-hypothesis, not rw-on-goal); symbolic lookups `by rfl` not
  `by decide`; TAKEN-branch end PCs via `chainEndPC_eq_bt` (multi-block only).

## Checking scripts (the coordinator loop per wave)

1. `scripts/abs_inventory.sh` — before every dispatch.
2. Per agent file: `lake env lean <file>` (green) + `#print axioms` (clean).
3. Wire: imports into `Vsa.lean`, entries into `scripts/check_all.sh` THEOREMS.
4. `lake env lean -o .lake/build/lib/lean/Vsa.olean Vsa.lean` — ALWAYS regen the
   top olean after editing Vsa.lean (else stage c sees unknown constants). If it
   reports a missing module olean, rebuild that module with `-o` serially (the
   dirty-tree cascade); NEVER `lake build`, never LSP tools.
5. `bash scripts/check_all.sh` on the QUIESCED tree (no agent WIP — stage b scans
   untracked files). Stages: a=build+elab-budget, a4=discipline
   (`check_discipline.py`), b=sorry/axiom scan, c=axiom audit of every listed
   theorem. Beware pipefail illusions: `cmd | grep -c error` exits 1 on ZERO
   matches — read the actual tail, don't trust `$?` through a pipe.
6. Commit per wave with the wave summary; end each commit message with the
   check_all count. Update this plan + the memory file every 2-3 waves.

## Standing risks

- The watchdog stalls (infrastructure): mitigated by the log protocol, not fixed.
- Editor/LSP racing builds invalidate oleans mid-wave: rebuild serially, don't fight it.
- An 8th falsity may exist in the un-exercised residue: the pattern says it costs
  one wave, found via the same Law-4 route.
- Generator emissions: trust nothing without the self-verification pass (two real
  bug classes found: false decide → sorryAx; zero-pinned lds).
