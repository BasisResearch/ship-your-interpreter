# The tooling & abstraction stack

This proof stays subexponential because every layer below turns a class of
hand-proofs into a generator run, a combinator application, or a validation
query. The effort curve bends exactly where these layers exist, measured
repeatedly in `experiments/observations.md`, the append-only ledger of every
missing-abstraction observation and how it resolved.

Enforcement is mechanical. `scripts/check_all.sh` stage a4
(`check_discipline.py` + `discipline_rules.tsv`) fails any file that hand-rolls
what a layer already provides. `CLAUDE.md` is the contract; this file is the
map.

## 1. The Lean abstraction stack (proof-side)

The stack is layered bottom-up, and each generation subsumed the per-instance
cost of the one below it. Reuse by name: run `scripts/abs_inventory.sh` before
any proof work.

| Layer | What it kills | Key names |
|---|---|---|
| Block reflection | per-site `StepObs` batteries (~180→39 lines/run) | `bblock_sound_bt`, `block_facts`, `chain_facts` (`BlockMem/BlockDecode/BlockTerm/LoopStep.lean` — the `MKind` decoder, 34 kinds, widths {1,2,4,8}) |
| Segments | hand block-chains; straight-line/branch/jump spans | `#derive_case` + `segToTriple` (`DeriveCase/DeriveCaseRow.lean`), `segToTripleFramed`/`segRowFramed` (`SegToTripleFramed.lean` — keeps the frame + sailOutput clauses) |
| Call seams | jal/jalr splices | `callSeg`/`callSegConseq` (`DeriveCallSeg.lean`), `bridgeOfSeg` + `jalStep_of_obs` (`BridgeSeg.lean`), `stepObs_jal/jalr` |
| Loops | whole-loop total correctness from ONE body obligation | `loopFromBody` (`DeriveLoop.lean`), `Triple.loop`, `LoopSteps` |
| Whole functions | multi-block CFGs: branches+loops+calls+tail-j+tohost seams | `FnSummary.{seq,callSplice,tailJump}` (`FnSummary.lean`); model folds `rows/FnWrite{,R}Fold.lean`, `rows/FnSwriteFold.lean`, `rows/FnSfvwriteFold.lean` (2782-line fold incl. the first indirect-`jalr` seam) |
| Frames | per-site ABI/memory frame threading | `FrameMeta.abiFrame_of_wrChain` / `memFrame_of_chain` (one `decide` each) |
| Widening | the 5-widener zoo → one parametric structure | `Widen` + bridges (`WidenMeta.lean`); pinned-exit variants `LeafMemPin`/`ExecLeafWidenP` etc. |
| Marshalling | bundle→bundle field threading, `.2.2.2` towers | the `repack` tactic (`RepackTac.lean` — field-matching metaprogram over named-field structures), named destructurers, `EntryBridge` (prototype: entry-leg transport) |
| Entry grounding | per-site ground literals | `EvalGround`/`ExecGround`/`NBSPins`/`EntryImage` + generated pin tables (`EntryGround.lean`, `rows/Layout*TableGen.lean`) |
| HTIF | console/exit semantics | `htif_store_putchar/exit`, `mem_write_value_tohost_*` (`Htif.lean`, `HtifLift.lean`), `try_step_tohost_*` |

The elaboration laws below are non-negotiable, enforced by experience and by
gate rules. Reflect on the first-order write-log, never whnf Sail state. One
small `decide` per fact. Emit terms, not tactic scripts. Never raise
`maxHeartbeats`: a timeout means the construction is wrong.

## 2. Generators (`scripts/`)

Every generator is self-verifying (`lake env lean` + a sorryAx grep, hard-error
on failure). Grep for the target artifact before you generate, since the tree
has repeatedly run ahead of the plans.

| Tool | Emits |
|---|---|
| `genseg.py` | seg + post + row from an arm TOML (`scripts/arms/`); callee-saved-write guard; framed-bridge mode |
| `gen_fn.py` | whole-function block arms + (recognised loop shapes) the derived `FnSummary` fold (`--fold`, templates in `genfn_templates/`) |
| `gen_code_lemmas.py` (`experiments/`) | per-function code-byte pin modules (`Vsa/Sim/Code/`) with discipline-allow emission |
| `gen_transport.py` | per-byte code/pin transport lemmas (the `writeLoaded_of_agree_lo` class) |
| `gen_layout.py`, `gen_image_pins.py` | layout↔ELF pins, jump-table slot pins, static-data images (cross-checked against `objdump` of the proof ELF) |
| `gen_err_spill_rows.py`, `gen_m5_error_routing.py` | the 19 error-site span rows + 42 hsite links (idempotent) |
| `gen_arm_bridge.py`, `gen_stagepre.py`, `gen_*_row.py` | blockA bridges, eval/exec stage-pre rows, recursor case rows (TSV-driven) |
| `gen_assembly_skeleton.py` (`experiments/`) | `rows/AssemblySkeleton.lean` — one named hole per record field + the total assembler; regenerate after any field change |

## 3. The validation stack (design-time; NOTHING here enters a proof)

The deliverable's purity is triple-gated (`check_all` stages b/c: the
banned-tactic scan plus `#print axioms` ⊆ {propext, Classical.choice,
Quot.sound}). These tools exist so no session is ever again spent proving
toward a false statement, which has been the dominant historical cost
(falsities #1–#16).

| Tool | Question it answers | Status/limits (honest) |
|---|---|---|
| `field_census.py` | "does a landed theorem discharge this record field outright?" (`exact?` probe per field) | THE progress metric; recomputed from the compiled library, cannot rot |
| `statement_fuzz.py` | pre-proof refutation by witness. v1: outer-telescope lethal witnesses. `--descend`: nested conjuncts (2-row builder table = regression guard for known forms). `--semantic` (v2.1): the uncovered-address interval algebra — general over the literal address-map fragment, verified on fresh probes | v2.1 analysis is general; the probe-EMITTER lacks the agree-demand template (honest UNDECIDABLE). Symbolic bounds → SMT territory |
| `--gen-battery N` | fresh sampled probe pairs with ground truth by construction — the uncontaminated acceptance that can't be trained on | any FIXED battery is spent once used in development (proven twice) |
| `smt_check.py` | Z3 countermodel search (`--refute`, model replayed through Lean — Lean remains the authority), validity (`--validate`), inhabitation (`--inhabit`); encoder v2 = the `dump_smt_lib` export tactic (`experiments/smt/DumpSmtLib.lean`) walking the elaborated Expr | search layer general; REPLAY generator template-bound (loud ENCODING-GAP on novel shapes — flagged witness + ~5-line hand refutation is the operating mode). Opaque predicates (ValueRepr/CString/GoodState/…) uninterpreted → REFUTED-MODULO-OPAQUE never auto-replayed |
| `smt_check.py --joint` (in flight) | INTERLOCK validation: joint inhabitation of a whole structure + producer⇒statement + statement⇒consumer queries — the 48e/48g composition failures as machine checks | in-fragment only; opaque demands → UNKNOWN-OPAQUE |
| `cegis_cure.py` (in flight) | candidate AMENDED statements for a false/blocked Resid: enumerate the cure-template space (entry-conditioning, quantifier repair, guard repair, redundancy deletion, oracle re-homing), filter by elaboration/Z3/traces/descent | acceptance = rediscover the landed 47i/48f cures from history |
| Batteries | `experiments/fuzz-battery/` (NovelProbe, FreshTriWin, FreshValDemand) | spent-vs-fresh discipline: generality claims only via probes the tool never saw |

## 4. Invariant generation (mining pipeline)

The pipeline is validated end-to-end, over a plan plus four validation rounds
(`experiments/invariant-gen-plan.md`). Two flagship measurements: the complete
`WInv` loop invariant mined from one 6-second model run, and falsity #13's
budget ladder refound from depth traces alone. The hand fold is 873 lines; the
mined-invariant residual obligation is 3 sub-goals over 4 lines (omega/rfl).

| Stage | Tool |
|---|---|
| Trace | `gen_trace.py` — patches a traced loop into a /tmp COPY of the emulator (probe PCs + regs + mem windows), runs the `.wl` corpus, JSONL out |
| Segment | `segment.py` — per call-instance (frame register), the fix that recovers relational facts |
| Mine | `mine.py` — T1 constants / T2 linear / T3 strides / T4 guards / T5 mem-window facts, corpus-vocabulary-scoped |
| Relational | `mine_relational.py` + `wl_to_lean.py` + the spec-trace driver — machine trace × executable spec semantics aligned at seams; mined conjuncts matched the landed bridge facts field-for-field on the pilot |
| Orchestrate | `invgen.py --case/--batch` — one command per case; auto-fuzz (candidate + mutant) built in |
| Ladder miners | `mine_stack_ladder.py`, `mine_crux_ladder.py` — recursion depth/budget relations (crux inputs validated: every mined relation matched the design) |

The corpus comes from `gen_corpus.py` → `experiments/corpus/` (97 cases, one
CFG+calls+cluster per case, INDEX.md). Candidates land in
`experiments/invariants/` (with `SEEDS-io.md`, `BATCH-REPORT.md`,
`crux-relations.md`).

## 5. The empirical harness

`riscv-lean/lean_emulator` runs ELFs in the EXACT proof model (~10 s). The
recipe (the "t5" harness): craft a `.wl`, build it in a **/tmp COPY of `c/`**
(NEVER build in `c/`; the proof ELF is the object under study, sha256
`b146c6ed…d0f0`, verify after any session), run, then compare output and exit.
It retracted one false "falsity" (stdout buffering, where `setvbuf` is main's
first statement), confirmed the io contracts, the String-order direction and the
div-overflow wrap, and refuted a wrong dead-code claim (`print(null)` does
reach `fwrite`). Standing rule: trace absence is driver-relative, so a deadness
claim needs a static call-graph proof or all-kind driver coverage.

## 6. Process machinery

- **The scoreboard**: `experiments/field-census.tsv` (via `field_census.py`)
  is the only trustworthy progress metric. The map is `experiments/REMAINING.md`
  (reconciled 2026-09-02). Plans go historical the moment they lag the tree, so
  reconcile-first is a standing brief preamble.
- **Fleet protocol**: workers run in APFS COW clones (`cp -Rc`, warm oleans),
  touch NEW files only, and return staged; the coordinator wires and gates.
  Per-landing incremental logs (`experiments/logs/`) are the stall-recovery
  seeds. Bounded single-mandate tasks with commit-at-green beat monoliths,
  measured at ~9/9 against 0/2.
- **Gates**: `check_all.sh` (discipline + purity scan + axiom audit of the
  battery theorems); `rbuild.sh` offloads full builds to the remote box. Never
  `lake build` locally in the proof tree, never LSP (the coordinator's
  build-guard auto-kills both); `lake env lean <file> [-o olean]` only.
- **Overnight rule**: `caffeinate -ims`, and it needs AC power. It does NOT
  hold on battery. macOS Maintenance Sleep killed agent streams until this was
  found.
- **Adversarial everything**: statements are validated by refutation attempts
  (the fleet proved the record itself uninhabitable, which was falsity #12);
  tools are validated by batteries they couldn't train on (two overfit claims
  caught this way); cures are validated jointly rather than per-statement (the
  48e interlock lesson). Law 4 stands: a blocked step returns a machine-checked
  obstruction, never a workaround.

## 7. Where things stand

`experiments/REMAINING.md` is authoritative. `experiments/design/MASTER.md`
holds the 31-task execution plan, and the wave logs live under
`experiments/logs/`. The commit history (waves 41–48+) narrates each layer
landing with its measurements.
