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
| `smt_check.py --joint` | INTERLOCK validation: joint inhabitation of a whole structure + producer⇒statement + statement⇒consumer queries — the 48e/48g composition failures as machine checks | landed; all 4 history failure modes detected at intended verdicts. Fixtures cover the encodable fragment only; opaque geometry → MODULO-OPAQUE, never silent. Prospective test = live use in the interlock sessions |
| `cegis_cure.py` | candidate AMENDED statements for a false/blocked Resid: enumerate the cure-template space (entry-conditioning, quantifier repair, guard repair, redundancy deletion, oracle re-homing), filter by elaboration/Z3/`--joint`/descent | landed; history acceptance rank-1 on the 47i/48f/48g cures, and GENUINE under `--blind` ablation (statement + machine-checked obstruction only, docs excluded — the ghost the refutation witness degenerates names the repair template). Intra-candidate ranking on symbolic-window forms stays a template+edit-cost heuristic; prospective sealed suites are the strongest test. Only `REFUTED-REPLAYED` drops a candidate |
| `smt_check.py` bounded (`experiments/smt/bounded/gen_probe.py`) | prove a supplier field by definition-encoding — datatypes + `define-fun-rec` + QF_ABV Mem, negation-UNSAT = a validity proof | proves the non-recursive stratum (ValueRepr null/bool/int readback → UNSAT ~20ms, replayable to `read32_copy`/`readLE_copy`). The inductive wall is sharp: recursive Repr (CString) → SAT until the IH is added, because the gap is the hypothesis, not depth |
| `writelog_smt.py` | emit an arm's computed write-log (block-reflection's `wlogM`/`writeLog`) as SMT array-stores, so the machine effect is expressible without encoding the Sail step | flips exec-arm FRAME obligations (`MemExtends` + window-`agree` + pins) from ENCODE-GAP to Z3-UNSAT ~20ms, control-SAT faithful. The recursive `StoreRepr` survival half stays Houdini territory; data-value readbacks thread `runGM` (encodable, not yet exercised) |
| `houdini_ih.py` | in-house Houdini IH-selector: seed candidates (the `*_agree`/`*_preserves` zoo + Z3's CTI + traces), drop the non-inductive ones against Z3, keep the maximal inductive subset | rediscovered `cstring_agreeP` blind (Z3-oracle only, no Spacer), and the acceptance held under ablation. Houdini SELECTS from the vocabulary, it does not invent — the LLM expands the vocabulary when the pool is short |
| `autoprove.py` + skill (`experiments/autoprove/`) | the integrated IVy-style loop per field: write-log encode → Z3 close → Houdini IH-select → LLM-protocol on a vocabulary gap → transcribe to Lean, kernel-check | in build (write-log emitter landed first). Decomposes the field bundle: frame → Z3, recursion → Houdini, novel induction → LLM; a Z3-UNSAT is a design-time certificate, the Lean term is still transcribed |
| Batteries | `experiments/fuzz-battery/` (NovelProbe, FreshTriWin, FreshValDemand) | spent-vs-fresh discipline: generality claims only via probes the tool never saw |

`autoprove` is the IVy loop for supplier fields, with an LLM where IVy keeps a
human. IVy proposes an inductive invariant, Z3 checks it, and a
counterexample-to-induction sends you back to strengthen. The pieces map
straight across. Z3 checks a candidate in ~20ms. Z3's SAT model is the CTI. The
LLM reads that CTI and proposes the strengthening through the request/response
protocol. Houdini prunes to the maximal inductive subset, and the loop repeats
to UNSAT. Two guards go beyond vanilla IVy: every proposed clause is
fuzzer-checked for falsity before it is accepted, so a bad proposal cannot slip
a false lemma into the chain, and the loop ends in a Lean term the kernel
checks rather than a formula in its own logic. The discipline that makes the
oracle complete is IVy's own: stay in a decidable fragment. IVy uses EPR; we
bound the datatypes so every check lands in QF_ABV and Z3 always answers.

The reach is a decomposition, not a blanket. A supplier field is a conjunction
of obligations, so `autoprove` splits it: frame and window and pin clauses go
to Z3, recursive-Repr clauses go to Houdini, and the genuinely novel induction
goes to the LLM or a hand proof. Nearly all of this corpus closes at the design
level. The residue is three things, each real and each smaller than "not
provable": the Lean transcription of a closed loop, the rare invariant the
vocabulary cannot reach, and convergence reliability. Undecidability is why it
is not literally all; the machine encoding is not the wall.

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
- **The cure-wave protocol** (waves 47e–48g taught it, the validation stack
  now runs it). A blocked field means a false statement. The prep step runs
  `cegis_cure.py` to generate ranked amended statements, filters them through
  `smt_check.py --joint` for the interlock traps, seals the surviving suite,
  and only then opens a writer session to transcribe the top candidate and
  relight. Discovery moves out of the proving session, where it used to turn
  one wave into a ladder.
- **Adversarial everything**: statements are validated by refutation attempts
  (the fleet proved the record itself uninhabitable, which was falsity #12);
  tools are validated by batteries they couldn't train on (two overfit claims
  caught this way) and by ablation (CEGIS's history acceptance held with the
  answer-bearing docs stripped); cures are validated jointly rather than per-statement (the
  48e interlock lesson). Law 4 stands: a blocked step returns a machine-checked
  obstruction, never a workaround.

## 7. Where things stand

`experiments/REMAINING.md` is authoritative. `experiments/design/MASTER.md`
holds the 31-task execution plan, and the wave logs live under
`experiments/logs/`. The commit history (waves 41–48+) narrates each layer
landing with its measurements.
