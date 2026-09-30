# Abstraction-discovery round 4: the Iris-level interpreter proofs (2026-09-30)

Branch `exp-R4`, from `exponentiate` 95acd019 (after ROUND-3). Target: the separation-logic
plumbing of the interpreter's arm, spec and call-adapter proofs in `VsaIris/Interp` (frames,
spec applications, call adapters, continuation shapes, register-keep facts, stack arithmetic).
Machine runs (`sym_run`, `IW`, `MRun`) are not the target. Raw material (briefs, the twelve
ontologist answers, profiles, timings) is in `~/syi-exp-logs/round4/`.

Primary measure, fixed before the bake-off (E14): agent effort on held-out proofs = theorem lines
+ failed compile attempts. Secondary: module CPU (`lake env lean`, 8 threads, min of 3).

## 1. Census

Script: `abstractions/round4_census.py` (declaration units of `VsaIris/Interp`, statement split at
the top-level `:=`/`by`, conclusion head = text after the last top-level `⊢` or `:`).
All of `VsaIris/Interp`: 2,675 units, 42,430 non-blank lines.

| cluster (conclusion head) | units | lines | files |
|---|---:|---:|---:|
| `… ⊢ Wp.W Φ` / `(wpW _).W Φ` / `twpW` | 226 | 13,222 | 64 |
| spec bodies (`evalSpec{T,P}_body`, `execDisp{T,P}_body`, `fnSpecW`, `env*Spec`, `interpSeqT_body`) | 90 | 3,966 | 53 |
| `ArmAt` / `BinTail` (the record-shaped expression-arm frame) | 37 | 934 | 14 |
| (the cluster: union of the three rows) | 353 | 18,122 | 109 |
| of which contain ≥ 5 proof-mode steps (the target obligations, E21) | 256 | 16,396 | 98 |
| per-callee call adapters `ms_call*` (inside the cluster) | 37 | 1,935 | 20 |
| machine runs `IW …` / `#ix_piece` (not the target) | 220 | 4,901 | 53 |

The coordinator's census (144 `MachWP` units / 7,944 lines, 110 `p`-binder units, 33 `HasLC`
units) is the same population split by a coarser head extraction (it read `(Wp : MachWP …)`
binders and `∀ p` spec binders as heads); by conclusion the cluster is the 353 units above.

Cost over time (mean lines per unit by quartile of the file's first appearance in history):
72.6, 39.8, 70.4, 22.8. The last quartile is the `ArmCore`/`ArmEval`/`ExecChild` refactor
(expression arms on the record frame `evalArmF` with combinators `ArmAt.run/.callHelper/
.callEvalT/.finish`, ~23 lines per arm). The other 300 units do not use it: `wp_swpF` is called
directly 176 times in 50 files, `ArmAt.` 109 times in 12 files; 37 call adapters (1,935 lines)
instantiate two generic call rules (`ms_callRegs`, `ms_callHelper`) by hand.

Seconds axis (E18; clean build `~/syi-exp-logs/clean2.log` of 95acd019, 730 rebuilt modules,
3,283 module-seconds): `VsaIris/Interp` 936 s (28.5%); the 98 modules holding the 256 target units
525 s. Heaviest: ProofStringify 52 s, EnvDefineSpans 36, CmpRuns* 19–20, ProofNativePrint 19.

Where the body lines go (14,315 body lines of the 353 units): proof-mode steps 33% (splitting and
naming 9%, applying lemmas/specs 13%, framing named hypotheses 11%), stack/frame arithmetic 17%,
unfold/rewrite 11%, local `have`s 7%, register keep 3.5%, machine runs 3%, other 24% (explicit
arguments to spec applications: P/Q/X/Y lambdas, register lists, bullets).

Obligation shapes in a stratified random sample of 10 units (read by hand) and by regex over the
256 target units: (a) reshuffle between equal multisets of atoms (10/10); (b) run bracket
`wp_swpF … rotate_left … intro F' … swp_close…` (7/10; 37% of 256); (c) call: carve the callee's
precondition out, keep the rest, merge its post (8/10; 45%); (d) register keep by enumerating a
list (6/10; 27%); (e) stack arithmetic (8/10; `omega` in 55%); (f) exit rebuild (6/10; 30%).

Profile of one instance (E19). Proof-mode cost is lines, not seconds: `ExecOom` (137-line
`ms_callEnvDefineP` plus three more adapters) compiles in 2.4 s. In the heaviest target module
(ProofStringify, 66 s user) tactic time is `simp` 8.8 s (949 calls), `omega` 5.9 s (311), `rw`
4.6 s, kernel checking 11.1 s; every Iris proof-mode tactic together is under 1.5 s. So the
plumbing costs agent effort and the offset arithmetic costs time.

## 2. Laws

| law | statement | status |
|---|---|---|
| L-perm | `A₁ ∗ … ∗ Aₙ ⊢ B₁ ∗ … ∗ Bₘ ∗ Rest` when {B} ⊆ {A} modulo persistent duplication; Rest is the difference | true of BI; iris-lean has `iframe ∗` (type-class `Frame`), unused in the project (0 uses; every frame is named) |
| L-frame-run | a run from `ms pc R S Mt` to `ms pc' R' S Mt'` preserves every other resource | proved: `wp_swpF` + `swp_closeF`; packaged only for `evalArmF` frames (`ArmAt.run`) |
| L-frame-call | a call `{P} f {Q}` from `P ∗ F` continues with `Q ∗ F`; registers outside the clobber set are kept | proved: `ms_callRegs` (any `fnSpecW`, literal register split, user P/Q/X/Y + two entailments), `ms_callHelper` (`helperSpec`) |
| L-keep | `KeepOut C R R'` composes; decided by list computation on literal lists | instances proved by hand (`HiKeep.trans`, `Frame3.helper`, `rcases hx with rfl|…`) |
| L-offset | stack addresses are `top + literal`; fit/overlap are literal comparisons given one window fact | ROUND-3 `Win` decides it for newlib code; Interp re-derives with `omega` |
| L-exit | an arm's post is determined by its semantic result and the caller frame; an abort/tail exit needs forgetting (`ms … S Mt ⊢ ownSet S byteAny ∗ …`), not framing | the abort continuations differ per frame (`abortAt Core s n ∗ slot24 sret` vs `abortRes … (R 2) n ∗ valAt … ∗ ownSet S byteAny`) |

All six laws are lemmas already; the stall is in applying them (ROUND-1 finding E4 again).

## 3. Blind ontologist fan-out

Deep seeded fan-out, 2 rounds × 6 agents (4 character seeds, 2 word seeds per round), brief only
(`round4/BRIEF.md`: machine semantics, the census, the laws, three held-out statements quoted
exactly, forbidden vocabulary = named-hypothesis proof mode, explicit remainder bundles,
per-callee adapters, `ms`, the record arm frame and its combinators, continuation lambdas,
register-list enumeration, `omega` on offsets, the symbolic executor). Round 2 also read every
raw round-1 answer and `round4/ADDENDUM_R2.md` (the profile, the unused `iframe ∗`, the existing
generic call rule, the `Win` layer, the total/partial doubling). Answers: `round4/onto/r{1,2}_*.md`.

Round 1: all six agents reached K, M, S and X; four reached F.

| cluster | mechanism | R1 | R2 | answers (R = round, c/w = seed type) |
|---|---|---:|---:|---|
| K keyed context | context as a keyed table (atom kind + key positions, payloads opaque); the remainder is computed, never written; persistent atoms duplicate | 6/6 (deep embedding, reflective `decide`) | 6/6 *object* to the deep embedding: do it shallowly in the existing proof mode (keyed `Frame` instances, key = FD, payload mismatch → pure goal) | R1: 1A c, 2A c, 3C1 c, 4C4 c, 5C1 w, 6#1 w; R2: 1-I3 c, 2-I1 c, 3-#1 c, 4-#1 c, 5-#1 w, 6-#4 w |
| M clobber mask | register preservation as `R ≈[C] R'` with a literal mask; composition = union; the post-call file is `R.patch C ω` | 6/6 | extended: masks as reducible abbreviations of the legacy `∀ x ∈ fRegs, x ∉ C → …` form (no conversion); parametric `∀ Rs, regs Saved Rs` | R1: 1B, 2B, 3C2, 4C1, 5C2, 6#2; R2: 1-I1, 5-#4 |
| F calling convention from the spec | one call rule per spec *family*, the per-callee adapter is a corollary; "seam form" so the generic rule's entailments hold by reflexivity; the descriptor is read off the spec, not written beside it | 4/6 (per-callee `Sig` descriptor) | 5/6 (*object* to hand-written descriptors: "the adapter again under a new name") | R1: 2E, 3C5, 5C5, 6#4; R2: 1-I2, 2-I1, 3-#2, 4-#5, 6-#5 |
| S stack chart / credits | one window certificate per frame; offsets and budgets become literal comparisons | 6/6 (charts, credits, DBMs) | 5/6 *object* to DBMs (truncated subtraction in `hfit`; kernel cost) and to new charts: reuse ROUND-3's `Win`, certificate at entry, `Nat.ble`/`rfl`; max-plus need polynomials | R1: 1C, 2C, 3C3, 4C2, 5C3, 6#3; R2: 1-I4, 2-I3, 3-#5, 4-#2, 5-#2, 6-#2 |
| X exit ports | continuations as labelled handlers (normal/abort, next/done, none) | 6/6 | 5/6 *object*: abort needs forgetting, not forwarding (erasure table per atom kind), or an ambient abort handler installed once; one BI law `(A-∗C)∧(B-∗C) ⊣⊢ (A∨B)-∗C` | R1: 1D, 2D, 3C4, 4C3, 5C4, 6#5; R2: 1-I5, 2-I4, 3-#3, 4-#4, 5-#3, 6-#1 |
| R mode-polymorphic recursion | prove each arm once over a recursion interface (costed IH / later), total and partial as instances | 0/6 | 3/6 (new in R2) | R2: 2-I5, 3-#4, 4-#3 |
| one-offs | wiring diagrams with coherence (R1 2E); typed assembly with one fundamental theorem (R1 3C5); footprint-typed havoc (R1 4C5); strided cursors for `argv + 24·i` (R2 2-I2); hindsight ledger of side conditions discharged by one `decide` at the end (R2 6-#3); surrogate places (R2 6-#4); entry bridges per statement family (R2 5-#5) | | | |

| seed type | ideas returned | mechanisms only this type produced |
|---|---:|---|
| characters (8 agents) | 40 | wiring diagrams, TAL judgement, strided cursors, mode-polymorphic recursion, footprint havoc |
| words (4 agents) | 20 | hindsight ledger, surrogate places, entry bridges |

Blind convergence is strongest on K and F (round 2 turned K from a deep embedding into a shallow
one after learning `iframe ∗` exists, and turned F from per-callee descriptors into per-family
seams after learning the generic call rule exists): the addendum facts moved the proposals from
new machinery toward the cheapest realisation of the same laws.

Non-blind pool (kept out until clustering): ROUND-2's `iperm` reflective AC checker (= K deep)
and "named arm-frame bundles" (= the existing `evalArmF`, generalised: K/F).

## 4. Retrieval by law

| cluster | law phrasing searched | known theory | status here |
|---|---|---|---|
| K | "frame inference: find the leftover heap in A ⊢ C ∗ ?F" | frame inference (Berdine, Calcagno & O'Hearn, Smallfoot, APLAS 2005); bi-abduction (Calcagno et al., POPL 2009); reflective cancellation in Bedrock/MirrorShard (Malecha, Chlipala & Braibant, ITP 2014); Iris Proof Mode `iFrame` (Krebbers et al., POPL 2017); Diaframe hint search (Mulder, Krebbers & Geuvers, PLDI 2022) | **known**; available (`iframe ∗`) and unused |
| F | "call rule with frame from a function specification; calling-convention preservation" | the frame rule applied at call sites by symbolic-execution verifiers (VeriFast, Viper's consume/produce); CompCert callee-save invariants; Lithium's goal-directed spec application (Sammler et al., RefinedC, PLDI 2021) | **known**; the generic rule exists (`ms_callRegs`), its instantiation is hand-written 37 times |
| M | "kill sets / modifies clauses as literal sets" | modifies clauses (JML, Dafny), Iris invariant masks (`solve_ndisj`), bit-vector dataflow kill/gen | **known** |
| S | "base-plus-offset addressing, one no-wrap fact per frame" | CompCert Stacking layouts; ROUND-2/3 windows (`Win`) | **known, in the project at another layer** (newlib) |
| X | "multiple exits as additive conjunction / handlers" | algebraic effects and handlers (Plotkin & Pretnar 2009); multi-return functions (Shivers & Fisher 2006); abrupt termination in Hoare logic (Huisman & Jacobs 2000) | **known** |
| R | "one proof for total and partial correctness via a later/credit parameter" | later credits (Spies et al., PLDI 2022), transfinite Iris (Spies et al., PLDI 2021) | **known** (citations recalled, check) |

Recognition again: every cluster is known; K and S are already in the project (the proof mode's
`iframe ∗`; ROUND-3 windows) and simply not used at this layer.

## 5. Variation

`/ideonomy` draw: tree-finding × combination, periodic grid, prompts reversibility / age / rate,
applied to F (seam call rule) and K (shallow keyed framing).

Grid: obligation (a)–(f) × time the obligation is decided (spec definition time / arm entry /
use site / end of proof). Filled cells: F decides (c) at definition time; K decides (a) at the
use site; S decides (e) at entry. Gaps and their predictions:

- (d) at definition time → the keep fact of a call is part of the seam lemma, never a use-site
  goal (added to F).
- (e) at end of proof → hindsight ledger: collect pure side conditions, one `decide` (R2 6-#3);
  forecast only.
- (f) at definition time → erasure table per atom kind makes abort exits a definition-time fact
  (added to K).
- reversibility: split/merge of the register file as one `⊣⊢` lemma used both ways (added to F).
- rate ×1000 slower (the rule runs once per family, not per call): generate the corollary adapter
  by a command from the spec; not built.
- F × K: "call = seam lemma + `iframe ∗` for X + auto intro of Y" — the combination iteration.

## 6. Pilot bake-off

Held-out suite (`abstractions/ROUND-4-heldout.json`, commit ff27a765, before any candidate):
the 256 target units split into three size strata; per stratum two pilot and two fresh cases by
`random.seed(20260930)`. No unproved cases exist, so every case is a statement-identical re-proof
(`#check @Name` under `pp.all`, byte-identical output against the base worktree, checked by `cmp`).
Incumbent = the landed proofs. Candidates in separate worktrees from ff27a765 with the build
outputs of the base. Lines = non-blank lines of the declaration (census script).

### Candidate A — SEAM (cluster F + M), worktree syi-expR4a, commits 1dd57308, 38bb4084

Family call seams stated as `spec ⊢ codeRes -∗ ms … -∗ K -∗ W`, applied by `iapply ms_callK … $$
Hspec Hcode Hms` so the spec's P/Q are read off the hypothesis (the older shape with user-written
X/Y and entailments cannot be applied with implicit P/Q: "istart does not support creating
mvars"). `ms_callK`/`ms_callWK`/`ms_callLK`, the env/allocator seam `ms_callABIK` (returns a named
`Merged` keep fact), the newlib seam `ms_callNewlibK` + `newlib_seamP/Q`, the callee-side eval
seam `evalSpecT_intro` + `EvalEntryT`, `KeepOut C R R'` (reducible abbreviation of the legacy
shape) with `.get/.trans/.mono/.upd_ra/.regs` by `decide`.

### Candidate B — KEYFRAME (cluster K + X + S), worktree syi-expR4b, commit 0421fd3e

Plain iris-lean `iframe ∗ #` and `$$ [$]` (automatic framing) framed the project's contexts
correctly and fast in all nine cases, so no keyed instances for exact matches were built. Added:
scoped erasure `Frame` instances (valAt→slot24/blockOwn, slot24→blockOwn, `ownSet S img`→`ownSet
S byteAny`, register `sepL`→`clobbered`/`savedOwn`), `regs_forget`, `keep_cut`, `keep_upd_ra`, saved
contexts (`irest` closes a frame metavariable with the whole remaining context; `irestore`/
`iresume` rebuild the named hypotheses: the frame argument of `wp_swpF` is never written), and an
entry window `EnvFit` / `EvalFrameG.slotWin`. Hazard found: an unassigned `?F` in the goal can
absorb a hypothesis framed to its right (spatial) or anywhere (persistent).

| case | incumbent | A SEAM | A fails | B KEYFRAME | B fails |
|---|---:|---:|---:|---:|---:|
| 1 `ms_tailNewlibA` | 33 | 24 | 2 | 31 | 0 |
| 2 `ms_callOut` | 31 | 27 | 0 | 31 | 0 |
| 3 `cloDefineStepP` | 43 | 43 | 0 | 36 | 1 |
| 4 `caseT_CallPrintln` | 47 | 40 | 0 | 46 | 1 |
| 5 `ms_callEnvDefineP` | 137 | 75 | 1 | 96 | 1 |
| 6 `cloParamStep` | 242 | 238 | 1 | 219 | 2 |
| pilots | 533 | 447 (−16%) | 4 | 459 (−14%) | 5 |
| 7 `ms_callEvalP` (fresh) | 64 | 62 | 0 | 60 | 0 |
| 8 `cmpStrTail` (fresh) | 38 | 38 | 0 | 33 | 0 |
| 9 `cloCallT` (fresh) | 158 | 153 | 0 | 139 | 0 |
| fresh | 260 | 253 (−3%) | 0 | 232 (−11%) | 0 |
| setup (new non-blank lines) | 0 | 308 (119 statements + 189 proof; +127 moved from Arm/NewlibCall) | | 173 (128 KeyFrame incl. 31 tactic, 33 KeyWin, 12 fresh-case fix) | |

A also re-proved two adapters outside the suite through its newlib seam: `ms_callNewlibA` 41 → 27,
`ms_callNewlibAbort` 51 → 37. Module CPU: every case within ±10% of the incumbent in interleaved
min-of-3 runs at load 13–28 (an unchanged module moved 7.3 → 8.6 s, so ±10% is the noise band);
no change is attributable to either layer.

Defects the fresh cases found: B's `irestore` reused hypothesis identifiers when the same
persistent hypotheses were still in context (fixed by `freshenHyps`, counted as setup); A none, but
fresh cases 8 and 9 barely touched A.

Reading. Each candidate wins where the other names its residue. A cuts the family-bridging proofs
(cases 1, 2, 4, 5: −27% to −45%) and does nothing on arm proofs (3, 6, 8: 0 lines; A's report:
"removing the two 14-line `wp_swpF` frames needs automatic framing, candidate B's scope"). B cuts
arm proofs and never-written frames (3, 6, 8, 9) and leaves the explicit P/Q of abstract spec
predicates (cases 1, 2: "framing cannot pick out the contents of an abstract predicate", A's
territory). Neither alone beats its setup on nine cases (A: −94 lines for 308; B: −102 for 173),
and both leave the memory/offset arithmetic of case 6 (~130 lines) untouched. By the rule for
disjoint winners, one more iteration on the combination, with fresh cases and no new abstraction
code (below).
