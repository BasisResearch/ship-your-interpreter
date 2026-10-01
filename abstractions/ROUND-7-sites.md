# Abstraction-discovery round 7: per-site machine proofs (2026-10-01)

Branch `exp-R7`, from `exponentiate-next` 1e575ef0 (PR #14 snapshot 5, after ROUND-6). Trigger:
the abstraction gate (`abstraction_gate.py --root`, no baseline on this branch) fires on 28 name
clusters; the firing ones that are not already falling sit in three groups, about 10k lines:

* **libgcc arithmetic** (14 files, 5.6k lines): `Vsa/Sim/Div*.lean`, `Muldi3*.lean`,
  `Code/__{divdi3,moddi3,muldi3,umoddi3,hidden___udivdi3}.lean` — per-pc `site_*`,
  `*_taken/_nottaken`, `tr_*`/`utr_*` transfer lemmas, `__*_at_<pc>` code pins. Restored from main
  for the compiler's `divdi3_wrap_spec` (Vsa/Compiler/Lift) and the interpreter's arithmetic
  (`VsaIris/Interp/ProofArith`, `SnpArith`, `SnprintfSpec`).
* **the fast-path allocator** (7 files, 3.2k lines): `VsaIris/Vsa/MallocFast*.lean` — `path_at_*`,
  `line_*`, `bins_facts_*`.
* **newlib site pins** (2 files, 1.3k lines): `VsaIris/Vsa/OomSites.lean`, `H5Sites.lean` —
  `*Code_at_<pc>`.

Raw material (census scripts and tables, timings, profile, briefs, ontologist answers) is in
`~/syi-r7/`.

## 0. Primary measure (stated before the bake-off)

Single-file user-CPU of the 23 target modules is 234 s, of which one dead module
(`MallocFastSegs`) is 167 s; the 14 libgcc modules cost 30 s and the two newlib site files 13 s
for 7k lines (§1c). Time is not where the live cost is; lines are. The primary measure is
**agent effort: lines of statement-identical re-proofs of held-out cases, counting the per-pc
helper lemmas each case needs (shared helpers divided among their users, E34), plus failed
compiles**, with the abstraction's generic setup counted separately (break-even). Secondary:
user-CPU of touched modules; a candidate that wins on lines may lose at most 10% of the touched
modules' time. Per E33, the fresh-case saving is the forecast for the rollout and the adoption
decision weighs setup against it.

## 1. Census

Data: a meta script over the `Vsa`+`VsaIris`+`VsaBoot`+`WhileC` environment (§12) listing every
constant of the `Vsa*` modules with kind, source range, conclusion head and membership in the
constant closure of the roots; an edge dump of intra-cluster constant uses; per-module user-CPU
of single-file compiles (copies outside the repo, `-Dbackward.isDefEq.respectTransparency=false`
for `Vsa` files; load 12–15 on 32 cores).

Roots: every declaration of the result modules named in the README (`EndToEnd`,
`EndToEndTrichotomy`, `Exclusive`, `Boot/EndToEnd`, `Boot/Audit`, `Boot/Gen/*`,
`TypePreservation`, `TypeProgress`, `TypeCheck`, `TypeInfer`, `TypeSafety`, `WhileLogic/Adequacy`,
`WhileLogic/Machine`, `AbsInt/{Sound,CostSound,ErrSound}`, `VsaIris/AbsInt/Machine`,
`TrichotomyCorollaries`, `Compiler/{Correct,CorrectG,Checked,CompiledG,WhileWl}`,
`CheckedBoundary`, `EndToEndChecked`) and the `whilec` executable.

### 1a. Reachability (run first, E23/E38)

| group | on-path decls (lines) | off-path decls (lines) |
|---|---:|---:|
| libgcc (14 modules) | 443 (5,609) | 4 (13) |
| newlib site pins (2) | 214 (1,315) | 10 (16) |
| fast-path allocator (7) | 12 (87) | 484 (3,223) |

The fast-path allocator is dead. Its 484 off-path declarations include every `path_at_*`,
`line_*`, `bins_facts_*`, the `seg_norm`/`bins_case` macros (used only inside the seven files)
and `MallocFastSegs` (167 s CPU, the most expensive target module). Outside users reference only
12 small helpers: `gpV`, `wordOf`, `wordOf_value`, `ult_iff`, `ult_false_iff`, `uge_iff`,
`and_high_toNat`, `and_m2_toNat` (Segs), `stackBase`, `stackBase_get`, `or_one_even` (Chain),
`ChunkWalk.extend` (Heap), plus auto-realised equation lemmas (`ChainFacts.eq_def`,
`runGM.match_1.splitter`). That cluster leaves the round through the cut (§9a), not a bake-off.

### 1b. Clusters (live)

Clustered by conclusion head and name stem (on-path theorems):

| cluster | law | units | lines | files |
|---|---|---:|---:|---:|
| K-exec: instruction semantics at fixed registers (`exec_*`, `Eq:EStateM.run`) | L-step | 41 | 540 | 4 |
| K-site: one machine step at a pc (`site_*`, `site2_*`, `site3_*`, `_taken`/`_nottaken`, `∃ Step`) | L-step, L-pin | 60 | 1,026 | 4 |
| K-tr: one-instruction transfer over a register record (`tr_*`, `utr_*`, `Triple`) | L-step, L-read | 33 | 666 | 2 |
| K-run: hand-driven multi-instruction runs (`divdi3_spec`, `moddi3_spec`, `moddi3_tail`, `divdi3_mixed_tail`, `udivdi3_spec`) | L-run, L-read | 5 | 1,100 | 2 |
| K-read: readbacks through the observational post (`obs_*`, `post_*`, `frame_*`, `Eq:get?`) | L-read | 54 | 240 | 5 |
| K-pin (generated): per-word byte pins of libgcc code (`__*_at_<pc>`) | L-pin | 48 | 384 | 5 |
| K-pin (newlib): per-word byte pins (`*Code_at_<pc>`) | L-pin | 105 | 630 | 2 |
| per-site certificates and descriptors (`*_cert`, `oom*_ok`, `JalSite` defs) | L-pin (decode) | 27 | 520 | 2 |
| composition, loops, arithmetic (`loop_body`, `div_loop_body`, `mag_*`, `res_*`, `toInt_*`) | — | ≈ 90 | ≈ 1,250 | 6 |

Per-case cost is flat by construction: every proof is a copy of its neighbour with other
literals. A libgcc instruction costs about 55 lines across three files (an `exec_` lemma of
10–17 lines, a `site_` lemma of 15–17, a `tr_` lemma of 19–23 with five to seven register
readbacks each carrying seven or eight `by decide` side conditions); inside the two large runs an
instruction costs about 25 lines (one `site_` application, then one `have` per live register per
step, each a readback with a `by decide`, plus memory/code-residency transport). Each run proof
re-derives the whole register file after every instruction.

Use counts of existing abstractions in the target files (libgcc / newlib pins):
`stepObs_exec`, `Fetched.of_word`, `RetireReads` 63 / 0 (one per `site_`); `rX_bits_gpr` 48,
`wX_bits_gpr` 25 / 0; `reg_reads` 18 / 0; `decodeW` 0 / 15; `TextIn`/`TextPiece`/`piecesText`
0 / 0; `chain_facts` 3 (DivWrap) / 8 (all with a `with "…_at_"` prefix, i.e. through named pins);
`#derive_case` + `segEval_selected_framed` 3 (DivWrap's overflow paths) / 0;
`bblocks_sound_bt`/`block_mem_run` 0 / 0; `Triple.of_step` 34 / 0; hand readbacks
`obs_*_other(')` 257 / 0; `by decide` 587 / 286.

Import positions (E35/E36): the block route (`BlockTerm`, `SegEval`, `DeriveCase`,
`ChainFactsTac`, `SegEffect`) sits **above every libgcc module** (it imports `Muldi3Spec` through
`ObsAvoid ← BlockMem`, `DivLoops` through `RegPins ← BlockPilot`, and `DivSpec3` through
`SnprintfSpec ← SnprintfSpec5 ← SnprintfSpec19 ← WriteLogNF ← SegEval`), so none of the libgcc
spec files can use it without moving modules. `TextImage` (`TextPiece`, `TextIn.pin4`) imports
only `Std` and is importable everywhere. The reflective executors (`SymExec`/`sym_run`,
`SymExecX`/`xrun`) and `StepGen`/`step%` live in `VsaIris` and cannot be used from `Vsa/Sim`
(the compiler, in `Vsa`, consumes `divdi3_wrap_spec`). The newlib site files live in `VsaIris` and
can use everything.

### 1c. Time

| module | user-s | what |
|---|---:|---|
| MallocFastSegs (dead) | 166.7 | `bins_facts_*` `decide` over chain facts |
| MallocFastChain (dead) | 11.6 | |
| MallocFastCode (dead) | 8.9 | |
| OomSites | 7.7 | `decide +kernel` on code lists, certs |
| DivSpec3 | 5.6 | the two large runs |
| H5Sites | 5.6 | |
| 17 others | 28.0 | median 1.3 s (import floor ≈ 0.6–0.9 s) |

### 1d. Profile of one instance, and obligation shapes

Profile of `DivSpec3` (4.5 s under the profiler): tactic execution 2.6 s, type checking 0.76 s,
typeclass inference 0.43 s, elaboration 0.27 s, `simp` 0.07 s; no declaration over 50 ms
of any single category. The cost is the number of lines per instruction, not their speed.

A random sample of ten members (seed 20261001, 490 on-path theorems of the libgcc and newlib-site
modules): three per-word pins (`interpLandCode_at_80004514`, `…_8000453c`,
`setjmpCode_at_80007010`), one jal-site certificate (`oom80002bd0Fw_cert`: decode + pins by
`decide`), one code-text check (`exitCodeE_text`), one exec lemma (`exec_bgtz_a1_taken`), two
readbacks (`frame_bnottaken_m`, `obs_jal_pc`), one record projection (`ra`), one arithmetic fact
(`bgtz_true'`). Eight of ten contain an obligation of the laws below; the projection and the
arithmetic fact contain none.

## 2. Laws

| law | statement | status |
|---|---|---|
| L-pin | for a code list `C` at base `B` held in memory in any of the project's residency shapes (`∀ k < n, m[B+k]? = some (C.getD k 0)`, a conjunction of chunk facts, `TextIn (piecesText ps) m`), the four bytes at a literal `pc` with `B ≤ pc`, `pc + 4 ≤ B + n` are `C[pc-B .. pc-B+3]`; one Boolean evaluation over `C` decides it | proved generically for `TextIn` pieces (`TextIn.pin4`, `bytePinsM_of_text`); for the other two shapes, once per address (153 named pins) |
| L-step | from a state whose register file satisfies a record `P` at `pc` with instruction word `w` resident at `pc`, one step reaches a state satisfying `P[rd ↦ f(regs)]` at `next(pc, w, regs)`, with memory, output, `GoodState` and `tick < 2` preserved; one rule per instruction class (ALU write, conditional branch, jal, jalr) | proved per instance (`exec_` + `site_` + `tr_`, 101 + 33 units) |
| L-run | a straight-line run of `k` instructions composes L-step `k` times; the register record afterwards is the composed update; every register outside the run's write set keeps its value | proved generically by the block executor (`bblocks_sound_bt`, `segEval_sound`, `GHolds`), which sits above the libgcc modules; hand-composed in K-run |
| L-read | `ReadsLikePost σ' (sigmaPost_k σ …)` gives `σ'.regs.get? R = σ.regs.get? R` for every `R` outside `{rd, PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip}` | proved (`obs_*_other`, `frame_*_m`); applied once per register per step, 7–8 `by decide` each |

Checks: L-pin is `decide` on literal lists (true for all 153 pins by construction of the
generator). L-step and L-read are instances of proved lemmas; L-run is proved by `segEval_sound`
for `GHolds` register lists with symbolic values and concrete or hypothesised branch guards.

The stall is in applying proved laws: the libgcc files bypass the block route (import position)
and the newlib site files bypass `TextIn` (residency shape).

## 3. Held-out suite (drawn before any candidate was built)

`abstractions/ROUND-7-heldout.json`. Populations: L = libgcc run units with per-pc helpers (5);
S = single-instruction transfer units (33: 22 `utr_*`, 11 `tr_*`); P = code lists whose consumers
use named pins (10). `random.Random(20261001)`: `sample(L,3)`, `sample(S,5)`, `sample(P,3)`;
first 2/3/2 primary, the rest fresh (run after the first pilots). Baseline = declaration lines +
apportioned per-pc helper lines.

| case | stratum | file | decl | helpers | baseline |
|---|---|---|---:|---:|---:|
| `divdi3_spec` | L | DivSpec3 | 439 | 379 | 818 |
| `moddi3_spec` | L | DivSpec3 | 435 | 352 | 787 |
| `utr_d8_dc` | S | DivSpec | 20 | 33 | 53 |
| `tr_58_5c` | S | Muldi3Spec | 21 | 38 | 59 |
| `tr_5c_60` | S | Muldi3Spec | 21 | 31 | 52 |
| `ljCode` | P | H5Sites + RuntimeError | 2 | 102 | 104 |
| `crt0JCode` | P | H5Sites + MainErr + MainOk | 2 | 6 | 8 |
| fresh `udivdi3_spec` | L | DivLoops | 65 | 33 | 98 |
| fresh `utr_b0_b4` | S | DivSpec | 21 | 36 | 57 |
| fresh `tr_4c_54` | S | Muldi3Spec | 23 | 37 | 60 |
| fresh `setjmpCode` | P | H5Sites + Setjmp | 1 | 96 | 97 |

Primary baseline 1,881 lines; fresh 312. The two large runs dominate the primary set (1,605 of
1,881): that is what the cluster holds.

## 4. Blind ontologists

Six agents (five seeded by random 256-character strings, one by a random dictionary sentence) got
the semantics, the census, the laws, the held-out statements verbatim, a forbidden list (per-pc
`exec_`/`site_`/`tr_` lemmas, per-address pins, per-register readback chains and `(by decide)`
batteries, hand record rebuilds, generators, SMT, "write a tactic"), the importable abstractions
with use counts and import positions (E31/E36: the block executor and the reflective executors marked
"exists, not importable from the libgcc modules"), and the decision-procedure restrictions. Each
returned 4–5 candidates in 86–123 s. Raw answers: `~/syi-r7/fanout/answers-notes.md`.

| candidate (as proposed) | agents | rules = laws | built first by | decided by |
|---|---:|---|---:|---|
| R. register view / record over a first-order register list keyed by `Fin 32` or GPR number (literal keys, symbolic values), one Triple rule per instruction class, bridges `St ↔ View`, `Ust ↔ View` | 6/6 | L-step, L-read | 5/6 | `decide` on keys, `rfl`/`simp` on lookups, branch guard from the frozen hypothesis |
| I. one code image: every residency shape mapped once to one predicate, a pin is one Boolean evaluation; `chain_facts` closes pins from a term instead of a name prefix | 6/6 | L-pin | (with R) 6/6 | `decide +kernel` on literal lists |
| E. straight-line executor placed below the libgcc modules (rebuild the block executor low, or move it: "sever the import") | 6/6 | L-run | 1/6 | `simp only [eval]` with symbolic values, or reflection |
| C. call rule / adaptation: a proved callee Triple and a caller whose live registers are outside the callee's write set compose | 6/6 | L-run across calls | — | `decide` on closed mask inclusion |
| F. write-set footprints as masks/monoid (`Agree M σ σ'`) | 3/6 | L-read | — | `decide` on literal masks |
| X. reflected value syntax + `decide +kernel` run | 3/6 | L-run | — | kernel evaluation |
| P. staged pages: the decoded instruction list of a routine computed once | 1/6 | L-pin + decode | — | `decide +kernel` |

Theories cited: bidirectional lenses and the view-update problem (Foster et al.; Bancilhon–Spyratos),
relational `UPDATE … WHERE`, materialised views and index lookup, snapshot isolation and OCC
read/write sets, content-addressed storage, range indexes; separation logic's frame rule,
rely-guarantee (Jones), Kleymann's adaptation rule, procedure summaries (Sharir–Pnueli), Dijkstra
predicate transformers, VC generation, partial evaluation and binding-time analysis (Futamura;
Jones–Gomard–Sestoft), proof by reflection (Boutin), abstract interpretation (Cousot), Kleene algebra
with tests (Kozen), basic-block transfer functions, Kleisli composition, fibred reindexing,
stratified Datalog, ports-and-adapters; capability systems (Dennis–Van Horn), Noether conservation,
gauge equivalence, percolation; neo-Riemannian voice leading, chess FEN, the lexicon, Montague
type-shifting, MetaOCaml staging, page imposition, principal–agent contracts, double-entry
bookkeeping.

## 5. Retrieval by law

All candidates are **known**, and each is already used by this project at another layer:

* R: Hoare logic for machine code with registers as resources (Myreen & Gordon, TACAS 2007, the
  decompilation route; Jensen, Benton & Kennedy, POPL 2013, high-level separation logic for low-level
  code); the project's block executor states exactly this over `GRegs`/`GHolds`
  (`Vsa/Sim/BlockPilot`), and `SymExec` does at the interpreter layer.
* I: code-relative specifications over a code image (Kennedy, Benton, Jensen & Dagand, PPDP 2013;
  Myreen's `code` predicate); the project has `TextPiece`/`TextIn.pin4` (README: "per-address
  code-byte lemmas: code residency is a range of the ELF image").
* E: symbolic execution over basic blocks; in this project `segEval_sound`/`#derive_case` (lower
  library, above the libgcc files) and `SymExec` (upper library).
* C: the adaptation rule (Kleymann, FAC 1999); procedure summaries. The project composes the core's
  Triple by hand at each call.
* F: modifies clauses / dynamic frames (Kassios 2006).

Recognition, not invention: the cluster bypasses two existing abstractions, one because of the code
residency shape (the newlib pins and the generated libgcc pins), one because of import position (the
block executor).

## 6. Variation

Ordered by generality, the candidates sit on two axes: whether the rule quantifies over a new state
predicate (R's view, E's executor) or over the existing terms (`St`/`Ust` records, raw
`σ.regs.get?` facts, `GHolds` register lists), and where the run is composed (by hand with
`Triple.seq`, or by an executor). The meet of R with the incumbent is "the laws as lemmas over the
existing terms": one generic site lemma per instruction class, readbacks with one decidable premise,
one transfer rule per class for each existing record, and an "all carried facts after one step" lemma
for the raw-hypothesis runs (no new datatype, no executor). The meet of E with the incumbent is "use
the existing block executor": remove the aggregation imports that put it above the libgcc modules and
re-prove with `GHolds`, `#derive_case` and `segEval` as `DivWrap` already does (no new datatype, no new
executor). For I, the meet is a rule over the existing residency terms (`chain_facts` recognising the
`xCodeLoaded` and chunk shapes), no new image type.

Pilots (built in parallel worktrees from 31221490; suite committed first):

* P1 = R (the 6/6 recommendation; new view predicate, class rules, bridges), placed below the libgcc
  modules;
* P2 = the meet of E (import surgery + the existing block executor);
* P3 = the meet of R (generic lemmas over existing terms);
* PA = the meet of I (pins over the existing residency terms; the P-cases).
C (call rule) is allowed inside each libgcc pilot; F and X are subsumed (F inside R's rules; X is a
decision procedure for E).

## 7. Bake-off

Each candidate was built by its own agent in its own worktree from 31221490 (suite committed first;
`.lake` and the path dependency's `riscv-lean/*/.lake` copied; `lake build --no-build` up to date in
each). Commits: P1 2d6ccdc9 (`exp-R7-P1`), P2 24d70526 (`exp-R7-P2`), P3 c08e64be (`exp-R7-P3`),
PA a61f4b85 (`exp-R7-PA`). Every pilot ended with `lake build Vsa.Sim.DivWrap Vsa.Compiler.Lift
Vsa.Sim.SnprintfSpec` (P2 also `lake build Vsa`; PA the VsaIris consumers) green.

**What each built.**

* **P1 = R** (`Vsa/Sim/RegView.lean`, 599 lines, below every libgcc module; bridges `St.view`/
  `RView.st`, `Ust.view`/`RView.ust`, `NotWrittenD.avoid`: 60 lines): `RView g ws img m0 o pc L c`
  over a GPR-number list, write set `ws` as a literal list (decided by `decide`), one generic step lemma
  and class rules `itype`/`mv`/`shifti`/`rtype`/`btaken`/`bnot`/`jal`/`j`/`jr`, `RView.next`,
  `RView.reg`.
* **P2 = meet of E** (import surgery + the existing executor): two low modules of MOVED lemmas
  (`ObsBasics` 280 lines from `Muldi3Spec`, `MemWriteBasics` 40 lines from `SnprintfSpec5/19`), 13
  import edges changed (each recorded with the constant that justified it; the block executor's
  closure fell from 151 to 123 modules and contains no libgcc module), `Muldi3Spec` imports
  `SegEffect`. New generic lines: 55 (`SelectedFramedSegResult.mem_eq`/`frameD`, `mulRegs`, `mulKeep`,
  `jr_tgt_ok`, `core_call_seg`, `divIn`) + 36 of record bridges (`St.held`/`St.of_seg`,
  `Ust.held`/`Ust.of_seg`). Proofs are `#derive_case` segments run by `segEval_selected_framed`.
* **P3 = meet of R** (`Vsa/Sim/SiteLaws.lean`, 449 lines of which 61 moved; class rules for each
  record `St.alu/br/bnt/bt`, `Ust.*`: 184 lines): generic `exec_*`, `site_alu/bt/bnt/jal/jr`,
  readbacks `keep_*`/`eq_*` with one `Unwritten [..] R = true := by decide` premise; no new state type.
* **PA = meet of I** (62 lines): `TextIn.of_loaded` turns the `xCodeLoaded` shape into a piece
  footprint; `chain_facts`'s candidate search accepts it, and a fact-projection path closes pins from
  shape-(a) chunk conjunctions. No new residency type.

**Held-out cost, primary** (declaration lines + apportioned per-pc helpers still used, measured by
one script on every branch, `~/syi-r7/meas/meas.py`; for the two runs the helper closure includes the
DivSpec3 tails and arithmetic they still use, so the old-encoding tails P1/P3 kept are charged to
them; failed compiles in brackets):

| case | incumbent | P1 | P2 | P3 |
|---|---:|---:|---:|---:|
| `divdi3_spec` (+ tails, helpers) | 1,111 | 489 [2] | 490 [1] | 534 [1] |
| `moddi3_spec` (+ tails, helpers) | 1,160 | 529 [0] | 465 [0] | 583 [0] |
| `utr_d8_dc` | 53 | 10 [0] | 19 + 3 seg [0] | 10 [0] |
| `tr_58_5c` | 59 | 13 [0] | 20 + 1 seg [1] | 13 [0] |
| `tr_5c_60` | 52 | 10 [0] | 19 + 3 seg [0] | 10 [0] |
| libgcc total | 2,435 | 1,051 + 2 = **1,053** (−57%) | 1,020 + 2 = **1,022** (−58%) | 1,150 + 1 = **1,151** (−53%) |
| `ljCode` (PA) | 104 | | 2 [0] | |
| `crt0JCode` (PA) | 8 | | 2 [0] | |

Without the tails (declaration + per-pc helpers only): incumbent 1,748; P1 346; P2 354; P3 455.
Setup: P1 659 lines; P2 91 new lines + 320 moved + 13 import edges; P3 572 (388 new); PA 62.

**Time** (user-CPU, single-file compiles of copies, `LEAN_NUM_THREADS=1`, min of 3, the four variants
interleaved per round, load 5–18 on 32 cores):

| module | incumbent | P1 | P2 | P3 |
|---|---:|---:|---:|---:|
| DivLoops | 1.72 | 1.78 | 2.16 | 2.09 |
| DivSites | 2.25 | 2.21 | 2.56 | 2.45 |
| DivSites2 | 0.98 | 0.76 | 0.50 | 0.71 |
| DivSites3 | 2.07 | 1.00 | 0.78 | 1.01 |
| DivSpec | 2.32 | 2.54 | 2.84 | 2.98 |
| DivSpec3 | 4.66 | 3.79 | 4.92 | 4.31 |
| DivWrap | 1.04 | 1.13 | 1.09 | 1.21 |
| Muldi3Sites | 1.26 | 1.12 | 1.15 | 1.15 |
| Muldi3Spec | 2.12 | 2.26 | 1.85 | 2.49 |
| layer modules | — | 2.41 | 1.81 (moved lines) | 4.41 |
| sum | 18.42 | 19.00 (+3%) | 19.66 (+7%) | 22.81 (+24%) |

P2's increase is the import floor of `SegEffect` in DivSpec/DivLoops (≈ +0.3–0.5 s each); P3 fails the
10% secondary bound on its layer file. PA: no measurable change (H5Sites 5.17 → 4.44 s, RuntimeError
47.2 → 46.6 s, MainErr 4.07 → 2.99 s; `decide` on the longest 280-byte list costs the same ≈ 65 ms per
pin as the old named pins).

**Fresh cases** (run after the pilots, no new layer code allowed): on P1 (3bc8d61e) and on the
combination C = P2 + PA (`exp-R7-C`, 77817442), both with zero layer changes:

| case | incumbent | P1 | C |
|---|---:|---:|---:|
| `udivdi3_spec` | 98 | 62 [0] | 60 + 8 seg [1] |
| `utr_b0_b4` | 57 | 13 [0] | 13 + 1 seg [1] |
| `tr_4c_54` | 60 | 10 [0] | 15 + 3 seg [1] |
| `setjmpCode` | 97 | — | 2 [0] |
| libgcc fresh | 215 | 85 (−60%) | 100 + 3 = 103 (−52%) |

`udivdi3_spec` is mostly loop-invariant reasoning over already proved per-step triples; both
candidates touch only its entry and `ret` (C also folded four `utr_*` into one entry segment and
deleted them, 214 lines of helpers).

Defects found (E15): P1 — autoParam-heavy rules swallow forward arguments (`RView.next` added),
`rop` constructor order differs from the `*_char` lemmas, name clashes with `View`/`CodeAt` already in
scope in `Vsa.Compiler`. P2/C — the executor has no `jal`-with-link terminator (calls still need the
old jal site lemma plus `core_call_seg`); `decide` refuses `KeysOK (keysG L)` and end-pc goals with
free variables (`show … [literal keys]; decide`, end pc by `rfl`); branch guards and selected registers
come out as unreduced `wvalM (mkLine …)` terms that need a `show` before rewriting; a run crossing two
code regions must be split (one residency hypothesis per `chain_facts`); `jr_tgt_ok` sits too high
(DivSpec3). P3 — the class rules are written twice (St, Ust); register numbers must be passed
explicitly; nested `keep_*` terms grow O(k²) per path. PA — shape (a) is closed by fact projection,
not by one Boolean evaluation.

## 8. Decision

**Adopted: the combination C = P2 + PA** — the laws as rules over existing terms: the existing block
executor (`GHolds`, `#derive_case`, `segEval_selected_framed`, `chain_facts`) made importable by the
libgcc modules by import surgery, and `chain_facts` closing code pins from the existing residency
shapes. Reasons, by the measures fixed in §0:

* Primary: C 1,022 vs P1 1,053, P3 1,151, incumbent 2,435 on the libgcc primaries; pins 112 → 4.
* Fresh (the forecast, E33): P1 85, C 103 (incumbent 215). P1 is cheaper per one-instruction case (5–6
  lines against 13–15 + a segment), which is its real advantage.
* Setup decides it: C needs 91 new lines (+ 62 for pins) against P1's 659; the 33 one-instruction
  units of the cluster would need ≈ 8 more lines each under C (≈ 260 lines), far below P1's extra
  ≈ 570 setup lines. C introduces no second register-list vocabulary beside `GRegs` (P1's `RView`
  re-states what `GHolds` already is) and makes the existing executor available to every libgcc file.
* Secondary: +7% on the touched modules (import floor), within the 10% bound; recorded as C's named
  cost together with the per-instruction cost of one-step transfers.

Not adopted: P1 (cheaper per instruction, but its setup re-builds the existing executor's register
view; kept on `exp-R7-P1` as the reference if a lower-library executor is wanted later); P3 (most
lines, duplicated class rules, +24% time).

As in rounds 5 and 6 (E25, E32), the winner is the meet — and here the meet is not even new lemmas
but making an existing abstraction reachable (E30b: bypass by import position).

Route (this branch has no CLAUDE.md or discipline script; per E16 the rule text is recorded here):

| task shape | use |
|---|---|
| machine run of fixed code in `Vsa/Sim` (straight-line or ending in a branch/j/jr) | `#derive_case` segment + `segEval_selected_framed` (+ `St.held`/`St.of_seg`-style record bridge); never per-pc `exec_*`/`site_*`/`tr_*` |
| code bytes for `chain_facts` | `chain_facts h` with the residency hypothesis (`TextIn`, `xCodeLoaded`, `__xLoaded`); never `with "…_at_"` and never a named per-address pin |

Discipline rules (TSV lines for `scripts/discipline_rules.tsv`):

```
R18	{Vsa,VsaIris}/**/*.lean	chain_facts .* with "	code pins come from the residency hypothesis (chain_facts h), not named per-address pins
R19	Vsa/Sim/**/*.lean	^theorem (exec|site[0-9]*)_[a-z0-9_]+	machine steps of fixed code go through #derive_case + segEval (ROUND-7), not per-pc exec_/site_ lemmas
```

## 9. Rollout

### 9a. Reachability cut (§1a)

Commit 29780b97 (branch `exp-R7-cut`, merged): `MallocFastCode`, `MallocFastLines`,
`MallocFastJal`, `MallocFastRun` deleted; `MallocFastSegs`/`Chain`/`Heap` trimmed to the 12 helpers
other modules use (imports kept as the union of what the deleted modules imported, so downstream
transitive environments are unchanged). 7 files, +9 −3,489. Full `lake build` green on the first try
(no restore loop: a constant-level dump had listed every external use beforehand).

### 9b. Layer rollout

On `exp-R7-C` (P2 + PA + the cut). One libgcc rollout agent (disjoint files, shared worktree, one build
lock) and the coordinator (pins and DivSpec3):

* libgcc (3dfbbe36): the remaining 8 `tr_*` of muldi3 and 16 `utr_*` of the udivdi3 core re-proved on
  one-instruction `#derive_case` segments through two record wrappers `St.seg`/`Ust.seg` (18 lines
  each): 19–27 → 5–6 lines each (`tr_60_ret` 27 → 15). `Muldi3Sites` (260 lines) and `DivSites`
  (539) deleted outright; `frame_*`/`NotWritten*.x10..x13` projections (55 lines) gone;
  `ret_tgt_aligned` added beside `ret_tgt` in `ObsBasics`.
* pins (0ffa7398, 10c4414e): every `chain_facts … with "…"` in the repository dropped its prefix
  (OomSites, Landing, MainErr, MainOk, RuntimeError, Setjmp, DivSpec3, DivWrap, Muldi3Spec, DivSpec);
  all named per-address pins of `H5Sites`/`OomSites` deleted (511 lines), and the generated
  `__x_at_<pc>` pins of the five libgcc code files except the three still used by the jal sites (423
  lines). `jr_tgt_ok` unified into `ret_tgt_aligned`.

Members left on the old encoding, by reason:

* the three `jal` sites (`site3_8000471c`, `site3_80004734`, `site3_8000474c`) and their pins: the
  executor has no `jal`-with-link terminator (P2 defect 1); `core_call_seg` wraps them;
* `core_call_tail_f`, `divdi3_same_tail`, the loop proofs (`iter_48_5c`, `loop_body`,
  `div_loop_body`, `norm_loop_body`) and the arithmetic (`mag_*`, `res_*`, `tdiv_of_natAbs_sign`):
  no stepping obligation; they compose the per-instruction triples, which are now 5–6-line terms;
* the six model re-proofs (`tr_58_5c`, `tr_5c_60`, `tr_4c_54`, `utr_d8_dc`, `utr_b0_b4`,
  `udivdi3_spec`) keep their explicit 12–15-line forms so the measured numbers stay reproducible
  (with `St.seg`/`Ust.seg` they would be 5–6 lines each);
* per-site jal certificates (`*_cert`, 8 units, the gate's 'oom cert') and the `OomSite.OK`
  descriptors: a decode + `decide` record, not a pin or step obligation.

Layer defects the rollout found (next round's input, E22): (1) a generic wrapper's binder needs an
explicit `k : Nat` or the `GetElem?` instance on `ExtHashMap` gets stuck and the error surfaces at
every caller as "unknown constant"; (2) ≈ 8 lines of `segEval_selected_framed` boilerplate per call
(minstret, literal-key `KeysOK`/`ChainOK`, noise, record exit) — packaged per record as `St.seg`/
`Ust.seg`, duplicated because `St` and `Ust` differ only in their residency field; (3) the shared git
index: a deletion staged by the rollout agent landed in the coordinator's pins commit 0ffa7398
(content correct, attribution wrong); (4) `jr_tgt_ok` sat above its natural users (fixed).

## 10. Measurements (31221490 → 10c4414e)

| measure | before | after |
|---|---:|---:|
| target files (23 → 18; lines) | 11,297 | 3,542 (+ 324 in the two modules of moved lemmas) |
| of which libgcc (14 → 12 files) | 6,126 | 2,600 |
| of which newlib sites (2) | 1,554 | 805 |
| of which fast-path allocator (7 → 3) | 3,617 | 137 |
| repository diff (`Vsa`, `VsaIris`) | | 46 files, +1,139 −8,544 |
| per-pc `exec_*`/`site*_*` lemmas | 101 | 3 (jal sites) |
| named per-address pins | 201 | 3 |
| `chain_facts … with "prefix"` uses | 21 | 0 |
| target-module user-CPU, single-file, min of 2, interleaved (load 7–9) | 236.2 s | 26.8 s |
| of which live (without the allocator files) | 33.2 s | 25.0 s (−25%) |
| largest module changes | | MallocFastSegs 180.9 → 0.6, H5Sites 4.53 → 1.55, DivSites3 2.09 → 0.76, DivSites + Muldi3Sites 3.51 → 0 |

Full `lake build` (all default targets, executables included) green at 10c4414e. Statement check (type
hash of every constant of the `Vsa*` modules, both environments, joined by name): 0 changed types among
non-auxiliary declarations except the tactic metaprogram `cfSolve` (its signature gained the fact list;
used only inside `ChainFactsTac`); 790 non-auxiliary names gone (the dead allocator, per-pc lemmas,
named pins, `utr_ac_b0`…`utr_bc_c0` folded into `udivdi3_spec`'s entry segment, the two replaced tails),
none of them used by any remaining declaration and none in the externally used interface of the
clusters (`muldi3_spec`, `moddi3_spec`, `divdi3_wrap_spec`, `DivWrapPost.*`, `DivK`, `NotWritten*`,
`readback`, `ret_tgt`, `obs_*`, `post_*`, `St`, the `Loaded`/`Chunk0` predicates: all present, same
types). Axioms (the 14-line file): every theorem [propext, Classical.choice, Quot.sound]; the two
WhileLogic adequacy theorems [propext, Quot.sound]. No `sorry`, `axiom`, `native_decide`,
`bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth` added.

Gate re-run (`abstraction_gate.py --root`, no baseline): 28 firing clusters → 12. Gone: `site`,
`site taken`, `site nottaken`, `path at`, `line`, `bins facts`, `hidden udivdi at`, `moddi at`,
`muldi at`, `umoddi at`, `oom ode at`, `interp Land Code at`, `lj Code at`, `main Err Code at`,
`rt Err Code at`, `setjmp Code at`. Left in this round's territory: `tr` (10 units, 5 → 9 lines) and
`utr` (11, 8 → 6): flat at the adopted route's per-instruction floor (one `St.seg`/`Ust.seg` term);
the last quarter holds the six long model re-proofs kept for reproducibility. To leave the gate they
need a baseline entry (automation floor), not another round. `oom cert` (8): decode certificates, not
targeted. The other nine (`Call run`, `Cat Tail run`, `Clo run`, `get Elem write Map`, `hex bits
forwards resp`, `lj fin`, `sprint Err`, `svf Pro`, `sx`) were outside the three groups this round
targeted and are unchanged.

Calibration (E21/E33): primary −58% (libgcc), fresh −52%, rollout: the 24 rolled-out transfer units
19–27 → 5–6 lines (−73%), the cluster's live files −58% of lines; the fresh set predicted the rollout
of the one-instruction units well; the run units (`divdi3_spec`, `moddi3_spec`) carry fixed residue
(arithmetic, calls) that no step rule touches.

## 11. What remains

* A `jal`-with-link terminator for the block executor (`TKind.jal rd`): removes the last three per-pc
  sites, the pins they use, and most of `core_call_seg`; then a call rule over `GHolds` (the 6/6 call
  candidate C of §4) for the runs.
* One record family parametrised by its residency predicate would merge `St.seg`/`Ust.seg` and the
  bridges (P3 and the rollout both report the duplication).
* `tr`/`utr` into the gate baseline as an automation floor; the six model re-proofs can then shrink to
  the `seg` form.
* P1's register view stays on `exp-R7-P1` (cheapest per one-instruction case: 5–6 lines without a
  segment); if a lower-library executor is ever wanted, it is the reference.
* `StepGen` still emits `chain_facts … with` strings for on-demand step lemmas (VsaIris generator;
  harmless now that the generic path runs first).

## 12. Scripts

Census, user dump, edge dump: `~/syi-r7/census/{Census,Users2,Users3,Edges}.lean` (the §12 script of
ROUND-6 with roots = every declaration of the README's result modules and `whilec`, and a name filter
that keeps `__`-prefixed names). Case measurement: `~/syi-r7/meas/{MeasV.lean,meas.py}` (declaration
lines + helper lines apportioned by number of users, helper modules given by a regex). Statement check:
`~/syi-r7/hash/Hash.lean` (name, type hash, module for every `Vsa*` constant; joined by name).
Timing: `~/syi-r7/time/tm.sh` (copies outside the repo, `LEAN_NUM_THREADS=1`, user CPU).
