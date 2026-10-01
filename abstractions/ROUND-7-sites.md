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
