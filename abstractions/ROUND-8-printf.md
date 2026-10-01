# Abstraction-discovery round 8: the printf family (2026-10-01)

Branch `exp-R8`, from `exponentiate-next` a5156edb (PR #14 snapshot 6, after ROUND-7). Target: the
printf family, 69 modules, 15.3k raw / 13.9k non-blank lines:

* `VsaIris/Vsa/Snp*.lean` (19 files, 6.8k lines): `snprintf` → `_svfprintf_r` → `__ssprint_r`, run
  predicate `SnpW`;
* `VsaIris/Vsa/Fprintf/*.lean` (28 files, 5.8k): `fprintf` → `_vfprintf_r` → `__sprint_r` →
  `__sfvwrite_r`, `__sbprintf`, flush; run predicate `SWPO` (console output);
* `VsaIris/Vsa/Stderr/*.lean` (17 files, 2.3k): the error-message path (fprintf/fwrite to stderr);
* `Vsa/Sim/Snprintf*.lean` (5 files, 0.3k).

Trigger: the gate (`abstraction_gate.py --root`, run by hand: this branch has no `scripts/` and no
CLAUDE.md, see C1) fires on 12 clusters, two of them in the target (`svf Pro` 8 units, 8.5 → 19.5
lines; `sprint Err` 11 units, 10.0 → 11.3). The round was also asked to test three hypotheses: (a)
`_svfprintf_r` and `_vfprintf_r` are one source compiled twice, so the two proof sets re-prove the same
code at two addresses; (b) every call site passes a constant format, so a format-specialised route
could replace the general per-conversion proofs; (c) the existing executors now cover more of these
runs than when the files were written.

Raw material (census scripts and tables, disassembly, timings, profiles, briefs, ontologist answers,
measurement script) is in `~/syi-r8/`.
## 0. Primary measure (stated before the bake-off)

Agent effort on statement-identical re-proofs of the held-out cases: non-blank lines of the case's
declarations (all pieces of a chain) + the declarations only it uses (dominated in the constant graph;
other cases' roots excluded) + shared target helpers divided by the number of run units reaching them,
measured by one script on every branch (`~/syi-r8/meas/{run.sh,MeasT.tail,meas.py,measfull.sh}`), plus
failed compiles. Generic layer lines are setup (break-even against the fresh-case saving, E33).
Secondary: single-file user-CPU of the touched modules; a candidate may lose at most 10% there. The
target is 694 s of CPU for 13.9k lines, so time is a real second axis this round (unlike ROUND-7).

## 1. Census

### 1a. Gate and reachability (run first, C1, E23/E38)

The gate runs only by hand (`--root`); `scripts/` and CLAUDE.md are absent on this branch (C1).
Reachability (constant closure of every declaration of the README's result modules, the census script
of ROUND-7 §12): 13,882 non-blank target lines, of which ≈ 730 lines in 323 declarations are off the
path — all of them `syntax`/`macro`/`elab` declarations (elaboration-only, kept) except one 9-line
definition (`Vsa.Sim.Pin8`). The cut is empty (E38). Outside users of the target: 19 constants
(`snprintf_ok`, `fprintf_ok`, `fwrite_proved`, `fprintf_out`, `snprintfInt_out`, `snprintfFn_out`,
`snpText`/`snpPieces`/`snpCodeRanges`/`snp_code`/`nRegs`, `obs_jalr_*`, `post_jalr_other`,
`lw_cap_reassemble_sp`, `stackMb_of_stackGeom`, `instDecidableInExt`, `natDigits.eq_def`).

### 1b. Time (single-file user-CPU, `LEAN_NUM_THREADS=1`, copies outside the repo; load 3–8 on 32 cores)

| group | modules | user-s |
|---|---:|---:|
| Snp | 19 | 276.5 |
| Fprintf | 28 | 276.5 |
| Stderr | 17 | 138.1 |
| Vsa/Sim/Snprintf | 5 | 3.2 |
| all | 69 | 694.2 |

Largest: SnpSvf 61.2, SnpSvfConv 45.3, SnpPrint 42.1, SnpStrlen 41.6, Stderr/FwriteRun 37.9,
Fprintf/SConv 34.4, SnpMove 30.0, Fprintf/Flush 29.8, Fprintf/Sfv 22.3, Sbprintf 21.3. The bridged
clone files cost 0.8 s each (Fprintf/Arith, Fprintf/Strlen) against 4.2 s (SnpArith) and 41.6 s
(SnpStrlen) for the same code re-proved.

Profile (`profiler true`, threshold 30 ms): SnpSvf — tactic execution 27.4 s, kernel type checking
18.6 s (10.7 s in 106 declarations over 30 ms), `simp` 16.6 s, typeclass 2.7 s; `omega` 4.8 s in 20
calls over 30 ms, step drivers 4.2 s. Fprintf/SConv — tactics 17.9 s, `simp` 7.1 s, kernel 4.9 s.
Stderr/FwriteRun — tactics 15.8 s, `simp` 10.8 s, kernel 6.8 s. No single declaration dominates: the
cost is spread over many small `simp`/`omega` calls in the glue and over kernel checking of the
step-driver proof terms.

### 1c. Clusters (by conclusion head and by name stem)

| cluster | units | lines | what is re-proved |
|---|---:|---:|---|
| K-run: run pieces (`SnpW` 76 theorems, `SWPO` 47, `NW` 8, `#ix_piece` 121, `#ix_seg` 4) | 256 (+ 19 chains) | 7,046 (2,177 statements) | a machine run between two pcs: 1–3 executor calls, then glue |
| K-clone: entry runs of functions also proved in another file/host | 10 groups | 2,975 | see 1d |
| K-rec: state records | 78 structures | 638 | `SvfPro`, `SvfAt`, `SvfCore`, `SvfSt`, `LldMag`, `SfvRegs`, `FwritePost`, … |
| K-read: readback lemmas (`Eq:ldv`, `Eq:imgM`, record projections) | ≈ 280 | ≈ 560 | `ldv k (writeLog Mt …) a = …` |
| K-spec: Iris wrappers (`EmpValid`, `Entails`) | 34 | 1,302 | run → `⊢ fnSpecW …` |

Run units by age quarter (file creation; all files date from the 2026-09-25 move, then source line):
27.5, 20.3, 25.4, 33.6 lines per unit — flat to rising. Body anatomy (sampled): 1–3 executor lines
(`snp_run`/`nx_run` 141 uses, `xrun` 14), the rest glue: `rsimp`/`simp only [upd_apply …]` readbacks
(561 lines), `omega` (1,980 lines), address re-spellings (`toNat_ofNat_lt` 74, `sp_lit`
35, `show … by omega`), memory readbacks (`svf_mem` 131, `nx_mem` 86), frame transport (`Frame.` 85),
record rebuilds (`refine hk _ _ ⟨?_, …⟩` + one bullet per field).

Random sample of ten run units (seed 20261001 over the 284 `SnpW`/`SWPO`/`NW` theorems):
`mm_byteLoop0` (wrapper, 16 lines: argument plumbing into a loop lemma), `svfPro_p1` (piece), `svf_flush`
(59: two runs, a callee, 7 readback/address bullets, a nested continuation), `sprintErr_hook` (37:
xrun + record), `svf_digExit` (14: case split on the sign byte into two 46-line twins), `vfp_outer`
(chain), `sStage_6c` (piece, 2 lines), `sfv_fetch` (20: step% + nx_run + 6-field record), `lldMag_big` (62:
two runs, a callee, 7 load readbacks, 14-way keep split, frame chain), `fprintf_via` (45). Eight of ten
carry the L-carry obligation (record rebuild/readbacks), five the L-addr one, one L-split; two are
wrappers with none.

### 1d. Clone census (hypothesis a)

Disassembly (capstone over the ELF): `_svfprintf_r` 3,212 instructions, `_vfprintf_r` 3,395. With
registers kept and branch targets made function-relative, 14% of instructions align (difflib); the
longest identical run is 13 instructions; histogram of identical blocks: 210 of length 1, 43 of 2,
one of 13. Mnemonic-only sequences align 66% (blocks up to 66 instructions, 1,511 instructions in blocks
≥ 10): the same source with different register allocation, stack slots (0x50 vs 0x40) and block order,
plus FILE-specific code in vfprintf (orientation, `__sinit`, `cantwrite`, `__sbprintf`). A relocation
certificate (prove once over a code shape, instantiate per address by `decide`) has nothing to apply
to: hypothesis (a) is false at the instruction level; what remains is a simulation up to register and
slot renaming with block reordering.

The real clones are elsewhere. Functions whose entry is proved in two or more files touching the target
(conclusion `… 0x<entry>#64 R Mt`):

| function | files | kind |
|---|---|---|
| memmove | SnpMove (595 lines, 30 s), Fprintf/Move (747, 14 s), ReallocMove (380, allocator host) | same code, other host |
| strlen | SnpStrlen (307, 41.6 s), Interp/StrlenRun, Stdout/Strlen, Fprintf/Strlen (embeds StrlenRun, 76 lines, 0.8 s) | same code, other host |
| `__udivdi3`, `__umoddi3` | SnpArith (224, 4.2 s), Interp/ProofArith, Fprintf/Arith (bridges, 75 lines, 0.8 s) | same code, other host |
| `__swrite` | Stderr/Swrite, Stdout/Swrite | same code and host, six constants differ |
| fwrite, `__sflush_r`, `_fflush_r`, `__sfvwrite_r`, `__sprint_r`, `_vfprintf_r` entry | Stderr/* or Fprintf/* beside Stdout/* or each other | same code, other FILE; stderr is unbuffered (`__SNBF`), so paths diverge after the flag test |

### 1e. Format census (hypothesis b)

Call sites in the ELF: `snprintf` 10 (8 with a constant format by `auipc`/`addi` into `a2`; 2 with a
format passed through a parameter: `runtime_error(fmt, a1, a2)` at 0x80002dc8 and the parser's error
helper at 0x800007f8), `fprintf` 5 (all constant: `"%lld"`, `"<fn %s>"`, `"<native fn %s>"` to stdout
from `value_print`, `"%s\n"` twice to stderr from `main`), `fiprintf` 1 (out of memory, not via these
proofs). The stdio proofs are already per format (`Fprintf/Fmts.lean`, `fprintfOut` over three formats;
`fprintfSpec` fixes `errLineFmt`). `SnprintfProved` (frozen; a field of `NewlibHoles`, used by
`EndToEnd` and `Supply`) quantifies over every format with `FmtArgsOK` (`parseFmt bytes = some convs`,
≤ 5 args), which `runtime_error`'s pass-through format needs; the two constant-format snprintf theorems
(`snprintfInt_out` for `%lld`, `snprintfFn_out` for `<fn %s>`) already exist beside it for content.
Hypothesis (b) cannot replace the general proofs without changing a frozen statement, and its
specialised half is already in place.
## 2. Laws

| law | statement | status / check |
|---|---|---|
| L-reloc (hyp. a) | the svfprintf and vfprintf pieces are one proof relocated | false: 14% instruction identity, longest identical block 13 instructions (§1d) |
| L-fmt (hyp. b) | a format-specialised run replaces the per-conversion proofs | blocked by the frozen `SnprintfProved` (quantifies over formats); the specialised half exists (§1e) |
| L-host | a run proved over (text1, rs1, S1, no output) holds in every host with text2 ⊇ text1, rs2 ⊇ rs1, S2 ⊇ S1 and any output wrapper, the extra registers/bytes kept | proved (`swp_text_mono`, `swpo_bridge`, `LocalRun.embed`); used 3 times; memmove, strlen and udiv/umod re-proved per host instead. Check: the two bridged files compile in 0.8 s each |
| L-param | a run of fixed code whose data dependence is only through constants (FILE address, flags, fd) is one proof parametric in them; branches the constants decide are decided at instantiation | new; holds verbatim for `__swrite` (a diff of the two proofs differs in exactly six constants and one stack bound); for fwrite/sflush/sfvwrite/sprint it holds up to the `__SNBF` test (ROUND-3 found the same for bit 13 in `__swbuf_r`) |
| L-carry | at a piece boundary, facts about registers outside the run's write set, loads outside its store footprint and bytes outside its footprint carry unchanged; the outgoing record is the incoming one minus the overwritten facts plus the run's new facts | true by `SegFrom`'s frame clauses; applied by hand at every boundary |
| L-addr | stack addresses are `top − K + k`; two spellings with the same literal offset are equal; disjointness of two such addresses is a comparison of literals | used by the window layer for side conditions (ROUND-3); the record fields still re-spell by `omega` |
| L-split | twins that differ only by a constant the run tests are one piece with the branch decided by the constant | twin pairs exist (`svf_digExit0/45`, 46 lines each) |
| L-exec (hyp. c) | the executor (`xrun` with `calls`) crosses what are today piece boundaries | to measure (P3) |

The stall is partly in applying proved laws (L-host: bypassed by host; L-carry: proved inside the
executor's fact handling and by `SegFrom`, re-applied by hand at boundaries) and partly new (L-param).

## 3. Held-out suite (drawn before any candidate was built; commit 28d2fd88)

`abstractions/ROUND-8-heldout.json`. Populations: C = the 10 clone groups of §1d (2,975 lines); R = the
other 107 run units (theorems with `SnpW`/`SWPO`/`NW` conclusions, `#ix`/`#nx` chains and segments),
stratified by measured cost: R-S ≤ 30 (17 units), R-M 31–100 (69), R-L > 100 (21).
`random.Random(20261001)`: `sample(C,4)`, `sample(R-S,2)`, `sample(R-M,2)`, `sample(R-L,2)`; the first two C
and the first of each R stratum are primary, the rest fresh.

| case | stratum | file | baseline |
|---|---|---|---:|
| `udiv_nw`+`umod_nw` | C | SnpArith | 211 |
| `fwriteErr_run` (33 pieces) | C | Stderr/FwriteRun | 152 |
| `vfp_lit` | R-S | Fprintf/Scan | 30 |
| `snp_epi` | R-M | SnpSnprintf | 56 |
| `sbprintf_run` (6 pieces) | R-L | Fprintf/Sbprintf | 171 |
| fresh `sprintErr_run` | C | Stderr/SprintErr | 85 |
| fresh `sflushF_run`+`sflushF_run0`+`fflushF_run`+`fflushF_run0` | C | Fprintf/Flush | 240 |
| fresh `udiv_sw` | R-S | Fprintf/Arith | 13 |
| fresh `ssp_B` | R-M | SnpPuts | 46 |
| fresh `fprintfHead_run` (3 pieces) | R-L | Stderr/FprintfHead | 167 |

Primary baseline 620 lines, fresh 551. `udiv_sw` is already a bridge at the floor (11 lines).

## 4. Blind ontologists

Six agents (five seeded by random 256-character strings, one by a random dictionary sentence) got the
semantics, the census, the laws, the clone and format measurements, the held-out statements verbatim,
the importable abstractions with use counts (all importable; E36), the forbidden vocabulary (hand
records, field-by-field rebuilds, readback bullets, `show … by omega` re-spellings, per-host re-proofs,
per-address lemmas, SMT/model checking, generators, "a better tactic") and the decision-procedure
restrictions. Each returned five candidates in 75–91 s. Raw answers: `~/syi-r8/fanout/`.

| candidate | agents | rules = laws | recommended first by | decided by (flagged search) |
|---|---:|---|---:|---|
| K. fact ledger: records as `List Fact` (`reg`/`ld`/`byte`/`frame`) with a computable `kill W F` and one carry rule | 6/6 | L-carry | 6/6 (with A) | `decide` on literal keys; cross-base or symbolic-offset disjointness by search (all six flag it) |
| A. address normal form `⟨base, k : Int⟩` with hit/miss readback by literal comparison, normaliser by reflection or simproc | 6/6 | L-addr (+ K-read) | 6/6 (with K) | `decide` on `Int` literals; different bases fall back to `omega` on a filtered context |
| H. minimal-host summaries + one base-change rule (a `Host` class, texts as named segments so inclusion is a name check) | 6/6 | L-host | — (third) | instance search + `decide` on segment names; footprint inclusion via A |
| P. constant-parametric runs with constant-decided branch guards (L-split as the depth-1 case) | 6/6 | L-param, L-split | — (fourth) | `decide` at literal instantiation; a genuinely symbolic flag (`ConsoleMt fl`) is a case split (search) |
| S. simulation up to register/slot renaming between svf and vfp blocks | 6/6 | L-reloc (weakened) | 0/6 (all: defer) | `decide` on decoded blocks; the alignment is search |
| E. computed effect signatures (a reflective footprint analysis producing K's write sets) | 1/6 | L-carry premises | — | kernel evaluation |
| N. reflective boundary states normalised by evaluation (port `sym_run`) | 1/6 | L-carry + L-addr | — | kernel evaluation |

Theories cited: gen/kill dataflow and reaching definitions, incremental view maintenance, lenses,
double-entry bookkeeping, AGM belief revision, transaction write sets, LZ77 back-references, dead
reckoning, Noll's frame-indifference; base+offset and zone/octagon/DBM domains, Karr's affine relations,
manifold charts, geodetic datums, torsors, linker relocations (symbol + addend), crystallographic
fractional coordinates; Grothendieck fibrations and base change, sheaf restriction, covering spaces,
full faith and credit, separate compilation and dynamic linking; partial evaluation and Futamura
projections, binding-time analysis, Reynolds parametricity, software product lines and featured
transition systems, genotype/phenotype, jumper settings; translation validation, nominal sets,
synteny blocks, sequence alignment; normalisation by evaluation and proof by reflection.

## 5. Retrieval by law

All candidates are **known**:

* K: frame inference in separation logic (bi-abduction, Calcagno, Distefano, O'Hearn & Yang, POPL 2009;
  Smallfoot's frame inference); gen/kill dataflow. In this project the executor already carries
  facts across a run (`symRunX`'s introduced equations and `@[xrun_post]` facts), and `SegFrom` states
  the frame; the hand cost is at the boundaries the executor does not cross.
* A: base+offset pointer domains (Miné, LCTES 2006; value-set analysis, Balakrishnan & Reps, CC 2004);
  in this project the window layer `Win` (ROUND-3) is exactly this for side conditions.
* H: code-heap weakening/linking in certified assembly (Ni & Shao, XCAP, POPL 2006; Feng, Shao et al.,
  SCAP, PLDI 2006); Myreen's decompilation reuses callee specs across callers; here `LocalRun.embed`,
  `swpo_bridge`, `swp_text_mono`.
* P: specification polymorphism over auxiliary variables (higher-order Hoare logic); partial evaluation
  of proofs; in this project the `#fwrite_run_at` command instantiates one stdout chain for two flag
  constants, and ROUND-2's flag-parametric exit chain.
* S: translation validation (Necula, PLDI 2000), product programs (Barthe, Crespo & Kunz, FM 2011).

## 6. Variation

The ideonomy draw was combination and abstraction-lift, with a scale organon. It placed the candidates
on one scale: how much new vocabulary sits at a piece boundary.

- 0: fewer boundaries. Longer `xrun` runs with `calls` summaries (hypothesis c), giving P3.
- 1: the laws as lemmas and tactics over the existing terms, with no new datatype. This is the meet, P2.
- 3: the fact ledger plus the offset normal form (6/6), giving P1.
- 4: reflective boundary states (1/6), not piloted.

The clone stratum used the same scale. It runs from the existing transfer lemmas applied to minimal-text cores, up to a `Host` class with parametric configs. That pilot is PC.

## 7. Bake-off (primary cases; one measurement script on every branch, `~/syi-r8/meas`)

Pilot branches all start from 28d2fd88: P1 `exp-R8-P1` ccab9a8e, P2 `exp-R8-P2` 815b4ccd, P3 `exp-R8-P3` 7b9ef95f, PC `exp-R8-PC` 82906617. Each was built over all target modules that import its changes.

The case cost below counts declarations, plus the lines the case alone uses, plus apportioned shared helpers. Lines of case-local macros are added by hand (`sb_finish`). Failed compiles are in brackets.

| case | incumbent | P1 ledger+offsets | P2 meet | P3 executor reach |
|---|---:|---:|---:|---:|
| `vfp_lit` | 29.6 | 25.4 [4] | 23.4 [4] | 25.6 [4] |
| `snp_epi` | 55.8 | 51.8 [6] | 37.6 [≈6] | 55.8 [0] |
| `sbprintf_run` (+ `sb_finish` macro) | 170.8 + 46 | 164.7 + 18 [17] | 131.7 + 12 [≈22] | 210.8 + 0 [≈10] |
| R total | 302.2 | 259.9 (−14%) | **204.7 (−32%)** | 292.2 (−3%) |
| setup lines | — | 539 (Ledger.lean) | 167 (Carry.lean) | 63 (SymFront, XPost) |
| touched-module CPU, min of 3, interleaved | 43.6 s | 49.0 (+12%) | 46.9 (+7.6%) | 43.1 (−1%) |

| case (clone stratum) | incumbent | PC |
|---|---:|---:|
| `udiv_nw`+`umod_nw` | 214 | **78** [3] |
| `fwriteErr_run` | 151.8 + 15 macro | 151.8 + 15 (unchanged; only its callee `__swrite` merged) [6, all on `swriteP`] |
| setup | — | 89 (HostRun.lean) + 5 (`swriteP` over the old stdout proof) |
| touched-module CPU | 27.9 s | 21.9 s (−22%) |

Each pilot's findings:

- **P1.** The ledger needs adapters in both directions, because the executors read raw hypotheses and the statements are frozen. Store coverage is decided per store by search. It fails the 10% time bound on Sbprintf.
- **P2.** Most of its failed compiles came while building the tactic.
- **P3.** It removed 6 boundaries but almost no glue. It also fixed a silent `xrun` defect: facts introduced by a `calls` continuation never reached the normaliser.
  - Boundaries it could not cross: restart after an indirect `jalr`, the per-declaration heartbeat budget, and facts about large memory terms.
- **PC.** L-host is fully confirmed on udiv/umod. A host-generic core is proved once over the minimal text (ArithRun.lean, 214 lines) and replaces the SnpArith and ProofArith copies; the instances are 3 lines each.
  - L-param merges `__swrite` only. The stdout and stderr fwrite paths diverge at the `_bf._base`/cantwrite test, not at `__SNBF`: both FILEs have `__SNBF`.

## 8. Status at hand-off (decision pending fresh cases)

- **Top candidates.**
  - R stratum: P2 (the meet; −32% primary, setup 167, +7.6% time, within the bound).
  - Clone stratum: PC (L-host; −64% on udiv/umod, −22% time).
  - They cover disjoint strata, so the combination C = P2 + PC is on `exp-R8-C`: 24bb93d6, full `lake build` green with 1548 jobs.
- **Fresh cases are running on C** and have not been measured: `sprintErr_run`, the Flush group, `udiv_sw`, `ssp_B`, `fprintfHead_run`.
- **Not done:** the adoption decision, the rollout, the gate re-run and the statement and axiom checks on C.
- **Hypotheses.**
  - (a) False at the instruction level. The real clones are same-code-other-host (L-host), and there L-host pays.
  - (b) Blocked by the frozen `SnprintfProved`.
  - (c) Partly true: the executor crosses some boundaries, but saves 3% of lines.
