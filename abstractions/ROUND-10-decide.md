# Abstraction-discovery round 10: the decision procedures inside the tactics (2026-10-01)

Branch `exp-R10`, from `exponentiate-next` e0981ae6 (PR #14 snapshot 8, after ROUND-9). This is a
TIME round. Target: the decision calls (`omega`, `simp`, `decide`) that the proof tactics issue,
repo-wide over `VsaIris/Vsa` (225 modules), `VsaIris/Interp` (190) and `Vsa/Sim` (212): 627 modules,
115k non-blank lines. Round 9's finding was the start: `omega` was 149 of 229 tactic seconds in the
allocator, and most of its calls were issued by tactics, not written in proofs. Raw material (census
spy, scripts, per-call tables, kernel re-check, briefs, ontologist answers, timings) is in `~/syi-r10/`.

## 0. Primary measure (stated before the bake-off)

Single-file user CPU of the held-out modules (`LEAN_NUM_THREADS=1`, the module copied outside the
repo and compiled against the branch's build, contenders interleaved in one window, min of 3).
Secondary: non-blank lines (setup lines of the layer, lines changed in the cases). Rollout bound:
no file may get slower by more than 10% (E49). Headline: the full clean `lake build` (all default
targets including executables), wall and user time, before and after.

## 1. Census

### 1a. Gate and the clean build

The gate (`syi-gate/scripts/abstraction_gate.py --root`, run by hand; the branch still has no
`scripts/` and no CLAUDE.md, C1) fails with the same 12 clusters as at the end of round 9 (`Call run`,
`Cat Tail run`, `Clo run`, `get Elem write Map`, `hex bits forwards resp`, `lj fin`, `oom cert`,
`sprint Err`, `svf Pro`, `sx`, `tr`, `utr`). None is a decision-procedure cluster; this round is
driven by time, not by the gate.

Full clean build before the round (worktree `syi-r10-base` at e0981ae6, `rm -rf .lake/build` of the
project's own modules, dependencies kept; `LEAN_NUM_THREADS=10`, all default targets, 1,552 jobs,
load 8–17 on 32 cores): **wall 608.6 s, user 4,851 s**, 0 errors, 0 `sorry` warnings.

### 1b. The decision procedures, by the tactic that issued each call (E51, E52)

Tool: every module of the scope was compiled once (one thread, 12 in parallel) as a copy with a
spy prepended that wraps the elaborators of `omega`, `simp` and `decide` (`~/syi-r10/census/spy.lean`).
Each call records its time, success, the number of hypotheses, the kernel time of its certificate
(re-checked with `Environment.addDeclCore`), and the source position of the syntax that issued it:
a call made by a macro or an elaborator carries the position of the tactic the proof wrote, so the
token at that position names the originating tactic (`rgn_run`, `nx_run`, `omega`, …). The copies use
`Elab.async false`, so a call's time includes the synchronous kernel check of its auxiliary lemma (with
asynchronous elaboration the re-check timings were polluted by waiting on other tasks). 12 modules
needed `maxHeartbeats 0` in the census copy only (synchronous elaboration counts heartbeats per
declaration, not per proof task).

Scope total in census mode: 4,918 s user (≈ 4,400 s without the re-checks).

| decision procedure, issued by | calls | tactic s (incl. own kernel check) | of which kernel | failing calls | s in failing calls |
|---|---:|---:|---:|---:|---:|
| `omega` written in proofs (incl. `<;> omega`, `all_goals omega`) | 12,545 (10,868 sites) | 401.1 | 201.0 | 265 | 2.3 |
| `omega` from step drivers and other tactics | 20,126 | 487.5 | 209.5 | 6,977 | 40.6 |
| `omega` from the region tactics (`rgn_run`/`rgn_step`/`rgn_arith`/`rgn_ld`/`rd_log`/`log_in`) | 4,311 | 193.2 | 88.9 | 1,078 | 15.7 |
| `omega` from the carry family (`carry_close`, `region_close`) | 1,610 | 21.2 | 10.9 | 406 | 1.5 |
| **`omega` total** | **38,592** | **1,103** | **510** | 8,726 | 60.1 |
| `simp` written | 9,448 | 155.8 | – | 270 | 0.8 |
| `simp` from step drivers and other tactics (includes `omega` run as simp's discharger) | 133,633 | 1,306.4 | – | **90,443** | **385.7** |
| `simp` from the region tactics | 2,761 | 125.7 | – | 417 | 1.2 |
| `simp` from the carry family | 3,899 | 76.9 | – | 1,725 | 3.2 |
| `decide` (`decide +kernel`) in the generated boot witnesses (`boot_witness`, 10 modules) | 746 | 434.9 | – | 0 | 0 |
| `decide` elsewhere | 48,177 | 114.4 | – | 4,044 | 0.7 |

Executed against written (E52): 38,592 `omega` calls executed, 12,545 of them from the 10,868 written
sites; tactics issue two thirds of the calls and 64% of the `omega` time. For `simp` the written share
is 9% of the time.

Kernel re-check of every theorem of the scope (`~/syi-r10/kern/Kern.lean`, E51): 1,015 s over 29,322
declarations above 1 ms; `omega` certificates are 19,365 of them and 444 s (44%); the boot witnesses
238 s.

Per call: `omega` averages 28.6 ms including its kernel check; it grows with the hypotheses in context
(13.7 ms below 10, 21 ms at 20–49, 35–73 ms at 50–89; most calls see 20–80 hypotheses) and has a heavy
tail (the top 1,000 calls are a third of the time; the worst single calls are 2–6 s, e.g. a byte
decomposition `d.toNat / 2^(8i) % 256` in `Vsa/Sim/ValueSpec.lean` at 6.3 s). An oracle run on four
held-out modules (re-run each successful `omega` with only the hypotheses its certificate uses)
shows what context size costs: certificates use 5–15 of 30–76 hypotheses; tactic time −40–55%, kernel
−40–80% (VfpEntry kernel 3.7 → 0.7 s). Failing `simp` calls (no progress, inside `try`) cost 4.3 ms
each on average; a `simp only [30-lemma list]` costs ≈ 1.5 ms even on a trivial goal (the list is
elaborated at every call), a `simp only [attr_set]` ≈ 0.3 ms.

Top issuing tactics (omega s / simp s incl. nested omega / failing-simp s): per-file `*_tac` macros of
the stdout runs 56 / 145 / 22; `nx_run` 26 / 106 / 40; `ix_fwd` 8 / 112 / 4; `rd_log` 44 / 66 / 0;
`xh_step` 5 / 104 / 48; `rgn_run` 75 / 22 / 0; `carry_close` 21 / 74 / 3; `sym_run1` 24 / 71 / 40;
`sx_run` 47 / 38 / 10; `nx_addr` 41 / 43 / 1; `snp_runF` 11 / 68 / 45; `nf_go` 6 / 64 / 31.

Modules by family of their tactic-issued decision time: 23 modules are region-dominated (R:
MallocBlocks 68 s of R-time, FreePaths 40, ReallocPrevT 27, FreeBin 26, MallocPaths 26, …), 104 are
step-driver-dominated (T: Stdout/Fwrite, Stdout/Fputs, SnpSvf, SnpSvfConv, Stdout/Swbuf, Interp
ProofStringify, ExitH/RunHead, …), 22 are dominated by written `omega` (W: HeapFree, ReallocMal,
EnvDefineArms, Setjmp, HeapTake, ValueSpec, …).

**Where the cost is.** About a quarter of the scope's CPU is `omega` (half of it kernel), and a further
~9% is `simp` calls that fail. Tactics issue most of both. The region search (round 1's named cost) is
193 s of `omega`; the step drivers are larger (488 s of `omega`, 386 s of failing `simp`).

## 2. Laws

| law | statement | check |
|---|---|---|
| L-key | an address and a region base that are one atom plus literal offsets are compared by literals; membership needs no search over regions | exists as `Win` keys (newlib, one `decide`), not as `Rgn` keys (allocator, `omega` per candidate) |
| L-wrap | `(x + c) % 2^64` equals `x + c` or `x + c − 2^64`, decided by a bound fact; no `%` atom need reach `omega` | `key_toNat_add`/`key_sub` exist and are applied by `rgn_arith` as rewrites |
| L-hoist | within one run the facts the side goals need are fixed; side goals differ by literal offsets | oracle: certificates use 5–15 of 30–76 hypotheses; context size is 40–80% of a call's cost |
| L-guard | a rewriting pass whose rule heads do not occur in the goal makes no progress; a macro alternative whose goal shape cannot match fails | 90,443 failing `simp` calls (386 s); `sx_side` has 4–8 alternatives |
| L-cert | sibling side goals over the same facts share one certificate up to a literal comparison | not checked before the pilots |

## 3. Held-out suite (drawn before any candidate; commit 2e29cd47)

`abstractions/ROUND-10-heldout.json`. Population: modules with ≥ 5 s census CPU in the three families
(R 23, T 104, W 22). `random.Random(20261010).sample(sorted(stratum), 4)` per stratum; first two
primary, last two fresh.

| stratum | primary | fresh |
|---|---|---|
| R (region tactics) | MallocRebin (14.2 s), MallocBlocks2 (13.3) | ReallocTail (13.6), FreeLarge (8.5) |
| T (step drivers) | Stderr/VfpEntry (23.5), Interp/IntRunAdd (9.7) | Interp/ProofNativePrint (35.7), Interp/SeqLoopInterp (9.2) |
| W (written omega) | HeapMoveAt (5.3), HeapRealloc (6.7) | HeapCarve (12.8), Strlen (12.5) |

A tactic change reaches every module that uses the tactic; "held-out" here means the pilots tune on
the primary modules and the fresh ones are measured only by the coordinator.

## 4. Blind ontologists

Four agents (three random 256-character seeds, one random dictionary sentence; seeds pasted as
literal text, E53) got the semantics, the census, the laws, the existing pieces with use counts, the
real restrictions of the decision procedures, the forbidden vocabulary ("fewer hypotheses for omega",
"better region order", "more simp lemmas", "a faster omega", "cache by goal hash") and the held-out
modules (`~/syi-r10/fanout/brief.md`). Each returned five candidates in 71–78 s.

| candidate | agents | rules = laws | first choice of | decided by |
|---|---:|---|---:|---|
| K. atom + literal keys / frames (datum frames, reference electrodes, relocations, dead reckoning): reify an address as (atom, literal), pick the region by atom, close by `decide` on literals; symbolic extents as a second atom with a floor fact | 4/4 | L-key, L-wrap | 3/4 | syntactic reification, closed `decide`; omega fallback when not keyed (flagged as the only search) |
| G. head-symbol guards and shape dispatch (Rete, discrimination trees, triage, passivation) | 4/4 | L-guard | 2/4 (1 as "first", 3 as the cheap side task) | syntactic, microseconds |
| C. parametric certificates for literal siblings (template polyhedra, parametric Farkas, unit cells, stencils) | 4/4 | L-cert | 0/4 | one omega per family + `decide` per instance; family selection is search (flagged) |
| W. carry-bit arithmetic and byte lanes (wrapped intervals, two's-complement carry, SWAR) | 4/4 | L-wrap, heavy tail | 0/4 | propositional rewrites with bound facts |
| S. keyed store logs (select/store, Burstall–Bornat, stratigraphy) | 4/4 | L-key on read-over-write | 0/4 | key match + `decide` |
| H. run charter (proved once per run, side goals in a cleared context) | 2/4 | L-hoist | 0/4 | one omega per run |
| L. lazy register file (`updChain` lookup by literal index) | 1/4 | register readback | 0/4 | `decide` on literal index lists |

Theories cited: DBMs and octagons (Dill 1989; Miné 2001, 2006), linker relocations (Levine 2000),
affine access functions (Feautrier 1991), Rete (Forgy 1982), term indexing (McCune 1992; Graf 1996),
template polyhedra (Sankaranarayanan, Sipma & Manna 2005), parametric LP (Gal 1979; Schrijver 1986),
wrapped intervals (Navas et al. 2012; Gange et al. 2013), McCarthy arrays, Burstall/Bornat, separation
logic (Reynolds 2002), proof-carrying code (Necula 1997), loop-invariant code motion, CDCL clause
learning, call-by-need (Launchbury 1993), geodetic control networks, Athenian trierarchy.

## 5. Retrieval by law

All candidates are **known**, and most already exist at another layer of this project:

* K: relocation/affine keys and zones; in this project the `Win` keys of round 3 decide L-key by one
  `decide` for the newlib runs (44 files), 0 allocator files; the allocator's `Rgn` regions decide it
  by trying candidates with `omega` (round 1).
* G: Rete / discrimination trees — Lean's `simp` already indexes its lemmas by discrimination tree;
  what is missing is the guard at the call level (a pass is run whether or not its heads occur) and a
  precompiled set (`register_simp_attr`, used by `seval_state` elsewhere in the repo).
* H and C: loop-invariant code motion / proof-carrying code / parametric Farkas; round 9's
  `omega_near` was a per-goal version of H (lost).
* W: wrapped intervals; `key_toNat_add`, `key_sub` exist (rewrites in `rgn_arith`).
* The reflective difference checker for L-key/L-wrap exists on branch `exp-R9-P3` (4487f40d).

## 6. Variation

Lattice by where the decision is made (rows) and what it decides (columns):

```
               | which region / alternative | membership / bound    | which facts            | wrap / bytes
---------------+----------------------------+-----------------------+------------------------+--------------
search (today) | try each, omega each       | omega, full context   | all hypotheses         | omega with %
syntax         | atom match (K), shape (G)  | -                     | run's recorded set (H) | rewrite (W)
closed compute | -                          | decide on literals (K)| -                      | -
reflection     | -                          | DBM checker (P3)      | DBM collects its own   | DBM wrap term
skip           | head guard (G)             | -                     | -                      | -
```

Negating "the tactic must decide the side goal" gave "the tactic need not run": guards (G). Negating
"each side goal is decided alone" gave the per-run set (H) and parametric certificates (C). The meet
of K with the existing terms is "`Win`-style keys over `Rgn`, no new datatype" (round 3's decision
procedure reaching round 1's layer: E20, E41).

Pilots (worktrees from 2e29cd47, each its own tree, E56):

* PA (K + W, the meet; round 1's named cost): keys decide region membership inside `rgnTry`/`rgnSide`
  and `sx_addr`, over the existing `Rgn`/`ARgn`/`Win`; omega fallback.
* PB (G, laws as rules over existing tactics): head guards before the drivers' normalisation passes,
  precompiled simp sets, shape dispatch for side-condition alternatives.
* PC (H + C): per-run recorded fact set from earlier certificates; side goals first in the cleared
  context; fallback full.
* PD (reflection, round 9's P3 measured inside the tactics): the DBM checker as first pass in the
  region / `sx_addr` / `nx_addr` dischargers.

## 7. Bake-off (one timing script for all contenders, `~/syi-r10/bake/bake.sh`)

Pilot branches from 2e29cd47: PA `exp-R10-PA` f8a366fe, PB `exp-R10-PB` f8a450aa, PC `exp-R10-PC`
1ad83a55, PD `exp-R10-PD` 1f885b76. Each pilot built every importer of what it changed (PA the 58
allocator modules; PB, PC, PD all of `VsaIris`, PC also `Vsa`): 0 errors, 0 `sorry`. No statement
or proof file changed in any pilot; all four change tactics only.

Single-file user CPU, s, min of 5 rounds; per file the five contenders run back to back (base first),
three rounds in parallel, then two more; load 18–90 on 32 cores (the machine is shared with other
projects' builds).

| module | base | PA keys | PB guards | PC hint front end | PD checker first |
|---|---:|---:|---:|---:|---:|
| MallocRebin (R) | 10.29 | **8.51** | 10.01 | 8.76 | 8.95 |
| MallocBlocks2 (R) | 10.57 | 10.22 | 10.23 | 9.76 | **9.56** |
| Stderr/VfpEntry (T) | 13.56 | 13.52 | 13.80 | 13.42 | **7.91** |
| Interp/IntRunAdd (T) | 7.20 | 7.15 | **6.42** | 7.10 | 7.14 |
| HeapMoveAt (W) | 3.00 | 3.14 | 3.09 | **2.89** | 3.04 |
| HeapRealloc (W) | 4.01 | 4.02 | 3.95 | **3.49** | 4.03 |
| **primary total** | 48.63 | 46.56 (−4.3%) | 47.50 (−2.3%) | 45.42 (−6.6%) | **40.63 (−16.5%)** |
| fresh: ReallocTail | 8.93 | 8.85 | 9.72 | 7.87 | 9.24 |
| fresh: FreeLarge | 6.86 | 6.66 | 6.42 | 6.50 | 6.44 |
| fresh: Interp/ProofNativePrint | 25.54 | 28.98 | 24.30 | 28.54 | 27.33 |
| fresh: Interp/SeqLoopInterp | 8.16 | 8.30 | 7.71 | 8.67 | 8.75 |
| fresh: HeapCarve | 8.77 | 8.19 | 8.50 | 7.22 | 8.65 |
| fresh: Strlen | 9.32 | 9.59 | 9.32 | 9.57 | 9.56 |
| fresh total | 67.58 | 70.57 | 65.97 | 68.37 | 69.97 |
| fresh without ProofNativePrint | 42.04 | 41.59 (−1.1%) | 41.67 (−0.9%) | **39.83 (−5.3%)** | 42.64 (+1.4%) |
| setup (+/− lines) | | +253 | +350 / −58 | +123 | +741 / −42 |

ProofNativePrint is noise-dominated: base ranged 25.5–30.3 s over the five rounds, and PA, whose
change cannot reach that file (it uses `sym_run1`, and `rgnSide` returns at once without regions),
measured 29.0–31.7. The fresh total is therefore reported with and without it.

What each pilot found (census before/after on its modules, per-call costs measured inside the tactic):

- **PA (keys, the meet).** `rgnKeyed` normalises the keyed address and the region bases to atom +
  literal (atoms rewritten through `x.toNat = r` facts; `lin_mod` removes an inner `% 2^64` from the
  key's bound), picks the region by atom and closes membership by one lemma whose check is a closed
  `Nat.ble … = true` (`Eq.refl true`); symbolic extents use a literal floor fact, `StOK` alignment a
  `v % 16 = 0` fact. Region `omega` in the R modules 82 calls / 7.4 s → 33 / 3.3 s; 18 of 26 region
  obligations close by key, 8 fall back (negative offsets, an index-scaled static-table key, a
  two-atom sum). Per call: key route ≈ 27 ms (mostly the key simp), failed key attempt +28 ms, the old
  path ≈ 260 ms per obligation.
- **PB (guards).** `simp_set [(disch := t)] SET [at loc]` over 12 registered simp sets, with an exact
  guard (skip only if no subterm of the target or of the non-dependent Prop hypotheses can change:
  matched theorems/simprocs are tried, simp's own beta/let/proj/matcher reductions count;
  `SIMPSET_CHECK=1` re-runs every skipped call and warns on progress — 0 misses over all of
  `VsaIris`). Failing simp in IntRunAdd 161 calls / 0.70 s → 46 / 0.03 s, VfpEntry 0.78 → 0.30 s.
  Guard 0.6–1.2 ms per call. The registered sets saved almost nothing (`ix_reg` 0.50 → 0.51 s): the
  list-elaboration cost measured on trivial goals is small against the traversal on real goals. Shape
  dispatch was analysed and not built: alternatives that cannot match already fail in microseconds;
  the expensive failures are prune attempts whose outcome depends on hypotheses, not shape.
- **PC (hint front end).** A project-wide elaborator for the `omega` syntax (`Vsa/OmegaHint.lean`,
  imported by `Vsa/Elf.lean`, reaching 615 of the 627 modules), `@[no_fallback]`: per declaration it
  remembers the hypotheses earlier certificates used and, in contexts of ≥ 40 hypotheses, runs omega
  first on the last certificate's hypotheses (+ unseen ones), then on the union, then the full context.
  11.5% fallbacks; reduced runs 11–40 ms against 20–160 ms. Two census corrections: the oracle of §1b
  overstated the ceiling (the rerun hit `mkAuxTheorem`'s cache and skipped the kernel check; restoring
  state first gives tactic −27–49%, VfpEntry −11%), and a user elaborator that throws makes
  `evalTactic` run the builtin as well, so the census spy paid every failing call twice (needs
  `@[no_fallback]`; the recorded per-call times are right, the census CPU totals include the doubles).
- **PD (reflective checker first).** `VsaIris/Vsa/Dbm.lean` (615 lines, imports only Lean): round 9's
  checker with the omega fallback removed, a re-solve over only the facts the certificate uses (kernel
  re-walks 5–15 facts; disjunctive goals 80–118 → 6–30 ms kernel), search caps (96 cycle searches, ≤ 12
  disjunctive facts, ≤ 40 atoms); `omega_dc := first | dbm | omega` in 45 tactic dischargers of 12
  tactic files (carry, nx_fdisch, nx_win, nx_addr/nx_hb, sx_addr, rgn_*, rd_log, xrun, ExitH, int_post).
  On the six modules the checker closes 565 of 941 tactic-issued calls (60%) at 1.7 ms tactic + 6.5 ms
  kernel against 18.7 + 10.2 ms for omega on the same calls; a failed attempt costs 1.4 ms. It also
  closes 39% of written calls (not applied). On small isolated 2^64 goals it is slower than omega
  (13–17 vs 9–12 ms): it pays only in large contexts. `carry_close`'s omega calls 267 → 17.

Reading: the candidates act on different calls (PA region membership, PB failing normalisation, PC
written and driver omega in large contexts, PD tactic-issued omega), each names the others' territory
as its residue, and their setups do not conflict (merged with two trivial conflicts). Per the skill,
the next iteration is the combination, with no new abstraction code, measured on the whole scope.
