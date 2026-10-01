# Abstraction-discovery round 9: the dlmalloc proofs (2026-10-01)

Branch `exp-R9`, from `exponentiate-next` 451c6b8b (PR #14 snapshot 7, after ROUND-8). Target: the
allocator proofs, 72 modules, 18,449 non-blank lines at the start:

* path proofs `VsaIris/Vsa/{Malloc,Free,Realloc}*.lean` (run predicate `AW`, the allocator text);
* heap algebra `VsaIris/Vsa/Heap*.lean` (`PHeapAt` and the 13 heap-edit lemmas);
* their helpers found by the census: `Alloc*`, `Region`, `RegionCore`, `Bin*`, `Sbrk`, `Oom`,
  `OomSites`, `TopAbrupt`, `H5Sites`.

Round 1 was already this target: it adopted region keys (`Region.lean`) and heap permits
(`HeapPermit.lean`). This round measures what that rollout left. Raw material (census scripts, kernel
and tactic profiles, briefs, ontologist answers, measurement script, timings) is in `~/syi-r9/`.

## 0. Primary measure (stated before the bake-off)

Agent effort on statement-identical re-proofs of the held-out cases: non-blank lines of the case's
declarations + target declarations only the case uses (its constant tree, cut at other proof units) +
shared target helpers divided by the number of units reaching them, computed by one script on every
branch (`~/syi-r9/meas/{run.sh,MeasT.tail,meas.py}`), plus failed compiles. Generic layer lines are
setup (break-even against the fresh-case saving, E33). Secondary: single-file user CPU of the touched
modules (`LEAN_NUM_THREADS=1`, copies outside the repo); a candidate may lose at most 10% per file.
Tie-break (E14): the census found half of the target's CPU in one decision procedure, so a candidate
within 5% of the best on lines that cuts touched-module CPU by 15% or more is preferred.

## 1. Census

### 1a. Gate and reachability (run first)

The gate (`abstraction_gate.py --root`, run by hand; this branch has no `scripts/` and no CLAUDE.md, C1)
fails with 12 clusters; one is in the target (`oom cert`, 8 units, 9 → 9 lines, generated-looking
certificates in `OomSites.lean`). The allocator's cost does not show in name clusters: its units have
distinct names and one conclusion head.

Reachability (constant closure of every declaration of the README's result modules, ROUND-8's census
script): 456 of 9,840 target constants are off the path. After removing elaboration-only declarations
(tactics, macros, the `RgnHyp` meta structure, a tactic-used `SbrkPre.acc`) and unused fields of live
structures, 30 declarations remained (166 lines: `cp_pair`, `CPKeep`, `TopReserve`/`Reserve`,
`MHeap.off_stack(_w)`, `win_foot`, `WOK.*`, `PHeapAt.store_stack`, …). Deleted in 205acaac; the build
was green on the first try (E39). The cut is small (E38): round 7 already removed the dead fast path.

### 1b. Time (single-file user CPU, one thread)

**501.2 s** for the 72 modules (load 5–8 on 32 cores). Largest: FreePaths 50.5, MallocBlocks 32.4,
MallocExtend 26.3, FreeTrim 22.1, ReallocMal 20.4, HeapFree 19.5, ReallocPrev 19.2, MallocRebinL 16.3,
FreeBin 16.2, MallocPaths 14.4.

Profile of every module (`profiler true`, threshold 1 ms; `~/syi-r9/prof/all`):

| item | seconds |
|---|---:|
| tactic execution (cumulative) | 229.0 |
| of which `omega` | **149.3** (65% of tactic time) |
| `simp` / `refine` / `rw` / `sx_run` / `rgn_run` | 14.0 / 12.1 / 10.2 / 9.4 / 5.0 |
| kernel re-check of every target theorem (`addDecl` per theorem, `~/syi-r9/kern`) | 142.2 |
| of which `omega` certificates (4,700 auxiliary lemmas concluding `False`) | **121.2** |

In FreePaths `omega` is 16.7 of 20.9 tactic seconds; in MallocBlocks 12.5 of 14.4. An `omega`
certificate costs 22 ms of kernel time on average and grows with the hypotheses it collected (5–9: 12
ms; 20–24: 47 ms; 40+: 190 ms) and with disjunctive hypotheses (none: 22 ms; three: 84 ms; six: 192
ms). Sampled goals are small: `(R 14).toNat + 8 = A → d ≤ A ∧ A + 8 ≤ d + L`,
`((s + 2^64 − 16) % 2^64 + 16) % 2^64 = s`, `x + a + 16 ≤ top + 8`, "outside a store" disjunctions.
**About half of the target's CPU is `omega` on side goals.** (Two 9.5 s "kernel" entries in the
FreePaths profile are structure declarations waiting for earlier asynchronous proofs, not real cost;
isolated, the structures check in under 0.2 s.)

### 1c. Clusters (by conclusion head and by name stem)

| cluster | units | lines (declarations) | what is re-proved |
|---|---:|---:|---|
| K-path: theorems concluding `AW` | 156 | 6,800 | a machine path between two pcs: steps, side goals, register readbacks, a continuation call with a rebuilt record |
| K-edit: theorems concluding `PHeapAt`, ≥ 60 lines | 13 | 3,150 | a heap edit (release 548, moveBinAt 440, take 395, carve 322, cut 217, absorb 206, splitFree 198, setTop 179, topSplit 160, toTop 150, coalNext 129, topResize 113, coalPrev 97) |
| small `PHeapAt` lemmas (permits, store_errno, …) | 28 | 200 | wrappers |
| K-rec: record structures | 101 | 1,000 | `FNt`, `FPv`, `FreeLinks`, `PvIn`, `RD`, `BW`, … |
| readback / agreement equations (`Eq:getElem?`, `Eq:read64`, `Eq:toNat`) | 256 | 790 | `read64 (writeLog …) a = …`, `Mc[a]? = …`, BitVec spellings |

Path units by measured cost (script): 41 ≤ 30 lines, 52 in 31–100, 62 > 100; median declaration 37
lines. Body anatomy of a random sample of ten (seed 20261001): three are composition wrappers (≤ 25
lines, a continuation applied to a passed record, no obligations); the rest mix step rules
(`step% st <pc>`, 197 uses), per-branch register readbacks `simp only [upd_apply, Nat.reduceEqDiff,
ite_true, ite_false]` (400 lines in 35 files), address re-spellings `rw [show (R 15 + 8#64).toNat = x +
8 by rgn_arith]`, frame chains `((F.store (by omega)).store (by omega)).of_regs (by simp …)`, geometry
preludes (`have := HH.walk.chunk_bounds _ hX; unfold heapStart heapEnd at *`, 134 times) whose only job is
to feed `omega`, and bit arithmetic. `omega` is on 2,327 lines.

Heap edits: each re-establishes ~25 `HeapAt` fields after 1–5 writes. The untouched fields carry by a
"keep" argument per field (the word read is outside the written words; `read64_keep`, `writeLog_out`,
`omega`); the touched ones are re-proved. The full-agreement case is one lemma (`transport_read`, 22
uses); the "agree except W" case is re-proved inside every edit.

### 1d. Use of the existing layers in the target

| layer | uses in the target | importable |
|---|---:|---|
| region keys: `rgn_run` / `rgn_step` / `chunkK` / `frame_log`, `pres_log`, `log_in` | 129 / 66 / 46 / 27 each | yes |
| heap permits (`split/unlink/absorb_permit`) | 11 (3 files) | yes |
| `step% st` / `sx_run` | 197 / 52 | yes |
| `sym_run` / `xrun` | 0 / 5 (1 file) | yes |
| `carry_close`, `region_close`, `carry_arith` (round 8) | **0** | yes (Carry sits above 8 low allocator helpers only) |
| window keys decided by `decide` (`win_key`) | 0 | yes |
| `transport_read` (full-agreement heap transport) | 22 | yes |
| host-generic cores (`HostW`, `host_run`) | 0 | yes |
| block executor (`#derive_case`, `GHolds`, `segEval_selected_framed`) | 8 / 0 / 0 | yes |

What round 1's rollout left, measured now: permits reach 3 of the 13 edits (the other ten edit memory
relative to a base other than the invariant's); the region search is gone from the profile's top
(`rgn_run` 5 s), but the side goals it and the hand glue hand to `omega` are the main CPU cost; no
top-chunk region; frames are still carried store by store (`.store (by omega)`).

## 2. Laws

| law | statement | status / check |
|---|---|---|
| L-loc (time) | a side condition over address atoms follows from the facts about those atoms, not from the rest of the context | check: an `omega` front end that clears hypotheses sharing no atom with the goal (one round) kept 14 of 34 arithmetic facts on average and cut MallocBlocks 33.9 → 30.1 s even with 93 fallbacks to plain `omega`; closing over shared atoms kept 24 of 34 and saved nothing. Context size is part of the cost, not most of it |
| L-key | an address is `base + k` with `k` a literal; same-base comparisons are literal comparisons; disjunctions "outside a store" / "off the stack" are one relation between two windows | exists as region keys (decided by `omega`) and window keys (`decide`) in another lane |
| L-carry | registers outside a run's updates and loads outside its stores read back; the outgoing record is the incoming one minus overwritten facts | proved (`upd_other`, `read64_store_miss`, `frame_log`); `carry_close` applies it, 0 uses here |
| L-heapframe | `PHeapAt m … ∧ (m' agrees with m on the invariant's reads except W) ∧ (the fields reading W hold for the new shape) → PHeapAt m' …` | full-agreement case proved once (`transport_read`); the except-W case re-proved field by field in all 13 edits |
| L-compose | an edit that is a sequence of primitive edits is the composition of their rules | partly used (coalPrev calls take and absorb), junctions re-prove read-over-write and geometry |

## 3. Held-out suite (drawn before any candidate was built; commit f83224e1)

`abstractions/ROUND-9-heldout.json`. Population: the 197 proof units (theorems concluding `AW` or
`PHeapAt`) on the cut commit, measured by the script. Strata: H = heap edits (`PHeapAt`, ≥ 60
declaration lines, 13 units); S = `AW` with measured cost ≤ 30 (41); M = 31–100 (52); L = > 100 (62).
`random.Random(20261009)`, `sample(stratum, 2)` in the order H, S, M, L; the first of each pair is
primary, the second fresh.

| case | stratum | file | baseline (script) |
|---|---|---|---:|
| `PHeapAt.toTop` | H | HeapFree | 206.0 |
| `pvN_join` | S | ReallocPrevN | 26.1 |
| `mal_copy` | M | ReallocMal | 70.1 |
| `fl_exit` | L | FreeLarge | 143.9 |
| fresh `PHeapAt.coalPrev` | H | HeapFree | 129.9 |
| fresh `bb_top` | S | MallocTop | 22.7 |
| fresh `bw_scan` | M | MallocBlocks2 | 30.2 |
| fresh `realloc_grow` | L | ReallocGrow | 119.0 |

Primary baseline 446.1, fresh 401.8. Two of the four S cases are composition wrappers (the census
sample's 3/10).

## 4. Blind ontologists

Six agents (five seeded by random 256-character strings, one by a random dictionary sentence; the first
agent's seed reached it unexpanded and it was re-run with the real seed) got the semantics, the census,
the laws, the importable abstractions with use counts, the forbidden vocabulary, the decision-procedure
restrictions and the held-out statements verbatim (`~/syi-r9/fanout/brief.md`). Each returned five
candidates in 95–205 s.

| candidate | agents | rules = laws | recommended first by | decided by |
|---|---:|---|---:|---|
| F. footprinted views of the invariant: `PHeapAt ↔ ⋀ fields`, each field with a declared read set; one `transport_except`/`patch` rule; only fields whose read set meets the writes are re-proved (tiles, dynamic frames, lens-indexed fields, named cells + manifest, kind-indexed views with tagged writes, parish register) | 6/6 | L-heapframe (+ L-compose) | 4/6 (toTop ×3, coalPrev ×1) | read-set disjointness by literal comparison or list position; shape-indexed read sets do not reduce for symbolic `cs₁`, so stated as predicates (flagged by three) |
| D. relational address facts decided by closed computation: atoms + literal offsets, difference constraints / Allen relations / zones, reified and checked by a reflective DBM closure (Allen ledger, offset ledger, survey, anchored zones, apartness atoms + passes, Allen bonds) | 6/6 | L-loc, L-key | 2/6 (mal_copy) | `decide` on closed data; reification syntactic; non-difference terms (`2^(idx/4)`, masks, symbolic sizes) fall back (all flag `sym_run`'s unadopted geometry as the risk) |
| K. record footprints / modifies clauses (`Keeps K R R'`, effect signatures, kill/gen ledgers, invoices) | 6/6 | L-carry | 0/6 | `decide` on literal register lists |
| X. invariants with holes / excuse sets / defects; edits as composable patches | 5/6 | L-compose | 0/6 | enum lists by `decide` |
| W. wrap-free charts (`base + ofInt k`, no-wrap certificate) | 4/6 | L-key (BitVec) | 0/6 (front end of D) | syntactic literal recognition |
| one-offs: prefix-sum coordinates / top reservoir account (2), bin-ring zipper (1), compacted store-log journal (1) | | | | |

Theories cited: incremental view maintenance (Gupta & Mumick 1995), dynamic frames (Kassios 2006;
Smans, Jacobs & Piessens 2009), TBAA (Diwan, McKinley & Moss 1998), Burstall/Bornat component-as-array,
sheaves (Goguen 1992), DBMs (Dill 1989; Miné 2001), Allen's interval algebra (1983), Pratt's
separation theory, proof by reflection (Boutin 1997), Boogie expose/pack, ARIES, lenses (Foster et al.
2007), DPO rewriting, topological defects, LLVM `nuw`/`nsw`, gauge fixing, Torrens title, double-entry
bookkeeping, clearing houses.

## 5. Retrieval by law

All candidates are **known**:

* F: dynamic frames (Kassios, FM 2006) and incremental view maintenance; in this project the
  full-agreement case is `transport_read` (`AgreeP (vsaRead H)`), and round 1's permits were the
  same idea for a fixed base.
* D: difference-bound matrices (Miné 2001), reflection (Boutin 1997); in this project `sym_run`'s
  `obCheck` decides obligations over a per-atom interval geometry (`Geom`), 0 uses here.
* K: modifies clauses / effect systems; in this project `carry_close` (round 8), 0 uses here.
* X: Boogie's expose/pack, DPO rewriting; the edit lemmas already compose partly.
* W: wrapped intervals; `rgn_arith`/`key_sub` handle negative offsets today.

## 6. Variation

The ideonomy draw was tree-finding and negation, organised as a periodic grid, with the prompts
complexity, size and connectivity. The grid's rows are how much new vocabulary a candidate adds: 0 is
existing terms only, 1 is lemmas or tactics over existing terms, 2 is a new predicate, 3 is a new
datatype with a bridge, 4 is reflection. Its columns are the granularity the rule acts at: one side
goal, one edit or path, one field group or record, the whole invariant.

```
            | side goal                 | edit / path                 | field group / record          | whole invariant
------------+---------------------------+-----------------------------+-------------------------------+------------------------
0 existing  | omega over local facts    | carry_close reach (0 uses)  | transport_read (full agree)   | -
1 lemmas    | packaged geometry facts   | transport_except over       | field-group keep lemmas       | -
            | closed by lemma, win_key  | HeapAt fields (P2a)         | (globals / rings / prefix)    |
2 predicate | Apart atom (o5)           | Keeps K R R' (K, empty)     | invariant with holes (X)      | -
3 datatype  | -                         | patch category (X)          | record footprints (K)         | views + bridge (F, P1)
4 reflection| DBM / zone checker (D,P3) | -                           | -                             | reflective views (none)
```

Tree-finding moved F up one level: "a field's read set" sits below "a field group's read set". The
groups (globals, bin rings, walk prefix, top) are siblings at the level where the edits differ. That
gives the empty cell at row 1: keep lemmas per group over existing fields, with no view datatype.
Negation of "omega decides the side goal" gave three cells: decide it by `decide` on literal keys
(`win_key`, exists elsewhere), by a reflective checker (D), or by never putting the facts in the
context and applying the packaged region fact (row 1). Negating "the proof states every field" gave
the holes/excuse-set row, which no pilot takes (no held-out case composes edits except fresh
`coalPrev`).

Pilots (worktrees from f83224e1):

* P1 (row 3, 6/6, 4/6 first): footprinted views of the invariant with one `transport_except` rule.
* P2 (the meet, rows 0–1): except-window transport as lemmas over the existing `HeapAt` fields;
  `carry_close`/`region_close` made to reach the path cases; a local decision for side goals over
  existing terms.
* P3 (row 4, 6/6, 2/6 first): a reflective difference-constraint checker for address side goals.

## 7. Bake-off (primary cases; one measurement script on every branch)

Pilot branches start from f83224e1: P1 `exp-R9-P1` 9e887bb0, P2 `exp-R9-P2` 5ea57596, P3 `exp-R9-P3`
4487f40d. Case cost by `~/syi-r9/meas/meas.py`; failed compiles of the case's module in brackets.

| case | incumbent | P1 views | P2 meet | P3 DBM checker |
|---|---:|---:|---:|---:|
| `PHeapAt.toTop` | 206.0 | **67.4** [3] | 81.2 [0] | 199.0 [0] |
| `pvN_join` | 26.1 | 26.1 (no lever) | 25.1 [0] | 26.1 (no side goals) |
| `mal_copy` | 70.1 | 70.1 (no lever) | 68.1 [0] | 70.0 [6] |
| `fl_exit` | 143.9 | 143.9 (no lever) | **123.2** [2] | 142.9 [1] |
| total | 446.1 | 307.5 (−31%) | **297.7 (−33%)** | 437.9 (−2%) |
| setup lines | — | 189 (R9Views) | 201 (R9Frame 105, R9Omega 70, R9Path 26) | 569 (R9Dbm) |

Single-file user CPU, min of 3, interleaved (`~/syi-r9/time/bake.sh`; load 11–14 on 32 cores):

| module | incumbent | P1 | P2 | P3 |
|---|---:|---:|---:|---:|
| HeapFree | 19.22 | 18.11 | 18.12 | 19.21 |
| ReallocPrevN | 20.72 | 20.43 | 21.14 | 20.56 |
| ReallocMal | 20.65 | 19.48 | 19.72 | 20.15 |
| FreeLarge | 6.03 | 5.92 | 5.96 | 5.88 |
| four touched modules | 66.62 | 63.94 (−4.0%) | 64.94 (−2.5%) | 65.80 (−1.2%) |
| layer modules | — | 1.42 | 2.22 | 2.82 |

Each pilot's findings:

- **P1 (views).** `VGlob`/`VTop`/`VWalk`/`VFree`/`VExt` with read sets stated as predicates, frame and
  carry lemmas, a bridge `pheap_iff_views`, and `PHeapAt.transport_except`. toTop 150 → 58
  declaration lines. Limits: the rule needs `bins` and `brkv` unchanged and the same free chunks; the
  walk view is all or nothing (an edit to one header rebuilds the walk by hand); bin heads are one band.
  Nothing for the path cases.
- **P2 (meet).** The same carry as field-group lemmas over the existing `HeapAt` fields (`keep_globals`,
  `keep_hdr`, `keep_free`, `drop_inuse`, window agreement as an arbitrary predicate), no datatype:
  toTop 150 → 62. `carry_close` reached the three path cases for 1–2 lines each (they were already
  tight). fl_exit's 20 lines came from packaged geometry: `NodeK` plus one new fact (`NodeK.end_sep`)
  replaced a chain of three helpers. `omega_near` (local-context `omega` with fallback) saved kernel
  time inside toTop (0.54 → 0.17 s for the declaration, most of it from the lemma split) and nothing
  at file level.
- **P3 (DBM).** A reflective difference-constraint checker with negative-cycle certificates found by
  Bellman–Ford in the tactic and re-walked by the kernel, a `wrap` term for 2^64 offsets, clause
  selection for disjunctive facts, fallback to `omega` over the collected facts. Per goal it halves
  kernel time on disjunctive goals (≈ 10 vs 21 ms) and cuts tactic time 5× (≈ 1 vs 6 ms); toTop's
  declaration 2,885 → 2,555 ms. Lines did not fall (47 of 51 `omega` calls in toTop became `dbm`, same
  line count), the stack facts stay because `rgn_run`/`rgn_side` call `omega` internally (Region.lean),
  and file CPU did not move. 8 failed layer compiles (kernel deep recursion unfolding BitVec atoms
  until atoms and hypotheses were abstracted; CNF blow-up on a four-way disjunction).

The time law did not produce a time win at file level for any pilot. The census was right that
`omega` is about half the CPU, but most of those calls are made inside the step and region tactics and
in the edit lemmas' internal arguments, not in the side goals a held-out case writes; replacing the
written ones changes a file by 1–5%.

## 7b. Fresh cases (the forecast, E33)

H (fresh `PHeapAt.coalPrev`) ran on P1 and P2 (the two heap contenders); the path cases on P2 only
(P3 failed the primary measure on lines, −2%, with 569 setup lines, and did not win time).

| case | incumbent | P1 | P2 | what did the work |
|---|---:|---:|---:|---|
| `PHeapAt.coalPrev` | 129.9 | 119.2 [3] | 112.9 [5] (incl. a 2-line local macro) | **neither layer applies**: coalPrev composes `take` and `absorb`, which rebuild the invariant themselves. P1's saving is an existing helper (`PHeapAt.unlink`), P2's is cleanup plus a local read-after-write macro |
| `bb_top` | 22.7 | — | 22.7 | term-mode composition, no lever |
| `bw_scan` | 30.2 | — | 30.2 | composition; `omega_near` tried, no change |
| `realloc_grow` | 119.0 | — | 113.0 [0] | `carry_close` (3 readback blocks); +3.9% CPU, in bound; `omega_near` cost +0.6 s (fallbacks on `False` goals) and was reverted |
| total | 301.8 | | 278.8 (−7.6%) | layer-attributable: −6 (2%) |

Of the 13 heap edits, 10 rebuild `HeapAt` directly (2,940 lines) and 3 compose other edits (splitFree,
coalNext, coalPrev). The draw put a rebuild edit in the primary set and a composition in the fresh one.
Among the rebuilders, release, take, absorb, carve and moveBinAt relink bins, which both heap layers
exclude (`transport_except` and `keep_free` need the free chunks and bins unchanged); the top family
(toTop, setTop, topResize, topSplit, cut) is where either layer applies in full.

## 8. Decision

**Adopted: C = P2 without `omega_near`**, consolidated in 923a8ac1 on `exp-R9-C`:

* `VsaIris/Vsa/HeapWin.lean` (was R9Frame, 105 lines): the heap frame law as field-group lemmas
  over the existing `HeapAt` fields;
* round 8's `carry_close` made to reach the allocator (an import; no Carry change);
* `NodeK.end_sep` (moved into Region.lean, 8 lines): packaged geometry instead of preludes;
* `omega_near` and `rgn_arith_near` dropped (no file-level gain, fallback penalty on `False` goals and
  long fact chains; the fl_exit/HeapFree/ReallocMal call sites went back to `omega`/`rgn_arith`, full
  build green).

Reasons, by the measures fixed in §0:

* **Primary**: P2 297.7 vs P1 307.5 (P1 wins the heap case by 14 lines, P2 the path cases by 23);
  P3 437.9.
* **Lowest total on the heap cluster** (setup + primary + fresh, layer lines only): P1 189 + 67.4 +
  129.9 = 386; P2's heap part 105 + 81.2 + 129.9 = 316. P1's 14-line per-case advantage pays back its
  84 extra setup lines after six more top-family edits; four remain (setTop, topResize, topSplit, cut).
  The meet won on setup for the fifth round in a row (E25, E32, E41, E47).
* **Time**: no pilot cut touched-module CPU by 15%; all were within the bound. The tie-break did not
  apply.
* **Forecast**: fresh −7.6%, of which 2% is the layer. The adopted route is a modest one; the round's
  main yield is the measurement of where the cost is (§7, §10).

**Not adopted.**
* P1 views (6/6, 4/6 first): the better heap rule per case, but a datatype and bridge whose rule only
  fires when bins and free chunks are unchanged; on the remaining top-family edits it does not repay
  its setup against the meet.
* P3 DBM checker (6/6): halves per-goal kernel time on disjunctive goals but leaves the lines and the
  file CPU unchanged, because the `omega` calls that cost the time are inside `rgn_run`/`rgn_side` and
  the edit lemmas; 569 setup lines.
* `omega_near`: see above.

## 9. Rollout

On `exp-R9-C` (from exp-R9 + the P2 branch + the consolidation 923a8ac1): six agents worked on
disjoint files in one shared worktree, with one build lock, path-scoped commits and a per-file +10%
CPU bound. Merged into `exp-R9` as ea063bd8. Brief: `~/syi-r9/rollout-brief.md`.

| agent | files | non-blank lines | CPU (single file) | what did the work |
|---|---|---|---|---|
| A1 heap top family (owned HeapWin) | HeapRealloc, HeapGrow, HeapSplit, HeapWin | 976 → 714 | HeapRealloc 6.17 → 3.86, HeapGrow 1.75 → 1.15, HeapSplit 2.61 → 1.36 | setTop 179 → 91, cut 211 → 145, topResize 111 → 54, topSplit 158 → 82; HeapWin gained `volGlobal`, `keep_stable` (edits that change brk), `keep_freeV`, `free_mid`, `HeapAt.free_to`, `win_g` |
| A2 heap bins family | HeapFree, HeapMoveAt, HeapTake, HeapCarve, HeapClear + new HeapRead | 2,911 → 2,457 (incl. HeapRead 209) | HeapFree 18.5 → 14.3, HeapMoveAt 5.3 → 3.0, HeapTake 10.2 → 9.4 | take 385 → 240, moveBinAt 426 → 227, release 537 → 389, absorb 201 → 152, carve 314 → 264, splitFree 192 → 176, coalNext 125 → 110. The relinking counterparts of the pilot's lemmas, below HeapTake: `keep_scal`, `keep_fd`/`keep_bk`, `binList_keep`/`_remove`/`_insert`, `nodes_ne`, `node_loc`, `pred_mem`/`succ_mem`, `seg_pairs`, `wl_rd` |
| A3 free paths | Free* | 3,213 → 3,111 | each ≤ +7.5% (FreeLarge) | readbacks folded into one fact `simp`; `carry_close` where it also removes a `toNat_ofNat` step; `keep3` |
| A4 malloc blocks | MallocBlocks, MallocBlocks2, MallocExtend, MallocLarge, MallocSplit | 2,037 → 1,907 | each ≤ +4.6% | `refine … <;> upd_norm [facts]`, `carry_close` where normalising is not enough, `keep4`/`keep6` |
| A5 malloc rest | MallocRebin(L), MallocPaths, MallocTop, MallocLR, MallocPro, MallocCtx, MallocRunAll, … | 2,385 → 2,262 | each ≤ +3% (Sbrk reverted at +11–14%) | `reg_close`/`reg_try` (simp + reducible `exact` over the facts), `carry_close` in MallocRebinL |
| A6 realloc paths | Realloc* | 3,665 → 3,598 | each ≤ +5.3% | `carry_close`/`carry_norm` only; ReallocMove reverted (kernel deep recursion with `BitVec.toNat_add` among the facts) |

Consolidation (coordinator): the three glue modules the path agents created independently (FreeGlue,
MallocGlue, MallocGlue2) were merged into `RegKeep.lean` (48 lines: `keep3/4/6`, `upd_norm`,
`reg_close`/`reg_try`); the gate's one target cluster (`oom cert`, 8 JalSite certificates of 9 lines)
became `:= jal_cert` with one 4-line term macro in JalSite.lean (also the 7 in H5Sites), CPU neutral.

The rollout went further than the fresh forecast on the heap cluster. The forecast said both heap
layers stop at edits that relink bins; the agent that owned the heap layer and the one migrating the
relinking edits wrote the relinking counterparts (bin-list keep/insert/remove under window agreement)
during the rollout, and all 13 edits were migrated. The path cluster matched its forecast (−2% to −9%
per file): the path proofs were already short after round 1, and `carry_close` costs 100–150 ms per
call against ≈ 10 ms for a fact `simp`, so most path agents used the cheaper form.

Layer defects found (next round's input):

1. `carry_close` is 10× slower than `simp only [upd_apply, …, facts]` per site and runs its closer
   twice before failing; `try carry_close` on a goal it cannot close is a CPU trap. It respells
   `s − K + k` off the stack (breaks later `rw`), matches facts syntactically (`Sail.BitVec.extractLsb`
   vs `BitVec.extractLsb`), does not see `List.getLast` (needs `List.getLast_singleton`), and a fact
   that rewrites a register breaks the normalised copy of another fact.
2. `omega` produced an ill-typed proof ("Application type mismatch … coeffs") instead of failing when
   the context held `q = top ∨ ∃ c ∈ chunks, c.addr = q` together with `%`/`/` atoms (twice; worked
   around by clearing the existential or using `node_loc`).
3. Facts passed as `by tac` inside a try/catch search: a failing `tac` logs an error and elaborates to
   `sorry`, so `exact` "succeeds" (`reg_close` compares error counts; `carry_close` is probably exposed).
4. `keep_globals`/`keep_free` hard-code the topAddr word; a version parameterised by the written global
   words would cover HeapClear's window too. The walk has no field-group lemma (still `ChunkWalk.extend`).
5. With an implicit register file in an anonymous constructor, `rfl` readbacks assign the wrong one.
6. The shared worktree broke repeatedly: uncommitted edits to shared modules failed other agents'
   builds and deleted oleans; three agents moved to private worktrees at the shared HEAD.

## 10. Measurements (451c6b8b → hand-off)

| measure | before | after |
|---|---:|---:|
| target modules, non-blank lines (72 → 75 modules, incl. 3 new layer modules, 400 lines) | 18,449 | 17,040 (−7.6%) |
| of which the heap-edit files (Heap* except HeapWin/HeapRead/HeapPermit) | 4,554 | 3,473 (−24%) |
| `git diff --shortstat 451c6b8b` over Vsa/ and VsaIris/ | | +1,053 / −2,437 |
| 13 heap edits, declaration lines (script population H) | 3,083 | 2,067 (−33%) |
| 155 path theorems, declaration lines (71 changed) | 6,846 | 6,381 (−6.8%) |
| held-out primary, declaration lines (toTop, pvN_join, mal_copy, fl_exit) | 256 | 165 |
| held-out fresh, declaration lines (coalPrev, bb_top, bw_scan, realloc_grow) | 200 | 175 |

Single-file user CPU (`LEAN_NUM_THREADS=1`, copies outside the repo, base and after interleaved per
file, min of 2, load 7–14; `~/syi-r9/time/fin_*`): **500.0 → 492.9 s (−1.4%)**, the three new layer
modules included (3.5 s). Heap files 59.0 → 49.4 s (−16%: HeapFree 20.0 → 14.8, HeapMoveAt 5.5 → 3.4,
HeapRealloc 5.7 → 4.1, HeapSplit 2.8 → 1.4, HeapGrow 1.7 → 1.2); FreePaths 50.2 → 48.4. Every
file within +10% except MallocRunAll (0.89 → 1.02 s); its old source measures 0.84 → 0.92 s on the new
tree too, so the +0.08–0.13 s is import loading, not the migrated unit. The relative bound is
meaningless below ~2 s; ReallocMal (+4.8%), ReallocTail (+5.3%), ReallocCtx (+5.3%) are the largest real
increases.

Full `lake build` (all default targets, executables included) is green at ea063bd8: 1,552 jobs, 0
errors. Axioms check (the 14-line file): 12 theorems `[propext, Classical.choice, Quot.sound]`, the two
WhileLogic adequacy theorems `[propext, Quot.sound]`. No `sorry`, `axiom`, `native_decide`,
`bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth` added (diff scan).

Statement check (type hash of every constant of the `Vsa*` modules, base = the cut commit 205acaac's
build, joined by name, auxiliary constants excluded): **0 changed types**, 2 gone (`grow_keep`,
`split_keep`, local helpers used only in their files), 56 new, 5 moved module unchanged in type
(`read64_keep`, `binAt_geo`, `BlockHeapAt.node_foot`, `HeapAt.member`, `HeapAt.bin_unique`, from
HeapTake to HeapRead). The reachability cut (205acaac) removed 30 dead declarations; none had an
outside user. None of the 197 target constants used outside the target changed or disappeared.

Gate re-run (`--root`, no baseline): 12 → 12 firing clusters. The one target cluster, `oom cert`, is
now 8 one-line units (9 → 1 lines each): flat at the floor, which the one-third rule cannot register
(E45); record it in the baseline as an automation floor. The other eleven are outside this target.

Calibration: primary −33% (P2), fresh −7.6% (layer-attributable −2%), rollout −7.6% of target lines
(−24% of the heap files, −2% to −9% of the path files) and −1.4% CPU. The fresh set predicted the
path cluster and under-predicted the heap cluster, because the heap rollout widened the layer's
precondition (E54, E55).

## 11. Where the cost is now, and round-10 targets

* **Time is in the tactics' own `omega` calls.** 8,344 executed `omega` calls over 1 ms against 3,484
  written: the step and region tactics (`rgn_run`/`rgn_side`/`sx_side`/`rgn_arith`, `<;> omega`) issue
  most of them, and `omega` is ~half the target's CPU. Case-level vocabulary did not move it (P3's
  checker halves the per-goal cost but only for the goals a proof writes). Target: the region search
  inside `rgn_run`/`rgn_side` decides membership with `omega` per candidate region (round 1's named
  cost); replace that decision (keys by `decide`, or P3's certificate checker inside the tactic).
* **Path glue** is near its floor for this encoding: `carry_close` loses to a fact `simp`; the residue
  is register restore over long `upd` chains with symbolic registers (Sbrk), bin-ring arguments, and
  the step/branch skeleton.
* **Heap**: the walk has no frame lemma (truncate/extend still by `ChunkWalk.extend`); `live`/`exact`
  are re-proved per edit; HeapClear's window fits neither global lemma.
* **Composition edits** (splitFree, coalNext, coalPrev) remain glue over `take`/`absorb` with
  read-after-write chains (`wl_rd` helps).
