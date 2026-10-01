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
