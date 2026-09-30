# Abstraction-discovery round 1 (2026-09-30)

Trigger: the abstraction gate (`scripts/abstraction_gate.py`, PR #12) fires on
branch `exponentiate` (57 stalled name clusters with no baseline), and the
runtime-library path proofs keep getting more expensive per case.

## 1. Obligation census

Tools: `abstraction_gate.py --report` (name clusters) plus a census by
conclusion predicate over hand-written units (theorem/lemma/`#ix_seg`/
`#ix_piece`), with generated tables excluded. History order is the time git
added each unit's file.

| cluster (conclusion) | units | lines | files | mean cost, first → last quarter | trend |
|---|---:|---:|---:|---|---|
| `#ix_seg`/`#ix_piece` machine runs (interpreter) | 530 | 7,951 | 75 | 29.9 → 9.3 | falling (the `ix_run` driver works) |
| allocator paths `AW …` (Malloc*/Free*/Realloc*) | 149 | 10,151 | 39 | 53.9 → 84.7 | **rising** |
| snprintf paths `SnpW …` | 77 | 3,073 | 10 | 40.1 → 49.0 | **rising** |
| stdout paths `SWPO …` | 66 | 2,557 | 36 | 24.9 → 48.9 | **rising** |
| generic runs `SWP …` | 31 | 1,107 | 12 | 27.6 → 52.1 | **rising** |
| interpreter runs `IW …` (hand) | 17 | 638 | 9 | 25.0 → 38.2 | **rising** |
| exit paths `NW …` | 9 | 462 | 2 | 25.0 → 69.0 | **rising** |

Name clusters the gate reports that other lanes are already removing (per-pc
step tables `it_/st_/nt_/jalx`, byte pins `*_at_`, 12–39k lines each) are not
targets of this round.

**Target: runtime-library path proofs**, about 350 units and 17k lines, rising
cost. Representative instances:

- `free_nt` (VsaIris/Vsa/FreePaths.lean:36): per instruction `refine st_<pc> O.live ?_ ?_ ?_`; then `rw [hEn]; unfold StOK tohostAddr; omega` (address in range); `simp only [upd_apply, ite_true]` (register file); `rw [read64_store_miss _ _ (by omega)]` (read over write); `exact O.foot hnnF` (footprint); at the end a 25-line `refine hk … ⟨(D.frame.store (by omega)).of_regs …, Hp.disj, frame_store (win_foot hnf) Hp.frame, ?_ …⟩ <;> simp only [upd_apply …]` rebuilding every post field.
- `lr_split_ret` (VsaIris/Vsa/MallocSplit.lean): eight nested `writeLog` stores matched by hand against the chunk-walk invariant `PHeapAt`, with per-address footprint arithmetic.

Obligation shapes inside the cluster (from the shape census, `~/syi-exp-logs/round1/census.txt`):
(a) one instruction step; (b) address inside the owned window and off the mailbox; (c) a load reading through earlier stores; (d) the chunk-walk heap shape after header/footer/link writes; (e) every other post field preserved; (f) register-file bookkeeping; (g) spilled callee-saved words restored.

## 2. Laws

| law | statement | check |
|---|---|---|
| L1 step | executing the decoded instruction at pc maps a symbolic state to its successor by the instruction's semantics | proved once: `symRun_swp` (VsaIris/Vsa/SymExec.lean) |
| L2 read-over-write | a load disjoint from every logged store returns the prior value; a load inside one store returns its bytes | proved: `ldv_store_miss`/`ldv_store_hit`, `read64_store_miss` |
| L3 tiling | every address `c.addr + k` with `k < c.size` for a chunk `c` of the heap walk lies in the arena, off the stack, the statics and the mailbox; distinct chunks are disjoint | true of `HeapAt`'s walk (`walk.chunk_bounds`, arena bounds); not stated as one law |
| L4 heap edits | the header/footer/link write sequences of unlink, link, split, merge, reheader map `HeapAt h` to `HeapAt (op h)` | proved per operation: `links_unlink`, `links_link`, `walk_reheader`, `splitFree`, `reflag` (VsaIris/Vsa/Heap*.lean) |
| L5 frame | a post field whose footprint misses the written region is unchanged | proved per field kind: `frame_store`, `StableUnder`, `FrameMeta` |
| L6 callee-saved | a register stored in the prologue and loaded in the epilogue from the same slot is restored | instance of L2 on the stack slot |

Finding: every law is already a lemma. The cost is in *applying* them: each
path proof re-establishes L2, L3 and L5 by hand at every instruction and at the
exit. The cluster needs a vocabulary in which L2–L6 fire automatically.

## 3. Blind ontologist fan-out

Six blind agents (4 random-string seeds, 2 random-word seeds) read only the brief
(`~/syi-exp-logs/round1/BRIEF.md`: machine semantics, dlmalloc/newlib contracts,
the census, the laws, forbidden vocabulary = the current encoding's primitives:
per-pc step lemmas, symbolic executor/state, write logs, path trees, obligation
lists, interval environments, `omega`, WP over machine states). Raw candidates:
`~/syi-exp-logs/round1/ontologists_all.md` (24 candidates). Clustered by mechanism:

| cluster | law(s) | agents | members |
|---|---|---:|---|
| **K. Region-keyed addresses**: every address is `region ⊕ offset` (chart / capability / dimension / torsor / parcel); regions minted once from the heap invariant, the prologue, arguments; disjointness = distinct region names; in-window = offset + width ≤ extent | L3, (b) | 6/6 | o1-D Dimensioned addresses, o2-2 Ghost capabilities, o3-2 Atlas, o4-2 Dimensioned addresses, o5-4 Tidal torsors, o6-1 Charted addresses |
| **T. Title register / lenses / commutation**: memory seen as a finite map from (region, field) keys to value terms; read-over-write = key lookup; frame = key-set disjointness; path summarised by its changed-key set, not its history | L2, L5, (c), (e) | 6/6 | o1-B, o2-3 Lens algebra, o3-1 Trace normalisation, o3-4 Constant-complement views, o4-3 Trace commutation, o5-1 Torrens cadastre, o6-4 Torrens register |
| **S. Heap surgery vocabulary**: invariant as locally checkable sections glued globally; each dlmalloc edit is one rule (split/merge/unlink/link/reheader/extend/trim) with interface; a path names its edit word; "free = binned" carried as a conserved charge | L4, (d) | 6/6 | o1-C Wang tiling, o2-4 Edit grammar, o3-3 Materialised view deltas, o4-4 Strand splicing, o5-2 Surgical gluing, o6-2 Euler operators |
| **B. Bracket / catalyst frames**: prologue spills and epilogue reloads cancel as matched brackets when the body's slot footprint misses the slots; callee contracts are cancelled brackets | L6, (f), (g) | 5/6 | o1-A, o2-1 Echo frames, o4-1 Mirror brackets, o5-3 File-card discourse, o6-3 Catalytic registers |

Convergence without access to the code or to each other is the strongest signal of
the round; the one-offs worth keeping are o6-2's "unlink/link = multiplication of
the fd permutation by a transposition, so bk is free" and o5-2's "free = binned as
a conserved charge".

## 4. Retrieval by law

| cluster | law phrasing searched | known theory (citation) | status here |
|---|---|---|---|
| K | "block-offset pointers; distinct allocations never alias" | CompCert memory model: values `Vptr b ofs`, blocks disjoint by construction (Leroy & Blazy, JAR 41(1), 2008); provenance (Memarian et al., POPL 2019); units of measure (Kennedy, POPL 1997) | **known**; not used here — the machine layer reasons over flat `Nat` addresses with per-access linear arithmetic |
| T | "read-over-write axioms by location; component-as-array" | McCarthy's theory of arrays (select/store); Burstall 1972 / Bornat 2000 component-as-array; lenses (Foster et al., TOPLAS 2007) | **known**; partially present (store forwarding by syntactic address equality in the executor) |
| S | "invariant preservation per rewrite rule with interface" | DPO graph rewriting (Ehrig et al., 1973); correctness relative to nested conditions (Habel & Pennemann, MSCS 2009) | **known**; the per-operation lemmas exist (Heap*.lean) but are applied by hand per path |
| B | "callee-save preservation; compute–uncompute" | CompCert callee-save invariants; Bennett 1973; variables as resource (Bornat, Calcagno & Yang, MFPS 2005) | **known** |

Recognition, not invention, is the result: K+T together are a block-offset,
key-addressed memory view layered over the flat machine memory. Nothing in round 1
is novel as theory; the novel element is the combination as the symbolic state of a
reflective executor (keys are `(region atom, literal offset)`, so forwarding and
framing are decided by key equality inside `decide`).

## 5. Variation

`/ideonomy` draw: substitution × cross-domain re-instantiation, spectrum organon,
prompts size / rate / predictability, applied to K+T and S. Survivors added to the pool:

- **V1 boot-time static region table.** Text, statics, the bin array, FILE structs, the malloc state and the mailbox never move during the run; key them once against the image (one check), so every constant-address and gp-relative access is a table lookup.
- **V2 per-call-depth frame regions.** Each call gets a fresh frame region; caller slots are untouched by construction.
- **V3 micro-surgery.** Each heap store carries its local section check; the end-of-path heap proof is a fold over already-checked sections.
- **V4 permits.** Surgery descriptors are data (byte-write pattern + interface); a path proof is a permit list confirmed by one `decide` against the path's stores (the recognizer of fan-out idea "heap-edit recognizer").
- **V5 two-level keys.** Field key = (chunk key, offset): framing reads the chunk component, forwarding reads both.

Rejected variant (informative): sampling or fuzzing the heap is a law check only, never a proof route.

## 6. Pilot bake-off

Held-out suite (no unproved cases exist, so: re-proofs to identical statements, fixed before
any candidate was built): `free_nt` (FreePaths), `lr_split_ret` (MallocSplit), `realloc_next`
(ReallocNext). Incumbent = the landed proofs. CPU = user time of `lake env lean <file>`,
4 threads, min of two runs.

### Candidate SP — surgery permits (S + V4 + V3), worktree syi-expF, commits 257089fd, 1ef64b84

Setup: `VsaIris/Vsa/HeapPermit.lean`, 270 non-blank lines (237 new): sections `ChunkSec`/
`FreeSec`/`NodeSec` read off `BlockHeapAt`; per-store window check `wl_win`; permits
`split_permit`/`unlink_permit`/`absorb_permit` wrapping `splitFree`/`unlink`/`absorb`; `rd_log`.

| case | proof lines | module CPU | failed compiles | what did the work |
|---|---|---|---:|---|
| `free_nt` | 82 → 58 (−29%) | 54.4 → 53.2 s | 0 | sections only (no heap edit on this path) |
| `lr_split_ret` | 68 → 23 (−66%) | 20.7 → 20.3 s | 6 | split permit, `wl_win`, `rd_log` |
| `realloc_next` | 110 → 75 (−32%) | 8.13 → 8.03 s | 1 | sections only |
| `next_absorb` (refactor) | 151 → 108 (−28%) | same module | 5 | unlink + absorb permits |

Net lines: three modules 2406 → 2230, plus 270 setup = +94 (breaks even after 2–3 more paths).
Statements identical (`type_of%` check); axioms standard.
Findings: permits win only where a path ends in a heap edit; V4 "one `decide` against the
store list" is not achievable with symbolic addresses (one `omega` per store and read instead);
composition of permit words untested (all words have length 1–2); the sections are really
law L3 and overlap cluster K; the residue in `free_nt`/`realloc_next` is stepping, address
normalisation, footprint side goals and register-field rebuilds (cluster K/T territory).
CPU unchanged. Verdict for SP alone: shrinks the edit-ending proofs, does not bend the
cluster's cost curve; keep as a small layer under a K/T winner.

### Candidate KT — region-keyed memory (K + T + V1 + V5), worktree syi-expE, commit 6bc1cfad

Setup: `VsaIris/Vsa/Region.lean`, 389 non-blank lines (≈200 lemmas, 186 tactic): regions `Rgn P base ext`
minted from the chunk walk (`PHeapAt.chunkK/.freeSpan/.next/.nodeK`), the static table (`globRgn`, `binRgn`)
and the stack window; laws once: `Rgn.ldOK/.stOK`, `Rgn.offStack`, `frame_log`/`pres_log` over a whole store
log as a key list; two-level keys via `rgn_key`; drivers `rgn_run`, `rgn_side` (hooked into `sx_side`).
Integrated in the `st_`/`sx_run` route (the executor's `Geom` cannot separate two heap chunks yet).

| case | proof lines | theorem CPU | module CPU | iterations |
|---|---|---|---|---:|
| `free_nt` | 88 → 41 (−53%) | 0.86 → 1.59 s (1.85×) | 50.6 → 50.8 s | 3 |
| `lr_split_ret` | 78 → 34 (−56%) | 5.85 → 4.73 s (0.81×) | 18.6 → 17.1 s | 7 |
| `realloc_next` | 115 → 42 (−63%; 108 → 42 without 7 dead lines) | 1.92 → 3.08 s (1.6×) | 7.37 → 8.80 s | 2 |

Net lines: −163 in the three theorems against 389 setup (breaks even after ~5 more paths).
Findings: the law-level part wins on both measures (`frame_log (by log_in)` replaces the 8-deep
`frame_store` chain and nine read goals in `lr_split_ret`); the per-access region lookup is a search
(one `omega` per candidate region; `realloc_next` 29 → 48 `omega` calls), which is the CPU loss;
post-field assembly and the heap-edit calls did not shrink (clusters S and B). Proposed fix: decide
region membership by key equality inside the reflective checker (symbolic per-atom extents and a
disjoint-atom table in `Geom`).

### Reading of the two pilots

| | lines on held-out | CPU on held-out | setup | covers |
|---|---|---|---:|---|
| incumbent | 0 | 0 | 0 | — |
| SP | −29 / −66 / −32% | neutral | 270 | (d) heap edit, partly (c) |
| KT | −53 / −56 / −63% | +85% / −19% / +60% per theorem (≈ +1 s each) | 389 | (b) (c) (e) |

Neither candidate alone satisfies the rule "cheaper on held-out cases and the refactors shrink" on
every measure: SP does not bend the curve (most lines are stepping and address work), KT pays its
line savings with search time. They cover disjoint obligations, and both agents report the same
residue for the other. No adoption yet.

### Combined candidate KT∘SP (second bake-off iteration)

Build: merge exp-F into exp-E; per-path route = `rgn_run` stepping, `frame_log`/`log_in` frames,
sections + permits for the heap edit. Fresh held-out cases (not touched by either pilot):
`free_b2nl` (FreePaths), `mal_merge` (ReallocMal), `pvN_inline` (ReallocPrevN). Same measurements.

Worktree syi-expE, commits 7573a4df (merge of the two pilots into one layer) and 63648c7d.
3 threads, interleaved, min of 3, quiet machine.

Fresh cases (baseline = the merge commit, no case-specific abstraction allowed):

| case | theorem lines | theorem CPU | module CPU | failed compiles |
|---|---|---|---|---:|
| `free_b2nl` | 125 → 80 (−36%) | 2.88 → 2.96 s (1.03×) | 39.2 → 39.6 s | 1 |
| `mal_merge` | 89 → 50 (−44%) | 1.16 → 1.87 s (1.61×) | 15.3 → 16.3 s | 1 |
| `pvN_inline` | 168 → 35 (−79%) | 3.59 → 3.39 s (0.94×) | 17.9 → 17.8 s | 2 |

Original three on the combined layer (baseline = pre-pilot):

| case | theorem lines | theorem CPU | module CPU |
|---|---|---|---|
| `free_nt` | 88 → 41 (−53%) | 0.79 → 1.46 s (1.85×) | 40.0 → 39.6 s (approximate) |
| `lr_split_ret` | 78 → 30 (−62%) | 4.90 → 4.50 s (0.92×) | 13.4 → 13.2 s |
| `realloc_next` | 115 → 40 (−65%) | 1.29 → 2.50 s (1.94×) | 5.39 → 7.48 s |

Setup (non-blank lines): KT 389 + SP 270 = 659 separately; 539 after merging (SP's sections became
KT's regions); +84 marginal for the fresh cases (negative literal offsets `key_sub`, context-free
access regions `ARgn`, `rgn_step`, kernel-safe keys, two local lemmas); 623 now. The fresh cases
removed 217 theorem lines against those 84.

Defects the fresh cases exposed in the layer (all fixed): a kernel hang on negative offsets
(`BitVec.toNat_add` is an `rfl` lemma, so the kernel unfolded `Nat.mod` on a 2^64-sized literal);
a failed `omega` under `first … <;>` that was logged but let the macro continue; register-update
nesting on paths of seven or more instructions.

Residual cost: the per-access region search (one key normalisation plus one `omega` per candidate)
makes 4–5-instruction paths 1.6–1.9× slower per theorem (+0.7 to +1.2 s); longer paths are neutral
or faster.

## 7. Decision

**Adopted for the allocator path cluster: the combined layer** (`VsaIris/Vsa/Region.lean` with
`VsaIris/Vsa/HeapPermit.lean`): regions minted from the chunk walk, the static table and the stack
window; `rgn_run`/`rgn_side` for access obligations; `frame_log`/`log_in` for frames over a whole
store log; heap permits (`split_permit`, `unlink_permit`, `absorb_permit`) for the edit at the end
of a path.

Measured on six held-out proofs: 663 → 276 theorem lines (−58%), module CPU within ±6% on five
of six modules (+39% on the smallest, `ReallocNext`), 1–2 failed compiles per fresh case, and the
marginal setup for three fresh cases was 84 lines. The rule "held-out cases get cheaper and the
refactors shrink" holds for lines, attempts and refactors; it does not hold for per-theorem CPU on
short paths, which is recorded as the layer's known cost and is the first target of round 2.

Required route (to be written into CLAUDE.md and the discipline rules when this branch reaches a
tree that carries them; the gate is PR #12):

| task shape | use |
|---|---|
| allocator path: access inside a chunk / bin node / static / stack slot | mint the region once (`PHeapAt.chunkK`, `.freeSpan`, `.nodeK`, `globRgn`, `binRgn`) and step with `rgn_run`; never `rw [hE…]; unfold StOK/LdOK tohostAddr; omega` per access |
| frame or presence of a post field across the path's stores | `frame_log (by log_in)` / `pres_log`; never a `frame_store` chain |
| heap invariant after split / unlink / absorb | the permit; never a hand match of nested `writeLog` against `PHeapAt` |

Proposed rule R17 (scope `VsaIris/Vsa/{Malloc,Free,Realloc}*.lean`, new or edited proofs):
`unfold (StOK|LdOK) .*tohostAddr; omega` or `frame_store \(` more than twice in one proof.

Not adopted: SP alone (does not bend the curve), KT's tactic search as the final form (round 2
replaces the search by key equality decided inside the reflective checker). Offered, not adopted:
the language layer `Vsa/Lang` (ship-your-ocaml's own bake-off tied at 2+2 lines; it pays with two
or more language instances).

Remaining migration: ~143 allocator path proofs (`AW`), then the snprintf/stdout/exit path
clusters, which need regions for FILE structs and buffers (static table V1) and have no heap edits.

## Round 2 targets (from this round's residue)

1. Region membership by key equality inside `obCheck` (symbolic per-atom extents, disjoint-atom
   table), so stepping on the reflective executor costs no search.
2. Callee-saved frames and post-field assembly (cluster B): brackets/catalysts on the executor's
   forwarded spills.
3. The name gate misses obligation clusters with distinct names; cluster by conclusion head.
