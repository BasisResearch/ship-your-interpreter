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

(pending)

## 7. Decision

(pending)
