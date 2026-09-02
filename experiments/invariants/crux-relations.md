# crux-relations.md — mined hCallClosure depth/budget relations + fuzz verdicts

> ANALYSIS ONLY (pre-proof mining; same category as the fuzzer + ELF harness).
> Nothing here enters a proof. DRAFTs for the proving agent; Law 4 applies.
> Closes the round-4 open item "driver call descent → the crux hCallClosure
> depth/budget relations (the falsity-#13 class)" — the earlier
> `hCallClosure.md` was generated with the call-OPAQUE spec driver (no depth
> descent); this run traces the machine crux span directly at increasing
> closure-call depth.

## Trace
- program: `/tmp/wl-test/tests/crux/clo_depth.wl` (closures capturing vars,
  nested closure calls, recursion to depth 4 — `make_adder`/`apply_twice`/
  `compose`/`countdown`).
- probe (scripts/gen_trace.py, multi-PC): `0x80003254` callDispatchPC (sp pre-frame),
  `0x8000329c` depth read/bump (`call_depth` word at `8(s2)`), `0x800032bc` env_new,
  `0x800032dc` env_define fold, `0x80003354` callBodyLoopPC (body handoff).
  probe regs sp,s2,a0,a3,s0 + mem window `s2:8:4` (the call_depth word).
- trace: `/tmp/rl-trace/cruxDepth_trace.jsonl` (80 events, call_depth 0..4).
- miner: `scripts/mine_crux_ladder.py` (closure-call extension of the stack-ladder
  miner).

## Mined-relation table (vs Vsa/While/StackNeed.lean + the crux)

| # | Mined relation | Mined value | Design constant | Verdict |
|---|---|---|---|---|
| R1 | per-closure-call sp descent (min positive) | 1088 | `evalFrame` 1088 | **MATCH** |
| R1 | pure-recursion per-level descent (constant) | 1264 | `evalFrame`+`execFrame` = 1264 | **MATCH** |
| R1 | nested-closure descent (compose/apply) | 2352 | 2·`evalFrame`+`execFrame` | **MATCH** (structural `max` over children) |
| R2 | max per-call-level consumption | 2352 | ≤ `perCallBudget` 6144 | **MATCH** (budget holds) |
| R3 | crux `d` = machine `call_depth` (8(s2)) | 0..4 | runtime counter (--call_depth on ret), NOT sp nesting | **MATCH** (see note) |
| R4 | demand ladder consumed(d) ≈ perLevel·d + base | 1264·d + 1175 | ladder, not constant | **MATCH** (falsity-#13 form) |
| R4 | constant-budget refutation depth | depth 1 (2208 > 2176) | old `stackOK` 2176 unsound | **falsity #13 REFOUND** |
| R5 | depth guard `d < maxCallDepth` | max d = 4 < 1000 | `maxCallDepth` 1000 | **MATCH** (guard holds) |
| R6 | env_new (fresh frame) per closure call | 14 / 14 | one `allocFrame` per call = `PhiExtends` +1 frame | **MATCH** |

Full ladder-vs-reservation arithmetic (design doc confirmed):
`maxCallDepth·perCallBudget = 6144000 = 5 MiB ≤ 8 MiB linker stack`
(`[0x87800000,0x88000000)`), leaving ~2 MiB for top-level nesting.

**No mismatches. No pre-proof falsity found on this run.** Every mined constant
agrees with StackNeed; the only "mismatch" the miner first flagged (R3) is the
EXPECTED counter-vs-sp divergence (recorded in observations.md
`crux-depth-counter-is-runtime-not-sp-nesting`), not a machine falsity.

## R3 note (design-relevant)
The machine `call_depth` counter is post-bump and decremented on return, so it
tracks the *currently-active* closure-call chain, not sp-static lexical nesting
(which also counts top-level `println` frames). The crux's spec `d`
(`a_3 : d < maxCallDepth`) IS this counter. Within a single recursion chain the
counter and the sp ladder move in lockstep (mined `countdown` d=0..4, per-descent
sp delta constant 1264). StackNeed already indexes the budget by `d`
(`(maxCallDepth − d)·perCallBudget`), so the design is right — index by the
counter, not an sp reconstruction.

## Real-crux-input validation (against the in-tree statements)
- `Vsa.Sim.BodyGhostTie` — inhabited by the identity handoff `⟨rfl,rfl,rfl⟩`
  AND non-vacuous (a distinct-ghost mutant disagreeing on `sp` is refutable):
  correctly stated (`/tmp/crux_real_probe.lean`, axiom-clean).
- `Vsa.Alloc.StackOK.child` (the crux's real budget-ladder step) — carries the
  mined per-descent eval frame **1088** through the `(maxCallDepth − d)·perCallBudget`
  headroom ladder for all `d < maxCallDepth`, machine-checked axiom-clean
  (`/tmp/crux_budget_probe.lean`, axioms ⊆ {propext, Quot.sound}). The mined
  per-level demand (1264 < perCallBudget 6144) composes soundly through it.

## Fuzz verdicts (candidate .lean below, `statement_fuzz.py --file --struct`)
All axiom-free; CTI loop live (each mined candidate SURVIVED, each mutant REFUTED):

| candidate (struct) | verdict | mutant | verdict |
|---|---|---|---|
| `minedRecur` (PerCallBudgetOK 1264) | SURVIVED | `budgetMutant` (>6144) | REFUTED |
| `minedNest` (PerCallBudgetOK 2352) | SURVIVED | — | — |
| `minedLadder` (DepthLadderOK 1264 1175) | SURVIVED | `constMutant` (constant budget) | REFUTED |
| `minedFrameGrowth` (FrameGrowthOK 14 14) | SURVIVED | `frameMutant` (13≠14) | REFUTED |

## Candidate Lean structures
Hermetic, fuzzed: `experiments/invariants/crux_relations.lean` (elaborates
standalone; `PerCallBudgetOK`/`DepthLadderOK`/`FrameGrowthOK` mirror the crux's
budget obligations with the mined constants). These SEED — the real proof uses
`StackNeed.StackOK.child` (validated above) + `CallClosureGeom`/`BodyHandoff`;
the mined structures certify the constants those consume.

## Artifacts
- trace: `/tmp/rl-trace/cruxDepth_trace.jsonl`
- program: `/tmp/wl-test/tests/crux/clo_depth.wl`
- miner: `scripts/mine_crux_ladder.py`
- candidates: `experiments/invariants/crux_relations.lean`
- real-input probes: `/tmp/crux_real_probe.lean`, `/tmp/crux_budget_probe.lean`
