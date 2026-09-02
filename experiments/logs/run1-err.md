# run1 — err lane: the 42 `hsite_*` reachability residuals

Clone `/tmp/vsa-err-lane`, HEAD 2865529 (Wave 46). Mission: discharge as many of
the 42 per-error-site `hsite_*` residuals (feeding `errFamily_ofShared`) as
tractable; name the rest with machine-checked obstruction.

## Finding: the 42 hsites are ALREADY fully routed (landed before this lane)

The error-routing scaffold is COMPLETE and green in the clone:

- `errFamily_ofShared` (TermAssembly.lean:446) demands 44 premises: 42 `ReachJal`
  residuals + 2 non-`jal` passthroughs (`hBadClosure`/`hTopAbrupt`).
- All 42 `ReachJal` residuals are discharged by `errFamilyClosed` → the 19
  `errSite_<pc>` rows via the per-premise `route_h*` (`rows/ErrorRouting.lean`),
  each reducing to a `ReachJal … c` residual (the corrected, INHABITABLE shape;
  the old `∀c, JalErrPre` universal was refuted, `jalErrPre_forall_false`).
- Each `ReachJal` residual is in turn served by `<premise>_hsite_of_armBranch`
  (`rows/ErrSpillRows.lean` 16 Family-A, `rows/ErrSetupRows.lean` 26 Family-B),
  which composes `reachJal_of_armBranch` with a LANDED seg bridge
  `spill*_toJalErr` / `setup*_toJalErr` (`#derive_case` + `spillSeg_toJalErr` /
  `spillSetupSeg_toJalErr`, all axiom-clean).
- The whole feed is assembled once in `errFamily_ofArmLinks` / `errFamily_ofWork`
  (`rows/ErrFamilyAssembly.lean`, VERIFIED axiom-clean this lane).

So the residual per site is NOT the routing, the jal seam, or the setup-prefix
seg — those are all proved. It is exactly the collector field:

```
link_h* : <spec-error context> → SpillArmPre S m0 L lds <seg> pc0 pcJal … c   (Family A)
        | <spec-error context> → SetupArmPre S m0 L lds <seg> pc0 pcJal … c   (Family B)
```

`SpillArmPre`/`SetupArmPre` are the block-ENTRY predicates: they force `c` to be
parked EXACTLY at `pc0` (the block just before the jal) with full geometry
(`GoodState`, `mem = m0`, `PC = pc0`, `GHolds L`, `ChainFacts`, `x10 = inp`, the
`NotWrittenJmp` ghost frame, code loaded). Discharging one = proving the machine
RUNS to `pc0` under the premise's spec-error derivation — the deep eval/exec
recursion reachability into that error branch (the M4 arm-sim error edge).

## Obstruction (machine-checked): no landed span reaches any `pc0`

Every `link_h*` field is open. Verified: no M4 arm-sim pins any error-branch edge
(`0x800034c0→0x800034d0` for hNegType, etc.). `EvalNegSim` etc. model the SUCCESS
path (value IS an int); the error branch (value not an int → jal runtime_error)
is not threaded to a reachability. `grep` for the block-entry PCs finds only
byte-load/decode lemmas (`eval_expr_at_800034d0`), not reachability spans. This
matches the ledger `errlink-forall-shape-obstruction` and the `ErrorReachInhab`
doc note.

## LANDED this lane — `Vsa/Sim/rows/ErrReachSpan.lean` (green, axiom-clean)

The mission's requested combinator: `reachJal_of_span`. Currently
`reachJal_of_armBranch` only inhabits `ReachJal … c` when `c` is ALREADY at `pc0`
(`span := identity`). An M4 arm-sim error edge will instead land a NON-trivial
span `Triple SpanPre (SpillArmPre …)` (precondition = a real reachable entry,
post = the block-entry predicate). `reachJal_of_span` composes that span with the
landed seg bridge into `ReachJal … c` — the drop-in each `link_h*` becomes once a
span lands.

Theorems (all `{propext, Classical.choice, Quot.sound}`):
- `reachJal_of_span S pcJal b0..b3 (spanToBlock : Triple SpanPre BlockPre)
  (segToJal : Triple BlockPre (JalErrPre …)) c (hspan : SpanPre c) : ReachJal … c`
  — `= (Triple.seq spanToBlock segToJal) c hspan`; relation-agnostic in SpanPre,
  uniform over Family A/B (only sees the shared middle type BlockPre).
- `reachJal_of_armBranch_eq_span` — machine-checked `rfl`: the `span := Triple.rfl`
  case IS `reachJal_of_armBranch` (genuine strengthening, not a divergent copy).
- `negTypeReach_of_span` — DEMO on hNegType (jal 0x800034e4, block 0x800034d0):
  the corrected `ReachJal` residual closes from a NON-identity span
  `Triple SpanPre (SpillArmPre … spill800034e4Seg …)` + landed
  `spill800034e4_toJalErr` + the arm linkage `hlink : negType-ctx → SpanPre c`.
- `negType_hsite_of_span` — the FULL route residual to `ErrHalts c`
  (`route_hNegType ∘ negTypeReach_of_span`); the drop-in for `A.link_hNegType`.

Residual left by the combinator = the honest, named span `Triple SpanPre
(SpillArmPre …)` (an M4 arm's reach-to-`pc0`) — strictly weaker demand than
"`c` at `pc0`", so a real M4 arm-sim wires in directly.

## Wiring (report-only, NOT applied to Vsa.lean / check_all)

- `Vsa.lean`: `import Vsa.Sim.rows.ErrReachSpan` (near the other rows/Err* imports).
- `scripts/check_all.sh` axiom list:
  ```
  Vsa.Sim.reachJal_of_span              # rows/ErrReachSpan (reach-to-pc0 span ≫ seg ≫ jal → ReachJal; generalizes reachJal_of_armBranch)
  Vsa.Sim.negType_hsite_of_span         # rows/ErrReachSpan (hNegType route residual from a non-identity SpillArmPre span; drop-in for A.link_hNegType)
  ```

## What remains for full errFamily closure (unchanged by this lane — genuinely M4)

The 42 collector fields `ErrArmLinks.link_*` (16) + `ErrArmLinksB.link_*` (26),
each = the M4 arm-sim error-edge reachability to `pc0` (now compose-able via
`reachJal_of_span` once a span lands), PLUS the ErrShared inputs
(`SnprintfContract` + the 4 exit-tail residuals) and the 2 passthroughs. None of
these are straight-line spans derivable from an entry predicate this lane — they
are the interpreter-recursion error edges, out of the err lane's reach without
the M4 arm-sim layer landing them.

## The 42 × 19 PC map (all ROUTED; residual = the named collector field)

| PC (jal) | hsites (routed) | Family | collector field(s) |
|---|---|---|---|
| 0x80002e90 | hNotCallable hDepth hEscape hAssertArity hSeqTail | B | ErrArmLinksB.link_h* |
| 0x80002ebc | hArity hAssertFail hBody | B | ErrArmLinksB.link_h* |
| 0x800034e4 | hNegType hRet | A | ErrArmLinks.link_hNegType/link_hRet |
| 0x80003950 | hUnaryE hForLoop | A | ErrArmLinks.link_h* |
| 0x80003b54 | hVarUndef hExpr | A | ErrArmLinks.link_h* |
| 0x80003b9c | hAssignE hVarInit | B | ErrArmLinksB.link_h* |
| 0x80003bc8 | hAssignUnbound hBlock | A | ErrArmLinks.link_h* |
| 0x80003c10 | hBinaryL hIfCond | B | ErrArmLinksB.link_h* |
| 0x80003c7c | hBinaryR hIfThen | B | ErrArmLinksB.link_h* |
| 0x80003cc4 | hBinaryOp hIfElse | B | ErrArmLinksB.link_h* |
| 0x80003ce8 | hOrL hWhileCond | A | ErrArmLinks.link_h* |
| 0x80003d14 | hOrR hWhileBody | A | ErrArmLinks.link_h* |
| 0x80003d5c | hAndL hWhileLoop | B | ErrArmLinksB.link_h* |
| 0x80003da0 | hAndR hForInit | B | ErrArmLinksB.link_h* |
| 0x80003de8 | hCallF hFlCond | B | ErrArmLinksB.link_h* |
| 0x80003e98 | hCallArgs hFlBody | B | ErrArmLinksB.link_h* |
| 0x80003f58 | hCallC hFlStep | B | ErrArmLinksB.link_h* |
| 0x80003fac | hArgsHead hFlLoop | A | ErrArmLinks.link_h* |
| 0x80003fdc | hArgsTail hSeqHead | A | ErrArmLinks.link_h* |

All 42 dischargeable in principle via `reachJal_of_span` once the per-PC span
`Triple SpanPre (SpillArmPre/SetupArmPre …)` lands (one span serves the 2-5
hsites sharing a PC). No hsite is blocked at the routing layer — the sole open
input is the M4 arm-sim reach-to-`pc0`.
