# Cluster design — loop-arm (36 fields)

**Fields.** hAndFalse, hAndTrue, hAssign, hDivOv, hEq, hIAdd, hIDiv, hIGe, hIGt,
hILe, hILt, hIMod, hIMul, hISub, hNe, hNeg, hNot, hOrFalse, hOrTrue, hSExpr,
hSIfFalse, hSIfNone, hSIfTrue, hSRet, hSRetNull, hSWhileBreak, hSWhileFalse,
hSeqConsAbrupt, hSeqConsNormal, hSeqNil, hStrAddL, hStrAddR, hStrGe, hStrGt,
hStrLe, hStrLt.

All are arms reached by a computed jump off `eval_expr` (`0x80003164`) or
`exec_stmt` (`0x80003fe0`) jump tables. Each arm slice begins at the arm PC,
runs a few blocks, and rejoins the shared `eval_expr`/`exec_stmt` epilogue
(loop-head at `0x800033ec` / the exec tail). The "loop" tag is the shared
recursive-descent back-edge, not a counted loop.

## Sub-partition (they do NOT share one statement shape)

| Sub | Fields | Shape |
|-----|--------|-------|
| **LA-int** (11) | hIAdd hISub hIMul hIDiv hIMod hILt hILe hIGt hIGe hEq hNe | `BinIntCellResid`/`BinEqCellResid` — value-path already block-reflected; refuted only by X2 (∀-ghost, no entry) |
| **LA-str** (6) | hStrAddL hStrAddR hStrLt hStrLe hStrGt hStrGe | `EvalIH`-tail cells; blocked on X6 callee seams (strConcat / StrCmpOrderBridge) |
| **LA-unary** (2) | hNeg hNot | `NegResid`/`NotResid` + `NegExtras`/`NotExtras`; refuted by B2 (sp_headroom under ∀-sp) + X1 (hMcallPop) |
| **LA-logic** (4) | hOrTrue hAndFalse hOrFalse hAndTrue | logical short-circuit; same B2 + X1 class as LA-unary |
| **LA-div-ov** (1) | hDivOv | wrap-semantics `EvalIH` cell (X6 div seam) |
| **LA-stmt** (12) | hSExpr hSRet hSRetNull hSIfNone hSIfTrue hSIfFalse hSWhileFalse hSeqNil hSeqConsNormal hSeqConsAbrupt + (hSWhileBreak, hAssign spill here) | exec-arm dispatch (`Exec*Geom`) refuted by B5 (∀-m0 slot pin) + B6 (code-free SegEntry) |

## (a) Amended / new statement shapes

### Root cause of the falsities (machine-checked, do NOT re-introduce)

1. **B2 class** (LA-unary, LA-logic): `*Extras.sp_headroom : SL.lo + 3264 ≤ sp`
   is asserted as a *conclusion* under a ∀-quantified `sp`; refuted at `sp=0`
   (`fleet/obstructions/B2_Field_hAndFalse.lean`).
2. **B5 class** (LA-stmt dispatch): `StmtSlotPinned k armPC m0` asserted under
   ∀-`m0`; refuted at `m0=∅` (`B5ExecArmObstructions.lean`).
3. **B6 class** (LA-stmt seq/for): `mExecSeq`/`SegEntry` pins no code byte, so
   an off-diagonal span is unprovable (`B6LoopSeqObstruction.lean`).
4. **X1** (LA-unary, LA-logic): `hMcallPop` totality is refutable for every
   finite `Mem` (`McallPopTotality.lean`) — independent of geometry.

The one amendment shape that fixes 1–2 uniformly: **carry the entry as a field.**
Every arm residual must take `EvalEntry`/`ExecEntry` (or its `ground`
projection) as a *hypothesis field*, so `sp_headroom` and `StmtSlotPinned`
become preconditions supplied by the entry, not free conclusions. Restate as a
named-field `structure … : Prop` (kills the flat-∧ tower; R6/R7).

```lean
/-- LA-stmt dispatch (replaces the 12 `Exec*Geom` ∀-`m0` towers).
    `ExecEntry.ground : ExecGround` (landed interface) supplies `slot`/`table`. -/
structure StmtArmResid (armK : Nat) (armPC : BitVec 64)
    (g N A SL) (φf φc) (st st' : SpecSt) (aStmt sp aRet m0) (s : Stmt) : Prop where
  entry  : ExecEntry g N A SL φf φc st aStmt sp aRet m0 s   -- HYPOTHESIS (was absent)
  slot   : StmtSlotPinned armK armPC m0                     -- now: entry.ground.table.slotₖ
  kind   : read32 m0 aStmt = some (kindOfStmt s)            -- relational-mined (round-3 PASS)
  step   : ExecExitD g N A SL φf φc st' aRet m0 s           -- widened exit (Widen)
```

`StmtSlotPinned`/`read32-kind` discharge is the LANDED relational bridge
(`stmtRepr_kind` + `StmtTablePins.slotₖ`, round-3 pilot confirmed it
field-for-field for brk/cont; the same shape covers all 12).

```lean
/-- LA-unary / LA-logic (replaces `NegResid∧NegExtras`, etc.).
    `EvalEntry.ground`/`nbs_pins` supply the geometry; the dead-byte presence
    (was `hMcallPop`) is a field on the ACTUAL read footprint, not ∀-`mcall`. -/
structure UnaryArmResid (armK : Nat) (armPC : BitVec 64)
    (g N A SL) (φf φc) (st st' : SpecSt) (aExpr sp sret m0) (e : Expr) : Prop where
  entry     : EvalEntry g N A SL φf φc st aExpr sp sret m0 e   -- supplies sp_headroom
  slot      : KindSlotPinned armK armPC m0                     -- entry.ground.table
  deadPres  : ∀ a ∈ deadWindow sret, (m0[a]?).isSome           -- X1 fix: NAMED footprint
  exit      : EvalExitD g N A SL φf φc st' sret m0 e
```

`deadWindow sret := [sret+4,sret+8) ∪ [sret+16,sret+24)` (the exact dead-byte
read set the McallPop obstruction identified); supplied by the consumer's own
`writeMap8` chain via `MemExtends`, NOT a totality oracle.

### LA-int / LA-div-ov / LA-str

LA-int cells (`BinIntCellResid`) already have block-reflected value-path
suppliers (`AddResid`…`GeResid`, all LANDED). Their ONLY defect is X2: the cell
resid is stated under ∀-`m0` with no entry. **Amendment = the B2-shape carry:**
add `entry : EvalEntry …` field to `BinIntCellResid`/`BinEqCellResid`
(`rows/BinDispatchRow.lean`, ~12 cell sites, `hc` already in scope per X2). No
new value-path proof — the cells relight verbatim once `entry` is a field.

LA-str + LA-div-ov are `EvalIH`-tail cells whose CONTENT is a callee seam (X6);
their statement shape is already correct (they quantify only spec-level
`st''`/`sl`/`sr` and conclude `EvalIH`, no ghost geometry). **No amendment** —
they are genuinely blocked on suppliers, not falsities.

## (b) Invariants / bridges to mine

- **LA-stmt dispatch**: relational-lite (single seam), stage-4 pilot ALREADY
  PASSED for brk/cont; re-run `mine_relational.py` per arm PC (probe s0=aStmt +
  read32[s0] at the exec dispatch `0x80004014`, align by `kindOfStmt` tag) to
  confirm `read32 = kindOfStmt s` + `StmtSlotPinned` for tags {expr,ret,varDecl,
  if,while}. Stages: T5 mem-window (slot word), relational tag-align.
- **LA-unary/logic**: probe the eval dispatch `0x8000351c`-family + the dead-byte
  window at `sret` across the arm; T5 mem-window to confirm `deadWindow` reads
  are satisfied by the writeMap8 chain (grounds the `deadPres` field's footprint).
- **LA-int**: no mining needed — value paths landed; only the `entry` carry.

## (c) Supplier DAG

```
EvalEntry.ground / ExecEntry.ground  ── LANDED interface (EntryGround.lean)
    │  (needs INSERTION wave — fleet-scale, audit §D; MISSING)
    ├─▶ StmtArmResid.slot/kind   (execGround_caseGeom_* — LANDED discharges)
    ├─▶ UnaryArmResid.slot        (kindTablePins_of_bytes — LANDED)
    └─▶ BinIntCellResid.entry     (B2-carry amendment — MISSING, ~12 sites)
Value-path suppliers Add..GeResid  ── LANDED
StrConcat / StrCmpOrderBridge / div seam (X6)  ── MISSING (callee campaign)
Widen / ExecExitD                  ── LANDED
```

## (d) Proving-task decomposition (bounded, ≤1 session each)

1. **T-LA-carry** (statement wave): add `entry` field to `BinIntCellResid`/
   `BinEqCellResid` + restate the 12 `Exec*Geom` and `NegResid`/`NotResid`/
   logical-four as the named-field structures above. Pairs with the `ground`
   insertion (same rows). Template: `rows/BinDispatchRow.lean` B2-shape.
2. **T-LA-int-relight** (×1, after T-LA-carry): re-run the 11 int/eq cell rows —
   pure recompile, value paths unchanged. Template: existing `EvalAddRow` etc.
3. **T-LA-stmt-dispatch** (×1 per arm group, ~3 sessions): discharge
   `StmtArmResid` via `execGround_caseGeom_*` + `stmtRepr_kind`. Template:
   round-3 `exec_brkcont_relational.md` → `exec_brk_bridge.lean`.
4. **T-LA-unary** (×1): discharge `UnaryArmResid` for hNeg/hNot via `nbs_pins` +
   `deadPres` from the arm's writeMap8. Template: `Field_hNull`.
5. **T-LA-logic** (×1): same for the 4 logical fields. Template: `Field_hNeg`
   (inverted from obstruction).
6. **T-LA-str/divov** (X6, out of this pass's scope): 6+1 callee-seam splices —
   NOT bounded here (genuine content, separate campaign lanes).

Bounded tasks in this cluster (excluding X6 seams): **6** (T1 statement +
T2 relight + 3× dispatch + T4 + T5). Grandfathered blocked: 7 (6 str + 1 divov).
