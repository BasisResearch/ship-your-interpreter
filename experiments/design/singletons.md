# Cluster design — the 13 singletons (grouped)

Cases not in the four big clusters. Grouped by shape:

| Group | Cases | Shape |
|-------|-------|-------|
| **S-vparm** (6) | vparm_VP_NULL/BOOL/INT/STR/CLOSURE/NATIVE | value_print jump-table arms (feed hCallPrint/Println) |
| **S-value-box** (2) | hStr, io_value_print (dispatch head) | leaf/value-box tail + vp dispatch |
| **S-closure** (1) | hFn | closure-alloc arm + native-store repr |
| **S-exec-leaf** (2) | hSCont, hSBrk | register-only exec arms (single ret block) |
| **S-entry** (2) | hEpilogueSpill, hInitStore | interp_run prologue/epilogue (X8) |
| **S-divergence** (1) | hDivCorr | divergence oracle family (X8, no span) |

(hInitStore is designed in env-seam.md; io_value_print in io-loop-fold.md — the
S-vparm arms and hDivCorr/hEpilogueSpill/hSBrk/hSCont/hStr/hFn are new here.)

## (a) Amended / new statement shapes

### S-vparm (6) — straight-span value_print arms

Each is 1-3 blocks ending in a tail-`j` / call to fputs/fwrite/fprintf. All
LANDED callee contracts (`Fputs/Fwrite/FprintfContract`). Restate as a single
parametric structure keyed by the VP tag (NOT six ad-hoc rows):

```lean
/-- vparm arm for kind `vk`, emitting via callee `emit`. Fuzz-safe: no ghost. -/
structure VParmArmResid (vk : ValueKind) (armPC : BitVec 64) : Prop where
  slot   : VpSlotPinned vk armPC m0        -- vp jump table 0x80019f10 (needs m0-conditioning!)
  emit   : EmitsRendered vk                 -- the callee contract post = rendered bytes
  tailj  : ArmTailReaches armPC             -- straight-span terminator (tailj/ret)
```

**Falsity watch:** `VpSlotPinned` under ∀-`m0` is the SAME B5 class as the stmt
table — condition it on the pinned image (an `EvalGround`-style `VpTablePins`).
The vp table `0x80019f10` needs a `gen_layout.py` generator entry (like the N1
kind table / N2 stmt table). This is a THIRD table-pin generator — flag for the
entry-ground layer (it is io-side, not EvalEntry, so a small `IoGround`).

### S-value-box: hStr

hStr is the closest-to-landed field: wave 47f discharged code/slot geometry;
47g/h reduced the residual to EXACTLY ONE named premise `EvalEntryStrAstRegion`,
and the amendment INTERFACE is landed (`AstRegionPins`, `strAstRegionBody_of_ground`).

```lean
/-- hStr becomes a RECORD FILL the moment EvalEntry.ground is inserted. -/
-- StrLeafResid st s  ←  field_hStr_of_astRegion (LANDED)  ←  EvalEntry.ground.ast (N3)
```
No new shape — hStr is gated purely on the `ground` INSERTION wave (audit §D).

### S-closure: hFn

```lean
structure FnResid (st : SpecSt) (e : Expr) : Prop where
  entry     : EvalEntry …                  -- carry
  allocFr   : ClosureAllocated st st'       -- malloc + closure frame (malloc LANDED)
  nativeRep : NativeStoreRepr st'           -- native-store representation readback
  exit      : EvalExitD … (.closure …)
```
malloc/fwrite/exit callees LANDED; value_kind_name NONE (the error sub-arm only).
Content = the closure-alloc arm + repr, a bounded seg + `callSeg` on malloc.

### S-exec-leaf: hSBrk, hSCont

Register-only single-ret-block arms. The RELATIONAL PILOT (round-3) already
proved the bridge shape field-for-field. Restate as the `StmtArmResid` from
loop-arm.md (slot 7/8, conditioned on `m0`):

```lean
-- BrkResid / ContResid  ←  StmtArmResid 7/8 execArmBrk/Cont  ←  ExecEntry.ground (N2)
```
These are the acceptance cases — `exec_brk_bridge.lean` SURVIVED, mutant REFUTED.
Gated on the `ExecEntry.ground` insertion (same wave as loop-arm LA-stmt).

**WAVE 48b DELTA (X3, machine-checked).** The `ExecEntry.ground` insertion
LANDED (wave 47i) but does NOT alone flip hSBrk/hSCont: `execGround_caseGeom_brk/
_cont` supply only the SLOT-PIN + TABLE halves of `ExecCaseGeom`; the third
conjunct is the `ExecLeafWiden` widener, which needs the leaf exit's presence
monotonicity `MemExtends m0 mem`.  Wave 48b LANDED the full pinned re-seat
scaffold (`Vsa/Sim/rows/ExecLeafPin.lean`, all axiom-clean): `execBrkSimP`/
`execContSimP` (→ `ExecExitPinned`), `execBrkSimDP`/`execContSimDP` (→ the
`ExecExitD` motive shape via `execLeafWidenP_of_entry`), and `field_hSBrk`/
`field_hSCont`/`skelHS{Brk,Cont}_of_pin` — each discharging its skeleton hole
MODULO EXACTLY ONE named premise `ExecArmMemExt st .{brk,cont}` (the exit pin
`ExecLeafMemPin`, whose `pres` = `MemExtends m0 ment`).  That `pres` is provable
only from the prologue `writeMap8` chain INSIDE `execBlockA`, exposed by amending
the SHARED `ExecArmEntryK` ∧-tower — the exec twin of the 47e eval `blockA_k`
`MemExtends m0 ment` amendment (`EvalSimCommon.lean:907`), a ~10-file ITEM-ZERO
fan-out (`ExecBrkCont`/`ExecDispatch`/`ExecRecCommon` + 6 `Stmt*ArmStagePre`
rows).  So brk/cont are GATED on X3-b (the `execBlockA` MemExtends exposure),
which is its own ≤1-session amendment wave, NOT the pure-record-fill 0a shape.
Census UNCHANGED at 4/58 (the fields carry the premise; honest not-found).

### S-entry: hEpilogueSpill (X8)

```lean
structure EpilogueSpill (L : Layout) : Prop where
  latch   : S5Zero L              -- the s5=0 exit latch
  restore : RestoreChainFacts L   -- byte-level spill/frame/image restore (ChainFacts)
  tail    : InterpNormalExitReaches L
```
Not an entry NEED (interp_run epilogue). Content = one restore block's
`block_facts`. Bounded, straight-line.

### S-divergence: hDivCorr (X8)

No machine span — a per-load `DivCorrFamily L` progress-only family fact over
exec_stmt cases. Statement shape is the FAMILY (already correct as an oracle):
```lean
-- hDivCorr  ←  DivCorrFamily L  (recursor/metatheorem, progress-only: ≥1 step, still corresponds)
```
NO amendment; discharged by the M4 exec_stmt case Triples' progress skeleton.
Recursor-threaded (like the loop IHs). The divergence endgame (memory) has this
CLOSED onto hEntry+hIter+ArmStages — hDivCorr is that capstone's residual.

## (b) Invariants / bridges to mine

- **S-vparm + io_value_print**: relational-lite, align spec `Value` kind → vp
  arm PC (the io-doc T-IO-valueprint mine). Grounds `VpSlotPinned` per tag.
- **S-exec-leaf**: DONE (round-3 pilot).
- **hFn**: T5 mem-window on the closure frame slots (repr readback); low yield.
- **hEpilogueSpill**: T1 constants on the restore block (spill offsets); trivial.
- **hDivCorr**: no mining (family fact).

## (c) Supplier DAG

```
Fputs/Fwrite/FprintfContract          ── LANDED (vparm emit)
VpTablePins (vp jump table)           ── MISSING (gen_layout.py 3rd generator, IoGround)
malloc/fwrite/exit                    ── LANDED (hFn)
NativeStoreRepr readback              ── MISSING (hFn content, bounded)
EvalEntry.ground.ast (N3)             ── LANDED interface; INSERTION missing (hStr)
ExecEntry.ground (N2)                 ── LANDED interface; INSERTION missing (hSBrk/hSCont)
EpilogueSpill restore ChainFacts      ── MISSING (bounded block_facts)
DivCorrFamily                         ── capstone recursor (X8)
```

## (d) Proving-task decomposition (bounded, ≤1 session each)

1. **T-S-vparm** (×1): `VpTablePins` generator + parametric `VParmArmResid` for
   the 6 arms + io_value_print dispatch. Template: brk/cont pilot + gen_layout.py.
2. **T-S-hStr** (record fill, rides the ground-insertion wave — 0 proof).
3. **T-S-hFn** (×1): closure-alloc seg + `NativeStoreRepr` + malloc callSeg.
   Template: `callSeg` + repr readback.
4. **T-S-brkcont** (record fill, rides ExecEntry.ground insertion — pilot done).
5. **T-S-epilogue** (×1): hEpilogueSpill restore `block_facts`. Template: `block_facts`.
6. **T-S-divcorr** (recursor-threaded, capstone — NOT bounded here).

Bounded tasks: **≈3** (vparm, hFn, epilogue) + 2 record-fills gated on the
ground wave + 1 capstone-threaded.
