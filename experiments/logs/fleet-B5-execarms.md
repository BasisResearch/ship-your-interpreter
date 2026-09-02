# Fleet log — B5-execarms

Worker on clone /tmp/vsa-fleet-B5-execarms. Field order per brief.

## BATCH VERDICT (recorded first — read this before the per-field lines)

NO field of B5 is provable as stated. The 11 dispatch-family holes are
PROVABLY FALSE; the 3 loop-family holes demand self-referential oracles.
Machine-checked obstruction file (green, axiom-clean, 2.3s):

    Vsa/Sim/rows/B5ExecArmObstructions.lean

- `stmtSlotPinned_empty_false` — `StmtSlotPinned k armPC ∅` is refutable
  (empty `ExtHashMap` lookups are `none`).
- `skelHS{Expr,Ret,RetNull,VarNull,Brk,Cont,VarInit,IfNone,WhileFalse,
  IfTrue,IfFalse}_false : ∀ L, ¬ SkelH* L` — each residual bundle
  (`ExecCaseGeom`/`ExecExprGeom`/`ExecRetGeom`/`ExecRetNullGeom`/
  `ExecVarNullGeom`/`ExecVarInitGeom`/`IfNoneGeom`/`WhileFalseGeom`/
  `IfTrueGeom`/`IfFalseGeom`) asserts its `StmtSlotPinned k armPC m0`
  unconditionally under the residual's ∀-quantified `m0 : Mem`; instantiate
  `m0 := ∅` and project `hslot` (or `.1`).
- `termResidualsCore_false : ∀ L, ¬ TermResidualsCore L` — the record itself
  is uninhabited (via its `hSBrk` field), so NO supplier campaign fills it
  until the residual statements are amended.

AMENDMENT NEEDED (coordinator-owned; observations.md entries
`exec-resid-slot-pins-uninhabited` + `loop-geom-self-referential-oracles`,
2026-09-01): condition `hslot`/`htableStk` on the pinned image (byte-pin
premises in the wave-43 `gen_layout.py` `groundSlot_k` shape, or a named
`RodataPinned m0` hypothesis), and thread the loop IH/step oracles of
`BlockGeom`/`ForStartGeom`/`WhileGeom` from the recursor instead of
∀-ghost-closing them inside the residual.

## Per-field landings/skips (brief order)

1. hSExpr — SKIPPED (FALSE as stated). Obstruction: `skelHSExpr_false`
   (slot-pin `StmtSlotPinned 0 execArmExpr m0` under ∀ m0; refuted at ∅).
2. hSRet — SKIPPED (FALSE). `skelHSRet_false` (slot 6, `execArmRet`).
3. hSRetNull — SKIPPED (FALSE). `skelHSRetNull_false` (slot 6).
4. hSVarNull — SKIPPED (FALSE). `skelHSVarNull_false` (slot 1,
   `execArmVarDecl`).
5. hSBrk — SKIPPED (FALSE). `skelHSBrk_false` (slot 7, `execArmBrk`);
   also drives `termResidualsCore_false`.
6. hSCont — SKIPPED (FALSE). `skelHSCont_false` (slot 8, `execArmCont`).
7. hSVarInit — SKIPPED (FALSE). `skelHSVarInit_false` (slot 1).
8. hSIfNone — SKIPPED (FALSE). `skelHSIfNone_false` (slot 3, `execArmIf`,
   `IfNoneGeom.hslot`).
9. hSWhileFalse — SKIPPED (FALSE). `skelHSWhileFalse_false` (slot 4,
   `execArmWhile`, `WhileFalseGeom.hslot`).
10. hSIfTrue — SKIPPED (FALSE). `skelHSIfTrue_false` (slot 3,
    `IfTrueGeom.hslot`).
11. hSIfFalse — SKIPPED (FALSE). `skelHSIfFalse_false` (slot 3,
    `IfFalseGeom.hslot`).
12. hSBlock — SKIPPED (missing supplier, statement suspect). `BlockGeom`
    demands `hstep : ∀ φf₀ φc₀ stM sH ssH stM' stFinH statusH m00,
    ExecSeqStep …` + `hnil`/`hArm` ∀-ghost-closed: the seq-loop knot as an
    unconditional oracle over ARBITRARY unlinked `stM'/stFinH/statusH/m00`.
    grep confirms NO theorem in the tree produces `ExecSeqStep`; the honest
    supplier is the capstone under assembly. Not cheaply falsifiable (the
    oracles are Triples, vacuous unless a satisfying entry config is
    constructed — requires a full loaded-image witness). Named obstruction:
    observations.md `loop-geom-self-referential-oracles`.
13. hSForStart — SKIPPED (missing supplier, same class). `ForStartGeom.hstep`
    (`ExecForStep` ∀-closed) + `hForIH` (the FULL for-loop simulation Triple).
    No `ExecForStep` producer exists.
14. hSWhileBreak — SKIPPED (missing supplier, same class). `WhileGeom.hstep`
    (`ExecWhileStep` ∀-closed) + `hWhileIH` (the FULL `.whileStmt` simulation
    Triple, i.e. exactly the theorem the recursor is building). No
    `ExecWhileStep` producer exists.

## Verification

- `lake env lean Vsa/Sim/rows/B5ExecArmObstructions.lean` — green, 2.3s wall.
- Axioms of all 13 theorems = [propext, Classical.choice, Quot.sound].
- Probe scratch kept at `experiments/wip/b5_probe.lean` (0.8s).
- No shared file edited; only appends to observations.md + this log + the
  two new files above.
