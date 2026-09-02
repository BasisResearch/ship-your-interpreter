# Fleet B2-unary-logic — landing log

## hNeg — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hNeg.lean` — green via `lake env lean`, 1.9s,
  axioms exactly [propext, Classical.choice, Quot.sound].
- `field_hNeg_refuted (L : Layout) : ¬ SkelHNeg L`. The hole
  `∀ st esub, NegResid st esub` ∀-closes all ghosts with only the operand
  `read64`+`ExprRepr` hypotheses; `NegExtras.sp_headroom : SL.lo + 3264 ≤
  sp.toNat` fails at `sp = 0#64` (also independently: `op_lo`, `slot8` pin,
  `hMcallPop` totality vs a finite `m0`).
- Witness: `b2WitMem` (concrete ExtHashMap, `.null` nodes at 40/48, payload
  slots 16↦40, 24↦48; reads via `simp [read64, readLE,
  Std.ExtHashMap.getElem_insert]`), `b2WitSt`, `b2WitCfg` — shared template
  for the rest of the batch.
- observations.md: entry `2026-09-01 b2-resid-fields-refutable` appended
  (proposed amendment: thread `EvalEntry` into the Resid statements).

## hNot — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hNot.lean` — green, 1.0s, axiom-clean.
- `field_hNot_refuted (L : Layout) : ¬ SkelHNot L` via
  `NotSimExtras.sp_headroom` at `sp = 0#64`; consumes the shared
  `b2WitMem` template (imports `Vsa.Sim.rows.Field_hNeg`; its olean emitted
  via `lake env lean -o`, never lake build).

## hOrTrue — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hOrTrue.lean` — green, 1.0s, axiom-clean.
- `field_hOrTrue_refuted (L : Layout) : ¬ SkelHOrTrue L` via
  `OrTrueExtras.sp_headroom` at `sp = 0#64`; `b2WitCfg` fills the
  UNCONSTRAINED `c : Config` slot the logical Resids carry.

## hAndFalse — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hAndFalse.lean` — green, 1.0s, axiom-clean.
- `field_hAndFalse_refuted (L : Layout) : ¬ SkelHAndFalse L` via
  `AndFalseExtras.sp_headroom`, same witness.

## hOrFalse — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hOrFalse.lean` — green, 1.1s, axiom-clean.
- `field_hOrFalse_refuted (L : Layout) : ¬ SkelHOrFalse L` via
  `OrFalseExtras.sp_headroom`; two-operand witness (payload slots 16↦40,
  24↦48, `.null` nodes at both).

## hAndTrue — OBSTRUCTION LANDED (machine-checked refutation)
- File: `Vsa/Sim/rows/Field_hAndTrue.lean` — green, 1.2s, axiom-clean.
- `field_hAndTrue_refuted (L : Layout) : ¬ SkelHAndTrue L` via
  `AndTrueExtras.sp_headroom`, same two-operand witness.

## Batch verdict
- 0/6 holes provable as stated; 6/6 REFUTED (machine-checked, ∀ L).
- Root cause (one shape): the Resid ∀-closure carries no entry linkage; the
  Extras' `sp_headroom`/`op_lo`/`KindSlotPinned`/`hMcallPop` are entry-side
  facts. `TermResidualsCore L` is therefore uninstantiable until the six
  field statements are amended (proposal in observations.md entry
  `2026-09-01 b2-resid-fields-refutable`: thread `EvalEntry`/Layout into the
  Resids, or split Extras into Loaded-derivable pins + a blockA_k widening).
- discipline: OK (scripts/check_discipline.py, 9 rules).
