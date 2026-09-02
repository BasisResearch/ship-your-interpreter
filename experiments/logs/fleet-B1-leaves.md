# Fleet log — B1-leaves (hInt, hNull, hBool, hStr)

Worker clone: /tmp/vsa-fleet-B1-leaves.  Contract: one entry per field, appended
as each lands/skips.  Obstruction file (green, axiom-clean {propext,
Classical.choice, Quot.sound}, `lake env lean` 1.6s):
`experiments/fleet/obstructions/B1_leaves_obstructions.lean`.
Companion observation: `experiments/observations.md` entry
`2026-09-01 leaf-resid-forall-ghost-falsity`.

## hInt — SKIPPED (unprovable as stated; gap machine-checked)

- Target: `SkelHInt L = ∀ st n, IntLeafResid st n` where `IntLeafResid` ∀-closes
  `g N A SL φf φc sp r sret m0` over `LeafWiden = Widen (EvalExit …) (stackFoot SL)`.
- Obstruction: `Widen.pres` needs `MemExtends m0 c.σ.mem` for EVERY config `c`
  satisfying the bare `EvalExit` — but `EvalExit.memFrame` leaves presence in
  `[SL.lo, sp) ∪ [A.lo, A.hi)` and the sret padding bytes unconstrained (the
  `EvalRecCommon.lean` doc itself calls `MemExtends` "the fact EvalExit
  forgets").  `Widen.surv` needs `StoreRepr` stability under arbitrary rewrites
  of `[SL.lo, SL.hi)`, which needs `A ∩ [SL.lo, SL.hi) = ∅` — an
  `ImageGeom`-class fact absent from the ∀-ghost statement.
- Missing supplier by NAME: `GeomFrom` (named in the TSV + `TermAssembly.lean`
  field doc; does not exist in the repo — `grep -rln GeomFrom Vsa` hits only
  the doc comment).  Design-level supplier: `TermShared.geom : ImageGeom N A SL`
  (`TermBundles.lean` table row for `hInt`) — not a premise of the hole.
- Machine-checked reduction: `skelHInt_of (hPres : IntLeafPres)
  (hSurv : IntLeafSurv) : SkelHInt L` in the obstruction file proves the gap is
  EXACTLY those two named premises (the rest is a `Widen` record fill).
- No `Vsa/Sim/rows/Field_hInt.lean` emitted (a conditional theorem is not the
  hole; contract forbids touching the statement).

## hNull — SKIPPED (statement PROVABLY FALSE)

- Target: `SkelHNull L = ∀ st, NullLeafResid st`.  `NullLeafResid` asserts, for
  ARBITRARY `sret` and an UNCONSTRAINED `c : Config`, the conjunct
  `(sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat)` (sret buffer vs
  `value_null` code window).
- Falsity: `skelHNull_false (L) : ¬ SkelHNull L` — instantiate
  `sret := 0x800027f0#64` (inside the window; both disjuncts fail by `decide`),
  ghosts trivial, `c := ⟨default, 0, 0⟩`.
- Amendment implied: geometry conjuncts must be premises (or drawn from
  `ImageGeom`), not asserted ∀-ghost.

## hBool — SKIPPED (statement PROVABLY FALSE)

- Same shape as hNull at the `value_bool` window `[0x800027f8, 0x8000280c)`.
- Falsity: `skelHBool_false` at `sret := 0x80002800#64`.

## hStr — SKIPPED (statement PROVABLY FALSE)

- Same shape at the `value_str` window `[0x8000281c, 0x8000282c)` (third
  conjunct of `StrLeafResid`; the first two are conditional and irrelevant).
- Falsity: `skelHStr_false` at `sret := 0x80002820#64`.

## Batch summary

0/4 green, 4/4 skipped with machine-checked obstructions (3 falsities + 1
pinned two-premise gap).  The falsity class extends beyond B1: any `*Resid`
that ∀-closes geometry/image conjuncts over ghosts is refutable the same way
(e.g. B5 `BrkResid`'s `StmtSlotPinned k armPC m0` at `m0 = ∅`).  Coordinator
action: amend `rows/TermRouting.lean` residual defs to condition on
`ImageGeom`/populated-`m0` (rows already destructure the conjuncts, so
consumers are local), regenerate the skeleton, re-batch.
