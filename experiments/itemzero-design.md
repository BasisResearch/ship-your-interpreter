# ITEM ZERO — the record amendment (run 1, 2026-09-01)

The fleet machine-checked `termResidualsCore_false` (falsity #12): the record is
uninhabited as stated.  Root causes, verified against the 62-field audit + the
four fleet obstruction sets (`experiments/fleet/obstructions/`) + the
coordinator's budget analysis (observations `recursion-stack-budget-class`,
falsity #13):

1. **∀-ghost closure** — Resid/Geom statements close `sp/sret/m0/SL/c` over
   conclusions demanding entry-side reality (20 fields refuted).
2. **Stack-budget underivability** — even entry-conditioned, the recursive-case
   extras (`sp_headroom : SL.lo + 3264 ≤ sp`) exceed what the constant-headroom
   `EvalEntry.stackOK` (2176) supplies; `EvalIH` itself is false at depth ≥ 3
   under tight `SL` (falsity #13).
3. **Self-referential loop oracles** — `BlockGeom/ForStartGeom/WhileGeom`
   ∀-close `ExecSeqStep/ExecForStep/ExecWhileStep` + full loop IHs that only the
   recursor can supply.
4. **Motive shape** — `mExecSeq` independent `(p,q)` + code-free `SegEntry`;
   `mForLoop` identity-PC with store-mutating endpoints (B6, machine-checked).

## The uniform amendment (five phases, ONE design)

**Principle: a Resid may state only what its consuming row can instantiate —
each Resid gains exactly the hypotheses the row HAS (the entry bundle, the
recursor IHs) and every entry bundle must be recursion-sound (budget-indexed).**

### Phase B0 — budget layer (new defs, no consumer surface)
* `StackLayout` gains `perCall : Nat` (per-call-level stack budget).  All
  `⟨lo, hi⟩` literals gain a third component.
* Mutual `Vsa.While.Expr.stackNeed / Stmt.stackNeed / stackNeedList : … → Nat`:
  structural frame bytes — expr nodes cost 1088 + max over child exprs
  (call nodes: 1088 + max over f/args only; the BODY is accounted by the
  `perCall` term, not structurally); stmt nodes cost 176 + inner needs.
* `Expr.BodiesBound e P` / `Stmt.BodiesBound s P` (every `.fn` literal's body
  need ≤ P) and `StoreBodiesBound store P` (every closure body need ≤ P).
* Arithmetic kit: `stackNeed_pos`, subterm monotonicity lemmas, and the
  monotone bridge `StackOK.mono : h' ≤ h → StackOK SL sp h → StackOK SL sp h'`.

### Phase B1 — entry re-condition (field-type edits only; NO signature change)
* `EvalEntry.stackOK : StackOK SL sp (e.stackNeed + (maxCallDepth − d) * SL.perCall + 1088)`
  (+ new fields `store_bodies : StoreBodiesBound st.store SL.perCall`,
  `expr_bodies : Expr.BodiesBound e SL.perCall`).
* `ExecEntry.stackOK` likewise over `s.stackNeed` (+ same two fields over `s`).
* Every consumer of the OLD 2176 fact: one `StackOK.mono`/`stackOK_2176`
  application (the new headroom is ≥ 2176 since `stackNeed ≥ 1088`).
* Every CHILD-entry construction site (`armTail_rec`, `ArmSegSplit*`,
  `evalEntry_of_jalPrefix`, …): the child's stackOK now DERIVES by arithmetic
  (parent need = child need + 1088 for the consumed frame); the
  `sp_headroom`-class oracle premises are DELETED there.

### Phase A — Resid entry-threading (the fleet's 20 + eval-side twins)
* B1 leaves (`IntLeafResid/NullLeafResid/BoolLeafResid/StrLeafResid`): add
  `(d env aEnv aExpr c)` binders + `EvalEntry … → ` hypothesis; the extra
  conjuncts (sret-window vs value_* code, slot pins, `LeafWiden`'s
  pres/surv inputs) become derivable from the entry fields (sret_win +
  stack/code disjointness excludes the code windows; `mem`+`code` pin `m0`).
* B2 unary/logical (`NegResid/NotResid/OrTrue/AndFalse/OrFalse/AndTrueResid`):
  same threading; `sp_headroom/op_lo` now derivable via the budgeted stackOK;
  `KindSlotPinned … m0` from the entry's pinned-slot fields; `hMcallPop` from
  `GoodState` memory totality.
* `BinIntCellResid/BinEqCellResid` + `CallResid/FnResid/AssignResid/
  VarLeafResid`: audit says oracle-shaped (already conditional); re-condition
  their ghost closures on the same entry hypothesis where they carry naked
  geometry (`AddResid.SLloSp` class) — mechanical once B1-leaf template lands.
* Exec side (11 dispatch Geoms): add `ExecEntry … → ` hypothesis; the
  `StmtSlotPinned k armPC m0` pins condition on the entry's code/rodata
  fields (add the table-pin field to ExecEntry if absent — the wave-43
  generated `groundSlot_k` pins are the suppliers).

### Phase C — loop-oracle re-threading (hSBlock/hSForStart/hSWhileBreak)
Restate `BlockGeom/ForStartGeom/WhileGeom` with the loop IH/step oracles as
PREMISES in the Resid (filled by the row from its recursor IHs: `mExecSeq` for
block, `mForLoop` tail IH for forStart, `mExecS(.whileStmt)` for while), not
∀-closed fields.  Mirrors `SeqConsAbruptResid`'s landed threaded shape.

### Phase D — motive/SegEntry amendment (B6; AFTER wave-45 replay lands)
* `mExecSeq`: pin `p = execSeqLoopPC`, `q = execSeqContPC` (drop the
  independent ∀ p q).  Consumers reference the motive fully applied — the
  scaffold-motive precedent predicts near-zero re-threading; verify by census.
* `mForLoop`: honest distinct loop-head/exit PCs (or `True` if the consumer
  census shows no projection — B6's cheaper route; census first).
* `SegEntry` gains a code-image linkage field for the seq/for spans (the
  engine seam: `execSeqLoop`'s `ExecSeqExit` needs the memFrame/stackWin
  upgrade recorded in `rows/SeqForRows.lean`).
* Replace the 7 inline GAP fields in `TermResidualsCore` by the landed
  `SeqForRows` carriers (`SeqNilResid/SeqConsNormalResid/SeqConsAbruptResid/
  ForResid`), filled via the landed `hSeq*_row/hFl*_row`.

### Phase E — regen + census
`gen_assembly_skeleton.py` regen, `AssemblySkeleton.lean` + `assembly_skeleton.tsv`,
`field_census.py -j4` re-baseline.  The fleet obstruction certificates in
`experiments/fleet/obstructions/` go STALE by design (they refute the OLD
statements; git history keeps them).

## Sequencing
wave-45 replay (in flight) → B0 → B1 → {A, C} in parallel → D → E.
Validate every phase in /tmp/vsa-itemzero-sandbox (re-cloned from main after
the wave-45 sweep), sweep the touched cone, then apply to main in one motion.

## Top-level accounting
The concrete `Layout.atInterpRun` (entry seam) carries
`StackOK SL* sp₀ (p.stackNeed + maxCallDepth * SL*.perCall + 1088)` — "properly
loaded" includes the stack fitting the program (maxCallDepth-cap precedent).
`InterpSim`'s ∀-Layout shape is unchanged.
