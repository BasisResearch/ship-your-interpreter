# prove-unary log (clone /tmp/vsa-prove-unary)

Target: 6 fields hNeg hNot hOrTrue hAndFalse hOrFalse hAndTrue (LA-unary+LA-logic).
Each *Resid = ∀ entry+operand-facts → *Extras ∧ [aEnv3 x13-survival]? ∧ windowedPresence ∧ memExt.
McallPop oracle AMENDED OUT (47i): windowedPresence = presence on dead-byte footprint
([sp-1120,sp) ∪ [aExpr+4,aExpr+8)); memExt = MemExtends m0 mcall on off-stack-agreeing mcall.

## Design-order attempts

### hNeg (TEMPLATE, design-order first) — BLOCKED (Law 4)
- NegResid concludes: NegExtras ∧ presence(∀mcall) ∧ memExt(∀mcall).
- NegExtras fields (sp_headroom, slot8, geometry) ARE now entry-derivable post-47i
  (EvalEntry carried as hyp; stackBudget ⇒ sp_headroom; ground ⇒ slot8/expr_survives).
  The pre-47i B2 sp_headroom refutation NO LONGER applies.
- BUT the two amended `∀ mcall` conjuncts (presence, memExt) are FALSE as stated —
  they quantify over arbitrary off-stack-agreeing mcall; nothing forces such mcall
  to preserve m0 presence in [SL.lo,sp). MACHINE-CHECKED:
  fleet/obstructions/UnaryLogicMemExtOverquant.lean, UnaryLogicPresenceOverquant.lean
  (both clean axioms {propext,Classical.choice,Quot.sound}).
- Consumer (EvalNegSim3.lean:344) only ever needs the ONE structured mcall from
  blockB_unary → the statement is over-strong. STOP; re-amend needed (obs ledger).

### hNot, hOrTrue, hAndFalse, hOrFalse, hAndTrue — BLOCKED (same class)
- All 5 carry the IDENTICAL `∀ mcall` presence+memExt pair (verified in TermRouting.lean).
- Same machine-checked falsity applies verbatim. STOP each (Law 4). No new premise introduced.

## VERDICT: 6/6 BLOCKED on a shared post-47i statement falsity (not a supplier gap).
No new named premise was introduced (contract gate not triggered — nothing to fuzz/inhabit).
