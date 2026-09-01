# Wave 44 — lane storewf — StoreClosuresBounded global invariant

File (owned): `Vsa/Sim/rows/StoreWF.lean`. Imports `Vsa.While.Cost` (for `StoreLe`,
`define_size`, `set_preserves_size`) + `Vsa.Sim.rows.StoreReprPhicRebase` (reuses
`StoreClosuresBounded`/`ValueClosuresBounded` by name — no new predicate).

## LANDED (step 1 — store-op preservation lemmas), green + no warnings-of-substance
- `ValueClosuresBounded.mono` — size-weakening of a closure ref.
- `StoreClosuresBounded.atSize` — whole-store size weakening.
- `FrameClosuresBounded` (per-frame content) + `storeClosuresBounded_iff_frames`
  + `FrameClosuresBounded.of_eq` (frame-equality transport — the clean way past
  the dependent-getElem rewrite wall).
- `StoreClosuresBounded.allocFrame` — pushes empty frame, closures untouched.
- `StoreClosuresBounded.allocClosure` — frames unchanged, size grows → weakens.
- `frameClosuresBounded_defineVars` + `StoreClosuresBounded.define` — needs the
  bound value bounded (`ValueClosuresBounded s.closures.size v`).
- `StoreClosuresBounded.set` — gas-induction, one in-place slot rewrite.
- `StoreClosuresBounded.foldDefine` — `Call.closure` param-bind fold; size constant.

KEY DESIGN: the naive `StoreClosuresBounded s → StoreClosuresBounded s'` is NOT
inductive through `define` — the bound value must itself be an in-bounds closure
ref. So the mutual motive is a CONJUNCTION (store stays bounded ∧ produced value
bounded in the result store). NOT a Law-4 falsity — true+inductive once threaded.

## NEXT (step 2): the 9-motive mutual induction over EvalE.rec (model:
`Cost.execSeq_store_mono`), then `storeClosuresBounded_invariant` + consumer lemma.

## LANDED (step 2 + 3) — the full invariant, green + axiom-clean (~2s)
- Lookup boundedness: `FrameClosuresBounded.of_mem`, `StoreClosuresBounded.lookup_bounded`,
  `.get?_bounded` (a store-bound value is bounded — needed by the `.var` case).
- `StatusClosuresBounded`/`ValuesClosuresBounded` (+ `.mono`) — the produced-value
  carriers for statement status / argument lists.
- Nine motives `P1..P9`; 50 shared minor-premise lemmas `b_int..b_qca` (mirroring
  `Cost.lean`'s `c_*`, named intros, no positional-underscore reliance).
- `storeClosuresBounded_mutual : StoreWFClosure` — the 9-way mutual induction via
  `{EvalE,EvalArgs,...,ExecSeq}.rec` with the P* motives + b_* premises.
  **NAMED-FIELD structure `StoreWFClosure`** (onEvalE/onEvalArgs/onCall/onExecS/
  onExecInit/onForLoop/onForCond/onExecStep/onExecSeq) — R6 forbids the `.2.2…`
  chain into a raw 9-tuple; consumers project by field name.
- Public: `evalE_storeClosuresBounded`, `execS_storeClosuresBounded`,
  `execSeq_storeClosuresBounded`, `storeClosuresBounded_initSt` (globals frame binds
  only natives), `storeClosuresBounded_invariant` (whole-program run from initSt).
- `#print axioms` all 5 ⊆ {propext, Classical.choice, Quot.sound}. Discipline OK.

## NOT a Law-4 falsity
Naive `StoreClosuresBounded s → StoreClosuresBounded s'` is not inductive through
`define`, but the invariant IS true+inductive once the produced-value bound rides
alongside (the conjunctive motive). No spec amendment needed.

## Per-arm retirement (report-only — did NOT edit those files)
`StoreClosuresBounded st.store` is threaded as premise `hWF` at:
- `rows/FnResidSupply.lean`: `fnResid_of_pipeline_wf` (:212), `FnResidBundle.hWF` (:253)
- `rows/FnArmSeamSupply.lean`: `fnResidBundle_of_parts` (:122), `fnResid_of_parts` (:175)
These stay ∀-`st`-quantified premises (st not yet a reachable state). RETIREMENT =
at the top-level `interpSimClosed`/`TermAssembly` point where the EX_FN recursor row
(`eval_fn_row`, CallRows:369) is applied to a CONCRETE `EvalE initSt …`/`ExecSeq
initSt …` derivation, supply `hWF := evalE_storeClosuresBounded hEvalPrefix
storeClosuresBounded_initSt` (or `storeClosuresBounded_invariant` for a stmt-seq
run). The per-arm `hWF` premise then vanishes into this ONE theorem instead of being
an assumed input. No statement changes to the FnResid* files required — only the
capstone's instantiation supplies the now-proved fact.
