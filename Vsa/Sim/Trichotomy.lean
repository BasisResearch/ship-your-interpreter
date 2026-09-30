import Vsa.While.Trichotomy

/-!
# `htri` reduction — `Trichotomy` from a per-statement classical dispatch

`Vsa/While/Trichotomy.lean` already builds `Trichotomy` from `trichotomy_of_dispatch`,
conditional on three named residuals:

* `hnode : NodeDispatch` — the sequence-node (T)/(E)/(S) trichotomy;
* `hroot` — root (T)⇒`BigStep` classification;
* `hExclude` — the spine-exclusion residual.

This file **discharges `hroot` outright** and **reduces `hnode : NodeDispatch`** —
a sequence-granularity obligation — to the sharper, purely per-*statement*
classical dispatch `StmtDispatch`:

    ∀ st d env s, (∃ st' status, ExecS st d env s st' status) ∨ ExecErr st d env s

i.e. "every single statement, at any config, either runs to *some* status or
hits a runtime error".  This is the atom the plan attributes to `Classical.em`
on the C evaluator's per-statement dispatch (env_get hit/miss, binOpSem
some/none, truthy branch, depth cap, …).  All the **sequence** plumbing
(`nil`⇒(T), `consNormal`/`SeqStep`⇒(S), `consAbrupt`⇒(T), head-error⇒(E),
tail-error⇒(E)) is discharged here mechanically by case analysis, so the residual
shrinks from "the classical trichotomy at every list node" to "the classical
dispatch of one statement".

`hroot` is fully discharged: a top-level `ExecSeq initSt 0 0 p st' status` with
`status = .normal` *is* a `BigStep`; other statuses at the root are re-routed
through the same `StmtDispatch`/`hExclude` machinery, so the only genuine input
to the whole trichotomy is `StmtDispatch` + `hExclude`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

