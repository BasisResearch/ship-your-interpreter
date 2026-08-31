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

namespace Vsa.Sim.Trichotomy

open Vsa.While

/-- **The per-statement classical dispatch residual.**  Every statement `s`, at
any config `(st, d, env)`, either runs to *some* final state and status
(`ExecS`) or reaches a runtime error (`ExecErr`).  This is the atomic classical
case-split — the `Classical.em` on the C evaluator's per-statement dispatch — that
the whole `Trichotomy` construction rests on once the sequence plumbing is
discharged. -/
def StmtDispatch : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (s : Stmt),
    (∃ st' status, ExecS st d env s st' status) ∨ ExecErr st d env s

/-- **`NodeDispatch` from `StmtDispatch`.**  The sequence-node trichotomy is pure
plumbing over the per-statement one:

* `ss = []`: (T) via `ExecSeq.nil`.
* `ss = s :: ss'` and `s` runs to `status`:
  * `status = .normal`: (S) via `SeqStep` (`ExecS … .normal`);
  * `status ≠ .normal`: (T) via `ExecSeq.consAbrupt`.
* `ss = s :: ss'` and `s` errors: (E) via `ExecSeqErr.head`.

No classical content beyond `StmtDispatch`; a plain `Status`-case split. -/
theorem nodeDispatch_of_stmtDispatch (hstmt : StmtDispatch) : NodeDispatch := by
  intro st d env ss
  cases ss with
  | nil =>
    exact Or.inl ⟨st, .normal, .nil st d env⟩
  | cons s ss' =>
    rcases hstmt st d env s with ⟨st', status, hrun⟩ | herr
    · -- head runs to `status`; split on whether it is `.normal`
      cases status with
      | normal =>
        -- (S): one normal head step into the tail node
        exact Or.inr (Or.inr ⟨st', ss', s, rfl, hrun⟩)
      | brk =>
        exact Or.inl ⟨st', .brk, .consAbrupt st d env s ss' st' .brk hrun (by simp)⟩
      | cont =>
        exact Or.inl ⟨st', .cont, .consAbrupt st d env s ss' st' .cont hrun (by simp)⟩
      | ret v =>
        exact Or.inl ⟨st', .ret v, .consAbrupt st d env s ss' st' (.ret v) hrun (by simp)⟩
    · -- (E): the head statement errors
      exact Or.inr (Or.inl (.head st d env s ss' herr))

/-- **Root (T)-classification, discharged.**  A top-level terminating node
`ExecSeq initSt 0 0 p st' status` yields `∃ out, BigStep p out` exactly when
`status = .normal` (then `⟨st', hexec, rfl⟩` *is* a `BigStep`).

A non-`.normal` top-level status cannot arise as the trichotomy's (T) verdict at
the root while `hExclude` holds — but `trichotomy_of_dispatch` demands the (T)⇒
`BigStep` implication only for the fired verdict.  We therefore state the version
`trichotomy_of_dispatch` actually needs: the root terminating verdict is routed
to `BigStep` *when it is a normal-status completion*; the abrupt-status roots are
excluded by the same `hExclude` that excludes them everywhere on the spine.  This
lemma is the `.normal` core, which is all `hroot` requires once the top-level
sequence is known to complete normally (top-level scripts run to `.normal`; an
abrupt top-level status is itself a spec-level error routed through `ExecSeqErr`,
covered by `hExclude`). -/
theorem bigStep_of_execSeq_normal {p : Program} {st' : St}
    (h : ExecSeq initSt 0 0 p st' .normal) : ∃ out, BigStep p out :=
  ⟨st'.out, st', h, rfl⟩

/-- **`Trichotomy` from the per-statement dispatch + spine exclusion.**  The fully
assembled reduction: with `StmtDispatch` (the atomic per-statement classical
case-split) and the spine-exclusion residual `hExclude`, every program
terminates, errors, or diverges.  `hroot` is supplied by
`bigStep_of_execSeq_normal`; `hnode` by `nodeDispatch_of_stmtDispatch`.  So the
whole `htri` obligation is reduced to exactly two named residuals:

* `StmtDispatch` — every statement runs or errors (classical per-statement),
* `hExclude` — a non-terminating, non-erroring spine node stays that way.

Both are pure spec-layer statements over the WHILE semantics (no Sail state). -/
theorem trichotomy_of_stmtDispatch (hstmt : StmtDispatch)
    (hExclude : ∀ (p : Program) (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
      Spine p st d env ss →
      ¬ (∃ st' status, ExecSeq st d env ss st' status) ∧ ¬ ExecSeqErr st d env ss) :
    Trichotomy :=
  trichotomy_of_dispatch (nodeDispatch_of_stmtDispatch hstmt)
    (fun _p hterm => by
      obtain ⟨st', status, hexec⟩ := hterm
      -- A top-level completion routes to `BigStep` at `.normal`; an abrupt
      -- top-level status is excluded from the fired (T) verdict by `hExclude`
      -- at the root (`Spine.base`), which the caller supplies uniformly.
      cases status with
      | normal => exact bigStep_of_execSeq_normal hexec
      | brk =>
        exact absurd ⟨st', .brk, hexec⟩ (hExclude _ _ _ _ _ .base).1
      | cont =>
        exact absurd ⟨st', .cont, hexec⟩ (hExclude _ _ _ _ _ .base).1
      | ret v =>
        exact absurd ⟨st', .ret v, hexec⟩ (hExclude _ _ _ _ _ .base).1)
    hExclude

end Vsa.Sim.Trichotomy
