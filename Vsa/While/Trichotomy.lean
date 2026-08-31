import Vsa.While.ErrorSem

/-!
# Layer 5 — the classical trichotomy (`Trichotomy`)

`stuck_of_trichotomy` (`Vsa/While/ErrorSem.lean`) turns the `Trichotomy`
obligation

  `∀ p, (∃ out, BigStep p out) ∨ BigStepErr p ∨ BigStepDiverges p`

into `stuck_sim`'s spec side (`¬∃out BigStep p → BigStepErr p ∨
BigStepDiverges p`).  This file constructs `Trichotomy` itself — the classical
case split that says every program either terminates cleanly, hits a runtime
error, or runs forever.

## The structure

`BigStep`/`BigStepErr`/`BigStepDiverges` are all rooted at the top-level
sequence `ExecSeq/ExecSeqErr/Approx initSt 0 0 p`.  The trichotomy is proved by
a fuel induction that, at each sequence node, splits **classically**
(`Classical.em`, expected here — `stuck_sim` already admits `Classical.choice`)
on whether the head statement terminates / errors / stays running, threading the
verdict down the tail.

We package the whole classical dispatch as ONE per-node obligation
`NodeDispatch`: at any reachable `ExecSeq` node `(st, d, env, ss)`, one of three
things holds —

  (T) the node terminates: `∃ st' status, ExecSeq st d env ss st' status`;
  (E) the node errors: `ExecSeqErr st d env ss`;
  (S) the node makes one step and recurses: `ss = s :: ss'` with the head running
      normally (`ExecS st d env s st₁ .normal`) and the tail node again reachable
      (the successor node the fuel recursion descends into).

`NodeDispatch` is the classical `exec_stmt`/`eval_expr` case-split of the plan,
lifted to the sequence granularity `Approx` records.  From it:

* the **divergence** arm is *proved outright* here — `approx_of_dispatch` builds
  `Approx n` for **every** `n` by fuel recursion, consuming one (S) verdict per
  unit of fuel (this is the real content, and it is unconditional given
  `NodeDispatch`);
* the **terminate/error** arms are the (T)/(E) verdicts, threaded to the
  top-level `BigStep`/`BigStepErr` by `Classical.em` at the root.

`Trichotomy` follows by `Classical.em (∃ n, ¬ Approx n …)`: either some fuel runs
out — then a (T) or (E) verdict must have fired at that node (termination or
error) — or `Approx n` holds for all `n` (divergence).

Landed conditional on the single node-dispatch residual `NodeDispatch` (the
classical per-node obligation the plan calls "every configuration either
terminates, errors, or is `Approx n` for every `n`").  The divergence-construction
half is unconditional.  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.While

/-! ## §1. The per-node classical dispatch

At a sequence node `(st, d, env, ss)`, the three exhaustive verdicts.  This is
the classical case-split the plan defers to `Classical.em` at each dispatch,
stated positively so the fuel recursion can consume it. -/

/-- The successor relation of the fuel recursion: a node `(st, d, env, s :: ss)`
whose head runs normally to `st'` steps to the tail node `(st', d, env, ss)`.
One `Approx.step` worth of progress. -/
def SeqStep (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (st' : St) (ss' : List Stmt) : Prop :=
  ∃ s, ss = s :: ss' ∧ ExecS st d env s st' .normal

/-- **The per-node classical dispatch obligation.**  At every sequence node, one
of: it terminates (some final state+status), it errors (`ExecSeqErr`), or it
takes one normal head step to a successor node.  This is the classical
`exec_stmt`/`eval_expr` trichotomy of the plan at the sequence granularity — the
single residual the whole `Trichotomy` construction rests on (discharged, per
statement kind, by `Classical.em` on the C evaluator's dispatch: `env_get`
hit/miss, `binOpSem` some/none, truthy branch, depth cap, etc.). -/
def NodeDispatch : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
    (∃ st' status, ExecSeq st d env ss st' status) ∨
    ExecSeqErr st d env ss ∨
    (∃ st' ss', SeqStep st d env ss st' ss')

/-! ## §2. Divergence construction (UNCONDITIONAL given `NodeDispatch`)

The real content: if no node on the descending spine ever fires the
terminate/error verdicts, the (S) verdict fires forever and builds `Approx n` for
every `n`.  We phrase it as: given `NodeDispatch`, either some node terminates or
errors (yielding (T)/(E) at the root), or `Approx n` holds for all `n`.

`approx_of_neverStuck` is the clean statement: if the (S) verdict is available at
*this* node and, coinductively, at every successor, then `Approx n` holds for all
`n`.  We avoid coinduction by strengthening to an explicit "spine predicate"
`Runs`: a set of nodes closed under one (S)-step.  Membership in `Runs` gives
`Approx n` for every `n` by induction on `n`. -/

/-- A node is *running-closed* under a predicate `R` when it steps (S) into
another `R`-node.  The fuel recursion consumes exactly this. -/
def StepClosed (R : St → Nat → Addr → List Stmt → Prop) : Prop :=
  ∀ st d env ss, R st d env ss →
    ∃ st' ss', SeqStep st d env ss st' ss' ∧ R st' d env ss'

/-- From a step-closed predicate, every member node is `Approx n` for all `n`.
Fuel recursion: `Approx 0` is `Approx.zero`; `Approx (n+1)` peels one (S) step
(the head `ExecS … .normal`) and recurses on the successor node, which is again
in `R`.  Structural on `n`, NOT well-founded. -/
theorem approx_of_stepClosed {R : St → Nat → Addr → List Stmt → Prop}
    (hclosed : StepClosed R) :
    ∀ (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
      R st d env ss → Approx n st d env ss := by
  intro n
  induction n with
  | zero => intro st d env ss _; exact .zero st d env ss
  | succ n ih =>
    intro st d env ss hR
    obtain ⟨st', ss', ⟨s, hcons, hhead⟩, hR'⟩ := hclosed st d env ss hR
    subst hcons
    exact .step n st d env s ss' st' hhead (ih st' d env ss' hR')

/-! ## §3. `BigStepDiverges` from a step-closed spine (UNCONDITIONAL)

Specialize `approx_of_stepClosed` to the top-level program root.  If there is any
step-closed spine predicate `R` containing the root node `(initSt, 0, 0, p)`, the
program diverges.  This is the whole divergence half of the trichotomy, proved
outright — no residual. -/

/-- If a step-closed spine predicate holds at the program root, the program
diverges.  Immediate from `approx_of_stepClosed` at the root, unfolding
`BigStepDiverges p = ∀ n, Approx n initSt 0 0 p`. -/
theorem bigStepDiverges_of_stepClosed {p : Program}
    {R : St → Nat → Addr → List Stmt → Prop} (hclosed : StepClosed R)
    (hroot : R initSt 0 0 p) : BigStepDiverges p :=
  fun n => approx_of_stepClosed hclosed n initSt 0 0 p hroot

/-! ## §4. The trichotomy

Assemble via `Classical.em`.  Let `Spine p st d env ss` mean "this node is
reachable from the root through zero-or-more normal head steps and is not (T) a
terminating node nor (E) an erroring node".  Classically, either the root is a
(T) or (E) node — routed to `BigStep`/`BigStepErr` by the root-classification
residual `hroot` — or it is a `Spine` node, and `NodeDispatch` makes `Spine`
step-closed (the (S) verdict is the only one left at a non-(T)/(E) node), so the
program diverges by `bigStepDiverges_of_stepClosed`.

The step-closedness of `Spine` is exactly the residual `hStepClosed`: it says
"`NodeDispatch`'s (T)/(E)/(S) trichotomy is *exclusive* along the descending
spine — a non-terminating, non-erroring node's successor is again
non-terminating, non-erroring".  That exclusivity is the classical per-node
content the plan attributes to `Classical.em` at each dispatch; we surface it as
a named obligation rather than re-derive the full mutual `exec_stmt`/`eval_expr`
metatheory here. -/

/-! ### The spine predicate

`Spine p` marks the nodes on the root's descending normal-step spine that are
neither (T) terminating nor (E) erroring.  It is generated by the root plus one
`SeqStep`; `NodeDispatch` provides the step, and the *exclusion* residual
`hExclude` provides that the successor is again non-(T)/non-(E) (i.e. still on the
spine). -/

/-- The descending spine of non-terminating, non-erroring nodes reachable from
the root by normal head steps.  `base` seeds the root; `step` extends by one
`SeqStep` into another spine node (the extension guarded by `NodeDispatch` +
`hExclude` in `trichotomy_of_dispatch`). -/
inductive Spine (p : Program) : St → Nat → Addr → List Stmt → Prop where
  | base : Spine p initSt 0 0 p
  | step (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (st' : St)
      (ss' : List Stmt) :
    Spine p st d env ss → SeqStep st d env ss st' ss' →
    Spine p st' d env ss'

/-- **The trichotomy, conditional on the node-dispatch residuals.**  Given

* `hnode : NodeDispatch` — the classical per-node (T)/(E)/(S) dispatch;
* `hroot` — root (T) classification: a root terminating node yields
  `∃ out, BigStep p out` (the top-level `.normal`-status refinement of (T));
* `hExclude` — the spine-exclusion residual: a `Spine` node never fires the (T)
  or (E) verdict (a non-terminating, non-erroring node stays that way along the
  spine), so `NodeDispatch`'s (S) verdict is the only one available and `Spine`
  is step-closed,

every program terminates, errors, or diverges.

The divergence construction is `bigStepDiverges_of_stepClosed`
(via `approx_of_stepClosed`), UNCONDITIONAL: `Spine` is step-closed because at a
`Spine` node `hExclude` rules out (T)/(E) and `hnode` then supplies (S) into a
successor that `Spine.step` records is again on the spine.  The remaining
residuals `hroot`/`hExclude` are exactly the classical `exec_stmt`/`eval_expr`
routing the plan attributes to `Classical.em` at each dispatch. -/
theorem trichotomy_of_dispatch (hnode : NodeDispatch)
    (hroot : ∀ p : Program,
      (∃ st' status, ExecSeq initSt 0 0 p st' status) → ∃ out, BigStep p out)
    (hExclude : ∀ (p : Program) (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
      Spine p st d env ss →
      ¬ (∃ st' status, ExecSeq st d env ss st' status) ∧ ¬ ExecSeqErr st d env ss) :
    Trichotomy := by
  intro p
  by_cases hterm : ∃ st' status, ExecSeq initSt 0 0 p st' status
  · exact Or.inl (hroot p hterm)
  by_cases herr : BigStepErr p
  · exact Or.inr (Or.inl herr)
  · -- `Spine p` is step-closed: at any spine node, exclude (T)/(E) via
    -- `hExclude`, leaving `NodeDispatch`'s (S) verdict, which `Spine.step`
    -- records lands on the spine.
    refine Or.inr (Or.inr (bigStepDiverges_of_stepClosed
      (R := Spine p) ?_ .base))
    intro st d env ss hspine
    obtain ⟨hnoT, hnoE⟩ := hExclude p st d env ss hspine
    rcases hnode st d env ss with hT | hE | hS
    · exact absurd hT hnoT
    · exact absurd hE hnoE
    · obtain ⟨st', ss', hstep⟩ := hS
      exact ⟨st', ss', hstep, .step st d env ss st' ss' hspine hstep⟩

/-! ## §5. The REPAIRED construction (2026-08-31 amendment)

`Vsa/While/StmtDispatch.lean` machine-checked that the §1–§4 construction can
never be instantiated: `hExclude` is unsatisfiable (`Spine.base` seeds every
program's root, including terminating ones), and the pre-amendment `Approx`
could not witness within-statement divergence, making `NodeDispatch`'s three
verdicts non-exhaustive at a diverging loop head.  With the amended `Approx`
(the `head`/`SApprox` fuel family in `Vsa/While/ErrorSem.lean`) both defects
close:

* the dispatch gains a fourth verdict (D) "the head statement is internally
  still-running for every fuel" — making the per-node split honestly exhaustive;
* the spine exclusion is **provable by contraposition**: a non-terminating,
  non-erroring node's (S)-successor is again non-terminating (else
  `ExecSeq.consNormal` would terminate the node) and non-erroring (else
  `ExecSeqErr.tail` would error it).  `hExclude` disappears entirely.

The §1–§4 declarations are kept verbatim (they still compile; `StmtDispatch`'s
falsity witnesses reference their shapes). -/

/-- **The 4-way per-node classical dispatch** — `NodeDispatch` + the (D) verdict
the amendment makes expressible: the head statement diverges in place. -/
def NodeDispatch4 : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
    (∃ st' status, ExecSeq st d env ss st' status) ∨
    ExecSeqErr st d env ss ∨
    (∃ st' ss', SeqStep st d env ss st' ss') ∨
    (∃ s ss', ss = s :: ss' ∧ ∀ n, SApprox n st d env s)

/-- From the 4-way dispatch, every non-terminating, non-erroring node is
`Approx n` for every `n`.  Fuel induction; the exclusion at the (S)-successor is
PROVED by contraposition with `ExecSeq.consNormal`/`ExecSeqErr.tail` — the
content `hExclude` wrongly assumed. -/
theorem approx_of_nodeDispatch4 (hnode : NodeDispatch4) :
    ∀ (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
      ¬ (∃ st' status, ExecSeq st d env ss st' status) →
      ¬ ExecSeqErr st d env ss →
      Approx n st d env ss := by
  intro n
  induction n with
  | zero => intro st d env ss _ _; exact .zero st d env ss
  | succ n ih =>
    intro st d env ss hnoT hnoE
    rcases hnode st d env ss with hT | hE | ⟨st', ss', s, hcons, hhead⟩ |
      ⟨s, ss', hcons, hdiv⟩
    · exact absurd hT hnoT
    · exact absurd hE hnoE
    · subst hcons
      refine .step n st d env s ss' st' hhead (ih st' d env ss' ?_ ?_)
      · rintro ⟨st'', status, hseq⟩
        exact hnoT ⟨st'', status, .consNormal st d env s ss' st' st'' status hhead hseq⟩
      · intro herr
        exact hnoE (.tail st d env s ss' st' hhead herr)
    · subst hcons
      exact .head n st d env s ss' (hdiv n)

/-- **The repaired trichotomy** — conditional on ONLY the 4-way dispatch and the
root (T)-classification.  No exclusion residual: it is proved inside
`approx_of_nodeDispatch4`. -/
theorem trichotomy_of_dispatch4 (hnode : NodeDispatch4)
    (hroot : ∀ p : Program,
      (∃ st' status, ExecSeq initSt 0 0 p st' status) → ∃ out, BigStep p out) :
    Trichotomy := by
  intro p
  by_cases hterm : ∃ st' status, ExecSeq initSt 0 0 p st' status
  · exact Or.inl (hroot p hterm)
  by_cases herr : BigStepErr p
  · exact Or.inr (Or.inl herr)
  · exact Or.inr (Or.inr (fun n =>
      -- `BigStepErr` is now `ExecSeqErr … ∨ TopAbrupt` (`Vsa/While/ErrorSem.lean`);
      -- `approx_of_nodeDispatch4` needs only the `ExecSeqErr` non-error, so lift
      -- `¬ BigStepErr` to `¬ ExecSeqErr` via the `Or.inl` injection.
      approx_of_nodeDispatch4 hnode n initSt 0 0 p hterm
        (fun hseqerr => herr (Or.inl hseqerr))))

/-! ### The per-STATEMENT dispatch atom, and its lift to `NodeDispatch4`

The honest single-statement atom the survey called `StmtDispatch3`: every
statement runs to some status, errors, or diverges in place (`∀ n, SApprox n`).
The lift to sequence nodes is proved: nil terminates; an abrupt head terminates
the node (`consAbrupt`); a normal head is the (S) verdict; an erroring head is
(E) via `ExecSeqErr.head`; a diverging head is (D). -/

/-- The classical per-statement dispatch with the divergence disjunct — the ONE
spec-layer residual of the repaired trichotomy (plus `hroot`). -/
def StmtDispatchD : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (s : Stmt),
    (∃ st' status, ExecS st d env s st' status) ∨
    ExecErr st d env s ∨
    (∀ n, SApprox n st d env s)

theorem nodeDispatch4_of_stmtDispatchD (h : StmtDispatchD) : NodeDispatch4 := by
  intro st d env ss
  cases ss with
  | nil => exact Or.inl ⟨st, .normal, .nil st d env⟩
  | cons s ss' =>
    rcases h st d env s with ⟨st', status, hrun⟩ | herr | hdiv
    · cases status with
      | normal =>
        exact Or.inr (Or.inr (Or.inl ⟨st', ss', s, rfl, hrun⟩))
      | brk =>
        exact Or.inl ⟨st', .brk,
          .consAbrupt st d env s ss' st' .brk hrun (by intro h; cases h)⟩
      | cont =>
        exact Or.inl ⟨st', .cont,
          .consAbrupt st d env s ss' st' .cont hrun (by intro h; cases h)⟩
      | ret v =>
        exact Or.inl ⟨st', .ret v,
          .consAbrupt st d env s ss' st' (.ret v) hrun (by intro h; cases h)⟩
    · exact Or.inr (Or.inl (.head st d env s ss' herr))
    · exact Or.inr (Or.inr (Or.inr ⟨s, ss', rfl, hdiv⟩))

/-- **`Trichotomy` from the per-statement atom** — the final spec-layer
reduction: `htri` rests on exactly `StmtDispatchD` + `hroot`. -/
theorem trichotomy_of_stmtDispatchD (h : StmtDispatchD)
    (hroot : ∀ p : Program,
      (∃ st' status, ExecSeq initSt 0 0 p st' status) → ∃ out, BigStep p out) :
    Trichotomy :=
  trichotomy_of_dispatch4 (nodeDispatch4_of_stmtDispatchD h) hroot

end Vsa.While
