import Vsa.While.StackNeed

/-!
# Preservation of bounded closure bodies

Execution preserves `StoreBodiesBound`.  The proof follows the nine-way
mutual semantics recursor because expression evaluation, calls, statements,
and loop auxiliaries can invoke one another.
-/

namespace Vsa.While

private theorem StoreBodiesBound.of_closures_eq {s s' : Store} {P : Nat}
    (h : s'.closures = s.closures) (hs : StoreBodiesBound s P) :
    StoreBodiesBound s' P := by
  intro a cd ha
  apply hs a cd
  simpa [h] using ha

private theorem StoreBodiesBound.allocFrame {s s' : Store} {p : Option Addr}
    {a P : Nat} (h : s.allocFrame p = (s', a))
    (hs : StoreBodiesBound s P) : StoreBodiesBound s' P := by
  apply StoreBodiesBound.of_closures_eq (s := s) (s' := s') _ hs
  simpa [Store.allocFrame] using (congrArg (fun x => x.1.closures) h).symm

private theorem StoreBodiesBound.define {s : Store} {a : Addr} {x : String}
    {v : Value} {P : Nat} (hs : StoreBodiesBound s P) :
    StoreBodiesBound (s.define a x v) P :=
  StoreBodiesBound.of_closures_eq rfl hs

private theorem StoreBodiesBound.foldDefine {s : Store} {a : Addr}
    {xs : List (String × Value)} {P : Nat} (hs : StoreBodiesBound s P) :
    StoreBodiesBound
      (xs.foldl (fun store xv => store.define a xv.1 xv.2) s) P := by
  induction xs generalizing s with
  | nil => exact hs
  | cons xv xs ih =>
      simp only [List.foldl_cons]
      exact ih (StoreBodiesBound.define hs)

private theorem set_closures_eq : ∀ gas (s s' : Store) a x v,
    s.set gas a x v = some s' → s'.closures = s.closures := by
  intro gas
  induction gas with
  | zero =>
      intro s s' a x v h
      simp [Store.set] at h
  | succ gas ih =>
      intro s s' a x v h
      unfold Store.set at h
      cases hframe : s.frames[a]? with
      | none => simp [hframe] at h
      | some frame =>
          rw [hframe] at h
          simp only [bind, Option.bind] at h
          by_cases hhas : frame.vars.any (fun xv => xv.1 == x)
          · rw [if_pos hhas] at h
            injection h with h
            subst s'
            rfl
          · rw [if_neg hhas] at h
            cases hparent : frame.parent with
            | none => simp [hparent] at h
            | some parent =>
                rw [hparent] at h
                exact ih s s' parent x v h

private theorem StoreBodiesBound.set {s s' : Store} {a : Addr} {x : String}
    {v : Value} {P : Nat} (h : s.set? a x v = some s')
    (hs : StoreBodiesBound s P) : StoreBodiesBound s' P :=
  StoreBodiesBound.of_closures_eq (set_closures_eq _ _ _ _ _ _ h) hs

private theorem StoreBodiesBound.allocClosure {s s' : Store}
    {cd : ClosureData} {a P : Nat} (h : s.allocClosure cd = (s', a))
    (hcd : Stmt.stackNeedList cd.body ≤ P ∧
      Stmt.bodiesBoundList P cd.body = true)
    (hs : StoreBodiesBound s P) : StoreBodiesBound s' P := by
  have hs' : s' = { s with closures := s.closures.push cd } := by
    simpa [Store.allocClosure] using (congrArg Prod.fst h).symm
  subst s'
  intro i cd' hi
  obtain ⟨hib, hget⟩ := Array.getElem?_eq_some_iff.mp hi
  by_cases hil : i < s.closures.size
  · apply hs i cd'
    apply Array.getElem?_eq_some_iff.mpr
    refine ⟨hil, ?_⟩
    rw [← Array.getElem_push_lt (h := hil)]
    exact hget
  · have hieq : i = s.closures.size := by
      simp only [Array.size_push] at hib
      omega
    subst i
    have heq : cd = cd' := by
      rw [Array.getElem_push_eq] at hget
      exact hget
    simpa [heq] using hcd

private theorem Stmt.bodiesBound_if_then {P : Nat} {c : Expr} {t : Stmt}
    {e : Option Stmt} (h : (Stmt.ifStmt c t e).bodiesBound P = true) :
    t.bodiesBound P = true := by
  cases e <;> simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
  · exact h.2
  · exact h.1.2

private theorem StoreBodiesBound.callClosure {P : Nat} {s store' : Store}
    {a frame : Addr} {cd : ClosureData} {vs : List Value} {st' : St}
    (hget : s.closures[a]? = some cd)
    (halloc : s.allocFrame (some cd.env) = (store', frame))
    (ih : Stmt.bodiesBoundList P cd.body = true →
      StoreBodiesBound
        ((cd.params.zip vs).foldl
          (fun store xv => store.define frame xv.1 xv.2) store') P →
      StoreBodiesBound st'.store P)
    (hs : StoreBodiesBound s P) : StoreBodiesBound st'.store P := by
  have hbody := (hs a cd hget).2
  apply ih hbody
  exact StoreBodiesBound.foldDefine (StoreBodiesBound.allocFrame halloc hs)

private theorem StoreBodiesBound.ifTrue {P : Nat} {s s' : Store}
    {c : Expr} {t : Stmt} {e : Option Stmt}
    (hc : c.bodiesBound P = true → StoreBodiesBound s' P)
    (ht : t.bodiesBound P = true → StoreBodiesBound s' P → StoreBodiesBound s P)
    (h : (Stmt.ifStmt c t e).bodiesBound P = true) : StoreBodiesBound s P :=
  ht (Stmt.bodiesBound_if_then h) (hc (by
    cases e <;> simp_all [Stmt.bodiesBound]))

private theorem StoreBodiesBound.allocThen2 {P : Nat} {s s' t u : Store}
    {p : Option Addr} {a : Addr} (halloc : s.allocFrame p = (s', a))
    (h₁ : StoreBodiesBound s' P → StoreBodiesBound t P)
    (h₂ : StoreBodiesBound t P → StoreBodiesBound u P)
    (hs : StoreBodiesBound s P) : StoreBodiesBound u P :=
  h₂ (h₁ (StoreBodiesBound.allocFrame halloc hs))

private def EvalEMotive (P : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr)
    (st' : St) (v : Value) (_ : EvalE st d env e st' v) : Prop :=
  e.bodiesBound P = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def EvalArgsMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (es : List Expr) (st' : St) (vs : List Value)
    (_ : EvalArgs st d env es st' vs) : Prop :=
  Expr.bodiesBoundList P es = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def CallMotive (P : Nat) (st : St) (d : Nat) (fv : Value)
    (vs : List Value) (st' : St) (v : Value) (_ : Call st d fv vs st' v) : Prop :=
  StoreBodiesBound st.store P → StoreBodiesBound st'.store P

private def ExecSMotive (P : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt)
    (st' : St) (status : Status) (_ : ExecS st d env s st' status) : Prop :=
  s.bodiesBound P = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def ExecInitMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (init : Option Stmt) (st' : St) (_ : ExecInit st d env init st') : Prop :=
  Stmt.bodiesBoundOpt P init = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def ForLoopMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (cnd step : Option Expr) (body : Stmt) (st' : St) (status : Status)
    (_ : ForLoop st d env cnd step body st' status) : Prop :=
  Expr.bodiesBoundOpt P cnd = true →
  Expr.bodiesBoundOpt P step = true →
  body.bodiesBound P = true →
  StoreBodiesBound st.store P → StoreBodiesBound st'.store P

private def ForCondMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (cnd : Option Expr) (st' : St) (_ : ForCond st d env cnd st') : Prop :=
  Expr.bodiesBoundOpt P cnd = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def ExecStepMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (step : Option Expr) (st' : St) (_ : ExecStep st d env step st') : Prop :=
  Expr.bodiesBoundOpt P step = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

private def ExecSeqMotive (P : Nat) (st : St) (d : Nat) (env : Addr)
    (ss : List Stmt) (st' : St) (status : Status)
    (_ : ExecSeq st d env ss st' status) : Prop :=
  Stmt.bodiesBoundList P ss = true → StoreBodiesBound st.store P →
    StoreBodiesBound st'.store P

/-- Executing a bounded statement preserves boundedness of every closure body
stored in the resulting state. -/
theorem StoreBodiesBound.afterExecS {P : Nat} {st st' : St} {d : Nat}
    {env : Addr} {s : Stmt} {status : Status}
    (hExec : ExecS st d env s st' status)
    (hStmt : Stmt.bodiesBound P s = true)
    (hStore : StoreBodiesBound st.store P) :
    StoreBodiesBound st'.store P := by
  refine ExecS.rec
    (motive_1 := EvalEMotive P)
    (motive_2 := EvalArgsMotive P)
    (motive_3 := CallMotive P)
    (motive_4 := ExecSMotive P)
    (motive_5 := ExecInitMotive P)
    (motive_6 := ForLoopMotive P)
    (motive_7 := ForCondMotive P)
    (motive_8 := ExecStepMotive P)
    (motive_9 := ExecSeqMotive P)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hExec hStmt hStore
  all_goals intros
  all_goals
    simp_all only [EvalEMotive, EvalArgsMotive, CallMotive, ExecSMotive,
      ExecInitMotive, ForLoopMotive, ForCondMotive, ExecStepMotive,
      ExecSeqMotive, Expr.bodiesBound, Expr.bodiesBoundList,
      Expr.bodiesBoundOpt, Stmt.bodiesBound, Stmt.bodiesBoundList,
      Stmt.bodiesBoundOpt, Bool.and_eq_true]
  all_goals intros
  all_goals simp_all
  all_goals
    first
    | assumption
    | (apply StoreBodiesBound.callClosure <;> assumption)
    | (apply StoreBodiesBound.ifTrue <;> assumption)
    | (apply StoreBodiesBound.allocThen2 <;> assumption)
    | solve_by_elim (maxDepth := 5)
      [StoreBodiesBound.allocFrame, StoreBodiesBound.allocClosure,
       StoreBodiesBound.define, StoreBodiesBound.foldDefine, StoreBodiesBound.set,
       Stmt.bodiesBound_if_then, of_decide_eq_true]

#print axioms StoreBodiesBound.afterExecS

end Vsa.While
