import Vsa.While.ErrorSem

namespace Vsa.While

def SeqStep (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (st' : St) (ss' : List Stmt) : Prop :=
  ∃ s, ss = s :: ss' ∧ ExecS st d env s st' .normal

def NodeDispatch4 : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
    (∃ st' status, ExecSeq st d env ss st' status) ∨
    ExecSeqErr st d env ss ∨
    (∃ st' ss', SeqStep st d env ss st' ss') ∨
    (∃ s ss', ss = s :: ss' ∧ ∀ n, SApprox n st d env s)

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

end Vsa.While
