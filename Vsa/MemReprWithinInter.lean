import Vsa.MemReprWithin

/-! Intersection of hereditary read predicates over the same represented graph.
No agreement outside the intersected read footprint is required. -/

namespace Vsa.MemRepr

open Vsa.While

theorem Covers.inter {P Q : Nat → Prop} {a width : Nat}
    (hP : Covers P a width) (hQ : Covers Q a width) :
    Covers (fun k => P k ∧ Q k) a width :=
  fun i hi => ⟨hP i hi, hQ i hi⟩

/-- Intersection covers the string terminator as well as its content. -/
theorem CStringWithin.inter {m : Mem} {P Q : Nat → Prop} {a : Nat} {s : String}
    (hP : CStringWithin m P a s) (hQ : CStringWithin m Q a s) :
    CStringWithin m (fun k => P k ∧ Q k) a s :=
  ⟨hP.1, fun i hi => ⟨hP.2 i hi, hQ.2 i hi⟩⟩

/- The mutual recursor supplies an intersection hypothesis for every child.
Inverting the second representation exposes reads at the same parent fields.
Their equal Option results identify all pointer and count witnesses before
the child hypotheses are applied. -/
local macro "within_inter" rec:ident m:ident P:ident Q:ident h:ident : tactic =>
  `(tactic| (
    apply $rec
      (motive_1 := fun a e _ => ExprReprWithin $m $Q a e →
        ExprReprWithin $m (fun k => $P k ∧ $Q k) a e)
      (motive_2 := fun a n es _ => ExprArrayReprWithin $m $Q a n es →
        ExprArrayReprWithin $m (fun k => $P k ∧ $Q k) a n es)
      (motive_3 := fun a n xs _ => ParamsReprWithin $m $Q a n xs →
        ParamsReprWithin $m (fun k => $P k ∧ $Q k) a n xs)
      (motive_4 := fun a s _ => StmtReprWithin $m $Q a s →
        StmtReprWithin $m (fun k => $P k ∧ $Q k) a s)
      (motive_5 := fun a s _ => OptStmtReprWithin $m $Q a s →
        OptStmtReprWithin $m (fun k => $P k ∧ $Q k) a s)
      (motive_6 := fun a e _ => OptExprReprWithin $m $Q a e →
        OptExprReprWithin $m (fun k => $P k ∧ $Q k) a e)
      (motive_7 := fun a n ss _ => StmtArrayReprWithin $m $Q a n ss →
        StmtArrayReprWithin $m (fun k => $P k ∧ $Q k) a n ss)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $h
    all_goals
      intros
      intro hQ
      cases hQ
      all_goals
        try simp_all only [Option.some.injEq]
        constructor
        all_goals first
          | assumption
          | exact Covers.inter ‹_› ‹_›
          | exact CStringWithin.inter ‹_› ‹_›
          | (apply_assumption <;> trivial)))

theorem ExprReprWithin.inter {m : Mem} {P Q : Nat → Prop} {a : Nat} {e : Expr}
    (hP : ExprReprWithin m P a e) :
    ExprReprWithin m Q a e → ExprReprWithin m (fun k => P k ∧ Q k) a e := by
  within_inter ExprReprWithin.rec m P Q hP

theorem ExprArrayReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a n : Nat} {es : List Expr} (hP : ExprArrayReprWithin m P a n es) :
    ExprArrayReprWithin m Q a n es →
      ExprArrayReprWithin m (fun k => P k ∧ Q k) a n es := by
  within_inter ExprArrayReprWithin.rec m P Q hP

theorem ParamsReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a n : Nat} {xs : List String} (hP : ParamsReprWithin m P a n xs) :
    ParamsReprWithin m Q a n xs → ParamsReprWithin m (fun k => P k ∧ Q k) a n xs := by
  within_inter ParamsReprWithin.rec m P Q hP

theorem StmtReprWithin.inter {m : Mem} {P Q : Nat → Prop} {a : Nat} {s : Stmt}
    (hP : StmtReprWithin m P a s) :
    StmtReprWithin m Q a s → StmtReprWithin m (fun k => P k ∧ Q k) a s := by
  within_inter StmtReprWithin.rec m P Q hP

theorem OptStmtReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a : Nat} {s : Option Stmt} (hP : OptStmtReprWithin m P a s) :
    OptStmtReprWithin m Q a s → OptStmtReprWithin m (fun k => P k ∧ Q k) a s := by
  within_inter OptStmtReprWithin.rec m P Q hP

theorem OptExprReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a : Nat} {e : Option Expr} (hP : OptExprReprWithin m P a e) :
    OptExprReprWithin m Q a e → OptExprReprWithin m (fun k => P k ∧ Q k) a e := by
  within_inter OptExprReprWithin.rec m P Q hP

theorem StmtArrayReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a n : Nat} {ss : List Stmt} (hP : StmtArrayReprWithin m P a n ss) :
    StmtArrayReprWithin m Q a n ss →
      StmtArrayReprWithin m (fun k => P k ∧ Q k) a n ss := by
  within_inter StmtArrayReprWithin.rec m P Q hP

theorem ProgramReprWithin.inter {m : Mem} {P Q : Nat → Prop}
    {a n : Nat} {p : Program}
    (hP : ProgramReprWithin m P a n p) (hQ : ProgramReprWithin m Q a n p) :
    ProgramReprWithin m (fun k => P k ∧ Q k) a n p :=
  ⟨hP.1.inter hQ.1, hP.2⟩

/-- Agreement is needed only where both hereditary read predicates hold. -/
theorem ProgramReprWithin.transport_inter {m m' : Mem} {P Q : Nat → Prop}
    {a n : Nat} {p : Program}
    (hP : ProgramReprWithin m P a n p) (hQ : ProgramReprWithin m Q a n p)
    (hagree : ∀ k, P k ∧ Q k → m[k]? = m'[k]?) :
    ProgramReprWithin m' (fun k => P k ∧ Q k) a n p :=
  (hP.inter hQ).transport hagree

/-- Both predicates survive when the memory frame preserves their intersection. -/
theorem ProgramReprWithin.transport_both {m m' : Mem} {P Q : Nat → Prop}
    {a n : Nat} {p : Program}
    (hP : ProgramReprWithin m P a n p) (hQ : ProgramReprWithin m Q a n p)
    (hagree : ∀ k, P k ∧ Q k → m[k]? = m'[k]?) :
    ProgramReprWithin m' P a n p ∧ ProgramReprWithin m' Q a n p := by
  have h := hP.transport_inter hQ hagree
  exact ⟨h.mono (fun _ hk => hk.1), h.mono (fun _ hk => hk.2)⟩

#print axioms ExprReprWithin.inter
#print axioms StmtArrayReprWithin.inter
#print axioms ProgramReprWithin.inter
#print axioms ProgramReprWithin.transport_inter
#print axioms ProgramReprWithin.transport_both

end Vsa.MemRepr
