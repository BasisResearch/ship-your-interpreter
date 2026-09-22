import Vsa.MemReprWithin
import Vsa.Sim.MemRegion

namespace Vsa.Sim
open Vsa.MemRepr Vsa.While

/-- Legacy whole-node bounds cover each represented subread. -/
theorem NodeIn.covers {lo hi a off width : Nat} (h : NodeIn lo hi a)
    (hw : off + width ≤ 40) : Covers (regionP lo hi) (a + off) width := by
  intro i hi'
  have hlo := h.lo_le
  have hhi := h.hi_ge
  constructor <;> omega

/-- A legacy pointer-array cell covers its eight-byte read. -/
theorem CellIn.covers {lo hi a : Nat} (h : CellIn lo hi a) :
    Covers (regionP lo hi) a 8 := by
  intro i hi'
  have hlo := h.lo_le
  have hhi := h.hi_ge
  constructor <;> omega

/-- A represented string in a legacy region has hereditary byte coverage. -/
theorem cstringWithin_of_region {m : Mem} {lo hi a : Nat} {s : String}
    (h : CString m a s) (hin : StrIn lo hi a s) :
    CStringWithin m (regionP lo hi) a s := by
  refine ⟨h, ?_⟩
  intro i hi'
  have hlo := hin.lo_le
  have hhi := hin.hi_ge
  constructor <;> omega

local macro "within_region" rec:ident m:ident lo:ident hi:ident h:ident : tactic =>
  `(tactic| (
    apply $rec
      (motive_1 := fun a e _ => ExprIn $m $lo $hi a e →
        ExprReprWithin $m (regionP $lo $hi) a e)
      (motive_2 := fun a n es _ => ExprsIn $m $lo $hi a es →
        ExprArrayReprWithin $m (regionP $lo $hi) a n es)
      (motive_3 := fun a n xs _ => ParamsIn $m $lo $hi a xs →
        ParamsReprWithin $m (regionP $lo $hi) a n xs)
      (motive_4 := fun a s _ => StmtIn $m $lo $hi a s →
        StmtReprWithin $m (regionP $lo $hi) a s)
      (motive_5 := fun a s _ => OptStmtIn $m $lo $hi a s →
        OptStmtReprWithin $m (regionP $lo $hi) a s)
      (motive_6 := fun a e _ => OptExprIn $m $lo $hi a e →
        OptExprReprWithin $m (regionP $lo $hi) a e)
      (motive_7 := fun a n ss _ => StmtsIn $m $lo $hi a ss →
        StmtArrayReprWithin $m (regionP $lo $hi) a n ss)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $h
    all_goals
      try dsimp only
      intros
      simp only [ExprIn, ExprsIn, ParamsIn, StmtIn, OptStmtIn, OptExprIn, StmtsIn] at *
      constructor
      all_goals solve
        | assumption
        | (solve | simp_all)
        | (apply cstringWithin_of_region <;> simp_all)
        | (apply CellIn.covers <;> simp_all)
        | (apply NodeIn.covers (off := 0) <;> first | (solve | simp_all) | decide)
        | (apply NodeIn.covers <;> first | (solve | simp_all) | decide)
  ))

/-- Convert the legacy expression region using its actual representation. -/
theorem exprReprWithin_of_region {m : Mem} {lo hi a : Nat} {e : Expr}
    (h : ExprRepr m a e) : ExprIn m lo hi a e → ExprReprWithin m (regionP lo hi) a e := by
  within_region ExprRepr.rec m lo hi h

/-- Convert the legacy hereditary region using its actual representation. -/
theorem stmtReprWithin_of_region {m : Mem} {lo hi a : Nat} {s : Stmt}
    (h : StmtRepr m a s) :
    StmtIn m lo hi a s → StmtReprWithin m (regionP lo hi) a s := by
  within_region StmtRepr.rec m lo hi h

#print axioms stmtReprWithin_of_region

/-- Convert the legacy hereditary region using its actual representation. -/
theorem exprArrayReprWithin_of_region {m : Mem} {lo hi a : Nat} {n : Nat} {es : List Expr}
    (h : ExprArrayRepr m a n es) :
    ExprsIn m lo hi a es → ExprArrayReprWithin m (regionP lo hi) a n es := by
  within_region ExprArrayRepr.rec m lo hi h

#print axioms exprArrayReprWithin_of_region

/-- Convert the legacy hereditary region using its actual representation. -/
theorem paramsReprWithin_of_region {m : Mem} {lo hi a : Nat} {n : Nat} {xs : List String}
    (h : ParamsRepr m a n xs) :
    ParamsIn m lo hi a xs → ParamsReprWithin m (regionP lo hi) a n xs := by
  within_region ParamsRepr.rec m lo hi h

#print axioms paramsReprWithin_of_region

/-- Convert the legacy hereditary region using its actual representation. -/
theorem optStmtReprWithin_of_region {m : Mem} {lo hi a : Nat} {s : Option Stmt}
    (h : OptStmtRepr m a s) :
    OptStmtIn m lo hi a s → OptStmtReprWithin m (regionP lo hi) a s := by
  within_region OptStmtRepr.rec m lo hi h

#print axioms optStmtReprWithin_of_region

/-- Convert the legacy hereditary region using its actual representation. -/
theorem optExprReprWithin_of_region {m : Mem} {lo hi a : Nat} {e : Option Expr}
    (h : OptExprRepr m a e) :
    OptExprIn m lo hi a e → OptExprReprWithin m (regionP lo hi) a e := by
  within_region OptExprRepr.rec m lo hi h

#print axioms optExprReprWithin_of_region

/-- Convert the legacy hereditary region using its actual representation. -/
theorem stmtArrayReprWithin_of_region {m : Mem} {lo hi a : Nat} {n : Nat} {ss : List Stmt}
    (h : StmtArrayRepr m a n ss) :
    StmtsIn m lo hi a ss → StmtArrayReprWithin m (regionP lo hi) a n ss := by
  within_region StmtArrayRepr.rec m lo hi h

#print axioms stmtArrayReprWithin_of_region

#print axioms NodeIn.covers
#print axioms CellIn.covers
#print axioms cstringWithin_of_region
#print axioms exprReprWithin_of_region
end Vsa.Sim
