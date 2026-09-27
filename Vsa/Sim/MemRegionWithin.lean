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

/-- Convert the legacy hereditary region using its actual representation. -/
theorem stmtReprWithin_of_region {m : Mem} {lo hi a : Nat} {s : Stmt}
    (h : StmtRepr m a s) :
    StmtIn m lo hi a s → StmtReprWithin m (regionP lo hi) a s := by
  within_region StmtRepr.rec m lo hi h

end Vsa.Sim
