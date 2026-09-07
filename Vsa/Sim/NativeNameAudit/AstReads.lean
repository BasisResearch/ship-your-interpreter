import Vsa.Sim.NativeNameAudit.Memory
import Vsa.MemReprWithin
import Vsa.Sim.EnvGetSpec9

namespace Vsa.Sim.NativeNameAudit
open Vsa.MemRepr Vsa.While Vsa.While.LoadedOutputAlias

def AstPage (k : Nat) : Prop := 0x82000000 ≤ k ∧ k < 0x82000100

/-- Finite AST reads shared by the alias regression and its repaired control. -/
structure AstReads (m : Mem) : Prop where
  array0 : read64 m 0x82000000 = some 0x82000020
  array1 : read64 m 0x82000008 = some 0x82000020
  stmtTag : read32 m 0x82000020 = some 0
  stmtExpr : read64 m 0x82000028 = some 0x82000080
  callTag : read32 m 0x82000080 = some 9
  callCallee : read64 m 0x82000088 = some 0x820000a0
  callArgs : read64 m 0x82000090 = some 0
  callArgc : read32 m 0x82000098 = some 0
  varTag : read32 m 0x820000a0 = some 4
  varName : read64 m 0x820000a8 = some 0x820000c0
  astName : CString m 0x820000c0 "println"

namespace AstReads
variable {m : Mem} (v : AstReads m)
include v

theorem astNameWithin : CStringWithin m AstPage 0x820000c0 "println" := by
  refine ⟨v.astName, ?_⟩
  intro i hi
  change i ≤ 7 at hi
  unfold AstPage
  omega

theorem varWithin : ExprReprWithin m AstPage 0x820000a0 (.var "println") := by
  apply ExprReprWithin.var v.varTag _ v.varName _ v.astNameWithin
  all_goals intro i hi; unfold AstPage; omega

theorem callWithin : ExprReprWithin m AstPage 0x82000080
    (.call (.var "println") []) := by
  apply ExprReprWithin.call v.callTag _ v.callCallee _ v.varWithin v.callArgs _ v.callArgc _
    (by decide) ExprArrayReprWithin.nil
  all_goals intro i hi; unfold AstPage; omega

theorem stmtWithin : StmtReprWithin m AstPage 0x82000020 printLine := by
  apply StmtReprWithin.expr v.stmtTag _ v.stmtExpr _ v.callWithin
  all_goals intro i hi; unfold AstPage; omega

theorem programWithin : ProgramReprWithin m AstPage 0x82000000 2
    [printLine, printLine] := by
  refine ⟨StmtArrayReprWithin.cons v.array0 ?_ v.stmtWithin
    (StmtArrayReprWithin.cons v.array1 ?_ v.stmtWithin StmtArrayReprWithin.nil), rfl⟩
  all_goals intro i hi; unfold AstPage; omega

theorem astName_unique {s : String} (h : CString m 0x820000c0 s) :
    s = "println" := by
  obtain ⟨cs, hc, hs⟩ := h
  obtain ⟨cs', hc', hs'⟩ := v.astName
  rw [cstr_unique_eg9 _ _ _ _ hc hc'] at hs
  exact hs.trans hs'.symm

theorem var_unique {e : Expr} (h : ExprRepr m 0x820000a0 e) :
    e = .var "println" := by
  cases h <;> simp_all [v.varTag, v.varName]
  all_goals subst_vars; congr 1; apply v.astName_unique; assumption

theorem call_unique {e : Expr} (h : ExprRepr m 0x82000080 e) :
    e = .call (.var "println") [] := by
  cases h with
  | call ht hf hc ha hn hb hes =>
    have hfp := Option.some.inj (hf.symm.trans v.callCallee)
    have hap := Option.some.inj (ha.symm.trans v.callArgs)
    have hnp := Option.some.inj (hn.symm.trans v.callArgc)
    rw [hfp] at hc
    rw [hap, hnp] at hes
    have he := v.var_unique hc
    cases hes
    simp [he]
  | _ => simp_all [v.callTag]

theorem stmt_unique {s : Stmt} (h : StmtRepr m 0x82000020 s) :
    s = printLine := by
  unfold printLine
  cases h <;> simp_all [v.stmtTag, v.stmtExpr]
  all_goals subst_vars; congr 1; apply v.call_unique; assumption

theorem program_unique {p : Program} (h : ProgramRepr m 0x82000000 2 p) :
    p = [printLine, printLine] := by
  cases h.1 with
  | cons hp hs ht =>
    have hptr := Option.some.inj (hp.symm.trans v.array0)
    rw [hptr] at hs
    have hfirst := v.stmt_unique hs
    cases ht with
    | cons hp hs ht =>
      have hptr := Option.some.inj (hp.symm.trans v.array1)
      rw [hptr] at hs
      have hsecond := v.stmt_unique hs
      cases ht
      simp_all

#print axioms programWithin
#print axioms program_unique
end AstReads
end Vsa.Sim.NativeNameAudit
