import Vsa.Sim.NativeNameAudit.AstReads

namespace Vsa.Sim.NativeNameAudit

open Vsa.MemRepr Vsa.While Vsa.Sim.OutputAliasLoaded
open Vsa.While.LoadedOutputAlias
open Vsa.Sim.LayoutInstance

def nativeNameProgram : Program := [printLine, printLine]
def afterBoth : Vsa.While.St := ⟨initSt.store, "\n\n"⟩

theorem nativeName_bigStep : BigStep nativeNameProgram "\n\n" := by
  have hcall : Call afterFirst 0 (.native .println) [] afterBoth .null := by
    simpa [afterFirst, afterBoth, printArgs, initSt] using (Call.println afterFirst 0 [])
  have hsecond : ExecS afterFirst 0 0 printLine afterBoth .normal := by
    apply ExecS.expr afterFirst 0 0 (.call (.var "println") []) afterBoth .null
    apply EvalE.call afterFirst 0 0 (.var "println") [] afterFirst afterFirst afterBoth
      (.native .println) [] .null
    · exact EvalE.var afterFirst 0 0 "println" (.native .println) (by decide)
    · decide
    · exact EvalArgs.nil afterFirst 0 0
    · exact hcall
  refine ⟨afterBoth, ?_, rfl⟩
  exact ExecSeq.consNormal initSt 0 0 printLine [printLine] afterFirst afterBoth .normal
    first_prints_newline (ExecSeq.consNormal afterFirst 0 0 printLine [] afterBoth afterBoth
      .normal hsecond (ExecSeq.nil afterBoth 0 0))

local macro "name_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, nativeName_lookup]; decide))

theorem array0 : read64 nativeNameMem 0x82000000 = some 0x82000020 := by name_read
theorem array1 : read64 nativeNameMem 0x82000008 = some 0x82000020 := by name_read
theorem stmtTag : read32 nativeNameMem 0x82000020 = some 0 := by name_read
theorem stmtExpr : read64 nativeNameMem 0x82000028 = some 0x82000080 := by name_read
theorem callTag : read32 nativeNameMem 0x82000080 = some 9 := by name_read
theorem callCallee : read64 nativeNameMem 0x82000088 = some 0x820000a0 := by name_read
theorem callArgs : read64 nativeNameMem 0x82000090 = some 0 := by name_read
theorem callArgc : read32 nativeNameMem 0x82000098 = some 0 := by name_read
theorem varTag : read32 nativeNameMem 0x820000a0 = some 4 := by name_read
theorem varName : read64 nativeNameMem 0x820000a8 = some 0x820000c0 := by name_read

theorem astName : CString nativeNameMem 0x820000c0 "println" := by
  refine ⟨['p', 'r', 'i', 'n', 't', 'l', 'n'], ?_, rfl⟩
  exact CStr.cons (b := 112#8) (by name_read) (by decide) (by decide)
    (CStr.cons (b := 114#8) (by name_read) (by decide) (by decide)
      (CStr.cons (b := 105#8) (by name_read) (by decide) (by decide)
        (CStr.cons (b := 110#8) (by name_read) (by decide) (by decide)
          (CStr.cons (b := 116#8) (by name_read) (by decide) (by decide)
            (CStr.cons (b := 108#8) (by name_read) (by decide) (by decide)
              (CStr.cons (b := 110#8) (by name_read) (by decide) (by decide)
                (CStr.nil (by name_read))))))))

theorem astReads : AstReads nativeNameMem where
  array0 := array0
  array1 := array1
  stmtTag := stmtTag
  stmtExpr := stmtExpr
  callTag := callTag
  callCallee := callCallee
  callArgs := callArgs
  callArgc := callArgc
  varTag := varTag
  varName := varName
  astName := astName

theorem astNameWithin : CStringWithin nativeNameMem AstPage 0x820000c0 "println" :=
  astReads.astNameWithin

theorem varWithin : ExprReprWithin nativeNameMem AstPage 0x820000a0 (.var "println") :=
  astReads.varWithin

theorem callWithin : ExprReprWithin nativeNameMem AstPage 0x82000080
    (.call (.var "println") []) :=
  astReads.callWithin

theorem stmtWithin : StmtReprWithin nativeNameMem AstPage 0x82000020 printLine :=
  astReads.stmtWithin

theorem programWithin : ProgramReprWithin nativeNameMem AstPage 0x82000000 2
    nativeNameProgram :=
  astReads.programWithin

theorem astName_unique {s : String} (h : CString nativeNameMem 0x820000c0 s) :
    s = "println" :=
  astReads.astName_unique h

theorem var_unique {e : Expr} (h : ExprRepr nativeNameMem 0x820000a0 e) :
    e = .var "println" :=
  astReads.var_unique h

theorem call_unique {e : Expr} (h : ExprRepr nativeNameMem 0x82000080 e) :
    e = .call (.var "println") [] :=
  astReads.call_unique h

theorem stmt_unique {s : Stmt} (h : StmtRepr nativeNameMem 0x82000020 s) :
    s = printLine :=
  astReads.stmt_unique h

theorem program_unique {p : Program} (h : ProgramRepr nativeNameMem 0x82000000 2 p) :
    p = nativeNameProgram :=
  astReads.program_unique h

theorem astPage_owned {k : Nat} (hk : AstPage k) :
    ¬ LayoutInstance.AstMutableByte nativeNameMem arena (phif 0) k := by
  have hcap : read32 nativeNameMem 0x81000004 = some 8 := by name_read
  have hnames : read64 nativeNameMem 0x81000008 = some 0x81000040 := by name_read
  have hvalues : read64 nativeNameMem 0x81000010 = some 0x81000080 := by name_read
  intro hm
  unfold AstPage at hk
  change Vsa.Sim.AstMutableByte nativeNameMem stackSL arena 0x81000000 k at hm
  rcases hm with he | hs | ha | hh | ⟨cap, names, hc, hn, hw⟩ |
    ⟨cap, values, hc, hv, hw⟩
  · omega
  · change 0x87800000 ≤ k ∧ k < 0x88000000 at hs
    omega
  · change 0x81000000 ≤ k ∧ k < 0x81001000 at ha
    omega
  · change 0x81000000 ≤ k ∧ k < 0x81000000 + 32 at hh
    omega
  · have hc' := Option.some.inj (hc.symm.trans hcap)
    have hn' := Option.some.inj (hn.symm.trans hnames)
    subst cap
    subst names
    change 0x81000040 ≤ k ∧ k < 0x81000040 + 8 * 8 at hw
    omega
  · have hc' := Option.some.inj (hc.symm.trans hcap)
    have hv' := Option.some.inj (hv.symm.trans hvalues)
    subst cap
    subst values
    change 0x81000080 ≤ k ∧ k < 0x81000080 + 24 * 8 at hw
    omega

theorem nativeName_ast_owned (p : Program) (h : ProgramRepr nativeNameMem 0x82000000 2 p) :
    ProgramReprWithin nativeNameMem
      (fun k => ¬ LayoutInstance.AstMutableByte nativeNameMem arena (phif 0) k)
      0x82000000 2 p := by
  rw [program_unique h]
  exact programWithin.mono (fun _ hk => astPage_owned hk)

theorem nativeName_ast_readable (p : Program) (h : ProgramRepr nativeNameMem 0x82000000 2 p) :
    ProgramReprWithin nativeNameMem (fun k => 0x80000000 ≤ k ∧ k < 0x100000000)
      0x82000000 2 p := by
  rw [program_unique h]
  exact programWithin.mono (by intro k hk; unfold AstPage at hk; omega)

#print axioms nativeName_bigStep
#print axioms program_unique
#print axioms nativeName_ast_owned
#print axioms nativeName_ast_readable

end Vsa.Sim.NativeNameAudit
