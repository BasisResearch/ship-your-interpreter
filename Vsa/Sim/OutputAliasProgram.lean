import Vsa.While.Semantics

/-! Source-only derivation for the output-alias audit. No machine claim. -/

namespace Vsa.While.LoadedOutputAlias

def printLine : Stmt := .expr (.call (.var "println") [])
def condition : Expr := .binary .eq (.str "") (.str "\n")
def program : Program := [printLine, .ifStmt condition printLine none]
def afterFirst : St := ⟨initSt.store, "\n"⟩

theorem first_prints_newline : ExecS initSt 0 0 printLine afterFirst .normal := by
  have hcall : Call initSt 0 (.native .println) [] afterFirst .null := by
    simpa [afterFirst, printArgs, initSt] using (Call.println initSt 0 [])
  apply ExecS.expr initSt 0 0 (.call (.var "println") []) afterFirst .null
  apply EvalE.call initSt 0 0 (.var "println") [] initSt initSt afterFirst
    (.native .println) [] .null
  · exact EvalE.var initSt 0 0 "println" (.native .println) (by decide)
  · decide
  · exact EvalArgs.nil initSt 0 0
  · exact hcall

theorem condition_false : EvalE afterFirst 0 0 condition afterFirst (.bool false) := by
  apply EvalE.binary afterFirst 0 0 .eq (.str "") (.str "\n")
    afterFirst afterFirst (.str "") (.str "\n") (.bool false)
  · exact EvalE.str afterFirst 0 0 ""
  · exact EvalE.str afterFirst 0 0 "\n"
  · decide

theorem program_bigStep : BigStep program "\n" := by
  refine ⟨afterFirst, ?_, rfl⟩
  apply ExecSeq.consNormal initSt 0 0 printLine
    [.ifStmt condition printLine none] afterFirst afterFirst .normal
  · exact first_prints_newline
  · apply ExecSeq.consNormal afterFirst 0 0 (.ifStmt condition printLine none)
      [] afterFirst afterFirst .normal
    · exact ExecS.ifNone afterFirst 0 0 condition printLine afterFirst
        (.bool false) condition_false rfl
    · exact ExecSeq.nil afterFirst 0 0

#print axioms first_prints_newline
#print axioms condition_false
#print axioms program_bigStep

end Vsa.While.LoadedOutputAlias
