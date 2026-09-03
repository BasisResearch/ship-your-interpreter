import experiments.smt.ReflectSpan

/-!
# Per-residual span map + encodability check

`residualSpans` maps each of the 52 open `TermResidualsCore` residuals to the
concrete `[entry, exit)` code span whose `Steps` it constrains (from the arm
tables: `KindTablePins` for the eval arms, the exec_stmt dispatch for the
statement arms, `seqLoopImage` for the seq loops). Residuals sharing an arm map
to the same span (the per-op sub-dispatch is inside it).

`#check_residuals` reflects every span with `reflectExactD` and reports blocks /
summaries / term size — confirming each is encodable (gap-free, DAG-sized) with
the exact reflector.
-/

open Vsa.ReflectSpan

namespace Vsa.ReflectResiduals

/-- residual → (entry PC, exit PC). -/
def residualSpans : List (String × Nat × Nat) := [
  -- eval arms
  ("hVar",     0x80003434, 0x80003480), ("hAssign",  0x8000347c, 0x80003560),
  -- int/eq → the EX_BINARY arm (per-op sub-dispatch inside)
  ("hIAdd", 0x800034e8, 0x800037c0), ("hISub", 0x800034e8, 0x800037c0),
  ("hIMul", 0x800034e8, 0x800037c0), ("hIDiv", 0x800034e8, 0x800037c0),
  ("hIMod", 0x800034e8, 0x800037c0), ("hILt",  0x800034e8, 0x800037c0),
  ("hILe",  0x800034e8, 0x800037c0), ("hIGt",  0x800034e8, 0x800037c0),
  ("hIGe",  0x800034e8, 0x800037c0), ("hEq",   0x800034e8, 0x800037c0),
  ("hNe",   0x800034e8, 0x800037c0),
  -- str ops → the EX_BINARY arm (str operand path)
  ("hStrAddL", 0x800034e8, 0x800037c0), ("hStrAddR", 0x800034e8, 0x800037c0),
  ("hStrGe", 0x800034e8, 0x800037c0), ("hStrGt", 0x800034e8, 0x800037c0),
  ("hStrLe", 0x800034e8, 0x800037c0), ("hStrLt", 0x800034e8, 0x800037c0),
  -- div arithmetic → the div sub-arm
  ("hDivCorr", 0x800034e8, 0x800037c0), ("hDivOv", 0x800034e8, 0x800037c0),
  -- unary / logical
  ("hNeg", 0x800035e0, 0x80003628), ("hNot", 0x800035e0, 0x80003628),
  ("hAndTrue", 0x8000355c, 0x800035e0), ("hAndFalse", 0x8000355c, 0x800035e0),
  ("hOrTrue", 0x8000355c, 0x800035e0), ("hOrFalse", 0x8000355c, 0x800035e0),
  -- call / composition
  ("hCall", 0x800031b0, 0x80003360), ("hCallClosure", 0x800031b0, 0x80003360),
  ("hArgsCons", 0x800031b0, 0x80003360), ("hArgsNil", 0x800031b0, 0x800031b4),
  ("hCallPrint", 0x800031b0, 0x80003360), ("hCallPrintln", 0x800031b0, 0x80003360),
  ("hCallAssertOk", 0x800031b0, 0x80003360), ("hFn", 0x800033c4, 0x80003408),
  -- statement arms (exec_stmt dispatch 0x80004014)
  ("hSExpr", 0x80004014, 0x800041a4), ("hSBlock", 0x80004014, 0x800041a4),
  ("hSIfTrue", 0x80004014, 0x800041a4), ("hSIfFalse", 0x80004014, 0x800041a4),
  ("hSIfNone", 0x80004014, 0x800041a4), ("hSRet", 0x80004014, 0x800041a4),
  ("hSRetNull", 0x80004014, 0x800041a4), ("hSVarInit", 0x80004014, 0x800041a4),
  ("hSVarNull", 0x80004014, 0x800041a4), ("hSWhileBreak", 0x80004014, 0x800041a4),
  ("hSWhileFalse", 0x80004014, 0x800041a4), ("hSForStart", 0x80004014, 0x800041a4),
  -- seq loops (seqLoopImage)
  ("hSeqNil", 0x8000448c, 0x80004514), ("hSeqConsNormal", 0x8000448c, 0x80004514),
  ("hSeqConsAbrupt", 0x8000448c, 0x80004514),
  -- init / frame
  ("hEpilogueSpill", 0x800033ec, 0x80003408), ("hInitStore", 0x80004764, 0x800047a0),
  ("hFn2", 0x800033c4, 0x80003408) ]

end Vsa.ReflectResiduals

open Vsa.ReflectResiduals Vsa.ReflectSpan in
run_cmd Lean.Elab.Command.liftTermElabM do
  let img ← loadElf elfPath
  let mut ok := 0
  let mut fail := 0
  for (nm, lo, hi) in residualSpans do
    let (ev, _, binds, sums) := reflectExactD img hi 200 lo "s0" 0 [] []
    let sz := (wrapLets binds ev).length
    if sz > 0 && sz < 5000000 then ok := ok + 1
      else fail := fail + 1
    Lean.logInfo m!"{nm}: {binds.length}blk {sums.length}sum {sz}ch"
  Lean.logInfo m!"ENCODABLE: {ok}/{ok+fail} residual spans reflect gap-free + DAG-sized"
