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
  ("hEpilogueSpill", 0x800033ec, 0x80003408), ("hInitStore", 0x80004764, 0x800047a0) ]

/-- Splice: the reflected-Steps SMT for a residual's span + a Post-conjunct
validity query.  `postNeg` is the NEGATED post (SAT ⇒ refutable, UNSAT ⇒ valid,
unknown ⇒ needs invariant).  The default is the FRAME conjunct every residual
carries — memory below the stack frame is preserved — but any Post encoded over
`(mm state_exit)` / `(select (rr state_exit) n)` splices the same way. -/
def spliceResidualSmt (lo hi : Nat) (postNeg : String) : IO String := do
  let base ← reflectExactSmt lo hi
  return s!"{base}\n; ---- Pre ∧ ¬Post validity query (Pre trivial here; Post = frame conjunct) ----\n{postNeg}\n(check-sat)\n"

/-- The frame-conjunct negation: some address `A` below the stack frame differs
between entry and exit memory (should be UNSAT — the frame is preserved). -/
def frameNeg : String :=
  "(declare-const A Int)\n(assert (< A (- (select (rr s0) 2) 1000000)))\n(assert (not (= (select (mm state_exit) A) (select (mm s0) A))))"

/-- The GLOBAL summary closure: every `callee_`/`loop_` summary any of the 52
residual spans reaches, transitively.  Each is characterised once by the mined
clause set, then reused by every query that mentions it. -/
def globalSummaries : IO (List String) := do
  let img ← loadElf elfPath
  let mut acc : List String := []
  for (_, lo, hi) in residualSpans do
    let (_, _, _, sums) := reflectExactD img hi 200 lo "s0" 0 [] []
    acc := summaryClosure img sums acc
  return acc

end Vsa.ReflectResiduals

open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#splice_all "<dir>"` — write a per-residual validity SMT (reflected Steps +
frame Post) for every residual; a Python driver runs Z3 (unknown ok on loops). -/
elab "#splice_all " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll dir
    for (nm, lo, hi) in residualSpans do
      let smt ← spliceResidualSmt lo hi frameNeg
      IO.FS.writeFile s!"{dir}/{nm}.smt2" smt
    Lean.logInfo m!"#splice_all → {dir} ({residualSpans.length} residual validity queries)"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_campaign "<dir>"` — write the whole lemma-mode campaign:

* `<dir>/obligations/<sym>.smt2` — one per summary in the global closure: the
  one-step body under the `<sym>_ih` induction hypothesis, with `; @@ASSUME@@`
  and `; @@GOAL@@` injection points;
* `<dir>/queries/<field>.smt2` — one per residual: the span's exit-state DAG
  with summaries left uninterpreted, with `; @@ASSUME@@` and `; @@POST@@`;
* `<dir>/summaries.tsv`, `<dir>/query-summaries.tsv` — which summaries exist and
  which each query depends on (the driver only assumes the relevant ones).

The Houdini driver (`scripts/houdini_summary.py`) fills the injection points and
runs Z3.  Nothing here proves anything; run via `lake env lean`. -/
elab "#emit_campaign " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/queries"
    let img ← loadElf elfPath
    let syms ← globalSummaries
    for sym in syms do
      IO.FS.writeFile s!"{dir}/obligations/{sym}.smt2" (summaryObligationSmt img syms sym)
    let mut rows : List String := []
    for (nm, lo, hi) in residualSpans do
      let (txt, deps) ← lemmaModeSmt lo hi
      IO.FS.writeFile s!"{dir}/queries/{nm}.smt2" txt
      rows := rows ++ [s!"{nm}\t{String.intercalate "," deps}"]
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\n" ++ String.intercalate "\n" syms ++ "\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" rows ++ "\n")
    Lean.logInfo m!"#emit_campaign → {dir} ({syms.length} summaries, {residualSpans.length} queries)"
