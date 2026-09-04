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
  -- The `var` and `assign` arms do NOT tail into the shared epilogue at
  -- 0x800033ec: both end at eval_expr's SECOND epilogue, 0x80003448 (`ld a3,
  -- 240(sp)` … `ret` at 0x80003478) — `var` by falling through the `env_get`
  -- success test at 0x80003444, `assign` by `bnez a0, 0x80003448` after
  -- `env_set`.  The declared stops were 0x80003480 and 0x80003560, which are
  -- the SECOND INSTRUCTION of the next arm and of the logical arm: not
  -- reachable from these arms at all.  Measured, not guessed — `hAssign`'s arm
  -- runs 226 times over the difftest corpus and reaches 0x80003560 zero times
  -- (`scripts/difftest.sh` phase 1), and the query's dispatch pin and exit guard
  -- are contradictory, so every post came back VALID until the vacuity gate
  -- landed and then VACUOUS.
  ("hVar",     0x80003434, 0x80003448), ("hAssign",  0x8000347c, 0x80003448),
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
  -- The unary arm ENDS at 0x80003624 with `jal x0, 0x800033ec`, handing off to
  -- the shared epilogue; 0x80003628 (`addi x15,x10,-3`) is the next arm's code
  -- and is never reached from here.  Demanding it as the exit made these two
  -- queries' assumptions contradictory, so every post came back VALID.
  ("hNeg", 0x800035e0, 0x800033ec), ("hNot", 0x800035e0, 0x800033ec),
  -- Same defect as `hNeg`/`hNot` above, in the same shape and never fixed for
  -- these four: the logical arm ENDS at 0x800035dc with `j 0x800033ec`, and
  -- 0x800035e0 is the UNARY arm's first instruction, which no execution of the
  -- logical arm reaches (13 arm runs, 0 arrivals, over the difftest corpus).
  ("hAndTrue", 0x8000355c, 0x800033ec), ("hAndFalse", 0x8000355c, 0x800033ec),
  ("hOrTrue", 0x8000355c, 0x800033ec), ("hOrFalse", 0x8000355c, 0x800033ec),
  -- call / composition
  ("hCall", 0x800031b0, 0x80003360), ("hCallClosure", 0x800031b0, 0x80003360),
  ("hArgsCons", 0x800031b0, 0x80003360), ("hArgsNil", 0x800031b0, 0x800031b4),
  ("hCallPrint", 0x800031b0, 0x80003360), ("hCallPrintln", 0x800031b0, 0x80003360),
  ("hCallAssertOk", 0x800031b0, 0x80003360), ("hFn", 0x800033c4, 0x80003408),
  -- statement arms.  Each residual is about ONE `exec_stmt` arm, so its span is
  -- that arm's own `[execArm*, exec_stmt end)` — NOT the shared dispatch header
  -- `[0x80004014, …)`, which ends at the computed goto `jalr x0, 0(a5)` after
  -- seven instructions and reflects a stub (the old spans' "VALID" frame verdicts
  -- were verdicts about that stub).  The arm PCs are the ELF jump table's, and
  -- coincide with the proof's `Vsa.Sim.execArm*` constants.
  ("hSExpr", 0x80004170, 0x800043ec), ("hSBlock", 0x8000418c, 0x800043ec),
  ("hSIfTrue", 0x800041e8, 0x800043ec), ("hSIfFalse", 0x800041e8, 0x800043ec),
  ("hSIfNone", 0x800041e8, 0x800043ec), ("hSRet", 0x80004120, 0x800043ec),
  ("hSRetNull", 0x80004120, 0x800043ec), ("hSVarInit", 0x800040d8, 0x800043ec),
  ("hSVarNull", 0x800040d8, 0x800043ec), ("hSWhileBreak", 0x8000403c, 0x800043ec),
  ("hSWhileFalse", 0x8000403c, 0x800043ec), ("hSForStart", 0x80004234, 0x800043ec),
  -- seq loops (seqLoopImage)
  ("hSeqNil", 0x8000448c, 0x80004514), ("hSeqConsNormal", 0x8000448c, 0x80004514),
  ("hSeqConsAbrupt", 0x8000448c, 0x80004514),
  -- init / frame
  ("hEpilogueSpill", 0x800033ec, 0x80003408),
  -- `hInitStore` is `InterpInitStoreRepr` (`Vsa/Sim/EntrySeams.lean:182`): the
  -- drive from a `Loaded` config to `SegEntry` at `interpLoopHeadPC`.  That is
  -- `interp_run`'s prologue, `0x800043ec` (the `interp_run` symbol) through
  -- `0x8000448c` (`EntryHalts.lean:117`'s `interpLoopHeadPC`, which is also
  -- where the three `hSeq*` spans are entered).  It was mapped to
  -- `(0x80004764, 0x800047a0)` -- `exit` -- which is a different function
  -- entirely; with the noreturn model that span has NO exit arrival at all and
  -- is caught by the no-exit guard rather than answered against the entry state.
  ("hInitStore", 0x800043ec, 0x8000448c) ]

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
    IO.FS.createDirAll s!"{dir}/writes"
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
    -- per-summary immediate dependencies: the driver only re-checks a summary
    -- when one of the summaries its body applies has lost a clause.
    let depRows := syms.map (fun s => s!"{s}\t{String.intercalate "," (summaryDeps img s)}")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv" ("summary\tdeps\n" ++ String.intercalate "\n" depRows ++ "\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" rows ++ "\n")
    Lean.logInfo m!"#emit_campaign → {dir} ({syms.length} summaries, {residualSpans.length} queries)"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_machine "<dir>" <lo> <hi>` — the PC-THREADED campaign over the code
region `[lo,hi)`: one shared `mstep`/`mrun` pair and one query per residual.

* `<dir>/machine.smt2` — preamble + summary declarations + `mstep` + `mrun`;
* `<dir>/obligations/mrun.smt2` — the one-step `mrun` obligation under `mrun_ih`;
* `<dir>/queries/<field>.smt2` — `pc s0 = <entry>`, `STOP = <exit>`,
  `state_exit = (mrun s0)`, with `; @@ASSUME@@` / `; @@POST@@`;
* `<dir>/summaries.tsv`, `<dir>/unmodelled.tsv` — the out-of-region callee
  summaries, and every PC whose register effect is over-approximated.

Every residual whose span lies in `[lo,hi)` reflects with NO control-flow
analysis: computed gotos, shared epilogues, multi-exit loops and the
`eval_expr`↔`exec_stmt` recursion are all just PC values. -/
elab "#emit_machine " pathStx:str loStx:num hiStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    let lo := loStx.getNat
    let hi := hiStx.getNat
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/writes"
    IO.FS.createDirAll s!"{dir}/queries"
    IO.FS.createDirAll s!"{dir}/bounded"
    let img ← loadElf elfPath
    let (machine, sums, bad) := machineSmt img lo hi
    let decls := summaryDecls sums
    let unmodelledDecls := "(declare-fun unmodelled_step (MState) MState)"
    let pre := s!"{smtPreamble}\n{decls}\n{unmodelledDecls}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n{machine}"
    IO.FS.writeFile s!"{dir}/machine.smt2" (pre ++ "\n")
    -- the `mrun` induction obligation: `mrun` itself is NOT axiomatised here;
    -- the recursive occurrence is the free `mrun_ih`.
    let preNoRun := s!"{smtPreamble}\n{decls}\n{unmodelledDecls}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const STOP (_ BitVec 64))\n(declare-fun mrun_ih (MState) MState)"
    let stepOnly := (machine.splitOn "\n(declare-const STOP Int)").headD machine
    IO.FS.writeFile s!"{dir}/obligations/mrun.smt2"
      s!"{preNoRun}\n{stepOnly}\n(declare-const S0 MState)\n(define-fun fbody () MState {machineRunBody lo hi "S0"})\n; @@ASSUME@@\n; @@GOAL@@\n"
    let mut rows : List String := []
    for (nm, elo, ehi) in residualSpans do
      if lo ≤ elo && elo < hi then
        IO.FS.writeFile s!"{dir}/queries/{nm}.smt2"
          s!"{pre}\n(declare-const s0 MState)\n(assert (= {stPC "s0"} {bvN elo}))\n(assert (= STOP {bvN ehi}))\n; @@ASSUME@@\n(define-fun state_exit () MState (mrun s0))\n(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))\n; @@POST@@\n"
        -- BOUNDED companion: `mstep` unrolled `k` times with an explicit
        -- "the span actually finished" conjunct.  A SAT model here is a GENUINE
        -- countermodel (the run reached `STOP` inside `k` steps, so the unrolling
        -- is exact on it); an UNSAT is bounded validity, reported as such.
        IO.FS.writeFile s!"{dir}/bounded/{nm}.smt2"
          s!"{pre}\n(declare-const s0 MState)\n(assert (= {stPC "s0"} {bvN elo}))\n(assert (= STOP {bvN ehi}))\n; @@ASSUME@@\n; @@EXIT@@\n(assert (= {stPC "state_exit"} {bvN ehi}))\n; @@POST@@\n"
      rows := rows ++ [s!"{nm}\tmrun"]
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\nmrun\n")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv" ("summary\tdeps\nmrun\tmrun\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" rows ++ "\n")
    IO.FS.writeFile s!"{dir}/unmodelled.tsv"
      ("pc\n" ++ String.intercalate "\n" (bad.map toString) ++ "\n")
    Lean.logInfo m!"#emit_machine [{lo},{hi}) → {dir}: {(hi-lo)/4} instrs, {sums.length} out-of-region callee summaries, {bad.length} unmodelled PCs, {rows.length} queries"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_bmc "<dir>" <rounds>` — the BOUNDED-SYMBOLIC-EXECUTION campaign.

Per residual: the span's REGION is its enclosing function (bounded by the image's
`jal ra` target set), the STOP is the residual's declared exit PC, and the
frontier is merged by PC every round.  Writes

* `<dir>/queries/<field>.smt2` — `state_exit` as the guarded merge of every exit
  arrival, with `; @@ASSUME@@` / `; @@POST@@` for the driver;
* `<dir>/obligations/<sym>.smt2` — one per callee/loop/opaque summary reached;
* `<dir>/spans.tsv` — per residual: region, stop, rounds used, whether the
  frontier EMPTIED (`complete`, so the encoding is exact for this span), term
  size and summary count.  A residual is only ever reported VALID when its span
  is complete; otherwise its verdict is a BOUNDED one. -/
elab "#emit_bmc " pathStx:str roundsStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    let rounds := roundsStx.getNat
    IO.FS.createDirAll s!"{dir}/queries"
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/writes"
    IO.FS.createDirAll s!"{dir}/halts"
    let img ← loadElf elfPath
    let codeLo := 0x80000000
    let codeHi := 0x80018be0
    let starts := funcStarts img codeLo codeHi
    -- the image's writable static region, named as ground constants so the
    -- memory clauses can exempt it (see `writableRegion`).
    let (gLo, gHi) ← writableRegion elfPath
    let gDecl := s!"(define-fun G_lo () (_ BitVec 64) {bvN gLo})\n(define-fun G_hi () (_ BitVec 64) {bvN gHi})"
    -- the `jal ra` targets that never come back (the exit / _exit / abort
    -- family): a call to one ENDS the path instead of applying a `callee_`
    -- summary, because there is no return for a summary to describe.
    let noret := noReturnTargets img starts
    let mut rows : List String := []
    let mut deps : List String := []
    let mut noExit : List String := []
    let mut stopOutside : List String := []
    let mut allSums : List String := []
    for (nm, elo, ehi) in residualSpans do
      -- If the span's entry is a jump-table ARM, start at the FUNCTION entry with
      -- the AST kind pinned and let the dispatch derive the arm.  Everything the
      -- prologue establishes — `s1 = sret` (which every arm stores the boxed
      -- result through), the lowered `sp`, the callee-saved spills — is then
      -- DERIVED rather than assumed, exactly as `blockA_k` derives it in the
      -- proof.  Starting at the arm instead leaves those unconstrained, and the
      -- solver duly puts the result store inside the code image.
      let (bmcEntry, kindReg) :=
        match armDispatch img elo with
        | some (fe, reg, k) => (fe, some (reg, k))
        | none => (elo, none)
      let (rlo, rhi) := funcRange starts codeLo codeHi bmcEntry
      -- Is the span's stop the RETURN, or an internal pc?  The whole-arm
      -- convention puts the stop one instruction after the `ret`; a span that
      -- stops inside the function (hInitStore, at `interp_run`'s loop head)
      -- must not treat a return as an arrival at its exit.
      --
      -- A stop OUTSIDE the span's own region can never be an arrival at all
      -- (`stepBlock` only tests `stops` at PCs it walks through), so the span's
      -- exit is the function's RETURN and nothing else.  Reading `isRet` at
      -- `ehi - 4` there is reading a word in a DIFFERENT function: the twelve
      -- `exec_stmt` arms declare `0x800043ec` (`interp_run`), so their
      -- `retExit` was decided by `interp_init`'s `ret` at `0x800043e8` and came
      -- out true by luck.  Had that word not been a `ret`, all twelve spans
      -- would have had zero exit arrivals -- defect 2 of DIFFTEST-PLAN's table,
      -- one word away.  Decide it structurally instead, and record the
      -- mis-declared stops so they are visible rather than latent.
      let stopInRegion := rlo ≤ ehi && ehi < rhi
      let retExit := if stopInRegion then isRet (wordAt img (ehi - 4)) else true
      if !stopInRegion then
        stopOutside := stopOutside ++
          [s!"{nm}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t0x{String.ofList (Nat.toDigits 16 rlo)}\t0x{String.ofList (Nat.toDigits 16 rhi)}"]
      let (ev, binds, sums, complete, used, writes, dispG, halts, exitG) := reflectBmc img rlo rhi bmcEntry [ehi] starts noret retExit rounds "s0"
      -- The kind pin, PLUS which dispatch guard it makes true.  The encoder
      -- already resolved the jump table statically (that is how it knows the
      -- arms), so stating the selected guard here is the same ground fact as the
      -- rodata pins — just at the point of use.  Leaving it to the solver means
      -- re-deriving the dispatch through the prologue's store chain, which it
      -- does not do, so an arm the pin EXCLUDES still looks reachable and the
      -- span has to discharge invariants belonging to it.
      let kindPin :=
        match kindReg with
        | none => ""
        | some (reg, _) =>
          s!"; the arm is selected by the pinned AST kind (`ExprRepr`/`StmtRepr`)\n(assert (= (ld4 (mm s0) {stR "s0" reg}) {bvN (kindIndex img elo)}))\n"
      -- The guard selection has to come AFTER the binding chain: it names guard
      -- variables, and SMT-LIB wants them declared first.
      let dispPin :=
        match kindReg with
        | none => ""
        | some _ =>
          -- Pin ONLY the dispatch site whose arms include this residual's arm.
          -- Every other ground dispatch on the path -- eval_expr nests the
          -- operator table at 0x80003558 -- must be left free: asserting that
          -- none of ITS arms is taken, while the exit guard demands a path
          -- through one, makes the assumptions contradictory, and a query with
          -- contradictory assumptions reports VALID on every post.
          match dispG.find? (fun (t : Nat × Nat × String) => t.2.1 == elo) with
          | none => ""
          | some (site, _, _) =>
            let sel : List String :=
              (dispG.filter (fun (t : Nat × Nat × String) => t.1 == site)).map
                (fun (t : Nat × Nat × String) =>
                  if t.2.1 == elo then s!"(assert {t.2.2})"
                  else s!"(assert (not {t.2.2}))")
            "; and therefore which arm of THIS dispatch is taken (other ground\n"
              ++ "; dispatches on the path are left free)\n"
              ++ String.intercalate "\n" sel ++ "\n"
      let decls2 := bindsToDecls binds
      allSums := (allSums ++ sums).eraseDups
      let decls := summaryDecls sums
      -- NO-EXIT: `reflectBmc` returns the entry name unchanged when the span has
      -- no exit arrival at all (every path halts, or the stop PC is unreachable).
      -- Writing the query anyway would ask the post about the ENTRY state and
      -- report VALID.  Record the field and skip it instead.
      if ev == "s0" then
        noExit := noExit ++ [s!"{nm}\t0x{String.ofList (Nat.toDigits 16 bmcEntry)}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t{halts.length}"]
      else
      IO.FS.writeFile s!"{dir}/queries/{nm}.smt2"
        s!"{smtPreamble}\n{decls}\n{gDecl}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const s0 MState)\n{kindPin}{decls2}\n{dispPin}; only inputs that REACH the exit PC: without this the `ite` merge\n; falls through to the last arrival for an input no guard covers, and the\n; resulting state is one the machine is never in -- spurious REFUTED.\n(assert {exitG})\n; mined clause set for every summary\n; @@ASSUME@@\n(define-fun state_exit () MState {ev})\n(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))\n; @@POST@@\n"
      IO.FS.writeFile s!"{dir}/writes/{nm}.tsv"
        ("guard\twidth\taddr\n" ++ String.intercalate "\n"
          (writes.map (fun (g, a, w) => s!"{g}\t{w}\t{a}")) ++ "\n")
      -- The paths EXCLUDED from the exit merge because they transfer to a
      -- function that never returns.  A verdict on this span is a verdict on
      -- the paths that reach the exit PC; these ones halt instead, and are the
      -- error-site seam's obligation (`Vsa/Sim/ErrorSiteJal.lean`), not a frame
      -- post's.  Named here so the verdict can be qualified rather than bare.
      IO.FS.writeFile s!"{dir}/halts/{nm}.tsv"
        ("guard\tsite\n" ++ String.intercalate "\n"
          (halts.map (fun (g, a) => s!"{g}\t0x{String.ofList (Nat.toDigits 16 a)}")) ++ "\n")
      rows := rows ++ [s!"{nm}\t0x{String.ofList (Nat.toDigits 16 rlo)}\t0x{String.ofList (Nat.toDigits 16 rhi)}\t0x{String.ofList (Nat.toDigits 16 bmcEntry)}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t{used}\t{complete}\t{decls2.length}\t{sums.length}\t{halts.length}"]
      deps := deps ++ [s!"{nm}\t{String.intercalate "," sums}"]
    -- Summary obligations, over the SAME encoder.
    --   `callee_t` — symbolically execute the callee's own function;
    --   `loop_h`   — symbolically execute the loop from its header, stopping at
    --               the loop's exit edges, so the term IS the one-step body
    --               (a re-arrival at `h` becomes `loop_h_ih`, the IH);
    --   `icall_`/`idisp_` — opaque by construction (an indirect call through a
    --               register / an unlisted computed goto): NO obligation exists,
    --               so they are listed in `opaque.tsv` and their clauses can only
    --               ever be assumed, never established.
    -- A summary's own body reaches further summaries, so the obligation set is a
    -- FIXPOINT, not one pass over the residuals' summaries: iterate until nothing
    -- new is discovered, or the campaign silently assumes clauses for symbols it
    -- never generated an obligation for.
    let mut opaqueSyms : List String := []
    let mut symDeps : List String := []
    -- The campaign's scope is the INTERPRETER's own code, and no further.  A
    -- summary whose body lies outside the residual spans' own functions is a
    -- CALLEE CONTRACT — `value_int`, `value_bool`, `strcmp`, `malloc`, … — and
    -- the Lean development does not re-derive those either: they are landed
    -- specs (`TermCallees.valueInt`/`strcmp`/`divdi3`/`envGet`) or named open
    -- premises (`envDefine`/`malloc`/`realloc`).  Mining them would drag in the
    -- whole C runtime; they are ASSUMED, listed in `assumed.tsv`, and every
    -- verdict that rests on one says so.
    let armRegions := (residualSpans.map (fun (_, elo, _) =>
      funcRange starts codeLo codeHi elo)).eraseDups
    let inArm := fun (q : Nat) => armRegions.any (fun (a, b) => a ≤ q && q < b)
    let mut worklist := allSums
    let mut done : List String := []
    let mut assumedSyms : List String := []
    while !worklist.isEmpty do
      let sym := worklist.head!
      worklist := worklist.tail!
      if done.contains sym then continue
      done := sym :: done
      let tgt : Option Nat :=
        if sym.startsWith "callee_" then some (sym.drop 7).toNat!
        else if sym.startsWith "loop_" then some (sym.drop 5).toNat!
        else none
      if let some t := tgt then
        if !(inArm t) then
          assumedSyms := assumedSyms ++ [sym]
          continue
      let mk : Nat → Nat → Nat → List Nat → IO (String × List String) := fun rlo rhi entry stops => do
        let (ev, binds, subs, complete, _, writes, _, _, _) := reflectBmc img rlo rhi entry stops starts noret true rounds "S0"
        let declsB := (bindsToDecls binds).replace s!"({sym} " s!"({sym}_ih "
        let decls := summaryDecls ((allSums ++ subs).eraseDups ++ [s!"{sym}_ih"])
        IO.FS.writeFile s!"{dir}/obligations/{sym}.smt2"
          s!"{smtPreamble}\n{decls}\n{gDecl}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const S0 MState)\n{declsB}\n; complete={complete}\n(define-fun fbody () MState {ev})\n; clause set for every summary; `{sym}` itself is supplied as `{sym}_ih`\n; @@ASSUME@@\n; negated clause under test, over S0 / fbody\n; @@GOAL@@\n"
        IO.FS.writeFile s!"{dir}/writes/{sym}.tsv"
          ("guard\twidth\taddr\n" ++ String.intercalate "\n"
            ((writes.map (fun (g, a, w) => s!"{g}\t{w}\t{a}")).map
              (fun r => r.replace s!"({sym} " s!"({sym}_ih ")) ++ "\n")
        return (s!"{sym}\t{String.intercalate "," ((sym :: subs).eraseDups)}", subs)
      if sym.startsWith "callee_" then
        let t := (sym.drop 7).toNat!
        let (rlo, rhi) := funcRange starts codeLo codeHi t
        let (row, subs) ← mk rlo rhi t []
        symDeps := symDeps ++ [row]; worklist := worklist ++ subs
      else if sym.startsWith "loop_" then
        let h := (sym.drop 5).toNat!
        let (rlo, rhi) := funcRange starts codeLo codeHi h
        let (qs, _) := loopExits img rlo rhi [] h
        let (row, subs) ← mk rlo rhi h qs
        symDeps := symDeps ++ [row]; worklist := worklist ++ subs
      else opaqueSyms := opaqueSyms ++ [sym]
    IO.FS.writeFile s!"{dir}/opaque.tsv" ("summary\n" ++ String.intercalate "\n" opaqueSyms ++ "\n")
    -- Clauses that must NOT be assumed for a given summary, with the structural
    -- reason.  An assumed contract is checked by nobody, so anything the image
    -- itself contradicts has to be taken off the table here rather than left to
    -- be discovered by a countermodel (or not discovered at all).
    let mut drops : List String := []
    for sym in assumedSyms do
      if sym.startsWith "callee_" then
        let t := (sym.drop 7).toNat!
        if retsViaSaved img starts t then
          drops := drops ++ [s!"{sym}\tra_restore\treturns through a saved register / unresolved computed goto, so `ra` is not preserved"]
    IO.FS.writeFile s!"{dir}/clause-drop.tsv"
      ("summary\tclause\treason\n" ++ String.intercalate "\n" drops ++ "\n")
    IO.FS.writeFile s!"{dir}/regions.tsv"
      s!"region\tlo\thi\nwritable_static\t0x{String.ofList (Nat.toDigits 16 gLo)}\t0x{String.ofList (Nat.toDigits 16 gHi)}\n"
    IO.FS.writeFile s!"{dir}/assumed.tsv"
      ("summary\trole\n" ++ String.intercalate "\n"
        (assumedSyms.map (fun a => s!"{a}\tcallee contract outside the interpreter's own code")) ++ "\n"
        ++ "d < maxCallDepth\tentry stack budget: the 7408 headroom pin needs the closure depth guard; ExecEntry has no depth field\n")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv"
      ("summary\tdeps\n" ++ String.intercalate "\n" symDeps ++ "\n")
    IO.FS.writeFile s!"{dir}/stop-outside.tsv"
      ("field\tstop\tregion_lo\tregion_hi\n" ++ String.intercalate "\n" stopOutside ++ "\n")
    IO.FS.writeFile s!"{dir}/no-exit.tsv"
      ("field\tentry\tstop\thalts\n" ++ String.intercalate "\n" noExit ++ "\n")
    IO.FS.writeFile s!"{dir}/spans.tsv"
      ("field\tregion_lo\tregion_hi\tentry\tstop\trounds\tcomplete\tterm_bytes\tsummaries\thalts\n"
        ++ String.intercalate "\n" rows ++ "\n")
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\n" ++ String.intercalate "\n" done.reverse ++ "\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" deps ++ "\n")
    let nComplete := (rows.filter (fun r => (r.splitOn "\t").getD 6 "" == "true")).length
    Lean.logInfo m!"#emit_bmc → {dir}: {residualSpans.length} spans, {nComplete} COMPLETE at {rounds} rounds, {done.length} summaries: {done.length - assumedSyms.length - opaqueSyms.length} mined, {assumedSyms.length} assumed contracts, {opaqueSyms.length} opaque"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
elab "#bmc_trace " loStx:num hiStx:num stopStx:num rStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let img ← loadElf elfPath
    let starts := funcStarts img 0x80000000 0x80018be0
    let (rlo, rhi) := funcRange starts 0x80000000 0x80018be0 loStx.getNat
    let noret := noReturnTargets img starts
    let tr := bmcTrace img rlo rhi loStx.getNat [stopStx.getNat] starts noret true rStx.getNat
    let mut i : Nat := 0
    for f in tr do
      let pcs := f.map (fun q => String.ofList (Nat.toDigits 16 q))
      Lean.logInfo s!"round {i}: {f.length} pcs {pcs}"
      i := i + 1
