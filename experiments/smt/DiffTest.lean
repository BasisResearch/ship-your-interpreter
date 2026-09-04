import experiments.smt.ReflectResiduals

/-!
# `DiffTest` — the encoder's own semantics, dumped for differential testing

`experiments/smt/DIFFTEST-PLAN.md` phase 3 compares what the BMC encoder SAYS the
machine does against what the machine (`riscv-lean/lean_emulator`, the proof
model) actually does on a real run.  For that the comparison needs the encoder's
answer in a form a driver can evaluate, so this file dumps it.

Nothing here is a re-implementation: every row is produced by the SAME functions
`reflectBmc`/`stepBlock` use — `mkLine`, `modelled`, `blockState`, `rawRegVal`,
`branchCondSt`, `decodeTerm`, `dispatchArms`, `funcStarts`, `noReturnTargets`.
A defect in any of them shows up in the dump, which is the point; a
re-implementation here would only test itself.

* `#emit_step_table "<dir>" <lo> <hi>` → `<dir>/steps.tsv`, one row per 4-byte
  word in `[lo, hi)`:

  | class | columns |
  |---|---|
  | `alu` | `pc word alu <modelled?> <state term over S>` |
  | `raw` | `pc word raw <rd> <state term over S>` (`rawRegVal`'s exact word) |
  | `opaque` | `pc word opaque` (over-approximated by `unmodelled_step`) |
  | `branch` | `pc word branch <target> <condition over S>` |
  | `jal` | `pc word jal <rd> <target>` |
  | `jalr` | `pc word jalr <rd> <rs1> <imm> <arms or `-`>` |
  | `sys` | `pc word sys` |

* `#emit_encoder_facts "<dir>"` → the whole-image classifications a span's
  encoding rests on: `funcstarts.tsv`, `noreturn.tsv`, `armdispatch.tsv`.
-/

open Vsa.Sim Vsa.ReflectSpan Vsa.ReflectResiduals

namespace Vsa.DiffTest

/-- Hex of a Nat, `0x`-prefixed. -/
def hx (n : Nat) : String := s!"0x{String.ofList (Nat.toDigits 16 n)}"

/-- One `steps.tsv` row for the word at `p`. -/
def stepRow (img : Nat → Option (BitVec 8)) (p : Nat) : String :=
  let w := wordAt img p
  let hw := hx w.toNat
  if isTerm w then
    match decodeTerm p w with
    | .branch tgt => s!"{hx p}\t{hw}\tbranch\t{hx tgt}\t{branchCondSt "S" w}"
    | .jal rd tgt => s!"{hx p}\t{hw}\tjal\t{rd}\t{hx tgt}"
    | .jalr rd rs1 im =>
      let arms := match dispatchArms img p with
        | some as => String.intercalate "," (as.map hx)
        | none => "-"
      s!"{hx p}\t{hw}\tjalr\t{rd}\t{rs1}\t{im}\t{arms}"
    | .sys => s!"{hx p}\t{hw}\tsys"
  else if modelled p w then
    -- for a memory instruction, also the encoder's OWN effective-address
    -- expression (the one `blockState` builds), so a differential check can pin
    -- it against the address the machine used.  Without that a mis-decoded
    -- immediate makes the load read unconstrained memory and the comparison is
    -- answered by whatever the solver happens to pick.
    let i := mkLine (BitVec.ofNat 64 p) w
    let addr := s!"(bvadd {stR "S" i.rs1} {bv64 (imm12 i.imm)})"
    let mc : String := match i.kind with
      | .sd => "S8" | .sw => "S4" | .sh => "S2" | .sb => "S1"
      | .ld => "L8" | .lw | .lwu => "L4" | .lh | .lhu => "L2" | .lbu => "L1"
      | _ => "-"
    s!"{hx p}\t{hw}\talu\t{blockState "S" [i]}\t{mc}\t{if mc == "-" then "-" else addr}"
  else
    match rawRegVal "S" w with
    | some (rd, e) =>
      s!"{hx p}\t{hw}\traw\t{rd}\t(mst (mm S) (store (rr S) {bvN rd} {e}))"
    | none => s!"{hx p}\t{hw}\topaque"

end Vsa.DiffTest

open Vsa.DiffTest Vsa.ReflectSpan Vsa.ReflectResiduals in
/-- `#emit_step_table "<dir>" <lo> <hi>` — the encoder's per-instruction answer
for every word in `[lo, hi)`. -/
elab "#emit_step_table " pathStx:str loStx:num hiStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll dir
    let img ← loadElf elfPath
    let lo := loStx.getNat
    let hi := hiStx.getNat
    let mut rows : Array String := #[]
    let mut p := lo
    while p < hi do
      rows := rows.push (stepRow img p)
      p := p + 4
    IO.FS.writeFile s!"{dir}/steps.tsv"
      ("pc\tword\tclass\tf1\tf2\tf3\tf4\n" ++ String.intercalate "\n" rows.toList ++ "\n")
    Lean.logInfo m!"#emit_step_table [{hx lo},{hx hi}) → {dir}/steps.tsv: {rows.size} words"

open Vsa.DiffTest Vsa.ReflectSpan Vsa.ReflectResiduals in
/-- `#emit_encoder_facts "<dir>"` — the whole-image classifications the span
encoding rests on, so a trace can contradict them. -/
elab "#emit_encoder_facts " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll dir
    let img ← loadElf elfPath
    let starts := funcStarts img codeLo codeHi
    let noret := noReturnTargets img starts
    IO.FS.writeFile s!"{dir}/funcstarts.tsv"
      ("entry\n" ++ String.intercalate "\n" (starts.map hx) ++ "\n")
    IO.FS.writeFile s!"{dir}/noreturn.tsv"
      ("target\n" ++ String.intercalate "\n" (noret.map hx) ++ "\n")
    -- per residual: the arm it declares, the function entry the encoder actually
    -- starts at, the kind register + index it pins, the region, and whether the
    -- stop is classified as a return.
    let mut rows : List String := []
    for (nm, elo, ehi) in residualSpans do
      let (bmcEntry, kindReg) :=
        match armDispatch img elo with
        | some (fe, reg, k) => (fe, some (reg, k))
        | none => (elo, none)
      let (rlo, rhi) := funcRange starts codeLo codeHi bmcEntry
      let retExit := isRet (wordAt img (ehi - 4))
      let (kr, ki) := match kindReg with
        | some (reg, _) => (toString reg, toString (kindIndex img elo))
        | none => ("-", "-")
      -- the dispatch site whose arm list contains this arm (`""` when the span
      -- is not an arm span): the site a trace's computed goto can be checked at.
      let dsite := (dispatchSites.find? (fun (q, _, _) =>
        match dispatchArms img q with
        | some as => as.contains elo
        | none => false)).map (fun t => hx t.1) |>.getD "-"
      rows := rows ++ [s!"{nm}\t{hx elo}\t{hx ehi}\t{hx bmcEntry}\t{hx rlo}\t{hx rhi}\t{kr}\t{ki}\t{retExit}\t{dsite}"]
    IO.FS.writeFile s!"{dir}/armdispatch.tsv"
      ("field\tarm\tstop\tbmc_entry\tregion_lo\tregion_hi\tkind_reg\tkind_idx\tret_exit\tdispatch\n"
        ++ String.intercalate "\n" rows ++ "\n")
    -- every ground dispatch the encoder resolves, with its arm list: a trace's
    -- computed goto landing outside this list is a resolution defect.
    IO.FS.writeFile s!"{dir}/dispatchsites.tsv"
      ("site\ttable\tn\tarms\n" ++ String.intercalate "\n"
        (dispatchSites.map (fun (q, base, n) =>
          let arms := (dispatchArms img q).getD []
          s!"{hx q}\t{hx base}\t{n}\t{String.intercalate "," (arms.map hx)}")) ++ "\n")
    IO.FS.writeFile s!"{dir}/preamble.smt2" (smtPreamble ++ "\n")
    Lean.logInfo m!"#emit_encoder_facts → {dir}: {starts.length} function starts, {noret.length} no-return targets, {rows.length} spans"

open Vsa.DiffTest Vsa.ReflectSpan Vsa.ReflectResiduals in
/-- `#emit_loop_facts "<encdir>" "<bmcdir>"` — for every `loop_<h>` summary the
campaign generated (read from `<bmcdir>/summaries.tsv`), the loop's header,
region, BODY blocks and EXIT edges, exactly as `loopBody`/`loopExits` compute
them.  A trace instance of the summary is a run from the header to one of those
exits, which is what phase 2 needs in order to evaluate the clause set on real
`(pre, post)` pairs. -/
elab "#emit_loop_facts " encStx:str bmcStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let enc := encStx.getString
    let txt ← IO.FS.readFile s!"{bmcStx.getString}/summaries.tsv"
    let img ← loadElf elfPath
    let starts := funcStarts img codeLo codeHi
    let mut rows : List String := []
    for line in (txt.splitOn "\n") do
      let s := line.trim
      if !(s.startsWith "loop_") then continue
      let h := (s.drop 5).toNat!
      let (rlo, rhi) := funcRange starts codeLo codeHi h
      let body := loopBody img rlo rhi [] h
      let (qs, leaves) := loopExits img rlo rhi [] h
      rows := rows ++ [s!"{s}\t{hx h}\t{hx rlo}\t{hx rhi}\t{String.intercalate "," (body.map hx)}\t{String.intercalate "," (qs.map hx)}\t{leaves}"]
    IO.FS.writeFile s!"{enc}/loops.tsv"
      ("summary\theader\tregion_lo\tregion_hi\tbody\texits\tleaves\n"
        ++ String.intercalate "\n" rows ++ "\n")
    Lean.logInfo m!"#emit_loop_facts → {enc}/loops.tsv: {rows.length} loop summaries"
