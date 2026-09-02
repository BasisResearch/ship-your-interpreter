import Vsa
import experiments.smt.DumpSmtLib
import experiments.smt.EnumResiduals

/-!
# `#dump_residuals` — encode every residual to a per-field `.smt2` file

Encoding ONLY (no Z3 in the elaborator — Python runs the solver on the files,
so the elaborator's heartbeat budget never covers solving).  For each
`TermResidualsCore` field it writes `<dir>/<field>.smt2` (the negated query:
`(∧ hyps) ∧ ¬concl`, SAT ⇒ refutable), each field wrapped in `withCurrHeartbeats`
+ try/catch so one heavy field cannot sink the batch (a failure writes
`<dir>/<field>.gap`).  Structures expand to field conjunctions; recursive-over-
datatype predicates become Z3 recfun symbols (`rec_*`) — their fold/unfold
axioms are appended when available.  A `<dir>/manifest.tsv` records
`field\tcoverage` (full | recfun:… | gap).

Pure Lean encode; Python (`scripts/z3_residuals.py`) runs Z3 on the files.
-/

open Lean Elab Meta Command
open Vsa.SmtExport Vsa.EnumResiduals

elab "#dump_residuals " pathStx:str : command => do
  liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll dir
    let env ← getEnv
    let sName := ``Vsa.Sim.TermAssembly.TermResidualsCore
    let some info := getStructureInfo? env sName | throwError "no struct"
    let cinfo ← getConstInfo sName
    let rows ← forallTelescope cinfo.type fun params _ => do
      let structApp := mkAppN (mkConst sName (cinfo.levelParams.map mkLevelParam)) params
      withLocalDeclD `self structApp fun self => do
        let mut acc := #[]
        for fname in info.fieldNames do
          let name := fname.toString
          -- fresh heartbeat budget per field; a blowup is caught, not fatal
          let cov ← withCurrHeartbeats do
            try
              let proj := mkAppN (mkConst (sName ++ fname) (cinfo.levelParams.map mkLevelParam)) (params.push self)
              let propE ← inferType proj
              let ((hyps, concl), st) ← (runExportM propE).run {}
              let smt := buildSmt st hyps concl
              IO.FS.writeFile s!"{dir}/{name}.smt2" smt
              pure <|
                if !st.gaps.isEmpty then s!"gap×{st.gaps.size}"
                else if !st.recFuns.isEmpty then s!"recfun:{st.recFuns.toList}"
                else if !st.opaqueHeads.isEmpty then s!"opaque:{st.opaqueHeads.toList}"
                else "full"
            catch _ =>
              (try IO.FS.writeFile s!"{dir}/{name}.gap" "encode failed\n" catch _ => pure ())
              pure "ENCODE-FAIL"
          acc := acc.push (name, cov)
        return acc
    let body := String.intercalate "\n" (rows.toList.map fun (n, c) => s!"{n}\t{c}")
    IO.FS.writeFile s!"{dir}/manifest.tsv" ("field\tcoverage\n" ++ body ++ "\n")
    let full := rows.toList.filter (·.2 == "full") |>.length
    logInfo m!"#dump_residuals → {dir} ({rows.size} files, {full} fully-encoded)"
