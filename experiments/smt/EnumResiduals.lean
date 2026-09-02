import Vsa

/-!
# `#enumerate_residuals` — reflect over `TermResidualsCore`, emit a data manifest

Replaces the Python regex `extract_fields`.  Walks the ELABORATED structure via
`getStructureInfo` (no source parsing anywhere), and for each field writes its
name and the field's PROPOSITION (the `inferType` of the projected proof) to a
TSV manifest.  Python may read the manifest as DATA — it never parses Lean.

`#enumerate_residuals "<path>"` — write `field\tproposition` lines to `<path>`.
Proves nothing; run via `lake env lean`.
-/

open Lean Elab Meta Command

namespace Vsa.EnumResiduals

/-- For structure `S` (single parameter `L`), return `(fieldName, propText)` for
every field, where the proposition is `inferType (S.field L self)` under a fresh
`self : S L`.  All residual fields are independent `Prop`s, so the text depends
only on `L`. -/
def enumerate (structName : Name) : MetaM (Array (String × String)) := do
  let env ← getEnv
  let some info := getStructureInfo? env structName
    | throwError "not a structure: {structName}"
  -- the structure has one explicit parameter (Layout); introduce it + a self
  let cinfo ← getConstInfo structName
  forallTelescope cinfo.type fun params _ => do
    -- params = [L] (plus any instance args); use them all
    let structApp := mkAppN (mkConst structName (cinfo.levelParams.map mkLevelParam)) params
    withLocalDeclD `self structApp fun self => do
      let mut out := #[]
      for fname in info.fieldNames do
        let proj := mkAppN (mkConst (structName ++ fname) (cinfo.levelParams.map mkLevelParam))
          (params.push self)
        let ty ← inferType proj
        let txt ← ppExpr ty
        -- one line, tabs/newlines flattened so the manifest stays one row/field
        let flat := (toString txt).replace "\n" " " |>.replace "\t" " "
        out := out.push (fname.toString, flat)
      return out

end Vsa.EnumResiduals

open Vsa.EnumResiduals in
elab "#enumerate_residuals " pathStx:str : command => do
  let path := pathStx.getString
  liftTermElabM do
    let rows ← enumerate ``Vsa.Sim.TermAssembly.TermResidualsCore
    let body := String.intercalate "\n" (rows.toList.map fun (n, t) => s!"{n}\t{t}")
    IO.FS.writeFile path ("field\tproposition\n" ++ body ++ "\n")
    logInfo m!"#enumerate_residuals → {path} ({rows.size} fields)"
