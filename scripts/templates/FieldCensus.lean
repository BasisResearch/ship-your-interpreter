import Lean

open Lean Meta Elab Command

private def censusProjection (root field : Name) : CoreM Name := do
  let env ← getEnv
  unless isStructure env root do
    throwError "census: not a structure: {root}"
  let some owner := findField? env root field
    | throwError "census: no field {field} in {root}"
  let some projection := getProjFnForField? env owner field
    | throwError "census: no projection for {owner}.{field}"
  return projection

elab "census_fields " root:ident : command => do
  let env ← getEnv
  unless isStructure env root.getId do
    throwError "census: not a structure: {root.getId}"
  let fields := getStructureFieldsFlattened env root.getId false
  if fields.isEmpty then throwError "census: empty structure"
  for field in fields do
    let projection ← liftCoreM (censusProjection root.getId field)
    let record := Json.mkObj
      [("field", toJson field.toString), ("projection", toJson projection.toString)]
    logInfo m!"VSA_CENSUS_FIELD {record.compress}"

private def censusCheck (root field layout : TSyntax `ident)
    (proof : TSyntax `term) : CommandElabM Unit := do
  liftTermElabM <| Term.withoutErrToSorry do
    let projection ← censusProjection root.getId field.getId
    let info ← getConstInfo projection
    let .forallE _ layoutType rest _ := info.type
      | throwError "census: projection has no layout parameter"
    let layoutExpr ← Term.elabTermEnsuringType layout layoutType
    Term.synthesizeSyntheticMVarsNoPostponing
    let layoutExpr ← instantiateMVars layoutExpr
    let .forallE _ _ goal _ := rest.instantiate1 layoutExpr
      | throwError "census: projection has no record parameter"
    if goal.hasLooseBVars then
      throwError "census: dependent field requires its preceding record fields"
    unless ← isProp goal do throwError "census: field is not a proposition"
    let value ← Term.elabTermEnsuringType proof goal
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar || value.hasSorry then
      throwError "census: unresolved or admitted proof"
    addDecl (.thmDecl
      { name := `Census.result, levelParams := info.levelParams, type := goal, value })
    let axioms ← collectAxioms `Census.result
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    unless axioms.all allowed.contains do
      throwError "census: nonstandard axioms: {axioms}"
    let record := Json.mkObj
      [("field", toJson field.getId.toString), ("status", toJson "FOUND"),
       ("axioms", toJson (axioms.map Name.toString).toList)]
    logInfo m!"VSA_CENSUS_RESULT {record.compress}"

elab "census_probe " root:ident field:ident " at " layout:ident : command => do
  censusCheck root field layout (← `(by exact?))

elab "census_probe " root:ident field:ident " at " layout:ident
    " using " supplier:term : command => do
  censusCheck root field layout supplier
