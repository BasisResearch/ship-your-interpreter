import Vsa.Sim.TermCaseBundle

/-!
# `DeriveMeta` — structure-driven elab commands (L-meta)

Three commands that mechanize hand record-update probes and hand
destructuring, in the plain-term / cheap-elaboration style of `#derive_case`
(`DeriveCase.lean`), `#derive_error_site` (`DeriveErrorSite.lean`) and
`segToTriple` (`DeriveCaseRow.lean`).

## `#verify_slots <StructId> [ (<field>, <row>), … ]`

Mechanizes the ~50 hand record-update probes in `termCases_of_residuals`
(`TermAssembly.lean`).  For each `(field, row)` pair it checks that the row
theorem's conclusion type is defeq to what the structure field expects — i.e.
that `row (?resid)` would fill the `field` slot.  A mismatch is reported as an
elaboration error naming BOTH types; a full pass is silent (or, with a trailing
`report`, prints a one-line per-pair verdict).

The check is exactly the one `termCases_of_residuals` performs positionally, but
(a) named per pair so a break points at the offending row, and (b) re-run on
every build without threading the giant record.  A row may take a leading
*residual* hypothesis (`hR : Resid`) — the field type is then the row type with
that one binder stripped; a row with no residual (the unconditional scaffolds)
matches the field type directly.  Both are accepted.

## `#derive_destructurer <DefId>`

Mechanizes CLAUDE.md's "consuming a LANDED ∃/∧ tower" rule (task #32): given a
`def D … : Prop := c₁ ∧ c₂ ∧ …` right-nested conjunction tower, emit

* `structure D.Parts (args) : Prop where p1 : c₁ ; p2 : c₂ ; …` — named fields;
* `theorem D.destruct (args) (h : D args) : D.Parts args` — the forward iso,
  built by the generator with the positional `.1/.2.1/…` projections ONCE, so
  consumers `obtain ⟨p1, p2, …⟩ := D.destruct … h` with names, never indices;
* `theorem D.mk' (args) (h : D.Parts args) : D args` — the reverse iso.

(`#derive_row`, the third command, lives in `Vsa/Sim/DeriveRow.lean` — it needs
the heavier `segToTriple` import closure, kept out of this light meta file.)
-/

open Lean Elab Command Term Meta

namespace Vsa.Sim.DeriveMeta

/-! ## `#verify_slots` -/

/-- One `(field, row)` pair. -/
syntax vsPair := "(" ident ", " ident ")"

/-- `#verify_slots Struct [ (field, row), … ]` — optional trailing `report`
prints a per-pair verdict line. -/
syntax (name := verifySlotsCmd)
  "#verify_slots " ident " [" vsPair,* "]" (&" report")? : command

/-- Strip up to `n` leading `∀`/`→` binders off `t`, instantiating each with a
fresh metavariable, returning the resulting (partially applied) body type.
Used to peel the row's leading residual hypothesis before comparing to the
field type. -/
private def stripBinders (t : Expr) (n : Nat) : MetaM Expr := do
  let mut cur ← whnf t
  for _ in [0:n] do
    match cur with
    | .forallE _ d b _ =>
      let m ← mkFreshExprMVar d
      cur ← whnf (b.instantiate1 m)
    | _ => return cur
  return cur

/-- Count leading `∀`/`→` binders of a type (used to size the residual-strip
search: the row's residual count = its leading-binder count minus the field
type's). -/
private partial def leadingBinderCount (t : Expr) : MetaM Nat := do
  match ← whnf t with
  | .forallE _ d b _ =>
    withLocalDeclD `x d fun x => do
      return 1 + (← leadingBinderCount (b.instantiate1 x))
  | _ => return 0

@[command_elab verifySlotsCmd]
def elabVerifySlots : CommandElab := fun stx => do
  match stx with
  | `(command| #verify_slots $struct:ident [ $pairs,* ] $[report%$rep?]?) => do
    let structName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo struct
    let doReport := rep?.isSome
    liftTermElabM do
      -- Ensure it is a structure (its projections are `Struct.<field>`).
      let _ ← getConstInfoInduct structName
      let env ← getEnv
      let mut msgs : Array MessageData := #[]
      let mut nfail := 0
      for p in pairs.getElems do
        match p with
        | `(vsPair| ($fld:ident, $row:ident)) => do
          -- Resolve the projection `Struct.<fld>` and the row constant.
          let fldName := structName ++ fld.getId
          unless env.contains fldName do
            throwErrorAt fld "no field `{fld.getId}` on structure `{structName}`"
          let rowName ← realizeGlobalConstNoOverloadWithInfo row
          -- Field type: the result type of the projection, i.e. the type the
          -- structure field carries once the structure's own parameters are
          -- fixed by fresh metavariables.
          let projInfo ← getConstInfo fldName
          -- Strip ONLY the structure `self` parameter, keeping the field type's
          -- own `∀`-telescope intact, so the residual count below is accurate.
          let fldTy ← forallBoundedTelescope projInfo.type (some 1)
            fun _ body => pure body
          let rowInfo ← getConstInfo rowName
          -- The field type is the row type with its LEADING residual hypotheses
          -- stripped (`eval_int_row` takes 1 residual, `eval_binary_row` 18, the
          -- unconditional scaffolds 0).  Try each strip depth up to the row's
          -- residual-binder count until one is defeq to the field type.
          let rowBinders ← leadingBinderCount rowInfo.type
          let fldBinders ← leadingBinderCount fldTy
          let maxStrip := rowBinders - fldBinders
          let mut ok := false
          let mut depth := 0
          for k in [0:maxStrip+1] do
            unless ok do
              let cand ← stripBinders rowInfo.type k
              if ← isDefEq cand fldTy then
                ok := true
                depth := k
          if ok then
            if doReport then
              let note := if depth == 0 then "" else s!" (after {depth} residual(s))"
              msgs := msgs.push m!"  ✓ {fld.getId} ⟵ {row.getId}{note}"
          else
            nfail := nfail + 1
            msgs := msgs.push m!"  ✗ {fld.getId} ⟵ {row.getId}\n    field expects: {indentExpr fldTy}\n    row (full) type: {indentExpr rowInfo.type}"
        | _ => throwErrorAt p "malformed (field, row) pair"
      if nfail > 0 then
        throwError "#verify_slots {struct.getId}: {nfail} slot mismatch(es)\n{MessageData.joinSep msgs.toList "\n"}"
      else if doReport then
        logInfo m!"#verify_slots {struct.getId}: all {pairs.getElems.size} slots OK\n{MessageData.joinSep msgs.toList "\n"}"
  | _ => throwUnsupportedSyntax

/-! ## `#derive_destructurer` -/

/-- `#derive_destructurer D` — for a landed `def D … : Prop` that unfolds to a
right-nested `∧`-tower, emit `D.Parts` (named-field structure), `D.destruct`
(forward iso) and `D.mk'` (reverse iso).  An optional `as <ns>` renames the
generated namespace root (default: the def's own name). -/
syntax (name := deriveDestructurerCmd)
  "#derive_destructurer " ident (&" fields " ident+)? : command

/-- Flatten the top-level right-nested `And` spine of `e` into its conjuncts.
`Exists`/other heads are LEAVES (not descended into) — only `And` is split, so
`(∃ x, P) ∧ Q` yields `[(∃ x, P), Q]`. -/
private partial def flattenAnd (e : Expr) : Array Expr :=
  match e.and? with
  | some (a, b) => #[a] ++ flattenAnd b
  | none => #[e]

/-- The data extracted from a tower def for code generation: the parameter
binder syntax, the per-conjunct field-type syntax, and the conjunct count. -/
private structure TowerData where
  binders   : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF)
  paramIds  : Array Ident
  fieldTys  : Array (TSyntax `term)

/-- Inspect a tower `def`: telescope its parameters, δ-unfold + whnf the body,
flatten the top-level `And` spine, and delaborate everything back to syntax so
the generated `structure`/`theorem` commands round-trip. -/
private def inspectTower (defName : Name) : TermElabM TowerData := do
  let info ← getConstInfo defName
  forallTelescope info.type fun params _ => do
    let app := mkAppN (mkConst defName (info.levelParams.map mkLevelParam)) params
    let body ← whnf (← Meta.unfold app defName).expr
    let conjs := flattenAnd body
    let mut binders := #[]
    let mut paramIds := #[]
    for p in params do
      let ld ← p.fvarId!.getDecl
      let tyStx ← PrettyPrinter.delab ld.type
      let idStx := mkIdent ld.userName
      paramIds := paramIds.push idStx
      binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($idStx : $tyStx)))
    let fieldTys ← conjs.mapM (PrettyPrinter.delab ·)
    pure { binders, paramIds, fieldTys }

/-- Elaborate one iso `fun (params) (hyp : Src) => body : ∀ params, Src → Tgt`
and add it as a theorem via `addDecl` (synchronous — see the note at the call
site).  `fwd = true`: `Src = D params`, `Tgt = D.Parts params`; else swapped. -/
private def addIsoDecl (thmName defName : Name) (partsId : Ident) (appParams : Array Ident)
    (bodyStx : TSyntax `term) (fwd : Bool) : TermElabM Unit := do
  -- Build the closed iso type `∀ params, Src params → Tgt params` as syntax and
  -- elaborate the whole `fun params => bodyStx` term against it.
  let defId := mkIdent defName
  let srcTy ← if fwd then `($defId $appParams*) else `($partsId $appParams*)
  let tgtTy ← if fwd then `($partsId $appParams*) else `($defId $appParams*)
  -- Parameters of the def, as syntax binders, taken from the def's own signature.
  let info ← getConstInfo defName
  forallTelescope info.type fun params _ => do
    let mut binderStxs := #[]
    for p in params do
      let ld ← p.fvarId!.getDecl
      let tyStx ← PrettyPrinter.delab ld.type
      binderStxs := binderStxs.push (← `(Lean.Parser.Term.funBinder| ($(mkIdent ld.userName) : $tyStx)))
    let full ← `(fun $binderStxs* => ($bodyStx : $srcTy → $tgtTy))
    let e ← Term.elabTerm full none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← inferType e
    let ty ← instantiateMVars ty
    addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := e })

@[command_elab deriveDestructurerCmd]
def elabDeriveDestructurer : CommandElab := fun stx => do
  match stx with
  | `(command| #derive_destructurer $defId:ident $[fields $fieldIds*]?) => do
    let defName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo defId
    let td ← liftTermElabM (inspectTower defName)
    let n := td.fieldTys.size
    let fieldNames : Array Ident ←
      match fieldIds with
      | some ids =>
        if ids.size ≠ n then
          throwError "#derive_destructurer {defId.getId}: {ids.size} field names given but the tower has {n} conjuncts"
        pure (ids.map fun i => mkIdent i.getId)
      | none => pure ((Array.range n).map fun i => mkIdent (Name.mkSimple s!"p{i+1}"))
    let partsId := mkIdent (defName ++ `Parts)
    let appParams := td.paramIds
    -- `structure D.Parts (params) : Prop where fieldᵢ : conjᵢ`
    let fieldStxs ← (fieldNames.zip td.fieldTys).mapM fun (fn, ct) =>
      `(Lean.Parser.Command.structSimpleBinder| $fn:ident : $ct)
    let structCmd ← `(command|
      structure $partsId $td.binders* : Prop where
        $[$fieldStxs]*)
    -- Emit the structure first (this commits `D.Parts` + its projections).
    elabCommand structCmd
    -- The two isos are added by direct `addDecl` (below) rather than by
    -- `elabCommand` on a generated `theorem`: a programmatic `theorem` command
    -- elaborates its body on an async snapshot whose environment extension is
    -- NOT visible to the rest of this command or file (measured: the constant
    -- reads back as "unknown"), whereas `addDecl` commits synchronously.
    let hId := mkIdent `hyp
    let projTerms ← (Array.range n).mapM fun i => buildProjSyntax hId i n
    let fwdBody ← `(term| fun ($hId : $(mkIdent defName) $appParams*) => ⟨$projTerms,*⟩)
    let fieldProjs ← fieldNames.mapM fun fn => `(term| $hId.$fn:ident)
    let revBody ← `(term| fun ($hId : $partsId $appParams*) => ⟨$fieldProjs,*⟩)
    liftTermElabM do
      addIsoDecl (defName ++ `destruct) defName partsId appParams fwdBody (fwd := true)
      addIsoDecl (defName ++ `mk') defName partsId appParams revBody (fwd := false)
  | _ => throwUnsupportedSyntax
where
  /-- Syntax for the `i`-th projection of a right-nested `And` proof `h`
  (`h.1`, `h.2.1`, …, last `h.2.2…2`). -/
  buildProjSyntax (h : TSyntax `term) (i n : Nat) : CommandElabM (TSyntax `term) := do
    let mut cur : TSyntax `term := h
    for _ in [0:i] do
      cur ← `($cur|>.2)
    if i + 1 < n then `($cur|>.1) else pure cur

end Vsa.Sim.DeriveMeta
