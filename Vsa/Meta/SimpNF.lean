import Lean

/-!
# `#simp_nf`: partial evaluation of a definition, once, under hypotheses

```
#simp_nf F (x : X) (y : Y) (h : P x y) : t x y using [l₁, …, lₙ]
```

runs `simp only [l₁, …, lₙ]` (default simprocs included; local hypotheses such as
`h` may appear in the list) on the symbolic term `t x y` a single time and adds

* `def F (x : X) (y : Y) := <simp normal form of t x y>` — the non-`Prop` binders
  become parameters, and the normal form must not mention the `Prop` binders;
* `theorem F_eq (x : X) (y : Y) (h : P x y) : t x y = F x y`.

A concrete instance `t a b = v` then costs one `F_eq` application and one `rfl`
that reduces `F a b` along the single branch `a b` selects, instead of a fresh
`simp` through the whole definition per instance. Typical use: a Sail decoder or
executor whose state reads are pinned by hypotheses (`Vsa.Sim.decodeN`).
-/

namespace Vsa.Meta

open Lean Meta Elab Command Term

syntax (name := simpNFCmd)
  "#simp_nf " ident bracketedBinder* " : " term " using " "[" ident,* "]" : command

private def addSimpArg (thms : SimpTheorems) (id : Syntax) : TermElabM SimpTheorems := do
  let n := id.getId
  if let some d := (← getLCtx).findFromUserName? n then
    return ← thms.add (.fvar d.fvarId) #[] d.toExpr
  let c ← realizeGlobalConstNoOverloadWithInfo id
  match ← getConstInfo c with
  | .thmInfo _ => thms.addConst c
  | _ => thms.addDeclToUnfold c

/-- Universe metavariables left unconstrained by elaboration are fixed at `0`. -/
private def zeroLvl (e : Expr) : Expr :=
  e.replaceLevel fun l =>
    if l.hasMVar then some (l.replace fun | .mvar _ => some .zero | _ => none) else none

@[command_elab simpNFCmd] def elabSimpNF : CommandElab := fun stx => do
  let `(#simp_nf $n:ident $bs:bracketedBinder* : $t:term using [$ls,*]) := stx
    | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let declName := ns ++ n.getId
  liftTermElabM do
    Term.elabBinders bs fun xs => do
      let lhs ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let lhs := zeroLvl (← instantiateMVars lhs)
      let mut thms : SimpTheorems := {}
      for l in ls.getElems do
        thms ← addSimpArg thms l
      let ctx ← Simp.mkContext (simpTheorems := #[thms])
        (congrTheorems := ← getSimpCongrTheorems)
      let (r, _) ← simp lhs ctx (simprocs := #[← Simp.getSimprocs])
      let nf ← instantiateMVars r.expr
      let params ← xs.filterM fun x => return !(← isProp (← inferType x))
      let val := zeroLvl (← instantiateMVars (← mkLambdaFVars params nf))
      if val.hasFVar || val.hasMVar then
        throwError "#simp_nf: the normal form still mentions a Prop binder:{indentExpr nf}"
      let ty := zeroLvl (← instantiateMVars (← inferType val))
      let us := (collectLevelParams {} val).params ++ (collectLevelParams {} ty).params
      let us := us.toList.eraseDups
      addDecl <| .defnDecl
        { name := declName, levelParams := us, type := ty, value := val,
          hints := .abbrev, safety := .safe }
      let fApp := mkAppN (mkConst declName (us.map mkLevelParam)) params
      let prf ← match r.proof? with
        | some p => instantiateMVars p
        | none => mkEqRefl lhs
      let prf := zeroLvl prf
      let eqTy ← mkEq lhs fApp
      let thmTy := zeroLvl (← instantiateMVars (← mkForallFVars xs eqTy))
      let thmVal := zeroLvl (← instantiateMVars (← mkLambdaFVars xs (← mkExpectedTypeHint prf eqTy)))
      if thmVal.hasMVar then
        throwError "#simp_nf: the simp proof has unassigned metavariables"
      addDecl <| .thmDecl
        { name := declName ++ `eq, levelParams := us, type := thmTy, value := thmVal }

end Vsa.Meta
