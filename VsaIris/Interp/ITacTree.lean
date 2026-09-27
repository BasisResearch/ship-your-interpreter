import VsaIris.Interp.ITac

namespace VsaIris.Sym

open Lean Elab Command Term Meta

declare_syntax_cat ixtree
syntax ident : ixtree
syntax ident " [" ixtree,* "]" : ixtree

inductive IxTree where
  | node (piece : Name) (children : Array IxTree)
  deriving Inhabited

partial def parseIxTree (stx : Syntax) : CoreM IxTree := do
  match stx with
  | `(ixtree| $p:ident) => return .node (← realizeGlobalConstNoOverload p) #[]
  | `(ixtree| $p:ident [ $cs,* ]) =>
    return .node (← realizeGlobalConstNoOverload p) (← cs.getElems.mapM parseIxTree)
  | _ => throwError "#ix_tree: bad tree syntax"

syntax (name := ixTree) "#ix_tree " ident " := " ixtree : command

private def leftovers (c : Expr) : MetaM (Array Expr) := do
  forallTelescope (← inferType c) fun hs _ => hs.mapM inferType

private partial def treeExports (vars : Array Expr) : IxTree → Array Expr → MetaM (Array Expr)
  | .node p cs, acc => do
    let hs ← leftovers (mkAppN (Lean.mkConst p) (vars ++ acc))
    if cs.size > hs.size then
      throwError "#ix_tree: {p} has {hs.size} leftovers, the tree gives {cs.size} continuations"
    let mut out := #[]
    for j in [0:hs.size] do
      if h : j < cs.size then
        let sub ← forallTelescope hs[j]! fun ys _ => do
          let inner ← treeExports vars cs[j] (acc ++ ys)
          inner.mapM fun t => pure t
        out := out ++ sub
      else
        out := out.push (← mkForallFVars acc hs[j]!)
    return out

private partial def treeBuild (vars exs : Array Expr) :
    IxTree → Array Expr → Nat → MetaM (Expr × Nat)
  | .node p cs, acc, j0 => do
    let c := mkAppN (Lean.mkConst p) (vars ++ acc)
    let hs ← leftovers c
    let mut args := #[]
    let mut j := j0
    for i in [0:hs.size] do
      if h : i < cs.size then
        let (arg, j') ← forallTelescope hs[i]! fun ys _ => do
          let (t, j') ← treeBuild vars exs cs[i] (acc ++ ys) j
          return (← mkLambdaFVars ys t, j')
        args := args.push arg
        j := j'
      else
        args := args.push (mkAppN exs[j]! acc)
        j := j + 1
    return (mkAppN c args, j)

@[command_elab ixTree] def elabIxTree : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let tree ← liftCoreM <| parseIxTree stx[3]
  let .node root _ := tree
  liftTermElabM do
    let info0 ← getConstInfo root
    forallTelescope info0.type fun xs0 goal => do
      let nv ← pieceVars xs0
      let vars := xs0.extract 0 nv
      let exTys ← treeExports vars tree #[]
      let exDecls := exTys.mapIdx fun j t => (Name.mkSimple s!"hx_{j + 1}", fun _ => pure t)
      withLocalDeclsD exDecls fun exs => do
        let (body, _) ← treeBuild vars exs tree #[] 0
        let val ← instantiateMVars (← mkLambdaFVars (vars ++ exs) body)
        let ty ← instantiateMVars (← mkForallFVars (vars ++ exs) goal)
        addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })

end VsaIris.Sym
