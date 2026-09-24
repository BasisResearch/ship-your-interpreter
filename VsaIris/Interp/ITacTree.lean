import VsaIris.Interp.ITac

/-!
# `#ix_tree`: a proof assembled from a tree of pieces (lane E2)

`#ix_chain` (lane G, `ITac.lean`) continues each piece's FIRST leftover with
the next piece and exports every other leftover as a hypothesis. A case whose
machine code branches after a shared prefix (the binary arm: one prefix, then
a row per operand kinds; INTERP_DESIGN.md §6) is a TREE of pieces instead: the
piece that splits leaves one leftover per branch, and each branch is continued
by its own piece (`#ix_piece q from p at k`).

`#ix_tree name := p [c₁, c₂, …]` proves `name` from the root piece `p`, its
`j`-th leftover continued by the subtree `cⱼ`. A node's leftovers beyond its
children are exported as hypotheses `hx_1, hx_2, …` of `name` (in tree order),
each quantified over the locals the path to it introduced, as `#ix_chain`
does. `#ix_chain name := [p₁, p₂, p₃]` is `#ix_tree name := p₁ [p₂ [p₃]]`.
-/

namespace VsaIris.Sym

open Lean Elab Command Term Meta

declare_syntax_cat ixtree
syntax ident : ixtree
syntax ident " [" ixtree,* "]" : ixtree

/-- A parsed tree of pieces. -/
inductive IxTree where
  | node (piece : Name) (children : Array IxTree)
  deriving Inhabited

partial def parseIxTree (stx : Syntax) : CoreM IxTree := do
  match stx with
  | `(ixtree| $p:ident) => return .node (← realizeGlobalConstNoOverload p) #[]
  | `(ixtree| $p:ident [ $cs,* ]) =>
    return .node (← realizeGlobalConstNoOverload p) (← cs.getElems.mapM parseIxTree)
  | _ => throwError "#ix_tree: bad tree syntax"

/-- `#ix_tree name := p [c₁, …]`: see the module doc. -/
syntax (name := ixTree) "#ix_tree " ident " := " ixtree : command

/-- The leftover types of a piece applied to its binders. -/
private def leftovers (c : Expr) : MetaM (Array Expr) := do
  forallTelescope (← inferType c) fun hs _ => hs.mapM inferType

/-- Pass 1: the exported leftovers, closed over the path's locals, in tree order. -/
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

/-- Pass 2: the proof of a node's goal, the exported hypotheses consumed from
`j` on; returns the term and the next export index. -/
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
