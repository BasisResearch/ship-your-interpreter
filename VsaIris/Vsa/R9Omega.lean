import Lean
import Lean.Elab.Tactic.Omega

namespace VsaIris.R9

open Lean Meta Elab Tactic

partial def atomsOf (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  let e := e.consumeMData
  match e.getAppFn, e.getAppNumArgs with
  | .const n _, k =>
    let args := e.getAppArgs
    if (n == ``And || n == ``Or || n == ``Iff) && k == 2 then atomsOf args[1]! (atomsOf args[0]! acc)
    else if n == ``Not && k == 1 then atomsOf args[0]! acc
    else if (n == ``Eq || n == ``Ne) && k == 3 then atomsOf args[2]! (atomsOf args[1]! acc)
    else if (n == ``LE.le || n == ``LT.lt || n == ``GE.ge || n == ``GT.gt) && k == 4 then
      atomsOf args[3]! (atomsOf args[2]! acc)
    else if (n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul || n == ``HDiv.hDiv ||
        n == ``HMod.hMod || n == ``HPow.hPow) && k == 6 then atomsOf args[5]! (atomsOf args[4]! acc)
    else if n == ``OfNat.ofNat then acc
    else if n == ``Nat.cast && k == 3 then atomsOf args[2]! acc
    else if n == ``Dvd.dvd && k == 4 then atomsOf args[3]! (atomsOf args[2]! acc)
    else if n == ``False || n == ``True then acc
    else acc.insert e
  | .lit _, _ => acc
  | .forallE _ t b _, _ => if b.hasLooseBVars then acc.insert e else atomsOf b (atomsOf t acc)
  | _, _ => acc.insert e

def isArithProp (e : Expr) : Bool :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const n _ => n == ``And || n == ``Or || n == ``Iff || n == ``Not || n == ``Eq || n == ``Ne ||
      n == ``LE.le || n == ``LT.lt || n == ``GE.ge || n == ``GT.gt || n == ``Dvd.dvd || n == ``False
  | _ => e.isArrow

def nearClear (rounds : Nat) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let mut atoms := atomsOf (← instantiateMVars (← g.getType)) {}
  let mut hyps : Array (FVarId × Std.HashSet Expr) := #[]
  let mut other : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then
      if isArithProp ty then hyps := hyps.push (d.fvarId, atomsOf ty {})
      else other := other.push d.fvarId
  let mut keep : Std.HashSet FVarId := {}
  let mut r := 0
  let mut changed := true
  while changed && r < rounds do
    changed := false
    r := r + 1
    let cur := atoms
    for (h, as) in hyps do
      if keep.contains h then continue
      if as.toList.any cur.contains then
        keep := keep.insert h
        for a in as.toList do
          if !atoms.contains a then
            atoms := atoms.insert a
            changed := true
  let drop := (hyps.filterMap fun (h, _) => if keep.contains h then none else some h) ++ other
  replaceMainGoal [← g.tryClearMany drop]

elab "omega_near_only" : tactic => do
  nearClear 1
  Lean.Elab.Tactic.Omega.omegaDefault

elab "omega_near" : tactic => do
  let s ← saveState
  try
    nearClear 1
    Lean.Elab.Tactic.Omega.omegaDefault
  catch _ =>
    s.restore
    Lean.Elab.Tactic.Omega.omegaDefault

end VsaIris.R9
