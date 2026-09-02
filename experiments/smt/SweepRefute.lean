import experiments.fleet.obstructions.RefutBatteryCur
import experiments.smt.EnumResiduals

/-!
# `#sweep_refute` — per-field ∅-refutation sweep (all 58 residuals, one run)

For every `TermResidualsCore` field, instantiate the outer `∀` with canonical
"empty" witnesses (`∅` for `Mem`, `fun _ => none` for register maps, `0` for
numerics/bitvectors, `.null` for `Expr`/`Value`, `witSt` for `St`, zero-structs
for the geometry records) and try to derive `False` from the resulting body via
the jump-table slot-pin closer.

* A field with a leading DATA `∀` whose body demands a static pin absent from `∅`
  ⇒ **REFUTED** (kernel proof of falsity).
* A field carrying an `EvalEntry …` (or any `Prop`) hypothesis ⇒ the witness
  chain stops (no proof of the hypothesis) ⇒ **NOT-REFUTED** (the entry blocks
  `∅`; correct for the 6 unary/logic + every composition field).
* A binder type with no canonical witness ⇒ **WITNESS-GAP** (reported honestly).

Pure Lean metaprogramming, nothing opaque, no solver.  Run via `lake env lean`;
proves nothing (an analysis command).
-/

open Lean Elab Meta Command
open Vsa.EnumResiduals

namespace Vsa.SweepRefute

/-- `some` iff `x` succeeds. -/
def tryOpt {α} (x : MetaM α) : MetaM (Option α) := do
  try return some (← x) catch _ => return none

/-- Canonical "empty" witness for a binder type, by its whnf'd head. -/
partial def synthWitness (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  match ty with
  | .const ``Nat _ => return some (mkNatLit 0)
  | .const ``Int _ => return some (← mkAppM ``Int.ofNat #[mkNatLit 0])
  | _ =>
    if ty.isAppOfArity ``BitVec 1 then
      return some (← mkAppM ``BitVec.ofNat #[ty.appArg!, mkNatLit 0])
    else if ty.isAppOfArity ``Std.ExtHashMap 4 then
      return some (← mkAppOptM ``EmptyCollection.emptyCollection #[ty, none])
    else if ty.isForall then
      -- function type : fun _ => <witness of codomain> (open one binder)
      forallBoundedTelescope ty (some 1) fun xs body => do
        match ← synthWitness body with
        | some w => return some (← mkLambdaFVars xs w)
        | none => return none
    else
      -- structures / inductives : `default`, else first synthesizable constructor
      match ← tryOpt (mkAppOptM ``default #[ty, none]) with
      | some d => return some d
      | none =>
        match ty.getAppFn with
        | .const tyName _ =>
          match (← getEnv).find? tyName with
          | some (.inductInfo iv) =>
            for ctor in iv.ctors do
              let ci ← getConstInfo ctor
              let ok ← forallTelescopeReducing ci.type fun args _ => do
                let mut vs := #[]
                for a in args do
                  match ← synthWitness (← a.fvarId!.getType) with
                  | some w => vs := vs.push w
                  | none => return none
                return some (mkAppN (mkConst ctor (iv.levelParams.map mkLevelParam)) vs)
              if let some e := ok then return some e
            return none
          | _ => return none
        | _ => return none

/-- The slot-pin closer as a fixed tactic term proving `¬ body`. -/
def closerStx : TSyntax `term := Unhygienic.run `(by
  first
  | (rintro ⟨_, _, _, _, _, _, hX, _⟩; exact kindSlot6_empty_false _ hX.slot6)
  | (rintro ⟨_, _, _, hX, _⟩; exact kindSlot6_empty_false _ hX.slot6))

/-- Tactic bank for DISCHARGING a Prop hypothesis at the empty witnesses (e.g.
the `hIDiv` guard `¬(a=-2^63 ∧ b=-1)` at `a=b=0`).  If it closes, the hypothesis
does NOT block the ∅ witness. -/
def hypStx : TSyntax `term := Unhygienic.run `(by first | decide | trivial | simp | omega)

/-- Elaborate `stx` at type `ty`; return the proof iff it is sorry/mvar-free. -/
def tryElab (stx : TSyntax `term) (ty : Expr) : TermElabM (Option Expr) := do
  try
    let pf ← Term.elabTermEnsuringType stx ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let pf ← instantiateMVars pf
    if pf.hasSorry || pf.hasExprMVar then return none else return some pf
  catch _ => return none

/-- Try to refute one field proposition at the empty witnesses. -/
partial def refuteField (e0 : Expr) : TermElabM String := do
  let e ← whnf e0
  match e with
  | .forallE _ dom body _ =>
    if (← Meta.isProp dom) then
      -- a Prop binder: try to PROVE it; supply the proof and continue if it
      -- closes, otherwise it genuinely blocks the ∅ witness (e.g. EvalEntry).
      match ← tryElab hypStx dom with
      | some pf => refuteField (body.instantiate1 pf)
      | none => return "NOT-REFUTED"
    else match ← synthWitness dom with
    | some w => refuteField (body.instantiate1 w)
    | none => return "WITNESS-GAP"
  | _ =>
    match ← tryElab closerStx (← mkArrow e (mkConst ``False)) with
    | some _ => return "REFUTED"
    | none => return "NOT-REFUTED"

end Vsa.SweepRefute

open Vsa.SweepRefute Vsa.EnumResiduals in
elab "#sweep_refute " pathStx:str : command => do
  liftTermElabM do
    let rows ← enumerate ``Vsa.Sim.TermAssembly.TermResidualsCore
    -- rows give names; re-derive the actual Expr props via the structure again
    let env ← getEnv
    let some info := getStructureInfo? env ``Vsa.Sim.TermAssembly.TermResidualsCore | throwError "no struct"
    let cinfo ← getConstInfo ``Vsa.Sim.TermAssembly.TermResidualsCore
    let out ← forallTelescope cinfo.type fun params _ => do
      let structApp := mkAppN (mkConst ``Vsa.Sim.TermAssembly.TermResidualsCore (cinfo.levelParams.map mkLevelParam)) params
      withLocalDeclD `self structApp fun self => do
        let mut acc := #[]
        for fname in info.fieldNames do
          let proj := mkAppN (mkConst (``Vsa.Sim.TermAssembly.TermResidualsCore ++ fname) (cinfo.levelParams.map mkLevelParam)) (params.push self)
          let ty ← inferType proj
          let v ← refuteField ty
          acc := acc.push (fname.toString, v)
        return acc
    let body := String.intercalate "\n" (out.toList.map fun (n, v) => s!"{n}\t{v}")
    IO.FS.writeFile pathStx.getString ("field\tsweep_verdict\n" ++ body ++ "\n")
    let refuted := out.toList.filter (·.2 == "REFUTED") |>.map (·.1)
    logInfo m!"#sweep_refute → {out.size} fields; REFUTED={refuted.length}: {refuted}"
