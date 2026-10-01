import Lean

namespace Vsa.OmegaHint
open Lean Meta Elab Tactic Omega

register_option vsa.omegaHint : Bool := {
  defValue := true
  descr := "omega first tries the hypotheses earlier omega certificates of this declaration used"
}

register_option vsa.omegaHintMin : Nat := {
  defValue := 40
  descr := "smallest number of hypotheses at which the reduced omega is tried first"
}

structure Keys where
  fv : Std.HashSet FVarId := {}
  ty : Std.HashSet Expr := {}

def Keys.union (a b : Keys) : Keys :=
  { fv := b.fv.fold (·.insert ·) a.fv, ty := b.ty.fold (·.insert ·) a.ty }

structure St where
  last : Keys := {}
  hot : Keys := {}
  seen : Keys := {}

initialize stRef : IO.Ref (Std.HashMap Name St) ← IO.mkRef {}

structure Info where
  nAll : Nat := 0
  sizes : Array Nat := #[]
  stage : Nat := 0
  failMs : Float := 0
  okMs : Float := 0

def record (d : Name) (s : St) (all : Array FVarId) (used : Array Expr) : MetaM Unit := do
  let mut seen := s.seen
  for f in all do
    unless seen.fv.contains f do
      seen := { fv := seen.fv.insert f, ty := seen.ty.insert (← instantiateMVars (← f.getType)) }
  let mut u : Keys := {}
  for a in used do
    if let .fvar f := a then
      if let some ld := (← getLCtx).find? f then
        u := { fv := u.fv.insert f, ty := u.ty.insert (← instantiateMVars ld.type) }
  let s' : St := { last := u, hot := s.hot.union u, seen := seen }
  stRef.modify fun m => (if m.size > 256 then {} else m).insert d s'

def solve (type : Expr) (hyps : List Expr) (cfg : OmegaConfig) : MetaM Expr := do
  let g' ← mkFreshExprSyntheticOpaqueMVar type
  omega hyps g'.mvarId! cfg
  mkAuxTheorem type (← instantiateMVars g') (zetaDelta := true)

def run (cfg : OmegaConfig) : TacticM Info := do
  let infoRef ← IO.mkRef ({} : Info)
  let d := (← Term.getDeclName?).getD .anonymous
  let minHyps := vsa.omegaHintMin.get (← getOptions)
  liftMetaFinishingTactic fun g0 => do
    let ctx0 ← g0.withContext getLCtx
    let some g ← g0.falseOrByContra | return ()
    g.withContext do
      let type ← g.getType
      let hyps ← getLocalHyps
      let all := hyps.filterMap fun e => if let .fvar f := e then some f else none
      let st? := (← stRef.get)[d]?
      let st := st?.getD {}
      let mut cands : Array (Array Expr) := #[]
      if st?.isSome && hyps.size ≥ minHyps then
        let mut s1 : Array Expr := #[]
        let mut s2 : Array Expr := #[]
        for h in hyps do
          let .fvar f := h | s1 := s1.push h; s2 := s2.push h; continue
          if !ctx0.contains f || st.last.fv.contains f then
            s1 := s1.push h; s2 := s2.push h; continue
          if st.hot.fv.contains f then s2 := s2.push h; continue
          if st.seen.fv.contains f then continue
          let t ← instantiateMVars (← f.getType)
          if !st.seen.ty.contains t || st.last.ty.contains t then
            s1 := s1.push h; s2 := s2.push h
          else if st.hot.ty.contains t then s2 := s2.push h
        if s1.size < s2.size then cands := cands.push s1
        if s2.size < hyps.size then cands := cands.push s2
      infoRef.set { nAll := hyps.size, sizes := cands.map (·.size) }
      let mut i := 0
      for c in cands do
        i := i + 1
        let s0 ← saveState
        let t0 ← IO.monoNanosNow
        try
          let e ← solve type c.toList cfg
          let t1 ← IO.monoNanosNow
          infoRef.modify fun r => { r with stage := i, okMs := (t1 - t0).toFloat / 1e6 }
          record d st all e.getAppArgs
          g.assign e
          return
        catch _ =>
          s0.restore
          let t1 ← IO.monoNanosNow
          infoRef.modify fun r => { r with failMs := r.failMs + (t1 - t0).toFloat / 1e6 }
      infoRef.modify fun r => { r with stage := if cands.isEmpty then 0 else 9 }
      let e ← solve type hyps.toList cfg
      record d st all e.getAppArgs
      g.assign e
  infoRef.get

def evalHint (stx : Syntax) : TacticM Info := do
  if !vsa.omegaHint.get (← getOptions) then evalOmega stx; return {}
  match stx with
  | `(tactic| omega%$tk $cfg:optConfig) =>
    recordExtraModUse (isMeta := false) `Init.Omega
    (do Meta.withReducibleAndInstances (evalAssumption tk); return {}) <|> do
      let cfg ← elabOmegaConfig cfg
      run cfg
  | _ => throwUnsupportedSyntax

@[no_fallback, tactic Lean.Parser.Tactic.omega] def evalOmegaHint : Tactic := fun stx => do
  if !vsa.omegaHint.get (← getOptions) || debug.terminalTacticsAsSorry.get (← getOptions) then
    throwUnsupportedSyntax
  discard <| evalHint stx

end Vsa.OmegaHint
