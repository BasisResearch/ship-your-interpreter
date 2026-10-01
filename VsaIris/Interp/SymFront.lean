import VsaIris.Vsa.SymExecX
import VsaIris.Interp.SymInterp
import VsaIris.Interp.XrunAttr

/-!
# `xrun`: the extended executor for every run predicate

`xrun [fuel] hlive using [facts] calls [summaries] at pcs` runs `symRunX` (`SymExecX.lean`) on a
goal `SWP live text rs S Q pc R Mt`, under any abbreviation of it (`IW`, `NW`, `SnpW`, `AW`,
`SWPO`). The run table of the text (`StepGen.swpTbl?`) supplies the image, the code ranges, the
tracked registers, the load kinds (`D` data view, `H` havoc, `P` stop) and the `TblOK` fact
that discharges `RunCtx`; a text without a data view runs as one with the empty view
(`swp_noData`).

The run is cut into segments at the branches that constants, known registers and path facts do
not decide; each segment is one `symRunX_cont`, and a side of such a fork carries the facts of
its outcome into the next segment. A load inside the code ranges for every value of a bounded
index splits the run (jump tables).

**Calls.** `calls [t₁, …]` lists summaries: terms whose conclusion is a run at a literal entry
`pc`. At a stop of the executor on `jal ra, f` (or at `f` itself, a tail jump) with `f` the entry
of a summary, the `jal` is stepped by its step lemma and the summary is applied; each premise is
closed by the normaliser, the side tactic or `rfl`, or left as a goal; the summary's
continuation (`∀ R' M', … → run (R 1) R' M'`) is introduced and the run goes on, with every
introduced equation and every `RetOK` keep fact added to the facts.

Leftover goals: the reached states (in the goal's own head), undecided memory obligations
(`SOb.den` after the normaliser) and summary premises the closers could not prove.
-/

namespace VsaIris.SymExec.Front

open Lean Meta Elab Tactic
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.SymExec.Interp Vsa.Sim Vsa.MemRepr
open VsaIris.MallocFast

/-- Extension point of the normaliser (a file adds `macro_rules` under a scoped namespace). -/
syntax "xrun_hook" : tactic
macro_rules | `(tactic| xrun_hook) => `(tactic| fail)

def XTree.allObs : XTree → List SOb
  | .leaf s _ => s.obs
  | .br _ _ _ _ o t f => o ++ XTree.allObs t ++ XTree.allObs f
  | .brD _ o t => o ++ XTree.allObs t
  | .jr s _ => s.obs
  | .hv _ t => XTree.allObs t
  | .raw _ _ _ _ t => XTree.allObs t
  | .fwd _ _ _ _ t => XTree.allObs t
  | .sel _ _ t f => XTree.allObs t ++ XTree.allObs f
  | .dead => []
  | .jal _ _ t => XTree.allObs t

register_option xrun.trace : Bool := { defValue := false, descr := "report each xrun stage" }

register_option xrun.geom : Bool :=
  { defValue := true, descr := "prove the interval facts of the obligation checker (`geomOf`)" }

register_option xrun.geomMin : Nat :=
  { defValue := 3, descr := "fewest accesses of an address atom for which its interval fact is proved" }

register_option xrun.subst : Bool :=
  { defValue := false, descr := "a fork's `x = c` facts rewrite the registers and stores of its side" }

/-- The run table of a goal: text, registers, pieces, image, code ranges and `TblOK` proof. -/
structure Tgt where
  tbl : StepGen.Tbl
  T : Expr
  rs : Expr
  ps : Expr
  img : Expr
  rT : Expr
  ok : Expr

/-- The interpreter's code and constant tables (`binByte`, `interpRanges`): its jump tables are
read from the image. -/
theorem interp_tblOKro : TblOK interpText iRegs interpCodePieces binByte interpRanges :=
  ⟨codeAt_interp, interp_code, by decide, by decide⟩

def tgtOf (ty : Expr) : MetaM Tgt := do
  let some t ← StepGen.swpTbl? ty | throwError "xrun: no run table for this goal"
  let some okN := (if t.key == "interp" then some ``interp_tblOKro else t.ok)
    | throwError "xrun: the table {t.key} has no `TblOK` fact"
  let okTy ← whnfR (← inferType (mkConst okN))
  let a := okTy.getAppArgs
  unless a.size == 5 do throwError "xrun: unexpected `TblOK` type"
  return ⟨t, a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, mkConst okN⟩

theorem cover_of_acc {P : Nat → Prop} {X Y : Nat} (h : ∀ b ∈ accAddrs X (Y - X), P b) :
    ∀ b, X ≤ b → b < Y → P b := fun b h1 h2 => h b (mem_accAddrs_iff'.2 ⟨h1, by omega⟩)

/-- `A + l`, without the `+ 0`: the kernel never compares `x + 0` with `x` (which can make it
unfold `x`, a `toNat` of a sum with a large literal). -/
def addOff (A l : Nat) : Nat := if l = 0 then A else A + l

theorem addOff_eq (A l : Nat) : addOff A l = A + l := by unfold addOff; split <;> omega

/-- Every range `(l, h)` of `rs`, relative to `A`, is covered by `P`, in the shape of an access's
cover goal. -/
def scList (P : Nat → Prop) (A : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | r :: rs => (∀ b ∈ accAddrs (addOff A r.1) (r.2 - r.1), P b) ∧ scList P A rs

theorem scList_sound {P : Nat → Prop} {A : Nat} :
    ∀ {rs : List (Nat × Nat)}, scList P A rs → ∀ r ∈ rs, ∀ b, A + r.1 ≤ b → b < A + r.2 → P b
  | r :: rs, h, q, hq, b, h1, h2 => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1 b (mem_accAddrs_iff'.2 ⟨by rw [addOff_eq]; omega, by rw [addOff_eq]; omega⟩)
    · exact scList_sound h.2 q hq b h1 h2

theorem scList_cons {P : Nat → Prop} {A l h : Nat} {rs : List (Nat × Nat)}
    (h1 : ∀ b ∈ accAddrs (addOff A l) (h - l), P b) (h2 : scList P A rs) :
    scList P A ((l, h) :: rs) := ⟨h1, h2⟩

theorem scList_nil {P : Nat → Prop} {A : Nat} : scList P A [] := trivial

/-- One interval fact from its parts. -/
theorem afact_intro {ρ : Env} {S : Nat → Prop} {DA : List Nat} (f : AFact)
    (hlo : f.lo ≤ (f.atom.den ρ + f.shift).toNat) (hhi : (f.atom.den ρ + f.shift).toNat ≤ f.hi)
    (hmod : (f.atom.den ρ + f.shift).toNat % f.amod = 0)
    (hsc : scList S (f.atom.den ρ + f.shift).toNat f.sc)
    (hdc : scList (· ∈ DA) (f.atom.den ρ + f.shift).toNat f.dc)
    (hgap : ∀ g, f.gap = some g → (f.atom.den ρ + f.shift).toNat + g.1 ≤ tohostAddr ∨
      tohostAddr + g.2 ≤ (f.atom.den ρ + f.shift).toNat) : Geom.holds ρ S DA [f] := by
  intro g hg
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨hlo, hhi, hmod, scList_sound hsc, scList_sound hdc, hgap⟩

/-- What the walk needs. -/
structure XCtx where
  ty0 : Expr
  C : Expr
  hX : Expr
  fuel : Nat
  stops : List Nat
  env0 : Expr
  S : Expr
  DA : Expr
  norm : Syntax
  facts : Array Term
  proveGeom : MVarId → TacticM Bool
  gcache : IO.Ref (Array (Expr × Option Expr))
  segs : IO.Ref Nat
  maxSegs : Nat
  dbg : String → TacticM Unit
  /-- the goal had no data view (`swp_noData`): leaves go back to the goal's text -/
  noData : Bool
  /-- `x = c` facts rewrite the registers and stores of a fork side -/
  sub : Bool

def XTree.shape : XTree → String
  | .leaf s _ => s!"leaf {s.pc.toNat}"
  | .br pc _ _ _ _ t f => s!"br {pc.toNat} ({XTree.shape t}) ({XTree.shape f})"
  | .brD pc _ t => s!"brD {pc.toNat} {XTree.shape t}"
  | .jr s _ => s!"jr {s.pc.toNat}"
  | .hv _ t => s!"hv {XTree.shape t}"
  | .raw _ _ _ _ t => s!"raw {XTree.shape t}"
  | .fwd _ _ _ _ t => s!"fwd {XTree.shape t}"
  | .sel _ j t f => s!"sel{j} ({XTree.shape t}) {XTree.shape f}"
  | .dead => "dead"
  | .jal _ _ t => s!"jal {XTree.shape t}"

def isDecOb : SOb → Bool
  | .decM .. | .decT .. | .decO .. => true
  | _ => false

/-- Close the obligation list `go : ObsOK ρ S DA obs`; the undecided ones are returned. -/
def closeObs (cx : XCtx) (obs : List SOb) (go : MVarId) : TacticM (List MVarId) := do
  let mut hos : Array MVarId := #[]
  let mut cur := go
  for _ in obs do
    let [ho, hr] ← cur.apply (mkConst ``ObsOK_cons) | throwError "xrun: obs"
    hos := hos.push ho
    cur := hr
  let [] ← cur.apply (mkConst ``ObsOK_nil) | throwError "xrun: obs"
  let mut pend : List MVarId := []
  for (o, ho) in obs.zip hos.toList do
    let [ho] ← evalTacticAt (← `(tactic| simp only [SOb.den])) ho | throwError "xrun: obs"
    if isDecOb o then
      let [] ← evalTacticAt (← `(tactic| sym_dec)) ho | throwError "xrun: decode"
      continue
    -- an access obligation is two side goals (the access check and the cover)
    let parts ← match o with
      | .ld .. | .ldD .. | .st .. =>
        try evalTacticAt (← `(tactic| refine ⟨?_, ?_⟩)) ho catch _ => pure [ho]
      | _ => pure [ho]
    for hq in parts do
      let t1 ← IO.monoMsNow
      let tyS ← if (← getOptions).getBool `xrun.trace false || (← IO.getEnv "XRUN_TRACE").isSome then
          pure (toString (← ppExpr (← instantiateMVars (← hq.getType)))) else pure ""
      let saved ← saveState
      let ok ← try
          let mut fl : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
          for f in cx.facts do fl := fl.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
          let gs ← if fl.isEmpty then evalTacticAt (← `(tactic| ((try sym_den) <;> sx_side))) hq
            else evalTacticAt (← `(tactic| ((try sym_den) <;> (try simp only [$fl,*]) <;> sx_side))) hq
          pure gs.isEmpty
        catch _ => pure false
      let ok ← if ok then pure true else do
        saved.restore
        try
          let gs ← evalTacticAt (← `(tactic| ((try sym_den) <;> (try $(⟨cx.norm⟩)) <;> sx_side))) hq
          pure gs.isEmpty
        catch _ => pure false
      unless ok do
        saved.restore
        let gs ← try evalTacticAt (← `(tactic| ((try sym_den) <;> (try $(⟨cx.norm⟩))))) hq
          catch _ => pure [hq]
        pend := pend ++ gs
      cx.dbg s!"obligation ({ok}) {(← IO.monoMsNow) - t1}ms {tyS.take 160}"
  return pend

/-- The normalised branch premise of a fork side, or `none` when it is contradictory. -/
def premNorm (cx : XCtx) (g : MVarId) : TacticM (Option MVarId) := do
  let [g1] ← evalTacticAt (← `(tactic| intro hc)) g | throwError "xrun: intro"
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| (simp (disch := decide) only [regsDen, memDen, SE.den,
        aluVal, Env.withH, hset_self, hset_ne, shamtOf, shamt5Of, imm20Of,
        BitVec.reduceExtractLsb', guard_beq, guard_bne, guard_blt, guard_bge, guard_bltu,
        guard_bgeu, gF_beq, gF_bne, gF_blt, gF_bge, gF_bltu, gF_bgeu, rawR_eq] at hc))) g1
    match gs with
    | [] => return none
    | [g2] =>
      let mut fl : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
      for f in cx.facts do fl := fl.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
      let g3 ← if fl.isEmpty then pure [g2] else
        try evalTacticAt (← `(tactic| (try simp only [$fl,*] at hc) <;> (try sym_hnorm hc))) g2
        catch _ => pure [g2]
      match g3 with
      | [] => return none
      | [g3] =>
        -- contradiction by the side tactic
        let s2 ← saveState
        let refuted ← try
            let gs ← evalTacticAt (← `(tactic| (exfalso; revert hc; sx_side))) g3
            pure gs.isEmpty
          catch _ => pure false
        if refuted then return none
        s2.restore
        return some g3
      | _ => return some g2
    | _ => saved.restore; return some g1
  catch _ =>
    saved.restore; return some g1

/-- The reached state of a leaf in the goal's head `ty0`, normalised once (the denotation, then
the table's normaliser). -/
def contNorm1 (ty0 : Expr) (norm : Syntax) (gk : MVarId) : TacticM MVarId := do
  let [gk] ← evalTacticAt (← `(tactic| (try sym_den))) gk | throwError "xrun: continuation"
  let kty ← whnfR (← instantiateMVars (← gk.getType))
  let a := kty.getAppArgs
  unless kty.getAppFn.isConstOf ``SWP && a.size == 8 do throwError "xrun: not a run"
  let gk ← gk.replaceTargetDefEq (withState ty0 a[5]! a[6]! a[7]!)
  let saved ← saveState
  try
    match ← evalTacticAt norm gk with
    | [g'] => return g'
    | _ => saved.restore; return gk
  catch _ => saved.restore; return gk

/-- A reached state, in the goal's own head. -/
def finish (cx : XCtx) (gk : MVarId) : TacticM MVarId := do
  let t1 ← IO.monoMsNow
  let gk ← if cx.noData then
      match ← evalTacticAt (← `(tactic| refine swp_ofNoData ?_)) gk with
      | [g'] => pure g'
      | _ => throwError "xrun: noData leaf"
    else pure gk
  let r ← contNorm1 cx.ty0 cx.norm gk
  cx.dbg s!"continuation {(← IO.monoMsNow) - t1}ms"
  return r

mutual

partial def runSeg (cx : XCtx) (s : SS) (pf : List PF) (ρE hp : Expr) (used : Nat)
    (gk : MVarId) : TacticM (List MVarId) := gk.withContext do
  cx.segs.modify (· + 1)
  if (← cx.segs.get) > cx.maxSegs || used ≥ cx.fuel then
    return [← finish cx gk]
  let fuel := cx.fuel - used
  let run := mkApp5 (mkConst ``symRunX) cx.C (toExpr cx.sub) (mkNatLit fuel) (toExpr s) (toExpr pf)
  let tree ← unsafe evalExpr XTree (mkConst ``XTree) run
  cx.dbg s!"segment from {s.pc.toNat}: {XTree.shape tree}"
  let mut Γ : Geom := []
  let mut pfs : Array Expr := #[]
  let allObs := XTree.allObs tree
  let gmin := xrun.geomMin.get (← getOptions)
  let uses (a : SE) : Nat := (allObs.filter fun o => match needOf o with
    | some (b, _, _, _) => b == a
    | none => false).length
  for f in (geomOf allObs).filter (fun f => uses f.atom ≥ gmin) do
    let fE := toExpr f
    let pf? ← match (← cx.gcache.get).find? (·.1 == fE) with
      | some (_, r) => pure r
      | none =>
        let gg ← mkFreshExprMVar (← mkAppM ``Geom.holds #[cx.env0, cx.S, cx.DA, toExpr [f]])
        let r ← if ← cx.proveGeom gg.mvarId! then
            cx.dbg s!"geometry fact proved: {← ppExpr fE}"
            pure (some (← instantiateMVars gg)) else
          cx.dbg s!"geometry fact dropped: {← ppGoal gg.mvarId!}"
          pure none
        cx.gcache.modify (·.push (fE, r))
        pure r
    if let some p := pf? then
      Γ := Γ ++ [f]
      pfs := pfs.push p
  let hΓ ← pfs.foldrM (fun p acc => mkAppM ``geom_cons #[p, acc])
    (mkApp3 (mkConst ``geom_nil) cx.env0 cx.S cx.DA)
  let hXs ← Term.exprToSyntax cx.hX
  let Γs ← Term.exprToSyntax (toExpr Γ)
  let hΓs ← Term.exprToSyntax hΓ
  let ρs ← Term.exprToSyntax ρE
  let ss ← Term.exprToSyntax (toExpr s)
  let pfS ← Term.exprToSyntax (toExpr pf)
  let hps ← Term.exprToSyntax hp
  let fuelS := Syntax.mkNumLit (toString fuel)
  let subS ← Term.exprToSyntax (toExpr cx.sub)
  let [gw] ← evalTacticAt (← `(tactic| refine symRunX_cont $subS $hXs $Γs (by decide) $hΓs $fuelS $ρs
    rfl rfl rfl $ss $pfS $hps ?_)) gk | throwError "xrun: refine"
  let [gw] ← evalTacticAt (← `(tactic| symx_eval)) gw | throwError "xrun: eval"
  let steps := ((XTree.allObs tree).filter isDecOb).length
  walk cx (tree.prune Γ) (used + steps) gw

partial def walk (cx : XCtx) (t : XTree) (used : Nat) (g : MVarId) : TacticM (List MVarId) := do
  match t with
  | .leaf s _ =>
    let [go, gk] ← g.apply (mkConst ``XTree.WP_leaf) | throwError "xrun: leaf"
    let pend ← closeObs cx s.obs go
    let [gk] ← evalTacticAt (← `(tactic| intro hpf; clear hpf)) gk | throwError "xrun: intro"
    return pend ++ [← finish cx gk]
  | .jr s _ =>
    let [go, gk] ← g.apply (mkConst ``XTree.WP_jr) | throwError "xrun: jr"
    let pend ← closeObs cx s.obs go
    return pend ++ [← finish cx gk]
  | .brD _ obs t' =>
    let [go, g1] ← g.apply (mkConst ``XTree.WP_brD) | throwError "xrun: brD"
    let pend ← closeObs cx obs go
    return pend ++ (← walk cx t' used g1)
  | .hv _ t' =>
    let [g1] ← g.apply (mkConst ``XTree.WP_hv) | throwError "xrun: hv"
    let [g2] ← evalTacticAt (← `(tactic| intro _)) g1 | throwError "xrun: hv intro"
    walk cx t' used g2
  | .raw _ _ _ _ t' =>
    let [g1] ← g.apply (mkConst ``XTree.WP_raw) | throwError "xrun: raw"
    walk cx t' used g1
  | .fwd _ _ _ _ t' =>
    let [g1] ← g.apply (mkConst ``XTree.WP_fwd) | throwError "xrun: fwd"
    walk cx t' used g1
  | .sel _ _ tt ff =>
    let [g1, g2] ← g.apply (mkConst ``XTree.WP_sel) | throwError "xrun: sel"
    let [g1] ← evalTacticAt (← `(tactic| intro _)) g1 | throwError "xrun: sel intro"
    let [g2] ← evalTacticAt (← `(tactic| intro _)) g2 | throwError "xrun: sel intro"
    return (← walk cx tt used g1) ++ (← walk cx ff used g2)
  | .dead =>
    let [] ← g.apply (mkConst ``XTree.WP_dead) | throwError "xrun: dead"
    return []
  | .jal _ _ t' =>
    let [gd, g1] ← g.apply (mkConst ``XTree.WP_jal) | throwError "xrun: jal"
    let [] ← evalTacticAt (← `(tactic| symx_dec)) gd | throwError "xrun: jal decode"
    walk cx t' used g1
  | .br _ _ _ _ obs tt ff =>
    let [go, gt, gf] ← g.apply (mkConst ``XTree.WP_br) | throwError "xrun: br"
    let pend ← closeObs cx obs go
    let side (gs : MVarId) (child : XTree) : TacticM (List MVarId) := do
      let some gs ← premNorm cx gs | return []
      match child with
      | .leaf cs pf' =>
        if cx.stops.contains cs.pc.toNat then return ← walk cx child used gs
        let [go, gk] ← gs.apply (mkConst ``XTree.WP_leaf) | throwError "xrun: leaf"
        let [] ← go.apply (mkConst ``ObsOK_nil) | throwError "xrun: obs"
        let [gk] ← evalTacticAt (← `(tactic| intro hpf)) gk | throwError "xrun: intro"
        gk.withContext do
          let hp := (← getLCtx).lastDecl.get!.toExpr
          let ρE := (← whnfR (← inferType hp)).getAppArgs[0]!
          runSeg cx cs pf' ρE hp used gk
      | _ => walk cx child used gs
    return pend ++ (← side gt tt) ++ (← side gf ff)

end

/-- The literal facts of the goal and of `facts`: known registers, known data-view and
entry-memory words (as `symRunCore`). -/
def readFacts (R Mt Dt : Expr) (facts : Array Term) :
    TacticM (List (Nat × BitVec 64) × List (MKind × SE × BitVec 64) × List (MKind × SE × BitVec 64)) := do
  let Rf := Id.run do
    let mut e := R
    while e.isAppOfArity ``upd 4 || e.isAppOfArity ``upd 3 do e := e.getAppArgs[0]!
    return e
  let written : List Nat := Id.run do
    let mut e := R
    let mut ws : List Nat := []
    while e.isAppOfArity ``upd 4 || e.isAppOfArity ``upd 3 do
      if let some k := e.getAppArgs[1]!.nat? then ws := k :: ws
      e := e.getAppArgs[0]!
    return ws
  let regOf? (lhs : Expr) : Option Nat :=
    if lhs.isApp && lhs.appFn! == R then lhs.appArg!.nat?
    else if lhs.isApp && lhs.appFn! == Rf then
      match lhs.appArg!.nat? with
      | some i => if written.contains i then none else some i
      | none => none
    else none
  let mut known : List (Nat × BitVec 64) := []
  let mut rch := R
  let mut seenK : List Nat := []
  while rch.isAppOfArity ``upd 4 || rch.isAppOfArity ``upd 3 do
    if let some k := rch.getAppArgs[1]!.nat? then
      unless seenK.contains k do
        seenK := k :: seenK
        if let some ⟨64, v⟩ ← getBitVecValue? rch.getAppArgs[2]! then known := known ++ [(k, v)]
    rch := rch.getAppArgs[0]!
  let mut regEqs : Array (Nat × Expr) := #[]
  let mut ldFacts : Array (Expr × Expr) := #[]
  for f in facts do
    let fe ← try Term.elabTerm f none catch _ => continue
    let fty ← instantiateMVars (← inferType fe)
    if let some (_, lhs, rhs) := fty.eq? then
      if let some i := regOf? lhs then
        regEqs := regEqs.push (i, rhs)
        if let some ⟨64, v⟩ ← getBitVecValue? rhs then
          unless known.any (·.1 == i) do known := known ++ [(i, v)]
      else if lhs.isAppOfArity ``ldv 3 then
        ldFacts := ldFacts.push (lhs, rhs)
  let mut kv : List (MKind × SE × BitVec 64) := []
  let mut kvM : List (MKind × SE × BitVec 64) := []
  for (lhs, rhs) in ldFacts do
    let args := lhs.getAppArgs
    let some ⟨64, v⟩ ← getBitVecValue? rhs | continue
    let onD ← isDefEq args[1]! Dt
    let onM := !onD && args[1]! == Mt
    unless onD || onM do continue
    let kE ← whnfR args[0]!
    let some k := kE.constName?.bind mkindOf? | continue
    let ad := args[2]!
    if let some n := ad.nat? then
      if onD then kv := kv ++ [(k, .c (BitVec.ofNat 64 n), v)]
      else kvM := kvM ++ [(k, .c (BitVec.ofNat 64 n), v)]
      continue
    unless ad.isAppOfArity ``BitVec.toNat 2 do continue
    let x := ad.appArg!
    let (xb, off) ← do
      if x.isAppOfArity ``HAdd.hAdd 6 then
        match ← getBitVecValue? x.appArg! with
        | some ⟨64, c⟩ => pure (x.appFn!.appArg!, c)
        | _ => pure (x, (0 : BitVec 64))
      else pure (x, (0 : BitVec 64))
    for (i, e) in regEqs do
      if e == xb then
        if onD then kv := kv ++ [(k, addC (.r i) off, v)]
        else kvM := kvM ++ [(k, addC (.r i) off, v)]
  return (known, kv, kvM)

/-- The normaliser of a run table, as the table's step driver normalises after each step
(`nx_run` for stdio, `snp_run`, `sym_run`, `sx_run`); it is parsed in the caller's environment,
whose imports declare the table's tactics. `F` is the fact rewrite. -/
def normStr (key F : String) : String :=
  match key with
  | "stdio" => s!"((try nx_tidy) <;> (try simp only [VsaIris.Sym.updAll] at ⊢) <;> (try simp only [nx_mt] at ⊢) <;> (try nx_norm) <;> (try {F}) <;> (try nx_norm) <;> (try nx_mem) <;> (try nx_console) <;> (try {F}) <;> (try nx_norm) <;> (try simp (disch := omega) only [toInt_ofNat_small, BitVec.toInt_zero]) <;> (try simp (disch := decide) only [VsaIris.Sym.update_aligned]) <;> (try simp only [BitVec.sub_self, VsaIris.Sym.sext_zero32, BitVec.toInt_zero]))"
  | "snp" => s!"((try sx_norm) <;> (try {F}) <;> (try ((try nx_tab) <;> (try ix_mem) <;> (try {F}))) <;> (try sx_norm) <;> (try ix_mem))"
  | "interp" => s!"((try sx_norm) <;> (try {F}) <;> (try ix_tab) <;> (try sx_norm) <;> (try ix_mem))"
  | _ => s!"((try sx_norm) <;> (try {F}) <;> (try sx_mem) <;> (try sx_norm) <;> (try {F}))"

/-- The literal entry of a summary: the `pc` of its conclusion. -/
def entryOf (t : Term) : TacticM (Option Nat) := withoutModifyingState do
  try
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (postpone := .yes)
    let ty ← instantiateMVars (← inferType e)
    forallTelescopeReducing ty fun _ body => do
      let w ← whnfR body
      unless w.getAppFn.isConstOf ``SWP && w.getAppNumArgs == 8 do return none
      match ← getBitVecValue? w.getAppArgs[5]! with
      | some ⟨_, v⟩ => return some v.toNat
      | none => return none
  catch _ => return none

/-- The run goal's literal `pc`, if it is a run. -/
def runPC? (g : MVarId) : MetaM (Option Nat) := g.withContext do
  let w ← whnfR (← instantiateMVars (← g.getType))
  unless w.getAppFn.isConstOf ``SWP && w.getAppNumArgs == 8 do return none
  match ← getBitVecValue? w.getAppArgs[5]! with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- Whether `g` is a run (any head that unfolds to `SWP`). -/
def isRun (g : MVarId) : MetaM Bool := g.withContext do
  let w ← whnfR (← instantiateMVars (← g.getType))
  return w.getAppFn.isConstOf ``SWP

/-- Whether `g` is a summary continuation: binders, then a run. -/
def isCont (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  forallTelescopeReducing ty fun xs body => do
    let w ← whnfR body
    return !xs.isEmpty && w.getAppFn.isConstOf ``SWP

/-- `t`, elaborated with its type, or `none`. -/
def elabFact? (t : Term) : TacticM (Option Expr) := do
  let saved ← saveState
  try
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasSyntheticSorry || e.hasMVar then saved.restore; return none
    return some e
  catch _ => saved.restore; return none

/-- The facts the run goes on with after a summary returns: every introduced equation, and the
instances of the `@[xrun_post]` lemmas at every introduced hypothesis. -/
def harvest (g0 g : MVarId) (facts : Array Term) : TacticM (Array Term) := g.withContext do
  let old ← g0.withContext do pure ((← getLCtx).getFVarIds)
  let posts ← labelled `xrun_post
  let mut fs := facts
  for d in ← getLCtx do
    if d.isImplementationDetail || old.contains d.fvarId then continue
    let ty ← instantiateMVars d.type
    if ty.isEq then
      fs := fs.push (← Term.exprToSyntax d.toExpr)
      continue
    let hS ← Term.exprToSyntax d.toExpr
    for L in posts do
      let some t ← elabFact? (← `($(mkCIdent L) $hS)) | continue
      let tty ← whnfR (← inferType t)
      if tty.isEq then
        fs := fs.push (← Term.exprToSyntax t)
      else if tty.isForall then
        let tS ← Term.exprToSyntax t
        for x in List.range 32 do
          let some tx ← elabFact? (← `($tS $(Syntax.mkNumLit (toString x)) (by decide))) | continue
          if (← inferType tx).isEq then fs := fs.push (← Term.exprToSyntax tx)
  return fs

/-- One `xrun` on `g`; the leftover goals. -/
partial def xrunGoal (fuel : Nat) (h : Syntax) (facts : Array Term) (stops : List Nat)
    (calls : Array (Term × Nat)) (depth : Nat) (normOverride : Option Syntax) (g : MVarId) :
    TacticM (List MVarId) := do
  let t0 ← IO.monoMsNow
  let trace := (← getOptions).getBool `xrun.trace false || (← IO.getEnv "XRUN_TRACE").isSome
  let dbg (m : String) : TacticM Unit := do
    if trace then IO.eprintln s!"xrun: {m} @{(← IO.monoMsNow) - t0}ms"
  let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $f:term))
  let post ← `(tactic| skip)
  let key ← g.withContext do
    match ← StepGen.swpTbl? (← whnfR (← instantiateMVars (← g.getType))) with
    | some t => pure t.key
    | none => pure ""
  let F := if facts.isEmpty then "skip" else
    "simp only [" ++ ", ".intercalate (facts.toList.map fun f => (f.raw.reprint.getD "").trimAscii.toString) ++ "]"
  let base ← match normOverride with
    | some n => pure n
    | none =>
      match Parser.runParserCategory (← getEnv) `tactic (normStr key F) with
      | .ok stx => pure stx
      | .error _ =>
        if lems.isEmpty then
          `(tactic| ((try sx_norm) <;> (try sx_norm) <;> (try ix_mem)))
        else
          `(tactic| ((try sx_norm) <;> (try simp only [$lems,*]) <;> (try sx_norm) <;> (try ix_mem) <;>
            (try simp only [$lems,*])))
  let norm ← `(tactic| ((try ($post:tactic)) <;> (try xrun_hook) <;> $(⟨base⟩)))
  let g ← do
    let saved ← saveState
    try
      match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) g with
      | [g'] => pure g'
      | _ => saved.restore; pure g
    catch _ => saved.restore; pure g
  -- a continuation's pc may be a register read (`R' 1`): normalise it first
  let g ← if (← runPC? g).isSome then pure g else do
    let saved ← saveState
    try
      match ← evalTacticAt norm g with
      | [g'] => pure g'
      | _ => saved.restore; pure g
    catch _ => saved.restore; pure g
  g.withContext do
  let ty0 := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  let w ← whnfR ty0
  unless w.getAppFn.isConstOf ``SWP && w.getAppNumArgs == 8 do throwError "xrun: goal is not a run"
  let a := w.getAppArgs
  let some ⟨_, pcv⟩ ← getBitVecValue? a[5]! | return [g]
  if stops.contains pcv.toNat then return [g]
  let entries := calls.toList.map (·.2)
  let tg ← tgtOf w
  -- the text: `T ++ dataOf Dt DA`, or `T` (no data view)
  let text ← whnfR a[1]!
  let (g, noData, a, Dt, DA) ← do
    if text.isAppOfArity ``HAppend.hAppend 6 then
      let d := text.getAppArgs[5]!
      let dArgs := d.getAppArgs
      if d.isAppOfArity ``dataOf 2 then
        pure (g, false, a, dArgs[0]!, dArgs[1]!)
      else throwError "xrun: unexpected data view"
    else
      let [g'] ← evalTacticAt (← `(tactic| refine swp_noData ?_)) g
        | throwError "xrun: noData"
      let ty' ← instantiateMVars (← g'.getType)
      let w' ← whnfR ty'
      let d := (w'.getAppArgs[1]!).getAppArgs[5]!
      pure (g', true, w'.getAppArgs, d.getAppArgs[0]!, d.getAppArgs[1]!)
  g.withContext do
  let R := a[6]!
  let Mt := a[7]!
  let (known, kv, kvM) ← readFacts R Mt Dt facts
  let variant (k : String) : List (BitVec 64) :=
    ((tg.tbl.variants.lookup k).getD []).map (BitVec.ofNat 64)
  let stopsAll := stops ++ entries.filter (· != pcv.toNat)
  let stopsBV : List (BitVec 64) := stopsAll.map (BitVec.ofNat 64) ++ variant "P"
  let C := mkAppN (mkConst ``Cfg.mk) #[tg.img, tg.rT, tg.rs, toExpr stopsBV,
    toExpr ([] : List SE), toExpr kv, toExpr kvM, toExpr known, mkApp (mkConst ``bytesHasB) tg.ps,
    toExpr (variant "D"), toExpr ([] : List (BitVec 64)), toExpr (variant "H"), toExpr true]
  let hX ← mkFreshExprMVar (mkAppN (mkConst ``RunCtx) #[a[0]!, tg.T, Dt, C, R, Mt])
  let okS ← Term.exprToSyntax tg.ok
  let gs ← evalTacticAt (← `(tactic| refine RunCtx.mk ($okS).code (fun _ _ hb => ($okS).foot hb)
    $(⟨h⟩) ($okS).pc ($okS).gp (by decide) ?_ ?_ (knownAll_mem ?_))) hX.mvarId!
  let [gK, gKm, gKn] := gs | throwError "xrun: refine RunCtx"
  let closers ← `(tactic| (and_intros <;> first | with_reducible rfl | with_reducible assumption))
  let knownA ← `(tactic| simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    false_implies, implies_true, and_true, SE.den, addC, BitVec.add_zero, BitVec.reduceToNat,
    $lems,*])
  let knownB ← `(tactic| simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
    false_implies, implies_true, and_true, SE.den, addC, upd_apply, Nat.reduceEqDiff, ite_true,
    ite_false, BitVec.add_zero, BitVec.reduceToNat, $lems,*])
  let tryKnown (tac : Syntax) (gg : MVarId) : TacticM Bool := do
    let saved ← saveState
    try
      let gs ← withoutRecover (evalTacticAt tac gg)
      for g1 in gs do
        unless (← withoutRecover (evalTacticAt closers g1)).isEmpty do throwError "open"
      return true
    catch _ =>
      saved.restore
      return false
  for gg in [gK, gKm] do
    unless ← tryKnown knownA gg do
      unless ← tryKnown knownB gg do throwError "xrun: known values"
  do
    let gs ← evalTacticAt (← `(tactic| (simp only [KnownAll] <;> and_intros))) gKn
    for g1 in gs do
      let saved ← saveState
      let ok ← try
          pure (← withoutRecover (evalTacticAt (← `(tactic| first
            | exact True.intro | exact rfl
            | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, $lems,*]; done)
            | assumption)) g1)).isEmpty
        catch _ => pure false
      unless ok do saved.restore; throwError "xrun: known register values"
  dbg "context"
  let rho := mkApp4 (mkConst ``Env.mk) R Mt Dt (.lam `_ (mkConst ``Nat) (toExpr (0 : BitVec 64)) .default)
  let mut glems := lems
  for n in headConsts a[3]! ++ headConsts DA do
    glems := glems.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  glems := glems.push (← `(Lean.Parser.Tactic.simpLemma| InExt))
  let geomTac ← `(tactic| (simp only [Geom.holds, List.mem_cons, forall_eq_or_imp,
    List.not_mem_nil, false_implies, implies_true, and_true, AFact.holds, SE.den, reduceCtorEq,
    Option.some.injEq, forall_eq', List.mem_append, mem_accAddrs_iff', Nat.mod_one, forall_const,
    BitVec.add_zero, upd_apply, Nat.reduceEqDiff, ite_true, ite_false, $glems,*] <;> and_intros <;>
    (try intros) <;> first | exact True.intro |
      (have _htoh : tohostAddr = 0x8001ad00 := rfl; omega)))
  let geomOn := (← getOptions).getBool `xrun.geom true
  -- one interval fact per address atom: its bounds and alignment by arithmetic, each covered
  -- range by the side tactic (the shape of an access's cover goal); no rewriting under the frame
  -- predicate
  let factSimp ← if lems.isEmpty then `(tactic| skip) else `(tactic| simp only [$lems,*])
  let arithTac ← `(tactic| ((try $factSimp:tactic) <;>
      first | (have _htoh : tohostAddr = 0x8001ad00 := rfl; omega) | sx_addr))
  let coverTac ← `(tactic| ((try $factSimp:tactic) <;> sx_side))
  let closeWith (tac : Syntax) (g : MVarId) : TacticM Bool := do
    let s1 ← saveState
    try
      if (← withoutRecover (evalTacticAt tac g)).isEmpty then return true
      s1.restore; return false
    catch _ => s1.restore; return false
  let geomParts (gg : MVarId) : TacticM Bool := do
    let gs ← evalTacticAt (← `(tactic| refine afact_intro _ ?_ ?_ ?_ ?_ ?_ ?_)) gg
    let [glo, ghi, gmod, gsc, gdc, ggap] := gs | return false
    -- the gap: none, or one disjunction over literals
    let ggs ← evalTacticAt (← `(tactic| (rintro ⟨g1, g2⟩ hg; cases hg))) ggap
    for g in ggs do
      let [g] ← evalTacticAt (← `(tactic| (dsimp only [SE.den]; try simp only [BitVec.add_zero]))) g
        | return false
      unless ← closeWith arithTac g do return false
    for g in [glo, ghi, gmod] do
      -- unfold the denotation definitionally, rewrite `+ 0` propositionally: a definitional
      -- `x + 0 ≡ x` can make the kernel unfold `x` (a `toNat` of a sum with a large literal)
      let [g] ← evalTacticAt (← `(tactic| (dsimp only [SE.den]; try simp only [BitVec.add_zero]))) g
        | return false
      unless ← closeWith arithTac g do return false
    for g in [gsc, gdc] do
      -- one cover goal per range, each brought to the access-cover shape by propositional
      -- rewrites (a definitional `x + 0 ≡ x` can make the kernel unfold `x`)
      let mut cur := g
      let mut covers : Array MVarId := #[]
      repeat
        let s1 ← saveState
        try
          let [] ← evalTacticAt (← `(tactic| exact scList_nil)) cur | throwError "nil"
          break
        catch _ => s1.restore
        let [h1, h2] ← evalTacticAt (← `(tactic| refine scList_cons ?_ ?_)) cur | return false
        covers := covers.push h1
        cur := h2
      for g in covers do
        let gs ← evalTacticAt (← `(tactic| (dsimp only [addOff, SE.den, Nat.reduceSub]))) g
        for g in gs do
          if (← getOptions).getBool `xrun.trace false || (← IO.getEnv "XRUN_TRACE").isSome then
            IO.eprintln s!"xrun: cover goal {← ppExpr (← instantiateMVars (← g.getType))}"
          unless ← closeWith coverTac g do return false
    return true
  let proveGeom (gg : MVarId) : TacticM Bool := do
    unless geomOn do return false
    let saved ← saveState
    let ok1 ← try geomParts gg catch _ => pure false
    if ok1 then return true
    saved.restore
    -- a frame predicate that unfolds to arithmetic: the whole fact by `omega`
    try
      let gs ← withoutRecover (evalTacticAt geomTac gg)
      if gs.isEmpty then return true
      saved.restore; return false
    catch _ => saved.restore; return false
  let hXe ← instantiateMVars hX
  let gc ← IO.mkRef #[]
  let sg ← IO.mkRef 0
  let sub := (← getOptions).getBool `xrun.subst false
  let cx : XCtx := XCtx.mk ty0 C hXe fuel stopsAll rho a[3]! DA norm facts proveGeom gc sg 64 dbg
    noData sub
  let s0 : SS := ⟨BitVec.ofNat 64 pcv.toNat, [], [], []⟩
  let hp := mkApp (mkConst ``pfok_nil) rho
  let gs ← runSeg cx s0 [] rho hp 0 g
  dbg s!"walk: {gs.length} goals, {← sg.get} segments"
  -- a stop of the executor: a summary at its entry, or the table's step lemma at an instruction
  -- the executor does not step (an indirect call, a console store); the run goes on from each
  -- continuation
  if depth ≥ 48 then return gs
  let mut out : List MVarId := []
  for g1 in gs do
    let some p ← runPC? g1 | out := out ++ [g1]; continue
    if stops.contains p then out := out ++ [g1]; continue
    let saved ← saveState
    let subs? ← match calls.find? (·.2 == p) with
      | some (t, _) =>
        try
          let r ← evalTacticAt (← `(tactic| apply $t)) g1
          dbg s!"summary at {p}: {r.length} premises"
          pure (some r)
        catch e =>
          dbg s!"summary at {p} does not apply: {← e.toMessageData.toString}"
          saved.restore; pure none
      | none =>
        let mut r : Option (List MVarId) := none
        for kind in tg.tbl.kinds do
          if kind == "jalx" then continue
          let some nm ← (try StepGen.stepLemma tg.tbl kind p catch _ => pure none) | continue
          let s1 ← saveState
          try
            r := some (← evalTacticAt (← `(tactic| apply $(mkCIdent nm) $(⟨h⟩))) g1)
            dbg s!"step lemma {nm} at {p}"
            break
          catch _ => s1.restore
        pure r
    let some subs := subs? | out := out ++ [g1]; continue
    for g2 in subs do
      if ← g2.isAssigned then continue
      if ← isCont g2 <||> (do pure (← runPC? g2).isSome <||> isRun g2) then
        let [g3] ← evalTacticAt (← `(tactic| intros)) g2 | out := out ++ [g2]; continue
        let rest ← g3.withContext do
          let fs ← harvest g2 g3 facts
          xrunGoal fuel h fs stops calls (depth + 1) normOverride g3
        out := out ++ rest
      else
        let s2 ← saveState
        let ok ← try
            let r ← evalTacticAt (← `(tactic| ((try $(⟨norm⟩)) <;> first | done | rfl | assumption | sx_side))) g2
            pure r.isEmpty
          catch _ => pure false
        unless ok do s2.restore; out := out ++ [g2]
  return out

syntax "xrun " ("[" num "] ")? term (" using " "[" term,* "]")? (" calls " "[" term,* "]")?
  (" at " num+)? (" xnorm " "(" tactic ")")? : tactic

elab_rules : tactic
  | `(tactic| xrun $[[$n]]? $h $[using [$fs,*]]? $[calls [$cs,*]]? $[at $stops*]? $[xnorm ($nt)]?) => do
    let fuel := (n.map (·.getNat)).getD 400
    let facts : Array Term := match fs with | some fs => fs.getElems | none => #[]
    let stopPCs : List Nat := match stops with | some ss => ss.toList.map (·.getNat) | none => []
    let g ← getMainGoal
    let cl ← g.withContext do
      let mut out : Array (Term × Nat) := #[]
      for c in (match cs with | some cs => cs.getElems | none => #[]) do
        match ← entryOf c with
        | some p => out := out.push (c, p)
        | none => throwError "xrun: the summary {c} does not conclude a run at a literal pc"
      pure out
    let gs ← xrunGoal fuel h facts stopPCs cl 0 (nt.map (·.raw)) g
    replaceMainGoal gs

end VsaIris.SymExec.Front
