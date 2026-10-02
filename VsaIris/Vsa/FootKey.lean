import VsaIris.Vsa.KeyNF
import VsaIris.Vsa.AllocTac

/-!
# Footprint membership by keys

A side goal of a run step is a footprint predicate (any definition that unfolds to `∨`/`∧` of
`Nat` comparisons, `x % w = 0` and literal constants), possibly under `∀ b ∈ accAddrs a w`.
`foot_key` brings every bound to an atom + literal key (`linNF`: register equations, `% 2^64`
wrap-around removed by a ceiling fact, negative offsets by a floor) and decides each disjunct by
its literals: same atom by a closed `Nat.ble`; across atoms by one fact or a chain of two
(facts: the comparisons of the context, conjunctions split, and the access range `a ≤ b < a+w`).
No `omega` runs; an undecided goal fails, and `sx_addr` falls back to its old route.
-/

namespace VsaIris.VsaHeap

open Lean Elab Tactic Meta VsaIris.Sym

theorem foot_intro {a w : Nat} {P : Nat → Prop} (h : ∀ b, a ≤ b → b < a + w → P b) :
    ∀ b ∈ accAddrs a w, P b :=
  fun b hb => (of_mem_accAddrs hb).elim (h b)
theorem le_lit_atom {x y t a b : Nat} (px : x = 0 + a) (py : y = t + b) (h : Nat.ble a b = true) :
    x ≤ y := by rw [Nat.ble_eq] at h; subst px py; omega
theorem dif_chain {x y y' z t s u a b b' c A B : Nat} (h1 : x ≤ y) (px : x = t + a) (py : y = s + b)
    (h2 : y' ≤ z) (py' : y' = s + b') (pz : z = u + c) (hA : a + b' = A) (hB : b + c = B) :
    t + A ≤ u + B := by omega
theorem dif_dropL {x y X Y T t r t2 a b c d : Nat} (h : x ≤ y) (px : x = T + a) (py : y = t2 + b)
    (hs : t + r = T) (pX : X = t + c) (pY : Y = t2 + d) (hc : Nat.ble (c + b) (a + d) = true) :
    X ≤ Y := by rw [Nat.ble_eq] at hc; omega
theorem dif_dropR {x y X Y t1 s r S a b c d : Nat} (h : x ≤ y) (px : x = t1 + a) (py : y = s + b)
    (hs : s + r = S) (pX : X = t1 + c) (pY : Y = S + d) (hc : Nat.ble (c + b) (a + d) = true) :
    X ≤ Y := by rw [Nat.ble_eq] at hc; omega
theorem al_key {x t c w : Nat} (px : x = t + c) (ht : t % w = 0) (hc : (c % w == 0) = true) :
    x % w = 0 := by
  simp only [beq_iff_eq] at hc; subst px; rw [Nat.add_mod, ht, hc, Nat.zero_add, Nat.zero_mod]
theorem key_ne {x y t a b : Nat} (px : x = t + a) (py : y = t + b) (h : (a == b) = false) :
    x ≠ y := by
  intro e; subst px py; simp only [beq_eq_false_iff_ne] at h; omega

/-- `Prod.fst/snd` of a pair and `Nat` constants whose value is a literal, reduced. -/
def footClean (e : Expr) : MetaM Expr := do
  if !(e.find? fun t => t.isAppOfArity ``Prod.fst 3 || t.isAppOfArity ``Prod.snd 3 || t.isConst).isSome then
    return e
  Core.transform e (post := fun t => do
    if (t.isAppOfArity ``Prod.fst 3 || t.isAppOfArity ``Prod.snd 3) then
      let p := t.appArg!
      if p.isAppOfArity ``Prod.mk 4 then
        return .done (if t.isAppOfArity ``Prod.fst 3 then p.getArg! 2 else p.getArg! 3)
    if let .const n _ := t then
      if let some (.defnInfo d) := (← getEnv).find? n then
        if d.type.isConstOf ``Nat && d.levelParams.isEmpty then
          if let some k := d.value.nat? then return .done (mkNatLit k)
    return .continue)

/-- The goal as a tree of `∨`/`∧` over leaves, definitions unfolded (bounded). `none` when no
leaf is a comparison. -/
partial def footPrep (fuel : Nat) (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Or 2 || e.isAppOfArity ``And 2 then
    let a ← footPrep fuel e.appFn!.appArg!
    let b ← footPrep fuel e.appArg!
    match a, b with
    | none, none => return none
    | a, b => return some (mkApp2 e.appFn!.appFn! (a.getD e.appFn!.appArg!) (b.getD e.appArg!))
  if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``Eq 3 ||
      e.isAppOfArity ``Ne 3 then
    let ty := e.getArg! 0
    unless ty.isConstOf ``Nat do return none
    return some (← footClean e)
  if fuel == 0 then return none
  let .const _ _ := e.getAppFn | return none
  let some e' ← unfoldDefinition? e | return none
  footPrep (fuel - 1) e'

/-- Split a fact into its conjuncts (bounded depth). -/
partial def footSplit (d : Nat) (ty h : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
  if d > 0 && ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!; let b := ty.appArg!
    let acc := footSplit (d - 1) a (mkApp3 (mkConst ``And.left) a b h) acc
    footSplit (d - 1) b (mkApp3 (mkConst ``And.right) a b h) acc
  else acc.push (ty, h)

/-- A comparison fact as a difference record. -/
def footRel (nc : NC) (ty h : Expr) : MetaM (Option DRec) := do
  let some (r, lt) ← relNF nc ty | return none
  return some { r with h := if lt then mkApp3 (mkConst ``lt_le1) (ty.getArg! 2) (ty.getArg! 3) h else h }

def hasMod (e : Expr) : Bool := (e.find? fun t => t.isAppOfArity ``HMod.hMod 6).isSome

structure FootCtx where
  nc : NC
  facts : Array DRec
  /-- other hypothesis types, for leaves closed by assumption -/
  hyps : Array (Expr × Expr) := #[]

/-- Facts: the comparisons of the context (conjunctions split) and `extra`; wrap-around
removed by ceilings (direct or through one atom). No `BitVec` register equations: a route
stronger than the `omega` it precedes would change which goals a run leaves to the proof. -/
def footFacts (extra : Array (Expr × Expr)) : MetaM FootCtx := do
  let mut kf ← keyFacts
  let mut raw : Array (Expr × Expr) := #[]
  let mut hyps : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``And 2 then
      for (t, h) in footSplit 3 ty d.toExpr #[] do
        let t ← footClean t
        -- floors and alignments of conjuncts and of bounds written with literal constants
        if t.isAppOfArity ``LE.le 4 && (t.getArg! 0).isConstOf ``Nat then
          let lhs := t.getArg! 2; let rhs := t.getArg! 3
          if let some n := lhs.nat? then kf := { kf with floors := kf.floors.push (rhs, n, h) }
          else if let some (c, pc) := litNF lhs then
            kf := { kf with floors := kf.floors.push (rhs, c,
              mkAppN (mkConst ``floor_nf) #[lhs, rhs, mkNatLit c, h, pc]) }
          raw := raw.push (t, h)
        else if t.isAppOfArity ``LT.lt 4 && (t.getArg! 0).isConstOf ``Nat then
          if let some n := (t.getArg! 2).nat? then
            kf := { kf with floors := kf.floors.push (t.getArg! 3, n + 1,
              mkAppN (mkConst ``floor_lt) #[mkNatLit n, mkNatLit (n + 1), t.getArg! 3, h,
                natRefl (n + 1)]) }
          raw := raw.push (t, h)
        else if t.isAppOfArity ``Eq 3 && isZeroLit (t.getArg! 2) &&
            (t.getArg! 1).isAppOfArity ``HMod.hMod 6 then
          if let some m := (t.getArg! 1).appArg!.nat? then
            kf := { kf with aligns := kf.aligns.push ((t.getArg! 1).appFn!.appArg!, m, h) }
        else hyps := hyps.push (h, t)
    else hyps := hyps.push (d.toExpr, ty)
  raw := raw ++ extra
  let nc0 : NC := { kf, rb := true }
  let mut s1 : Array DRec := #[]
  let mut redo : Array (Expr × Expr) := #[]
  for (ty, h) in raw do
    if let some r ← footRel nc0 ty h then
      if hasMod r.t1 || hasMod r.t2 then redo := redo.push (ty, h) else s1 := s1.push r
  let mut ceils := s1
  for f in s1 do
    if isZeroLit f.t2 || f.t1 == f.t2 then continue
    if let some g := s1.find? fun g => g.t1 == f.t2 && isZeroLit g.t2 && g.a ≤ f.b + g.b then
      let V := f.b + g.b - g.a
      let rhs := mkNatAdd (mkNatLit 0) (mkNatLit V)
      let h := mkAppN (mkConst ``dif_trans) #[f.lhs, f.rhs, g.lhs, g.rhs, f.t1, f.t2, mkNatLit f.a,
          mkNatLit f.b, mkNatLit g.a, mkNatLit g.b, mkNatLit V, f.h, f.px, f.py, g.h, g.px, g.py,
          natRefl (f.b + g.b)]
      ceils := ceils.push (DRec.mk f.lhs rhs f.t1 f.a f.px (mkNatLit 0) V (nrefl rhs) h)
  let nc : NC := { nc0 with mods := true, ceil := true, ceils }
  let mut facts : Array DRec := ceils
  for (ty, h) in redo do
    if let some r ← footRel nc ty h then
      unless hasMod r.t1 || hasMod r.t2 do facts := facts.push r
  return { nc, facts, hyps }

/-- `big = small ⊕ r` as sums of atoms: `(r, small + r = big)`. -/
def splitSum (big small : Expr) : Option (Expr × Expr) :=
  if isZeroLit big then none
  else if isZeroLit small then some (big, mkApp (mkConst ``Nat.zero_add) big)
  else match subAtoms big small with
    | some r => let (sm, h) := addAtoms small r; if sm == big then some (r, h) else none
    | none => none

/-- `lhs ≤ rhs` (keys `g`) from the facts: same atom, literal below atom, one fact, two facts. -/
def footLe (fc : FootCtx) (g : DRec) : Option Expr := Id.run do
  if g.t1 == g.t2 then
    if g.a ≤ g.b then
      return some (mkAppN (mkConst ``key_le) #[g.lhs, g.rhs, g.t1, mkNatLit g.a, mkNatLit g.b,
        g.px, g.py, trueRefl])
    return none
  if isZeroLit g.t1 && g.a ≤ g.b then
    return some (mkAppN (mkConst ``le_lit_atom) #[g.lhs, g.rhs, g.t2, mkNatLit g.a, mkNatLit g.b,
      g.px, g.py, trueRefl])
  for f in fc.facts do
    if let some p := difImp f f.h g then return some p
  -- one fact with an extra atom on the larger side (atoms are nonnegative)
  for f in fc.facts do
    unless g.a + f.b ≤ f.a + g.b do continue
    if f.t2 == g.t2 && f.t1 != g.t1 then
      if let some (r, hs) := splitSum f.t1 g.t1 then
        return some (mkAppN (mkConst ``dif_dropL) #[f.lhs, f.rhs, g.lhs, g.rhs, f.t1, g.t1, r, f.t2,
          mkNatLit f.a, mkNatLit f.b, mkNatLit g.a, mkNatLit g.b, f.h, f.px, f.py, hs, g.px, g.py,
          trueRefl])
    if f.t1 == g.t1 && f.t2 != g.t2 then
      if let some (r, hs) := splitSum g.t2 f.t2 then
        return some (mkAppN (mkConst ``dif_dropR) #[f.lhs, f.rhs, g.lhs, g.rhs, f.t1, f.t2, r, g.t2,
          mkNatLit f.a, mkNatLit f.b, mkNatLit g.a, mkNatLit g.b, f.h, f.px, f.py, hs, g.px, g.py,
          trueRefl])
  for f1 in fc.facts do
    unless f1.t1 == g.t1 do continue
    for f2 in fc.facts do
      unless f2.t1 == f1.t2 && f2.t2 == g.t2 do continue
      let A := f1.a + f2.a; let B := f1.b + f2.b
      let lhs := mkNatAdd g.t1 (mkNatLit A); let rhs := mkNatAdd g.t2 (mkNatLit B)
      let h := mkAppN (mkConst ``dif_chain) #[f1.lhs, f1.rhs, f2.lhs, f2.rhs, f1.t1, f1.t2, f2.t2,
        mkNatLit f1.a, mkNatLit f1.b, mkNatLit f2.a, mkNatLit f2.b, mkNatLit A, mkNatLit B,
        f1.h, f1.px, f1.py, f2.h, f2.px, f2.py, natRefl A, natRefl B]
      let c : DRec := DRec.mk lhs rhs g.t1 A (nrefl lhs) g.t2 B (nrefl rhs) h
      if let some p := difImp c h g then return some p
  return none

/-- A leaf that is literally a hypothesis. -/
def footHyp (fc : FootCtx) (e : Expr) : Option Expr := Id.run do
  for d in fc.hyps do
    if d.2 == e then return some d.1
  return none

/-- Decide a prepared goal tree. -/
partial def footDec (fc : FootCtx) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!; let b := e.appArg!
    if let some p ← footDec fc a then return some (mkApp3 (mkConst ``Or.inl) a b p)
    if let some q ← footDec fc b then return some (mkApp3 (mkConst ``Or.inr) a b q)
    return none
  if e.isAppOfArity ``And 2 then
    let a := e.appFn!.appArg!; let b := e.appArg!
    let some p ← footDec fc a | return none
    let some q ← footDec fc b | return none
    return some (mkApp4 (mkConst ``And.intro) a b p q)
  let nc := fc.nc
  if e.isAppOfArity ``Eq 3 then
    let x := e.getArg! 1; let y := e.getArg! 2
    if x.isAppOfArity ``HMod.hMod 6 && isZeroLit y then
      let some w := x.appArg!.nat? | return none
      if w == 0 then return none
      let z := x.appFn!.appArg!
      let some (t, c, pz) ← linNF nc 3 none z | return none
      unless c % w == 0 do return none
      let some ht ← alignOf nc.kf t w | return none
      return some (mkAppN (mkConst ``al_key) #[z, t, mkNatLit c, mkNatLit w, pz, ht, trueRefl])
    let some (tx, cx, px) ← linNF nc 3 none x | return none
    let some (ty, cy, py) ← linNF nc 3 none y | return none
    if tx == ty && cx == cy then return some (mkAppN (mkConst ``key_eq) #[x, y, tx, mkNatLit cx, px, py])
    return none
  if e.isAppOfArity ``Ne 3 then
    let x := e.getArg! 1; let y := e.getArg! 2
    let some (tx, cx, px) ← linNF nc 3 none x | return none
    let some (ty, cy, py) ← linNF nc 3 none y | return none
    if tx == ty && cx != cy then
      return some (mkAppN (mkConst ``key_ne) #[x, y, tx, mkNatLit cx, mkNatLit cy, px, py, boolRefl false])
    return footHyp fc e
  let some (g, lt) ← relNF nc e | return footHyp fc e
  let some p := footLe fc g | return footHyp fc e
  return some (if lt then mkApp3 (mkConst ``lt_of_le1) (e.getArg! 2) (e.getArg! 3) p else p)

/-- The access form `∀ b, b ∈ accAddrs a w → P b`: `(a, w, P)`. -/
def footAcc? (tgt : Expr) : Option (Expr × Expr × Expr) := do
  let .forallE n nat (.forallE _ mem body _) bi := tgt | none
  unless nat.isConstOf ``Nat do none
  if body.hasLooseBVar 0 then none
  let mem := mem.consumeMData
  unless mem.isAppOfArity ``Membership.mem 5 do none
  let coll := mem.getArg! 3
  unless coll.isAppOfArity ``accAddrs 2 do none
  if coll.hasLooseBVars then none
  some (coll.getArg! 0, coll.getArg! 1, .lam n nat (body.lowerLooseBVars 1 1) bi)

def footKey (g : MVarId) : MetaM Bool := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.consumeMData
  if let some (a, w, P) := footAcc? tgt then
    let nat := mkConst ``Nat
    let pf? ← withLocalDeclD `b nat fun b => do
      let lo := mkApp4 (mkConst ``LE.le [Level.zero]) nat (mkConst ``instLENat) a b
      let hi := mkApp4 (mkConst ``LT.lt [Level.zero]) nat (mkConst ``instLTNat) b (mkNatAdd a w)
      withLocalDeclD `h1 lo fun h1 => withLocalDeclD `h2 hi fun h2 => do
        let some e ← footPrep 6 (P.beta #[b]) | return none
        let fc ← footFacts #[(lo, h1), (hi, h2)]
        let some p ← footDec fc e | return none
        unless ← isDefEq e (P.beta #[b]) do return none
        return some (← mkLambdaFVars #[b, h1, h2] p)
    let some pf := pf? | return false
    let pf := mkApp4 (mkConst ``foot_intro) a w P pf
    unless ← isDefEq (← inferType pf) tgt do return false
    g.assign pf
    return true
  let some e ← footPrep 6 tgt | return false
  let fc ← footFacts #[]
  let some p ← footDec fc e | return false
  unless ← isDefEq e tgt do return false
  g.assign p
  return true

/-- `foot_key`: decide a footprint / address side goal by atom + literal keys; fails when
undecided. -/
elab "foot_key" : tactic => do
  let g ← getMainGoal
  if ← footKey g then replaceMainGoal [] else throwError "foot_key: undecided"

end VsaIris.VsaHeap

namespace VsaIris.Sym

macro_rules | `(tactic| sx_addr) => `(tactic| foot_key)

end VsaIris.Sym
