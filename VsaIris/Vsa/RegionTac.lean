import VsaIris.Vsa.Region

/-!
# Region tactics: atom + literal keys

The tactics over the laws of `Region.lean`. Every address and every region base is brought to
a key `t + c`: `t` an atom (a sorted sum of atoms, a literal multiple of an atom, or an atom
rebased below its context floor so that negative offsets become literals) and `c` a literal.
The normaliser reads through `BitVec.toNat` of additions, immediates and register updates and
removes each wrap-around from a bound (the chosen region, or a ceiling of the atom); it builds
its proof term directly, so no `simp` runs on the key.

* `rgnKeyed`: region membership by key: same atom, or the key in the middle or at the end of
  a symbolic extent (one difference fact); the check is a closed boolean on literals. Undecided
  obligations fall back to the candidate tries of `rgnTry`.
* `key_or tac`: an arithmetic side goal (`=`, `≤`, `<`, `∧`, `∨`) whose sides share an atom is
  decided by its literals (a refuted goal fails at once); across atoms, one difference fact or
  one case split of a disjunctive fact decides it. Otherwise `tac` runs. `rgn_arith`, and through
  it `rgn_norm`, `rgn_ld` and `rd_log`, discharge through `key_or` before `omega_dc`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-! ## Key lemmas -/

section KeyLemmas
theorem Rgn.sub_end {P : Nat → Prop} {b e B E T c0 k F : Nat} (r : Rgn P b e) (hb : b = B + c0)
    (he : e = E + k) (hF : F ≤ E) (hs : B + E = T) (c w : Nat)
    (h : (Nat.ble c0 (F + c) && Nat.ble (c + w) (c0 + k)) = true) : Rgn P (T + c) w := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact r.sub (by omega) (by omega)
theorem ARgn.sub_end {S : Nat → Prop} {b e B E T c0 k F : Nat} (r : ARgn S b e) (hb : b = B + c0)
    (he : e = E + k) (hF : F ≤ E) (hs : B + E = T) (c w : Nat)
    (h : (Nat.ble c0 (F + c) && Nat.ble (c + w) (c0 + k)) = true) : ARgn S (T + c) w := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  have := r.lo; have := r.hi
  exact ⟨r.own.sub (by omega) (by omega), by omega, by omega⟩
theorem Rgn.sub_mid {P : Nat → Prop} {b e B E X T c0 k F x y a bb : Nat} (r : Rgn P b e)
    (hb : b = B + c0) (he : e = E + k) (hF : F ≤ X) (hs : B + X = T) (hd : x ≤ y)
    (px : x = X + a) (py : y = E + bb) (c w : Nat)
    (h : (Nat.ble c0 (F + c) && Nat.ble (c + w + bb) (a + c0 + k)) = true) : Rgn P (T + c) w := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact r.sub (by omega) (by omega)
theorem ARgn.sub_mid {S : Nat → Prop} {b e B E X T c0 k F x y a bb : Nat} (r : ARgn S b e)
    (hb : b = B + c0) (he : e = E + k) (hF : F ≤ X) (hs : B + X = T) (hd : x ≤ y)
    (px : x = X + a) (py : y = E + bb) (c w : Nat)
    (h : (Nat.ble c0 (F + c) && Nat.ble (c + w + bb) (a + c0 + k)) = true) : ARgn S (T + c) w := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  have := r.lo; have := r.hi
  exact ⟨r.own.sub (by omega) (by omega), by omega, by omega⟩
theorem ceil_rgn {H : List (Nat × Nat)} {b e t c0 L : Nat} (r : Rgn (vsaFoot H) b e)
    (hb : b = t + c0) (he : L ≤ e) (hL : Nat.blt 0 L = true) : t + (c0 + 1) ≤ 0 + 0x87800000 := by
  rw [Nat.blt_eq] at hL
  have := vsaFoot_range (r.mem (a := b) (Nat.le_refl _) (by omega)); omega
theorem ceil_argn {S : Nat → Prop} {b e t c0 L : Nat} (r : ARgn S b e) (hb : b = t + c0)
    (he : L ≤ e) : t + (c0 + L) ≤ 0 + 4294967296 := by
  have := r.hi; omega
end KeyLemmas

/-! ## Meta -/

/-- Normalise a freshly introduced key equation `hA : a = A` to Nat arithmetic
(register updates, register additions, literal offsets of either sign,
wrap-around removed when the bound is in context). -/
macro "rgn_key_norm" : tactic =>
  `(tactic| (intro A hA
             (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
               LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
               BitVec.reduceAppend, BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
        VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat,
               Nat.reducePow, Nat.reduceMod] at hA)
             (repeat (first
               | (rw [Nat.mod_eq_of_lt] at hA; rotate_left; omega_dc)
               | (rw [VsaIris.VsaHeap.key_sub] at hA; rotate_left; omega_dc)
               | fail "no wrap-around to remove"))))

open Lean Elab Tactic Meta

/-- A region hypothesis: its name, base and extent. -/
structure RgnHyp where
  name : Name
  base : Expr
  ext : Expr
  acc : Bool := false

/-- The regions and ownership contexts in the local context. -/
def rgnScan (g : MVarId) : TacticM (Array Syntax.Term × Array RgnHyp) :=
  g.withContext do
    let mut oks : Array Syntax.Term := #[]
    let mut rgns : Array RgnHyp := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      let fn := ty.getAppFn
      if fn.isConstOf ``Rgn then rgns := rgns.push ⟨d.userName, ty.appFn!.appArg!, ty.appArg!, false⟩
      else if fn.isConstOf ``ARgn then
        rgns := rgns.push ⟨d.userName, ty.appFn!.appArg!, ty.appArg!, true⟩
      else if let .const n _ := fn then
        if n == ``WOK then oks := oks.push (mkIdent d.userName)
        else if (← getEnv).contains (n ++ `toWOK) then
          oks := oks.push (← `(($(mkIdent d.userName)).toWOK))
    return (oks, rgns)

/-- The first-order atoms (local constants other than register files) of `e`,
after replacing each `x.toNat` by the right side of a context equation
`x.toNat = rhs`. -/
def rgnAtoms (g : MVarId) (e : Expr) : MetaM (Array FVarId) := g.withContext do
  let mut eqs : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      if l.isAppOfArity ``BitVec.toNat 2 then eqs := eqs.push (l, r)
  let e' := e.replace fun t => eqs.findSome? fun (l, r) => if l == t then some r else none
  let mut out : Array FVarId := #[]
  for f in (collectFVars {} e').fvarIds do
    let fty ← whnfR (← f.getType)
    unless fty.isForall do out := out.push f
  return out

/-- Key an access (V5): replace the address term `a` in the goal of `g` by a bound
key `A` with `a = A`, through `key_gen`. -/
def rgnKey (g : MVarId) (a : Expr) : MetaM MVarId := g.withContext do
  let nat := mkConst ``Nat
  let abst ← kabstract (← instantiateMVars (← g.getType)) a
  let ty := mkForall `A .default nat
    (mkForall `hA .default (mkApp3 (mkConst ``Eq [levelOne]) nat a (mkBVar 0))
      (abst.liftLooseBVars 0 1))
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  g.assign (mkApp3 (mkConst ``key_gen) a (mkLambda `A .default nat abst) m)
  return m.mvarId!

inductive KeyKind | ld | st | acc (oks : Array Syntax.Term) | win (s : Expr)

/-- Ceilings from the regions of the context: a heap region lies below the arena end, an
access region inside RAM. -/
def rgnCeils (nc : NC) : MetaM (Array DRec) := do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let isR := ty.isAppOfArity ``Rgn 3; let isA := ty.isAppOfArity ``ARgn 3
    unless isR || isA do continue
    let b := ty.appFn!.appArg!; let e := ty.appArg!
    let some (t, c0, hb) ← linNF nc 3 none b | continue
    if isZeroLit t then continue
    let some (L, he) ← extFloor nc.kf e | continue
    let r? ← try
        if isR then
          if L == 0 then pure none else
          pure (some (c0 + 1, 0x87800000,
            ← mkAppM ``ceil_rgn #[d.toExpr, hb, he, trueRefl]))
        else pure (some (c0 + L, 4294967296, ← mkAppM ``ceil_argn #[d.toExpr, hb, he]))
      catch _ => pure none
    let some (a, U, h) := r? | continue
    let lhs := mkNatAdd t (mkNatLit a); let rhs := mkNatAdd (mkNatLit 0) (mkNatLit U)
    out := out.push (DRec.mk lhs rhs t a (nrefl lhs) (mkNatLit 0) U (nrefl rhs) h)
  return out

/-- The full decision: facts read once; same-atom literal checks, then difference facts. -/
def keyDecide (e : Expr) : MetaM KeyDec := do
  let kf ← keyFacts
  let nc0 : NC := { kf, rb := true }
  let (singles1, ors) ← difFacts nc0
  let singles0 := singles1 ++ (← rgnCeils nc0)
  -- ceilings through one intermediate atom
  let mut singles := singles0
  for f in singles0 do
    if isZeroLit f.t2 || f.t1 == f.t2 then continue
    if let some g := singles0.find? fun g => g.t1 == f.t2 && isZeroLit g.t2 && g.a ≤ f.b + g.b then
      let V := f.b + g.b - g.a
      let rhs := mkNatAdd (mkNatLit 0) (mkNatLit V)
      let py := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) rhs
      let h := mkAppN (mkConst ``dif_trans) #[f.lhs, f.rhs, g.lhs, g.rhs, f.t1, f.t2, mkNatLit f.a,
          mkNatLit f.b, mkNatLit g.a, mkNatLit g.b, mkNatLit V, f.h, f.px, f.py, g.h, g.px, g.py,
          natRefl (f.b + g.b)]
      singles := singles.push (DRec.mk f.lhs rhs f.t1 f.a f.px (mkNatLit 0) V py h)
  let nc : NC := { nc0 with mods := true, ceil := true, ceils := singles }
  match ← keyDec nc e with
  | .unk =>
    match ← difSearch nc singles ors e with
    | some p => return .pf p
    | none => return .unk
  | d => return d

/-- `key_or tac`: decide the goal by atom+literal keys; a refuted goal fails at once; an
undecided one runs `tac`. -/
elab "key_or " t:tactic : tactic => do
  let g ← getMainGoal
  let d ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    match ← keyDecide tgt with
    | .pf p => if ← isDefEq (← inferType p) tgt then pure (.pf p) else pure .unk
    | d => pure d
  match d with
  | .pf p => g.assign p; replaceMainGoal []
  | .no => throwError "key: refuted by literal offsets"
  | .unk => evalTactic t

/-! ## Region membership by key -/


structure Cand where
  rv : Expr
  acc : Bool
  tb : Expr
  c0 : Nat
  hb : Expr
  L : Nat
  he : Expr
  name : Name

def rgnKeyed (g : MVarId) (a : Expr) (rgns : Array RgnHyp) (kind : KeyKind) :
    TacticM (Option Name) := g.withContext do
  let s0 ← saveState
  let r? ← tryCatchRuntimeEx (do
    let kf ← keyFacts
    let tgt ← instantiateMVars (← g.getType)
    let wE? : Option Expr := match kind with
      | .win _ => match tgt with
        | .forallE _ _ (.forallE _ _ (.forallE _ lt _ _) _) _ => some lt.appArg!.appArg!
        | _ => none
      | _ => (tgt.find? fun e => e.isAppOfArity ``accAddrs 2 || e.isAppOfArity ``LdOK 2 ||
          e.isAppOfArity ``StOK 2).map (·.appArg!)
    let some w := wE?.bind (·.nat?) | return none
    for rb in [false, true] do
      let some (t, c, _) ← linNF { kf, rb, mods := true } 3 none a | continue
      let mut cands : Array Cand := #[]
      let mut difs : Option (Array DRec) := none
      for r in rgns do
        if (kind matches .win _) && r.acc then continue
        let some (tb, c0, hb) ← linNF { kf, rb } 3 none r.base | continue
        let rv := mkFVar (← getLocalDeclFromUserName r.name).fvarId
        if tb == t then
          let some (L, he) ← (do
              if let some L := r.ext.nat? then return some (L, mkApp (mkConst ``ext_lit) r.ext)
              let some (s, k, pe) ← linNF { kf } 3 none r.ext | return none
              let some (L0, hs) := floorOf kf s | return none
              return some (L0 + k, mkAppN (mkConst ``ext_le)
                #[r.ext, s, mkNatLit k, mkNatLit L0, mkNatLit (L0 + k), pe, hs, natRefl (L0 + k)]) :
              MetaM (Option (Nat × Expr)))
            | continue
          cands := cands.push ⟨rv, r.acc, tb, c0, hb, L, he, r.name⟩
        else if isNatAdd t && r.ext.nat?.isNone then
          -- the key is `tb + X + c` with `X` bounded by the extent `E + k`
          let some (E, k, pe) ← linNF { kf } 3 none r.ext | continue
          if isZeroLit E then continue
          let some X := subAtoms t tb | continue
          let (T, hs) := addAtoms tb X
          unless T == t do continue
          let some (F, hF) := floorOf kf X | continue
          unless c0 ≤ F + c do continue
          let mut rv'? : Option Expr := none
          if X == E then
            if c + w ≤ c0 + k then
              let sub := if r.acc then ``ARgn.sub_end else ``Rgn.sub_end
              rv'? := some (← mkAppM sub #[rv, hb, pe, hF, hs, mkNatLit c, mkNatLit w, trueRefl])
          else
            if difs.isNone then difs := some (← difFacts { kf }).1
            if let some f := difs.get!.find? fun f =>
                f.t1 == X && f.t2 == E && c + w + f.b ≤ f.a + c0 + k then
              let sub := if r.acc then ``ARgn.sub_mid else ``Rgn.sub_mid
              rv'? := some (← mkAppM sub #[rv, hb, pe, hF, hs, f.h, f.px, f.py, mkNatLit c,
                mkNatLit w, trueRefl])
          let some rv' := rv'? | continue
          let tc := mkNatAdd t (mkNatLit c)
          cands := cands.push ⟨rv', r.acc, t, c, nrefl tc, w, mkApp (mkConst ``ext_lit) (mkNatLit w),
            r.name⟩
      for cd in cands do
        let c0 := cd.c0; let L := cd.L; let hb := cd.hb; let he := cd.he; let rv := cd.rv
        unless c0 ≤ c && c + w ≤ c0 + L && 0 < w do continue
        let pre := if cd.acc then ``ARgn else ``Rgn
        -- the region's last byte bounds every partial sum of the key
        let cm := c0 + L - 1
        let hlt ← mkAppM (pre ++ `lt_k) #[rv, hb, he, mkNatLit cm, mkNatLit 1, trueRefl]
        let some (_, _, px) ← linNF { kf, rb, mods := true } 3 (some (t, cm, hlt)) a
          | continue
        let tc := mkNatAdd t (mkNatLit c)
        let hA := mkApp4 (mkConst ``Eq.symm [Level.one]) (mkConst ``Nat) a tc px
        let pf? : Option Expr ← match kind with
          | .ld => some <$> mkAppM (pre ++ `ldOK_k) #[rv, hb, he, hA, mkNatLit w, trueRefl]
          | .st => do
            let some hal ← alignOf kf t w | pure none
            if c % w != 0 then pure none else
            some <$> mkAppM (pre ++ `stOK_k) #[rv, hb, he, hA, mkNatLit w, trueRefl, hal, trueRefl]
          | .acc oks =>
            if cd.acc then some <$> mkAppM ``ARgn.acc_k #[rv, hb, he, hA, mkNatLit w, trueRefl] else do
              let mut res := none
              for o in oks do
                let some oe ← (try some <$> Term.withoutErrToSorry (Tactic.elabTerm o none)
                  catch _ => pure none) | continue
                if let some p ← (try some <$> mkAppM ``WOK.rgn_k #[oe, rv, hb, he, hA, mkNatLit w,
                    trueRefl] catch _ => pure none) then
                  res := some p; break
              pure res
          | .win s => some <$> mkAppOptM ``Rgn.win_k #[none, none, none, none, none, none, none,
              none, s, rv, hb, he, hA, mkNatLit w, trueRefl]
        let some pf := pf? | continue
        if ← isDefEq (← inferType pf) tgt then
          g.assign pf
          return some cd.name
    return none) (fun _ => pure none)
  if r?.isNone then s0.restore
  return r?

/-- Key the access `a` of goal `g`, rank the regions (the hinted one first, then
by atoms shared with the key, symbolic extents before literal ones), and try each
region's candidate tactics. Returns the region that closed the goal. -/
def rgnTry (g : MVarId) (a : Expr) (rgns : Array RgnHyp) (hint : Option Name)
    (mk : RgnHyp → TacticM (Array (TSyntax `tactic))) (extra : Array (TSyntax `tactic)) :
    TacticM (Option Name) := do
  let ka ← rgnAtoms g a
  let mut scored : Array (Int × RgnHyp) := #[]
  for r in rgns do
    let kb ← rgnAtoms g r.base
    let shared := (kb.filter ka.contains).size
    let sc : Int := (4 * shared : Int) - (2 * (kb.size - shared) : Nat) +
      (if r.ext.nat?.isNone then 1 else 0) + (if hint == some r.name then 1000 else 0)
    scored := scored.push (sc, r)
  let ranked := scored.qsort (fun x y => x.1 > y.1)
  let mut cands : Array (Name × TSyntax `tactic) := extra.map (Name.anonymous, ·)
  for (_, r) in ranked do
    for t in ← mk r do cands := cands.push (r.name, t)
  let s0 ← saveState
  let [g'] ← evalTacticAt (← `(tactic| rgn_key_norm)) (← rgnKey g a) | s0.restore; return none
  for (r, t) in cands do
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do pure (← evalTacticAt t g').isEmpty) (fun _ => pure false)
    if ok then return some r
    s.restore
  s0.restore
  return none

/-- Close an access goal of `g` (`∀ x ∈ accAddrs a w, C.S x`, `LdOK` or `StOK`) from
a region in context: by key, else by the candidate tries. -/
def rgnSide (g : MVarId) (hint : Option Name) : TacticM (Option Name) := do
  let (oks, rgns) ← rgnScan g
  if rgns.isEmpty then return none
  let tgt ← instantiateMVars (← g.getType)
  let some app := tgt.find? fun e =>
      e.isAppOfArity ``accAddrs 2 || e.isAppOfArity ``LdOK 2 || e.isAppOfArity ``StOK 2
    | return none
  let mk : RgnHyp → TacticM (Array (TSyntax `tactic)) := fun h => do
    let r := mkIdent h.name
    if app.isAppOf ``LdOK then
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.ldOK $r ?_; omega_dc))]
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.ldOK $r ?_; omega_dc))]
    else if app.isAppOf ``StOK then
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.stOK $r ?_; omega_dc))]
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.stOK $r ?_; omega_dc))]
    else
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.acc $r ?_; omega_dc))]
      oks.mapM fun o => `(tactic| (refine VsaIris.VsaHeap.WOK.rgn $o $r ?_; omega_dc))
  let kind : KeyKind :=
    if app.isAppOf ``LdOK then .ld else if app.isAppOf ``StOK then .st else .acc oks
  let a := app.appFn!.appArg!
  if let some r ← rgnKeyed g a rgns kind then return some r
  rgnTry g a rgns hint mk #[]

/-- Close an ownership (`∀ x ∈ accAddrs a w, C.S x`), `LdOK` or `StOK` goal
from any region in context. -/
elab "rgn_side" : tactic => do
  let g ← getMainGoal
  match ← rgnSide g none with
  | some _ => setGoals []
  | none => throwError "rgn_side: no region closes the goal"

macro_rules | `(tactic| sx_side) => `(tactic| rgn_side)

/-- Address arithmetic on the goal only: decide by keys, else normalise register updates and
`BitVec` additions, then `omega` over the facts in context (no hypothesis rewriting). -/
macro "rgn_arith" : tactic =>
  `(tactic| key_or (first
    | omega_dc
    | (simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceAppend,
        BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
        VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod]
       repeat (first
         | (rw [Nat.mod_eq_of_lt]; rotate_left; omega_dc)
         | (rw [VsaIris.VsaHeap.key_sub]; rotate_left; omega_dc)
         | fail "no wrap-around to remove")
       first | done | omega_dc)
    | fail "rgn_arith: address arithmetic failed"))
/-- Normalise the goal only (register updates, immediates, loads through stores). -/
macro "rgn_norm" : tactic =>
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, reduceIte, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat,
      VsaIris.Sym.ldv_store_hit, VsaIris.Sym.ldv_ld_hit_eq, VsaIris.Sym.ldv_ld_miss])

/-- Replace loads whose value the context knows (`read64 M a' = some x`) in the goal. -/
macro "rgn_ld " "[" hs:term,* "]" : tactic => do
  let ls ← hs.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| VsaIris.Sym.ldv_at $h)
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, VsaIris.Sym.ldv_ld_miss, $ls,*])


/-- Step the `st` family from `cur`, closing each access obligation with
`rgnSide` and leaving the context untouched; after each step the register reads in
the goal are resolved, so values stay terms over the entry registers. Stops at a listed pc, at a branch,
or when no step lemma applies; obligations no region closes are returned as
pending goals. -/
def rgnStep (h : Syntax) (stopPCs : List Nat) : TacticM (List MVarId × List MVarId) := do
  let mut cur ← getMainGoal
  let mut pending : List MVarId := []
  repeat
    let some pc ← cur.withContext (do VsaIris.Sym.swpPC? (← cur.getType)) | break
    if stopPCs.contains pc then break
    let some gs ← VsaIris.Sym.sxStep h cur | break
    let mut conts : List MVarId := []
    let mut hint : Option Name := none
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => VsaIris.Sym.isSWP b) then
        conts := conts ++ [g]
      else
        match ← rgnSide g hint with
        | some r => hint := some r
        | none =>
          let s ← saveState
          try
            let gs' ← evalTacticAt (← `(tactic| (simp only [VsaIris.Sym.upd_apply, VsaIris.ra,
              Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd, BitVec.reduceOfNat,
              BitVec.reduceToNat, Nat.reduceMod])) ) g
            unless gs'.isEmpty do s.restore; pending := pending ++ [g]
          catch _ => s.restore; pending := pending ++ [g]
    match conts with
    | [c] =>
      match ← evalTacticAt (← `(tactic| try simp only [VsaIris.Sym.upd_apply, VsaIris.ra,
          Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd, BitVec.reduceOfNat])) c with
      | [c'] => cur := c'
      | cs => return (pending, cs)
    | cs => return (pending, cs)
  return (pending, [cur])

/-- `rgn_run h at pc…`: step to a listed pc, then normalise the final goal with
`rgn_norm`. -/
elab "rgn_run " h:term " at " stops:num+ : tactic => do
  let rest := (← getGoals).tail
  let (pending, conts) ← rgnStep h (stops.toList.map (·.getNat))
  match conts with
  | [c] => setGoals (pending ++ (← evalTacticAt (← `(tactic| try rgn_norm)) c) ++ rest)
  | cs => setGoals (pending ++ cs ++ rest)

/-- `rgn_step h at pc…`: as `rgn_run`, leaving the final goal as the step lemmas
produce it (for paths with their own memory normal form). -/
elab "rgn_step " h:term " at " stops:num+ : tactic => do
  let rest := (← getGoals).tail
  let (pending, conts) ← rgnStep h (stops.toList.map (·.getNat))
  setGoals (pending ++ conts ++ rest)

/-- Close one `LogIn (MWin H s)` key `∀ b, a ≤ b → b < a + w → MWin H s b`: from a
region in context, or the stack window. -/
elab "rgn_win" : tactic => do
  let g ← getMainGoal
  let (_, rgns) ← rgnScan g
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ _ body _ := tgt | throwError "rgn_win: not a key goal"
  let .forallE _ le _ _ := body | throwError "rgn_win: not a key goal"
  let a := le.appFn!.appArg!
  if a.hasLooseBVars then throwError "rgn_win: not a key goal"
  let stack ← `(tactic| (refine VsaIris.VsaHeap.win_stack' ?_; omega_dc))
  let mk : RgnHyp → TacticM (Array (TSyntax `tactic)) := fun h => do
    if h.acc then return #[]
    return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.win $(mkIdent h.name) ?_; omega_dc))]
  -- a key over the context's stack pointer is tried against the stack window first; any
  -- other key against the regions first (a failing stack check is a wasted `omega`)
  let onStack := (a.find? (·.isConstOf ``MCtx.s)).isSome
  let rest := (← getGoals).tail
  let r ← if onStack then rgnTry g a rgns none mk #[stack] else do
    let k ← match (tgt.find? (·.isAppOfArity ``MWin 3)).map (·.getArg! 1) with
      | some s => rgnKeyed g a rgns (.win s)
      | none => pure none
    if k.isSome then pure k else
    match ← rgnTry g a rgns none mk #[] with
    | some r => pure (some r)
    | none => rgnTry g a #[] none mk #[stack]
  match r with
  | some _ => setGoals rest
  | none => throwError "rgn_win: no region contains the key"

syntax openFieldsSel := " [" ident,* "]"

/-- `open_fields h [f₁, …]` adds only the listed fields (a short proof should not pay for
unused geometry in every arithmetic query). `open_fields h` adds every field of the named-field structure `h` as a
hypothesis `h_<field>` (projections of constructor terms reduced), so the
arithmetic deciders see a minted region's geometry. -/
elab "open_fields " h:ident sel:(openFieldsSel)? : tactic => do
  let only : Option (Array Name) := sel.map fun s =>
    match s with
    | `(openFieldsSel| [$ids,*]) => ids.getElems.map (·.getId)
    | _ => #[]
  let g ← getMainGoal
  let n ← g.withContext do
    let d ← getLocalDeclFromUserName h.getId
    let ty ← whnfR (← instantiateMVars d.type)
    let .const n _ := ty.getAppFn | throwError "open_fields: not a structure"
    pure n
  let some info := getStructureInfo? (← getEnv) n | throwError "open_fields: not a structure"
  for f in info.fieldNames do
    if let some fs := only then unless fs.contains f do continue
    let nm := mkIdent (Name.mkSimple s!"{h.getId}_{f}")
    let pj := mkIdent (h.getId ++ f)
    evalTactic (← `(tactic| have $nm := $pj:ident))
    evalTactic (← `(tactic| try simp only at $nm:ident))

/-- Discharge `LogIn (MWin H s) L` for an explicit key list. -/
macro "log_in" : tactic =>
  `(tactic| (simp only [VsaIris.VsaHeap.LogIn, and_true]; repeat' apply And.intro) <;> rgn_win)

end VsaIris.VsaHeap
