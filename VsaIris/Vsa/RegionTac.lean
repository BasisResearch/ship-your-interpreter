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

theorem key_eq {x y t c : Nat} (px : x = t + c) (py : y = t + c) : x = y := px.trans py.symm
theorem key_le {x y t a b : Nat} (px : x = t + a) (py : y = t + b) (h : Nat.ble a b = true) :
    x ≤ y := by rw [Nat.ble_eq] at h; subst px py; omega
theorem lin_sub {x u a k c : Nat} (px : x = u + a) (hc : k + c = a) : x - k = u + c := by
  subst px hc; omega
theorem lin_rebase {t F : Nat} (h : F ≤ t) : t = (t - F) + F := by omega
theorem lin_modneg {y u c' c d M : Nat} (py : y = u + c') (hlt : u + c < M) (hd : M + d = c')
    (h : Nat.ble d c = true) : y % M = u + d := by
  rw [Nat.ble_eq] at h; subst py hd
  rw [show u + (M + d) = (u + d) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
def sxv (k : Nat) : Nat := if k % 4096 < 2048 then k % 4096 else k % 4096 + 18446744073709547520
theorem toNat_sext12 (k n : Nat) (h : sxv k = n) :
    (LeanRV64DExecutable.Functions.sign_extend (BitVec.ofNat 12 k) : BitVec 64).toNat = n := by
  subst h
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.msb_eq_decide, sxv]
  have : k % 4096 < 4096 := Nat.mod_lt _ (by decide)
  rw [Nat.mod_eq_of_lt (by omega : k % 4096 < 18446744073709551616)]
  by_cases h : k % 4096 < 2048
  · simp only [h, ↓reduceIte]; simp [show ¬ (2048 ≤ k % 4096) by omega]
  · simp only [h, ↓reduceIte]; simp [show 2048 ≤ k % 4096 by omega]
theorem toNat_upd_eq (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) (r : Nat)
    (h : Nat.beq r k = true) : (upd R k v r).toNat = v.toNat := by
  rw [Nat.beq_eq] at h; subst h; simp [upd]
theorem toNat_upd_ne (R : Nat → BitVec 64) (k : Nat) (v : BitVec 64) (r : Nat)
    (h : Nat.beq r k = false) : (upd R k v r).toNat = (R r).toNat := by
  have : r ≠ k := fun e => by subst e; simp at h
  simp [upd, this]
theorem floor_nf {x s c : Nat} (h : x ≤ s) (px : x = 0 + c) : c ≤ s := by omega
theorem floor_sub {F s k G : Nat} (h : F ≤ s - k) (hF : Nat.blt 0 F = true) (hc : F + k = G) :
    G ≤ s := by rw [Nat.blt_eq] at hF; omega
theorem lt_of_dif {x y t a b c M : Nat} (h : x ≤ y) (px : x = t + a) (py : y = 0 + b)
    (hc : Nat.blt (c + b) (a + M) = true) : t + c < M := by rw [Nat.blt_eq] at hc; omega
theorem dif_le {x y X Y t1 t2 a b c d : Nat} (h : x ≤ y) (px : x = t1 + a) (py : y = t2 + b)
    (pX : X = t1 + c) (pY : Y = t2 + d) (hc : Nat.ble (c + b) (a + d) = true) : X ≤ Y := by
  rw [Nat.ble_eq] at hc; omega
theorem lt_le1 {x y : Nat} (h : x < y) : x + 1 ≤ y := h
theorem lt_of_le1 {x y : Nat} (h : x + 1 ≤ y) : x < y := h
theorem dif_trans {x y y' z t s a b b' U V : Nat} (h1 : x ≤ y) (px : x = t + a) (py : y = s + b)
    (h2 : y' ≤ z) (py' : y' = s + b') (pz : z = 0 + U) (hc : b' + V = b + U) : x ≤ 0 + V := by
  omega
theorem al_of {t m w : Nat} (h : t % m = 0) (hc : (m % w == 0) = true) : t % w = 0 := by
  simp only [beq_iff_eq] at hc
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hc) (Nat.dvd_of_mod_eq_zero h))
theorem al_add {x y w : Nat} (h1 : x % w = 0) (h2 : y % w = 0) : (x + y) % w = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2))
theorem al_sub {s F w : Nat} (h : s % w = 0) (hc : (F % w == 0) = true) : (s - F) % w = 0 := by
  simp only [beq_iff_eq] at hc
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub (Nat.dvd_of_mod_eq_zero h) (Nat.dvd_of_mod_eq_zero hc))
theorem lin_add2 {x y tx ty sm a b c : Nat} (px : x = tx + a) (py : y = ty + b)
    (hs : tx + ty = sm) (hc : a + b = c) : x + y = sm + c := by subst px py hs hc; omega
theorem add_ins {s r q u : Nat} (h : s + q = u) : s + r + q = u + r := by subst h; omega
theorem add_assoc_ins {t p q s1 s2 : Nat} (h1 : t + p = s1) (h2 : s1 + q = s2) :
    t + (p + q) = s2 := by subst h1 h2; omega
theorem floor_add {x y f1 f2 : Nat} (h1 : f1 ≤ x) (h2 : f2 ≤ y) : f1 + f2 ≤ x + y := by omega
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
theorem lin_mul {x t a k c : Nat} (px : x = t + a) (hc : k * a = c) : k * x = k * t + c := by
  subst px hc; rw [Nat.mul_add]
theorem lin_mul0 {x a k c : Nat} (px : x = 0 + a) (hc : k * a = c) : k * x = 0 + c := by
  subst px hc; rw [Nat.zero_add, Nat.zero_add]
theorem al_mul (k t w : Nat) (hc : (k % w == 0) = true) : (k * t) % w = 0 := by
  simp only [beq_iff_eq] at hc
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hc) (Nat.dvd_mul_right k t))
theorem al_nf {x t m c w : Nat} (h : x % m = 0) (px : x = t + c)
    (hc : (m % w == 0 && c % w == 0) = true) : t % w = 0 := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have h1 : w ∣ t + c := px ▸ Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hc.1) (Nat.dvd_of_mod_eq_zero h)
  exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_left (Nat.dvd_of_mod_eq_zero hc.2)).mp h1)
theorem floor_eq {x a : Nat} (h : x = a) : a ≤ x := h ▸ Nat.le_refl a
theorem floor_or_eq {x a m m' : Nat} {R : Prop} (h : x = a ∨ R) (hr : R → m' ≤ x)
    (hm : (Nat.ble m a && Nat.ble m m') = true) : m ≤ x := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at hm
  rcases h with h | h
  · omega
  · have := hr h; omega
theorem ceil_rgn {H : List (Nat × Nat)} {b e t c0 L : Nat} (r : Rgn (vsaFoot H) b e)
    (hb : b = t + c0) (he : L ≤ e) (hL : Nat.blt 0 L = true) : t + (c0 + 1) ≤ 0 + 0x87800000 := by
  rw [Nat.blt_eq] at hL
  have := vsaFoot_range (r.mem (a := b) (Nat.le_refl _) (by omega)); omega
theorem ceil_argn {S : Nat → Prop} {b e t c0 L : Nat} (r : ARgn S b e) (hb : b = t + c0)
    (he : L ≤ e) : t + (c0 + L) ≤ 0 + 4294967296 := by
  have := r.hi; omega
theorem floor_lt {F G s : Nat} (h : F < s) (hc : F + 1 = G) : G ≤ s := hc ▸ h


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

def natRefl (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit n)
def trueRefl : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
def isZeroLit (e : Expr) : Bool := e.nat? == some 0

/-- The context facts the key route reads syntactically: atom rewrites `x.toNat = r`,
literal floors `L ≤ s` and alignments `t % m = 0`; `eqs` also holds atom definitions
`x = r` (either orientation). -/
structure KeyFacts where
  eqs : Array (Expr × Expr × Expr) := #[]
  floors : Array (Expr × Nat × Expr) := #[]
  aligns : Array (Expr × Nat × Expr) := #[]

inductive KeyKind | ld | st | acc (oks : Array Syntax.Term) | win (s : Expr)

def isArith (l : Expr) : Bool := l.isAppOfArity ``HAdd.hAdd 6 || l.isAppOfArity ``HSub.hSub 6 ||
  l.isAppOfArity ``HMod.hMod 6 || l.isAppOfArity ``HMul.hMul 6 || l.isAppOfArity ``HDiv.hDiv 6
def M64 : Nat := 18446744073709551616
def boolRefl (b : Bool) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (toExpr b)

/-- A closed sum of literals `e = 0 + c`. -/
partial def litNF (e : Expr) : Option (Nat × Expr) :=
  if let some n := e.nat? then some (n, mkApp (mkConst ``lin_lit) e)
  else if e.isAppOfArity ``HAdd.hAdd 6 && (e.getArg! 0).isConstOf ``Nat then
    match litNF (e.getArg! 4), litNF (e.getArg! 5) with
    | some (a, pa), some (b, pb) => some (a + b, mkAppN (mkConst ``lin_addL)
        #[e.getArg! 4, e.getArg! 5, mkNatLit 0, mkNatLit a, mkNatLit b, mkNatLit (a + b), pa, pb,
          natRefl (a + b)])
    | _, _ => none
  else none

/-- A floor from a disjunction of literal equations `x = a₁ ∨ x = a₂ ∨ …`. -/
partial def eqDisjFloor (e h : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Nat then
    let some a := (e.getArg! 2).nat? | return none
    return some (e.getArg! 1, a, mkAppN (mkConst ``floor_eq) #[e.getArg! 1, e.getArg! 2, h])
  if e.isAppOfArity ``Or 2 then
    let l := e.appFn!.appArg!; let R := e.appArg!
    unless l.isAppOfArity ``Eq 3 && (l.getArg! 0).isConstOf ``Nat do return none
    let some a := (l.getArg! 2).nat? | return none
    let x := l.getArg! 1
    let r? ← withLocalDeclD `hr R fun hr => do
      let some (x', m', p') ← eqDisjFloor R hr | return none
      unless x' == x do return none
      return some (m', ← mkLambdaFVars #[hr] p')
    let some (m', lam) := r? | return none
    let m := min a m'
    return some (x, m, mkAppN (mkConst ``floor_or_eq) #[x, l.getArg! 2, mkNatLit m, mkNatLit m', R, h,
      lam, trueRefl])
  return none

/-- Context facts read syntactically. Floors: `F ≤ s` and `F < s` with literal `F` (max per atom). -/
def keyFacts : MetaM KeyFacts := do
  let mut kf : KeyFacts := {}
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (α, l, r) := ty.eq? then
      if l.isAppOfArity ``BitVec.toNat 2 ||
          (α.isConstOf ``Nat && (l.isApp || l.isFVar) && l.nat?.isNone &&
            !(l.isAppOfArity ``HAdd.hAdd 6 || l.isAppOfArity ``HSub.hSub 6 ||
              l.isAppOfArity ``HMod.hMod 6 || l.isAppOfArity ``HMul.hMul 6 ||
              l.isAppOfArity ``HDiv.hDiv 6) && (r.find? (· == l)).isNone) then
        kf := { kf with eqs := kf.eqs.push (l, r, d.toExpr) }
      else if α.isConstOf ``Nat && (r.isApp || r.isFVar) && r.nat?.isNone && !isArith r &&
          isArith l && (l.find? (· == r)).isNone then
        kf := { kf with eqs := kf.eqs.push (r, l, mkApp4 (mkConst ``Eq.symm [Level.one]) α l r d.toExpr) }
      else if l.isAppOfArity ``HMod.hMod 6 && isZeroLit r then
        if let some m := l.appArg!.nat? then
          kf := { kf with aligns := kf.aligns.push (l.appFn!.appArg!, m, d.toExpr) }
    else if ty.isAppOfArity ``LE.le 4 && (ty.getArg! 0).isConstOf ``Nat then
      let lhs := ty.appFn!.appArg!; let s := ty.appArg!
      let fl? : Option (Nat × Expr) ← (do
        if let some n := lhs.nat? then return some (n, d.toExpr)
        if lhs.isAppOfArity ``HAdd.hAdd 6 then
          if let some (c, p) := litNF lhs then
            return some (c, mkAppN (mkConst ``floor_nf) #[lhs, s, mkNatLit c, d.toExpr, p])
        return none)
      if let some (n, h) := fl? then
        kf := { kf with floors := kf.floors.push (s, n, h) }
        if s.isAppOfArity ``HSub.hSub 6 && 0 < n then
          if let some k := s.appArg!.nat? then
            let s' := s.appFn!.appArg!
            kf := { kf with floors := kf.floors.push (s', n + k, mkAppN (mkConst ``floor_sub)
              #[mkNatLit n, s', mkNatLit k, mkNatLit (n + k), h, trueRefl, natRefl (n + k)]) }
    else if ty.isAppOfArity ``Or 2 then
      if let some (x, m, h) ← eqDisjFloor ty d.toExpr then
        if 0 < m then kf := { kf with floors := kf.floors.push (x, m, h) }
    else if ty.isAppOfArity ``LT.lt 4 then
      if let some n := ty.appFn!.appArg!.nat? then
        kf := { kf with floors := kf.floors.push (ty.appArg!,  n + 1,
          mkAppN (mkConst ``floor_lt) #[mkNatLit n, mkNatLit (n + 1), ty.appArg!, d.toExpr,
            natRefl (n + 1)]) }
  return kf

/-- The largest literal floor of `s` in the context. -/
def maxFloor (kf : KeyFacts) (s : Expr) : Option (Nat × Expr) :=
  kf.floors.foldl (init := none) fun acc (x, n, h) =>
    if x == s && 0 < n then match acc with
      | some (m, _) => if n > m then some (n, h) else acc
      | none => some (n, h)
    else acc

/-- A difference fact `lhs ≤ rhs` with `lhs = t1 + a`, `rhs = t2 + b`; `h` proves it. -/
structure DRec where
  lhs : Expr
  rhs : Expr
  t1 : Expr
  a : Nat
  px : Expr
  t2 : Expr
  b : Nat
  py : Expr
  h : Expr := mkConst ``True
deriving Inhabited

structure NC where
  kf : KeyFacts
  rb : Bool := false
  mods : Bool := false
  ceil : Bool := false
  ceils : Array DRec := #[]

def isNatAdd (e : Expr) : Bool := e.isAppOfArity ``HAdd.hAdd 6 && (e.getArg! 0).isConstOf ``Nat
def nrefl (e : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) e

/-- Insert atom `q` into the sorted sum `s`: `(u, s + q = u)`. -/
partial def insAtom (s q : Expr) : Expr × Expr :=
  if isNatAdd s then
    let s' := s.getArg! 4; let r := s.getArg! 5
    if q.lt r then
      let (u, h) := insAtom s' q
      (mkNatAdd u r, mkAppN (mkConst ``add_ins) #[s', r, q, u, h])
    else (mkNatAdd s q, nrefl (mkNatAdd s q))
  else if q.lt s then (mkNatAdd q s, mkApp2 (mkConst ``Nat.add_comm) s q)
  else (mkNatAdd s q, nrefl (mkNatAdd s q))

/-- `tx + ty` (both sorted sums of atoms) as a sorted sum, with its proof `tx + ty = sm`. -/
partial def addAtoms (tx ty : Expr) : Expr × Expr :=
  if isNatAdd ty then
    let p := ty.getArg! 4; let q := ty.getArg! 5
    let (s1, h1) := addAtoms tx p
    let (s2, h2) := insAtom s1 q
    (s2, mkAppN (mkConst ``add_assoc_ins) #[tx, p, q, s1, s2, h1, h2])
  else insAtom tx ty

/-- A literal floor of an atom or a sum of atoms. -/
partial def floorOf (kf : KeyFacts) (t : Expr) : Option (Nat × Expr) :=
  match maxFloor kf t with
  | some r => some r
  | none =>
    if isNatAdd t then
      match floorOf kf (t.getArg! 4), floorOf kf (t.getArg! 5) with
      | some (f1, h1), some (f2, h2) => some (f1 + f2, mkAppN (mkConst ``floor_add)
          #[t.getArg! 4, t.getArg! 5, mkNatLit f1, mkNatLit f2, h1, h2])
      | _, _ => some (0, mkApp (mkConst ``Nat.zero_le) t)
    else some (0, mkApp (mkConst ``Nat.zero_le) t)

/-- The atoms of a left-nested sum. -/
partial def sumAtoms (t : Expr) : List Expr :=
  if isNatAdd t then sumAtoms (t.getArg! 4) ++ [t.getArg! 5] else [t]

/-- `t` minus the atoms of `tb` (as multisets), as a sum; `none` unless `tb ⊆ t`. -/
def subAtoms (t tb : Expr) : Option Expr := do
  let mut rest := sumAtoms t
  for a in sumAtoms tb do
    let some i := rest.idxOf? a | none
    rest := rest.eraseIdx i
  match rest with
  | [] => none
  | x :: xs => some (xs.foldl mkNatAdd x)

/-- `e = t + c` with `t` an atom (or `0`) and `c` a literal. As `linNF`, and also through
`BitVec.toNat` of additions, literals and register updates, literal subtractions, and (with
`rb`) atoms rebased below their context floor so negative offsets become literals. -/
partial def linNF (nc : NC) (fuel : Nat) (bnd : Option (Expr × Nat × Expr))
    (e : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  let kf := nc.kf; let rb := nc.rb; let mods := nc.mods
  let atom (e : Expr) : Option (Expr × Nat × Expr) :=
    if rb then match maxFloor kf e with
      | some (F, h) => some (mkNatSub e (mkNatLit F), F,
          mkAppN (mkConst ``lin_rebase) #[e, mkNatLit F, h])
      | none => some (e, 0, mkApp (mkConst ``lin_atom) e)
    else some (e, 0, mkApp (mkConst ``lin_atom) e)
  if let some n := e.nat? then return some (mkNatLit 0, n, mkApp (mkConst ``lin_lit) e)
  let trans (r h : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
    let some (t, c, p) ← linNF nc fuel bnd r | return none
    return some (t, c, mkAppN (mkConst ``lin_trans) #[e, r, t, mkNatLit c, h, p])
  if e.isAppOfArity ``HAdd.hAdd 6 && (e.getArg! 0).isConstOf ``Nat then
    let x := e.getArg! 4; let y := e.getArg! 5
    let some (tx, cx, px) ← linNF nc fuel bnd x | return none
    let some (ty, cy, py) ← linNF nc fuel bnd y | return none
    let args (t : Expr) (p q : Expr) :=
      #[x, y, t, mkNatLit cx, mkNatLit cy, mkNatLit (cx + cy), p, q, natRefl (cx + cy)]
    if isZeroLit ty then return some (tx, cx + cy, mkAppN (mkConst ``lin_addL) (args tx px py))
    if isZeroLit tx then return some (ty, cx + cy, mkAppN (mkConst ``lin_addR) (args ty px py))
    let (sm, hs) := addAtoms tx ty
    return some (sm, cx + cy, mkAppN (mkConst ``lin_add2)
      #[x, y, tx, ty, sm, mkNatLit cx, mkNatLit cy, mkNatLit (cx + cy), px, py, hs, natRefl (cx + cy)])
  if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf ``Nat then
    if let some k := (e.getArg! 4).nat? then
      let x := e.getArg! 5
      let some (tx, cx, px) ← linNF nc fuel bnd x | return none
      if isZeroLit tx then
        return some (tx, k * cx, mkAppN (mkConst ``lin_mul0)
          #[x, mkNatLit cx, mkNatLit k, mkNatLit (k * cx), px, natRefl (k * cx)])
      return some (mkApp2 (mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat)
          (mkConst ``Nat) (mkApp2 (mkConst ``instHMul [0]) (mkConst ``Nat) (mkConst ``instMulNat)))
          (e.getArg! 4) tx, k * cx, mkAppN (mkConst ``lin_mul)
        #[x, tx, mkNatLit cx, e.getArg! 4, mkNatLit (k * cx), px, natRefl (k * cx)])
    return atom e
  if e.isAppOfArity ``HSub.hSub 6 && (e.getArg! 0).isConstOf ``Nat then
    if let some k := e.appArg!.nat? then
      let x := e.appFn!.appArg!
      let some (tx, cx, px) ← linNF nc fuel bnd x | return none
      if k ≤ cx then
        return some (tx, cx - k, mkAppN (mkConst ``lin_sub)
          #[x, tx, mkNatLit cx, mkNatLit k, mkNatLit (cx - k), px, natRefl cx])
    return atom e
  if e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat &&
      e.appArg!.nat? == some M64 then
    let y := e.appFn!.appArg!
    let some (ty, cy, py) ← linNF nc fuel bnd y | return none
    if isZeroLit ty then
      unless cy < M64 do return none
      return some (ty, cy, mkAppN (mkConst ``lin_mod0) #[y, mkNatLit cy, e.appArg!, py, trueRefl])
    unless mods do return atom e
    match bnd with
    | none =>
      if !nc.ceil then return some (ty, if cy ≥ M64 then cy - M64 else cy, mkConst ``True)
      -- the wrap-around is removed by a ceiling fact on the atom
      let d := if cy ≥ M64 then cy - M64 else cy
      let some f := nc.ceils.find? fun f => f.t1 == ty && isZeroLit f.t2 && d + f.b < f.a + M64
        | return atom e
      let hlt := mkAppN (mkConst ``lt_of_dif) #[f.lhs, f.rhs, ty, mkNatLit f.a, mkNatLit f.b,
        mkNatLit d, mkNatLit M64, f.h, f.px, f.py, trueRefl]
      if cy ≥ M64 then
        return some (ty, d, mkAppN (mkConst ``lin_modneg)
          #[y, ty, mkNatLit cy, mkNatLit d, mkNatLit d, e.appArg!, py, hlt, natRefl cy, trueRefl])
      return some (ty, cy,
        mkAppN (mkConst ``lin_mod) #[y, ty, mkNatLit cy, mkNatLit cy, e.appArg!, py, hlt, trueRefl])
    | some (t, c, hlt) =>
      unless ty == t do return none
      if cy ≥ M64 then
        let d := cy - M64
        unless d ≤ c do return none
        return some (ty, d, mkAppN (mkConst ``lin_modneg)
          #[y, t, mkNatLit cy, mkNatLit c, mkNatLit d, e.appArg!, py, hlt, natRefl cy, trueRefl])
      unless cy ≤ c do return none
      return some (ty, cy,
        mkAppN (mkConst ``lin_mod) #[y, t, mkNatLit cy, mkNatLit c, e.appArg!, py, hlt, trueRefl])
  if fuel > 0 then
    if let some (_, r, h) := kf.eqs.find? (·.1 == e) then
      let some (t, c, p) ← linNF nc (fuel - 1) bnd r | return none
      return some (t, c, mkAppN (mkConst ``lin_trans) #[e, r, t, mkNatLit c, h, p])
  if e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 0).nat? == some 64 then
    let x := e.appArg!
    if x.isAppOfArity ``HAdd.hAdd 6 then
      let h := mkApp2 (mkConst ``key_toNat_add) (x.getArg! 4) (x.getArg! 5)
      let some (_, _, r) := (← inferType h).eq? | return atom e
      return ← trans r h
    if x.isAppOfArity ``BitVec.ofNat 2 then
      let h := mkApp (mkConst ``key_toNat_ofNat) x.appArg!
      let some (_, _, r) := (← inferType h).eq? | return atom e
      return ← trans r h
    if x.isAppOfArity ``LeanRV64DExecutable.Functions.sign_extend 3 &&
        (x.getArg! 0).nat? == some 12 && (x.getArg! 1).nat? == some 64 then
      let v := x.appArg!
      if v.isAppOfArity ``BitVec.ofNat 2 then
        if let some k := v.appArg!.nat? then
          let n := sxv k
          return some (mkNatLit 0, n, mkAppN (mkConst ``lin_trans) #[e, mkNatLit n, mkNatLit 0,
            mkNatLit n, mkAppN (mkConst ``toNat_sext12) #[v.appArg!, mkNatLit n, natRefl n],
            mkApp (mkConst ``lin_lit) (mkNatLit n)])
    if x.isAppOfArity ``upd 4 then
      if let (some k, some r) := ((x.getArg! 1).nat?, (x.getArg! 3).nat?) then
        let R := x.getArg! 0; let v := x.getArg! 2
        if r == k then
          let h := mkAppN (mkConst ``toNat_upd_eq) #[R, x.getArg! 1, v, x.getArg! 3, trueRefl]
          return ← trans (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 64) v) h
        else
          let h := mkAppN (mkConst ``toNat_upd_ne) #[R, x.getArg! 1, v, x.getArg! 3, boolRefl false]
          return ← trans (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 64) (mkApp R (x.getArg! 3))) h
  return atom e

/-! ## Literal decision of an arithmetic side goal -/

inductive KeyDec | pf (e : Expr) | no | unk

/-- A comparison `x ≤ y` / `x < y` (as `x + 1 ≤ y`) in normal form; `conv` turns a proof of
the raw proposition into one of `lhs ≤ rhs` (facts) or back (goals). -/
def relNF (nc : NC) (e : Expr) : MetaM (Option (DRec × Bool)) := do
  if e.isAppOfArity ``LE.le 4 && (e.getArg! 0).isConstOf ``Nat then
    let x := e.getArg! 2; let y := e.getArg! 3
    let some (t1, a, px) ← linNF nc 3 none x | return none
    let some (t2, b, py) ← linNF nc 3 none y | return none
    return some ({ lhs := x, rhs := y, t1, a, px, t2, b, py }, false)
  if e.isAppOfArity ``LT.lt 4 && (e.getArg! 0).isConstOf ``Nat then
    let x := e.getArg! 2; let y := e.getArg! 3
    let some (t1, a, px) ← linNF nc 3 none x | return none
    let some (t2, b, py) ← linNF nc 3 none y | return none
    let x1 := mkNatAdd x (mkNatLit 1)
    let px1 := mkAppN (mkConst ``lin_addL) #[x, mkNatLit 1, t1, mkNatLit a, mkNatLit 1,
      mkNatLit (a + 1), px, mkApp (mkConst ``lin_lit) (mkNatLit 1), natRefl (a + 1)]
    return some ({ lhs := x1, rhs := y, t1, a := a + 1, px := px1, t2, b, py }, true)
  return none

/-- A literal floor `L ≤ e` of a region extent. -/
def extFloor (kf : KeyFacts) (e : Expr) : MetaM (Option (Nat × Expr)) := do
  if let some L := e.nat? then return some (L, mkApp (mkConst ``ext_lit) e)
  let some (s, k, pe) ← linNF { kf } 3 none e | return none
  let some (L0, hs) := floorOf kf s | return none
  return some (L0 + k, mkAppN (mkConst ``ext_le)
    #[e, s, mkNatLit k, mkNatLit L0, mkNatLit (L0 + k), pe, hs, natRefl (L0 + k)])

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

/-- The difference facts of the context: comparisons and disjunctions of comparisons. -/
def difFacts (nc : NC) : MetaM (Array DRec × Array (Expr × Expr × Expr × Array (DRec × Bool))) := do
  let mut singles : Array DRec := #[]
  let mut ors := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Or 2 then
      let p := ty.appFn!.appArg!; let q := ty.appArg!
      let some r1 ← relNF nc p | continue
      let some r2 ← relNF nc q | continue
      ors := ors.push (d.toExpr, p, q, #[r1, r2])
    else if let some (r, lt) ← relNF nc ty then
      singles := singles.push { r with h := if lt then mkApp3 (mkConst ``lt_le1) (ty.getArg! 2) (ty.getArg! 3) d.toExpr else d.toExpr }
  return (singles, ors)

/-- Same-atom decision (complete when both sides share their atom). -/
partial def keyDec (nc : NC) (e : Expr) : MetaM KeyDec := do
  if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!; let b := e.appArg!
    match ← keyDec nc a with
    | .pf p => return .pf (mkApp3 (mkConst ``Or.inl) a b p)
    | d1 =>
      match ← keyDec nc b with
      | .pf q => return .pf (mkApp3 (mkConst ``Or.inr) a b q)
      | .no => return if d1 matches .no then .no else .unk
      | .unk => return .unk
  if e.isAppOfArity ``And 2 then
    let a := e.appFn!.appArg!; let b := e.appArg!
    match ← keyDec nc a with
    | .no => return .no
    | .unk => return (if (← keyDec nc b) matches .no then .no else .unk)
    | .pf p =>
      match ← keyDec nc b with
      | .pf q => return .pf (mkApp4 (mkConst ``And.intro) a b p q)
      | d => return d
  if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Nat then
    let x := e.getArg! 1; let y := e.getArg! 2
    let some (tx, cx, px) ← linNF nc 3 none x | return .unk
    let some (ty, cy, py) ← linNF nc 3 none y | return .unk
    unless tx == ty do return .unk
    if cx == cy then return .pf (mkAppN (mkConst ``key_eq) #[x, y, tx, mkNatLit cx, px, py])
    return .no
  let some (r, lt) ← relNF nc e | return .unk
  unless r.t1 == r.t2 do return .unk
  unless r.a ≤ r.b do return .no
  let p := mkAppN (mkConst ``key_le) #[r.lhs, r.rhs, r.t1, mkNatLit r.a, mkNatLit r.b, r.px, r.py,
    trueRefl]
  return .pf (if lt then mkApp3 (mkConst ``lt_of_le1) (e.getArg! 2) (e.getArg! 3) p else p)

/-- Goal disjuncts (right-nested `∨`) of comparisons, with injections into the goal. -/
partial def goalDisj (nc : NC) (e : Expr) : MetaM (Array (DRec × (Expr → Expr))) := do
  if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!; let b := e.appArg!
    let l ← goalDisj nc a; let r ← goalDisj nc b
    return l.map (fun (d, f) => (d, fun p => mkApp3 (mkConst ``Or.inl) a b (f p))) ++
      r.map (fun (d, f) => (d, fun p => mkApp3 (mkConst ``Or.inr) a b (f p)))
  let some (r, lt) ← relNF nc e | return #[]
  return #[(r, fun p => if lt then mkApp3 (mkConst ``lt_of_le1) (e.getArg! 2) (e.getArg! 3) p else p)]

/-- `f` (a fact disjunct, proof `hf`) implies goal disjunct `g`. -/
def difImp (f : DRec) (hf : Expr) (g : DRec) : Option Expr :=
  if f.t1 == g.t1 && f.t2 == g.t2 && g.a + f.b ≤ f.a + g.b then
    some (mkAppN (mkConst ``dif_le) #[f.lhs, f.rhs, g.lhs, g.rhs, f.t1, f.t2, mkNatLit f.a,
      mkNatLit f.b, mkNatLit g.a, mkNatLit g.b, hf, f.px, f.py, g.px, g.py, trueRefl])
  else none

/-- A goal (a disjunction of comparisons) implied by one fact, or by both cases of one
disjunctive fact, through literal difference checks. -/
def difSearch (nc : NC) (singles : Array DRec)
    (ors : Array (Expr × Expr × Expr × Array (DRec × Bool))) (e : Expr) : MetaM (Option Expr) := do
  let gs ← goalDisj nc e
  if gs.isEmpty then return none
  let imp1 (f : DRec) (hf : Expr) : Option Expr :=
    gs.findSome? fun (g, inj) => (difImp f hf g).map inj
  for f in singles do
    if let some p := imp1 f f.h then return some p
  for (h, p, q, rs) in ors do
    let (r1, lt1) := rs[0]!; let (r2, lt2) := rs[1]!
    let ok ← withLocalDeclD `h1 p fun h1 => withLocalDeclD `h2 q fun h2 => do
      let c1 := if lt1 then mkApp3 (mkConst ``lt_le1) (p.getArg! 2) (p.getArg! 3) h1 else h1
      let c2 := if lt2 then mkApp3 (mkConst ``lt_le1) (q.getArg! 2) (q.getArg! 3) h2 else h2
      let some p1 := imp1 r1 c1 | return none
      let some p2 := imp1 r2 c2 | return none
      return some (mkApp6 (mkConst ``Or.elim) p q e h (← mkLambdaFVars #[h1] p1)
        (← mkLambdaFVars #[h2] p2))
    if let some pf := ok then return some pf
  return none

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

/-- `t % w = 0` from alignment facts, through sums, multiples and rebased atoms. -/
partial def alignOf (kf : KeyFacts) (t : Expr) (w : Nat) : MetaM (Option Expr) := do
  if w == 1 then return some (mkApp (mkConst ``Nat.mod_one) t)
  if isZeroLit t then return some (mkApp (mkConst ``Nat.zero_mod) (mkNatLit w))
  if let some (_, m, h) := kf.aligns.find? fun (x, m, _) => x == t && m % w == 0 then
    return some (mkAppN (mkConst ``al_of) #[t, mkNatLit m, mkNatLit w, h, trueRefl])
  if isNatAdd t then
    let some h1 ← alignOf kf (t.getArg! 4) w | return none
    let some h2 ← alignOf kf (t.getArg! 5) w | return none
    return some (mkAppN (mkConst ``al_add) #[t.getArg! 4, t.getArg! 5, mkNatLit w, h1, h2])
  if t.isAppOfArity ``HMul.hMul 6 && (t.getArg! 0).isConstOf ``Nat then
    let some k := (t.getArg! 4).nat? | return none
    if k % w == 0 then
      return some (mkAppN (mkConst ``al_mul) #[t.getArg! 4, t.getArg! 5, mkNatLit w, trueRefl])
    return none
  if t.isAppOfArity ``HSub.hSub 6 && (t.getArg! 0).isConstOf ``Nat then
    let some F := t.appArg!.nat? | return none
    let some h ← alignOf kf t.appFn!.appArg! w | return none
    if F % w == 0 then
      return some (mkAppN (mkConst ``al_sub) #[t.appFn!.appArg!, mkNatLit F, mkNatLit w, h, trueRefl])
    return none
  -- an alignment fact about a term that normalises to `t + c`
  for (x, m, h) in kf.aligns do
    unless m % w == 0 do continue
    let some (tx, cx, px) ← linNF { kf } 3 none x | continue
    if tx == t && cx % w == 0 then
      return some (mkAppN (mkConst ``al_nf) #[x, t, mkNatLit m, mkNatLit cx, mkNatLit w, h, px,
        trueRefl])
  return none

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
