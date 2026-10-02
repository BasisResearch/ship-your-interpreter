import VsaIris.Vsa.RegionCore

/-!
# Atom + literal keys (moved from `RegionTac`)

The region-free part of the key layer: the key lemmas, the context facts read syntactically,
the normaliser `linNF` (an address or bound as atom + literal, with its proof term), the
same-atom decision `keyDec`, difference facts and alignment. `RegionTac` adds regions on top;
`FootKey` decides footprint membership with it.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim VsaIris.Sym

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
theorem floor_lt {F G s : Nat} (h : F < s) (hc : F + 1 = G) : G ≤ s := hc ▸ h

/-- `BitVec.toNat_add` as a propositional rewrite. The core lemma is an `rfl` lemma,
so `simp` would leave the kernel a definitional check that unfolds `Nat.mod` on
the offset literal (2^64 steps for a negative offset); through this lemma the
kernel only infers a type. -/
theorem key_toNat_add (x y : BitVec 64) :
    (x + y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := (BitVec.toNat_add x y).trans rfl

theorem key_toNat_ofNat (x : Nat) : (BitVec.ofNat 64 x).toNat = x % 18446744073709551616 :=
  (BitVec.toNat_ofNat x 64).trans rfl

end KeyLemmas

open Lean Elab Tactic Meta

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

end VsaIris.VsaHeap
