import Lean

namespace VsaIris.Dbm

inductive Tm where
  | atom (i : Nat)
  | lit (n : Nat)
  | add (a : Tm) (n : Nat)
  | ladd (n : Nat) (a : Tm)
  | sub (a : Tm) (n : Nat)
  | wrap (a : Tm) (n : Nat)
  deriving Inhabited

def val (ρ : List Nat) (i : Nat) : Nat := (0 :: ρ).getD i 0

def Tm.den (ρ : List Nat) : Tm → Nat
  | .atom i => val ρ i
  | .lit n => n
  | .add a n => a.den ρ + n
  | .ladd n a => n + a.den ρ
  | .sub a n => a.den ρ - n
  | .wrap a n => (a.den ρ + n) % 18446744073709551616

inductive Fm where
  | le (a b : Tm)
  | lt (a b : Tm)
  | eq (a b : Tm)
  | ne (a b : Tm)
  | and (p q : Fm)
  | or (p q : Fm)
  | not (p : Fm)
  deriving Inhabited

def Fm.den (ρ : List Nat) : Fm → Prop
  | .le a b => a.den ρ ≤ b.den ρ
  | .lt a b => a.den ρ < b.den ρ
  | .eq a b => a.den ρ = b.den ρ
  | .ne a b => a.den ρ ≠ b.den ρ
  | .and p q => p.den ρ ∧ q.den ρ
  | .or p q => p.den ρ ∨ q.den ρ
  | .not p => ¬ p.den ρ

def Fm.all (ρ : List Nat) : List Fm → Prop
  | [] => True
  | f :: fs => f.den ρ ∧ Fm.all ρ fs

structure DC where
  a : Nat
  b : Nat
  c : Int
  deriving Inhabited

def DC.holds (ρ : List Nat) (d : DC) : Prop := (val ρ d.a : Int) - val ρ d.b ≤ d.c

def DC.neg (d : DC) : DC := ⟨d.b, d.a, -d.c - 1⟩

def norm : Tm → (Nat × Int) × List DC
  | .atom i => ((i, 0), [])
  | .lit n => ((0, n), [])
  | .add a n => let r := norm a; ((r.1.1, r.1.2 + n), r.2)
  | .ladd n a => let r := norm a; ((r.1.1, r.1.2 + n), r.2)
  | .sub a n => let r := norm a
      if (n : Int) ≤ r.1.2 then ((r.1.1, r.1.2 - n), r.2)
      else ((r.1.1, r.1.2 - n), ⟨0, r.1.1, r.1.2 - n⟩ :: r.2)
  | .wrap a n => let r := norm a
      if n ≤ 9223372036854775808 then
        ((r.1.1, r.1.2 + n), ⟨r.1.1, 0, 18446744073709551615 - r.1.2 - n⟩ :: r.2)
      else ((r.1.1, r.1.2 + n - 18446744073709551616),
        ⟨0, r.1.1, r.1.2 + n - 18446744073709551616⟩ ::
          ⟨r.1.1, 0, 36893488147419103231 - r.1.2 - n⟩ :: r.2)

def GOK (ρ : List Nat) (g : List DC) : Prop := ∀ d ∈ g, d.holds ρ

theorem val_zero (ρ : List Nat) : val ρ 0 = 0 := rfl

theorem norm_sound (ρ : List Nat) : ∀ t : Tm, GOK ρ (norm t).2 →
    (t.den ρ : Int) = val ρ (norm t).1.1 + (norm t).1.2
  | .atom i, _ => by simp [norm, Tm.den]
  | .lit n, _ => by simp [norm, Tm.den, val_zero]
  | .add a n, h => by
      have := norm_sound ρ a h
      simp only [norm, Tm.den] at *; omega
  | .ladd n a, h => by
      have := norm_sound ρ a h
      simp only [norm, Tm.den] at *; omega
  | .sub a n, h => by
      have ih := norm_sound ρ a
      by_cases hn : (n : Int) ≤ (norm a).1.2
      · simp only [norm, hn, ite_true] at h ⊢
        have := ih h; simp only [Tm.den]; omega
      · simp only [norm, hn, ite_false] at h ⊢
        have h0 := h _ List.mem_cons_self
        have := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
        simp only [DC.holds, val_zero] at h0
        simp only [Tm.den]; omega
  | .wrap a n, h => by
      have ih := norm_sound ρ a
      by_cases hn : n ≤ 9223372036854775808
      · simp only [norm, hn, ite_true] at h ⊢
        have h0 := h _ List.mem_cons_self
        have := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
        simp only [DC.holds, val_zero] at h0
        simp only [Tm.den]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · simp only [norm, hn, ite_false] at h ⊢
        have h0 := h _ List.mem_cons_self
        have h1 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have := ih fun d hd => h d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
        simp only [DC.holds, val_zero] at h0 h1
        simp only [Tm.den]
        have e : (a.den ρ + n) % 18446744073709551616 = a.den ρ + n - 18446744073709551616 := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [e]; omega

structure Lit where
  a : Tm
  b : Tm
  c : Int

def Lit.holds (ρ : List Nat) (l : Lit) : Prop := (l.a.den ρ : Int) ≤ l.b.den ρ + l.c

def Lit.guards (l : Lit) : List DC := (norm l.a).2 ++ (norm l.b).2

def Lit.dc (l : Lit) : DC :=
  ⟨(norm l.a).1.1, (norm l.b).1.1, (norm l.b).1.2 + l.c - (norm l.a).1.2⟩

theorem Lit.dc_sound {ρ : List Nat} {l : Lit} (hg : GOK ρ l.guards) (h : l.holds ρ) : l.dc.holds ρ := by
  have ha := norm_sound ρ l.a fun d hd => hg d (List.mem_append_left _ hd)
  have hb := norm_sound ρ l.b fun d hd => hg d (List.mem_append_right _ hd)
  simp only [Lit.holds] at h; simp only [Lit.dc, DC.holds]; omega

def prod (A B : List (List Lit)) : List (List Lit) := A.flatMap fun c => B.map fun d => c ++ d

def cnf : Bool → Fm → List (List Lit)
  | true, .le a b => [[⟨a, b, 0⟩]]
  | false, .le a b => [[⟨b, a, -1⟩]]
  | true, .lt a b => [[⟨a, b, -1⟩]]
  | false, .lt a b => [[⟨b, a, 0⟩]]
  | true, .eq a b => [[⟨a, b, 0⟩], [⟨b, a, 0⟩]]
  | false, .eq a b => [[⟨a, b, -1⟩, ⟨b, a, -1⟩]]
  | true, .ne a b => [[⟨a, b, -1⟩, ⟨b, a, -1⟩]]
  | false, .ne a b => [[⟨a, b, 0⟩], [⟨b, a, 0⟩]]
  | true, .and p q => cnf true p ++ cnf true q
  | false, .and p q => prod (cnf false p) (cnf false q)
  | true, .or p q => prod (cnf true p) (cnf true q)
  | false, .or p q => cnf false p ++ cnf false q
  | b, .not p => cnf (!b) p

def CHolds (ρ : List Nat) (cs : List (List Lit)) : Prop := ∀ c ∈ cs, ∃ l ∈ c, l.holds ρ

theorem prod_holds {ρ : List Nat} {A B : List (List Lit)} (hA : CHolds ρ A ∨ CHolds ρ B) :
    CHolds ρ (prod A B) := by
  intro c hc
  simp only [prod, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := hc
  rcases hA with h | h
  · obtain ⟨l, hl, hl'⟩ := h x hx; exact ⟨l, List.mem_append_left _ hl, hl'⟩
  · obtain ⟨l, hl, hl'⟩ := h y hy; exact ⟨l, List.mem_append_right _ hl, hl'⟩

theorem CHolds.append {ρ : List Nat} {A B : List (List Lit)} (hA : CHolds ρ A) (hB : CHolds ρ B) :
    CHolds ρ (A ++ B) := by
  intro c hc; rcases List.mem_append.1 hc with h | h
  · exact hA c h
  · exact hB c h

theorem one {ρ : List Nat} {l : Lit} (h : l.holds ρ) : CHolds ρ [[l]] := by
  intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact ⟨l, List.mem_singleton_self _, h⟩

theorem two {ρ : List Nat} {l m : Lit} (h : l.holds ρ ∨ m.holds ρ) : CHolds ρ [[l, m]] := by
  intro c hc; simp only [List.mem_singleton] at hc; subst hc
  rcases h with h | h
  · exact ⟨l, List.mem_cons_self, h⟩
  · exact ⟨m, List.mem_cons_of_mem _ List.mem_cons_self, h⟩

theorem cnf_sound (ρ : List Nat) : ∀ (f : Fm) (b : Bool), (if b then f.den ρ else ¬ f.den ρ) →
    CHolds ρ (cnf b f)
  | .le a b, true, h => one (by simp only [Lit.holds, Fm.den, reduceIte] at *; omega)
  | .le a b, false, h => one (by simp only [Lit.holds, Fm.den, Bool.false_eq_true, ite_false] at *; omega)
  | .lt a b, true, h => one (by simp only [Lit.holds, Fm.den, reduceIte] at *; omega)
  | .lt a b, false, h => one (by simp only [Lit.holds, Fm.den, Bool.false_eq_true, ite_false] at *; omega)
  | .eq a b, true, h => by
      simp only [Fm.den, cnf, ite_true] at *
      exact CHolds.append (one (by simp only [Lit.holds]; omega)) (one (by simp only [Lit.holds]; omega))
  | .eq a b, false, h => two (by simp only [Lit.holds, Fm.den, Bool.false_eq_true, ite_false] at *; omega)
  | .ne a b, true, h => two (by simp only [Lit.holds, Fm.den, reduceIte] at *; omega)
  | .ne a b, false, h => by
      simp only [Fm.den, cnf, Bool.false_eq_true, ite_false, Decidable.not_not] at *
      exact CHolds.append (one (by simp only [Lit.holds]; omega)) (one (by simp only [Lit.holds]; omega))
  | .and p q, true, h => by
      simp only [Fm.den, cnf, ite_true] at *
      exact CHolds.append (cnf_sound ρ p true (by simpa using h.1)) (cnf_sound ρ q true (by simpa using h.2))
  | .and p q, false, h => by
      simp only [Fm.den, cnf, Bool.false_eq_true, ite_false] at *
      refine prod_holds ?_
      by_cases hp : p.den ρ
      · exact .inr (cnf_sound ρ q false (by simp only [Bool.false_eq_true, ite_false]; exact fun hq => h ⟨hp, hq⟩))
      · exact .inl (cnf_sound ρ p false (by simpa using hp))
  | .or p q, true, h => by
      simp only [Fm.den, cnf, ite_true] at *
      refine prod_holds ?_
      rcases h with h | h
      · exact .inl (cnf_sound ρ p true (by simpa using h))
      · exact .inr (cnf_sound ρ q true (by simpa using h))
  | .or p q, false, h => by
      simp only [Fm.den, cnf, Bool.false_eq_true, ite_false, not_or] at *
      exact CHolds.append (cnf_sound ρ p false (by simpa using h.1)) (cnf_sound ρ q false (by simpa using h.2))
  | .not p, b, h => by
      cases b
      · exact cnf_sound ρ p true (by simpa [Fm.den] using h)
      · exact cnf_sound ρ p false (by simpa [Fm.den] using h)

def walk (ds : List DC) : Nat → List Nat → Option (Nat × Int)
  | x, [] => some (x, 0)
  | x, i :: is => match ds[i]? with
    | some d => if d.a = x then (match walk ds d.b is with
        | some r => some (r.1, d.c + r.2)
        | none => none) else none
    | none => none

theorem walk_sound {ρ : List Nat} {ds : List DC} (hds : ∀ d ∈ ds, d.holds ρ) :
    ∀ (x : Nat) (is : List Nat) (y : Nat) (w : Int), walk ds x is = some (y, w) →
      (val ρ x : Int) - val ρ y ≤ w
  | x, [], y, w, h => by
      simp only [walk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp
  | x, i :: is, y, w, h => by
      simp only [walk] at h
      split at h
      · rename_i d hd
        split at h
        · rename_i hx
          split at h
          · rename_i r hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have h1 := walk_sound hds _ _ _ _ hr
            have h2 := hds d (List.mem_of_getElem? hd)
            simp only [DC.holds] at h2; subst hx; omega
          · cases h
        · cases h
      · cases h

def cyc (ds : List DC) : List Nat → Bool
  | [] => false
  | i :: is => match ds[i]? with
    | some d => match walk ds d.a (i :: is) with
      | some r => decide (r.1 = d.a) && decide (r.2 < 0)
      | none => false
    | none => false

theorem cyc_sound {ρ : List Nat} {ds : List DC} {is : List Nat} (h : cyc ds is = true)
    (hds : ∀ d ∈ ds, d.holds ρ) : False := by
  cases is with
  | nil => cases h
  | cons i is =>
    simp only [cyc] at h
    split at h
    · split at h
      · rename_i r hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have := walk_sound hds _ _ _ _ hr
        rw [h.1] at this; omega
      · cases h
    · cases h

def ch : List (List DC) → List DC → List (List Nat) → Option (List (List Nat))
  | _, _, [] => none
  | [], acc, k :: ks => if cyc acc k then some ks else none
  | c :: cs, acc, k :: ks => if cyc acc k then some ks else c.foldl (fun o d => match o with
    | some ks => ch cs (d :: acc) ks
    | none => none) (some ks)

theorem ch_fold {cs : List (List DC)} {acc : List DC} :
    ∀ (l : List DC) (o : Option (List (List Nat))) (r : List (List Nat)),
      l.foldl (fun o d => match o with
        | some ks => ch cs (d :: acc) ks
        | none => none) o = some r →
      o ≠ none ∧ ∀ d ∈ l, ∃ k k', ch cs (d :: acc) k = some k'
  | [], o, r, h => by simp only [List.foldl_nil] at h; subst h; exact ⟨by simp, fun _ h => by cases h⟩
  | d :: l, o, r, h => by
      simp only [List.foldl_cons] at h
      obtain ⟨h1, h2⟩ := ch_fold l _ r h
      cases o with
      | none => exact absurd rfl h1
      | some k =>
        refine ⟨by simp, fun e he => ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨k, _, Option.ne_none_iff_exists'.1 h1 |>.choose_spec⟩
        · exact h2 e he

theorem ch_sound {ρ : List Nat} : ∀ (cs : List (List DC)) (acc : List DC) (ks r : List (List Nat)),
    ch cs acc ks = some r → (∀ d ∈ acc, d.holds ρ) → (∀ c ∈ cs, ∃ d ∈ c, d.holds ρ) → False
  | cs, _, [], r, h, _, _ => by cases cs <;> simp [ch] at h
  | [], acc, k :: ks, r, h, ha, _ => by
      simp only [ch] at h
      split at h
      · rename_i hc; exact cyc_sound hc ha
      · cases h
  | c :: cs, acc, k :: ks, r, h, ha, hc => by
      obtain ⟨d, hd, hd'⟩ := hc c List.mem_cons_self
      simp only [ch] at h
      split at h
      · rename_i hcy; exact cyc_sound hcy ha
      obtain ⟨k, k', hk⟩ := (ch_fold c _ r h).2 d hd
      exact ch_sound cs _ _ _ hk
        (fun e he => (List.mem_cons.1 he).elim (fun h => h ▸ hd') (ha e))
        (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

def all2 (p : DC → List Nat → Bool) : List DC → List (List Nat) → Bool
  | [], _ => true
  | d :: ds, k :: ks => p d k && all2 p ds ks
  | _ :: _, [] => false

theorem all2_sound {p : DC → List Nat → Bool} :
    ∀ {ds : List DC} {ks : List (List Nat)}, all2 p ds ks = true → ∀ d ∈ ds, ∃ k, p d k = true
  | [], _, _, _, h => by cases h
  | d :: ds, k :: ks, h, e, he => by
      simp only [all2, Bool.and_eq_true] at h
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨k, h.1⟩
      · exact all2_sound h.2 e he
  | _ :: _, [], h, _, _ => by cases h

def gfree (l : Lit) : Bool := l.guards.isEmpty

def baseOf (cs : List (List Lit)) : List DC :=
  cs.filterMap fun c => match c with
    | [l] => if gfree l then some l.dc else none
    | _ => none

def clausesOf (fs : List Fm) (g : Fm) : List (List Lit) := fs.flatMap (cnf true) ++ cnf false g

def guardsOf (fs : List Fm) (g : Fm) : List DC := (clausesOf fs g).flatMap fun c => c.flatMap Lit.guards

def check (fs : List Fm) (g : Fm) (sel : List Nat) (gk ck : List (List Nat)) : Bool :=
  all2 (fun d k => cyc (d.neg :: baseOf (fs.flatMap (cnf true))) k) (guardsOf fs g) gk &&
    (ch (sel.filterMap fun i => ((clausesOf fs g).map (·.map Lit.dc))[i]?) [] ck).isSome

theorem Fm.all_cnf {ρ : List Nat} : ∀ {fs : List Fm}, Fm.all ρ fs → CHolds ρ (fs.flatMap (cnf true))
  | [], _ => fun c hc => by simp at hc
  | f :: fs, ⟨h, hs⟩ => by
      rw [List.flatMap_cons]
      exact CHolds.append (cnf_sound ρ f true (by simpa using h)) (Fm.all_cnf hs)

theorem baseOf_sound {ρ : List Nat} {cs : List (List Lit)} (h : CHolds ρ cs) :
    ∀ d ∈ baseOf cs, d.holds ρ := by
  intro d hd
  simp only [baseOf, List.mem_filterMap] at hd
  obtain ⟨c, hc, he⟩ := hd
  split at he
  · rename_i l
    split at he
    · rename_i hg
      cases he
      obtain ⟨l', hl', hl''⟩ := h _ hc
      simp only [List.mem_singleton] at hl'; subst hl'
      refine Lit.dc_sound (fun e he => ?_) hl''
      simp only [gfree, List.isEmpty_iff] at hg; rw [hg] at he; cases he
    · cases he
  · cases he

theorem check_sound (ρ : List Nat) (fs : List Fm) (g : Fm) (sel : List Nat) (gk ck : List (List Nat))
    (h : check fs g sel gk ck = true) (hfs : Fm.all ρ fs) : g.den ρ := by
  refine Classical.byContradiction fun hng => ?_
  have hf := Fm.all_cnf hfs
  have hg := cnf_sound ρ g false (by simpa using hng)
  simp only [check, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨hgd, r, hch⟩ := h
  have hb := baseOf_sound hf
  have hG : ∀ d ∈ guardsOf fs g, d.holds ρ := fun d hd => Classical.byContradiction fun hn => by
    obtain ⟨k, hk⟩ := all2_sound hgd d hd
    exact cyc_sound (ρ := ρ) hk fun e he => by
      rcases List.mem_cons.1 he with rfl | he
      · simp only [DC.holds, DC.neg] at hn ⊢; omega
      · exact hb e he
  have hall : CHolds ρ (clausesOf fs g) := CHolds.append hf hg
  refine ch_sound (ρ := ρ) _ [] _ _ hch (fun _ h => by cases h) fun c hc => ?_
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hc
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hi)
  obtain ⟨l, hl, hl'⟩ := hall cl hcl
  exact ⟨l.dc, List.mem_map_of_mem hl, Lit.dc_sound (fun e he => hG e
    (List.mem_flatMap.2 ⟨cl, hcl, List.mem_flatMap.2 ⟨l, hl, he⟩⟩)) hl'⟩

open Lean Meta Elab Tactic

def tmE : Tm → Expr
  | .atom i => mkApp (mkConst ``Tm.atom) (mkNatLit i)
  | .lit n => mkApp (mkConst ``Tm.lit) (mkNatLit n)
  | .add a n => mkApp2 (mkConst ``Tm.add) (tmE a) (mkNatLit n)
  | .ladd n a => mkApp2 (mkConst ``Tm.ladd) (mkNatLit n) (tmE a)
  | .sub a n => mkApp2 (mkConst ``Tm.sub) (tmE a) (mkNatLit n)
  | .wrap a n => mkApp2 (mkConst ``Tm.wrap) (tmE a) (mkNatLit n)

def fmE : Fm → Expr
  | .le a b => mkApp2 (mkConst ``Fm.le) (tmE a) (tmE b)
  | .lt a b => mkApp2 (mkConst ``Fm.lt) (tmE a) (tmE b)
  | .eq a b => mkApp2 (mkConst ``Fm.eq) (tmE a) (tmE b)
  | .ne a b => mkApp2 (mkConst ``Fm.ne) (tmE a) (tmE b)
  | .and p q => mkApp2 (mkConst ``Fm.and) (fmE p) (fmE q)
  | .or p q => mkApp2 (mkConst ``Fm.or) (fmE p) (fmE q)
  | .not p => mkApp (mkConst ``Fm.not) (fmE p)

abbrev RM := StateT (Array Expr) MetaM

def atomIdx (e : Expr) : RM Nat := do
  let as ← get
  match as.findIdx? (· == e) with
  | some i => return i + 1
  | none => set (as.push e); return as.size + 1

def natLit? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default <| whnf e
  return e'.rawNatLit? <|> e'.nat?

partial def reifyT (e : Expr) : RM Tm := do
  if let some n ← natLit? e then return .lit n
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    if let some n ← natLit? b then return .add (← reifyT a) n
    if let some n ← natLit? a then return .ladd n (← reifyT b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    if let some n ← natLit? b then return .sub (← reifyT a) n
  | (``HMod.hMod, #[_, _, _, _, a, b]) =>
    if (← natLit? b) == some 18446744073709551616 then
      if let (``HAdd.hAdd, #[_, _, _, _, x, k]) := a.getAppFnArgs then
        if let some n ← natLit? k then return .wrap (← reifyT x) n
  | _ => pure ()
  return .atom (← atomIdx e)

def isNat (t : Expr) : Bool := t.isConstOf ``Nat

partial def reifyF (e : Expr) : RM (Option Fm) := do
  match e.getAppFnArgs with
  | (``LE.le, #[t, _, a, b]) => if isNat t then return some (.le (← reifyT a) (← reifyT b))
  | (``LT.lt, #[t, _, a, b]) => if isNat t then return some (.lt (← reifyT a) (← reifyT b))
  | (``GE.ge, #[t, _, a, b]) => if isNat t then return some (.le (← reifyT b) (← reifyT a))
  | (``GT.gt, #[t, _, a, b]) => if isNat t then return some (.lt (← reifyT b) (← reifyT a))
  | (``Eq, #[t, a, b]) => if isNat t then return some (.eq (← reifyT a) (← reifyT b))
  | (``Ne, #[t, a, b]) => if isNat t then return some (.ne (← reifyT a) (← reifyT b))
  | (``And, #[p, q]) =>
    if let some p' ← reifyF p then if let some q' ← reifyF q then return some (.and p' q')
  | (``Or, #[p, q]) =>
    if let some p' ← reifyF p then if let some q' ← reifyF q then return some (.or p' q')
  | (``Not, #[p]) => if let some p' ← reifyF p then return some (.not p')
  | _ => pure ()
  return none

partial def Tm.hasWrap : Tm → Bool
  | .wrap _ _ => true
  | .add a _ | .sub a _ | .ladd _ a => a.hasWrap
  | _ => false

partial def Fm.hasWrap : Fm → Bool
  | .le a b | .lt a b | .eq a b | .ne a b => a.hasWrap || b.hasWrap
  | .and p q | .or p q => p.hasWrap || q.hasWrap
  | .not p => p.hasWrap

def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

def findCycle (ds : List DC) : Option (List Nat) := Id.run do
  let es := ds.toArray
  let n := es.foldl (fun m d => max m (max d.a d.b + 1)) 0
  let mut dist : Array Int := Array.replicate n 0
  let mut pred : Array Nat := Array.replicate n 0
  let mut last : Option Nat := none
  for _ in [:n + 1] do
    last := none
    for i in [:es.size] do
      let d := es[i]!
      if dist[d.a]! + d.c < dist[d.b]! then
        dist := dist.set! d.b (dist[d.a]! + d.c); pred := pred.set! d.b i; last := some d.b
    if last.isNone then return none
  let some v0 := last | return none
  let mut v := v0
  for _ in [:n] do v := es[pred[v]!]!.a
  let mut out : List Nat := []
  let mut u := v
  for _ in [:n + 1] do
    let e := pred[u]!
    out := e :: out
    u := es[e]!.a
    if u == v then return some out
  return none

/-- Certificate search for `ch`, over constraints tagged with the clause they come from;
returns the cycle lists and the tags of the constraints the cycles use. -/
abbrev CM := StateT Nat Option

def cyc1 (acc : List (DC × Nat)) : CM (Option (List Nat × List Nat)) := do
  let n ← get
  if n = 0 then failure
  set (n - 1)
  let ds := acc.map (·.1)
  let ts := acc.toArray.map (·.2)
  return (findCycle ds).map fun k => (k, k.map fun i => ts[i]!)

def certCh : List (List (DC × Nat)) → List (DC × Nat) → CM (List (List Nat) × List Nat)
  | [], acc => do
    let some (k, t) ← cyc1 acc | failure
    return ([k], t)
  | c :: cs, acc => do
    if let some (k, t) ← cyc1 acc then return ([k], t)
    c.foldlM (fun (ks, ts) d => do
      let (ks', ts') ← certCh cs (d :: acc)
      return (ks ++ ks', ts ++ ts')) ([[]], [])

def subsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _, [] => [[]]
  | k + 1, x :: xs => (subsets (k + 1) xs) ++ (subsets k xs).map (x :: ·)

/-- The clause index range of each fact in `clausesOf`. -/
def factOf (fs : List Fm) (c : Nat) : Option Nat := Id.run do
  let mut lo := 0
  let mut i := 0
  for f in fs do
    let n := (cnf true f).length
    if c < lo + n then return some i
    lo := lo + n; i := i + 1
  return none

/-- A certificate for `check fs g`, and the facts it uses. -/
def certs (fs : List Fm) (g : Fm) : Option (List Nat × List (List Nat) × List (List Nat) × List Nat) := do
  let fcl := fs.flatMap (cnf true)
  let baseT : List (DC × Nat) := (List.range fcl.length).filterMap fun i => match fcl[i]! with
    | [l] => if gfree l then some (l.dc, i) else none
    | _ => none
  let mut gk : List (List Nat) := []
  let mut used : List Nat := []
  for d in guardsOf fs g do
    let acc := (d.neg, fcl.length + 1000000) :: baseT
    let some (some (k, t), _) := (cyc1 acc).run 1 | none
    gk := gk ++ [k]; used := used ++ t
  let cls := ((clausesOf fs g).map (·.map Lit.dc)).toArray
  let nf := fcl.length
  let idx := List.range cls.size
  let units := idx.filter fun i => cls[i]!.length == 1
  let goals := idx.filter fun i => i ≥ nf && cls[i]!.length != 1
  let multi := idx.filter fun i => i < nf && cls[i]!.length != 1
  let multi := multi.take 12
  let tries := (subsets 0 multi) ++ (subsets 1 multi).filter (·.length == 1) ++
    (subsets 2 multi).filter (·.length == 2) ++ (if multi.length ≤ 6 then [multi] else [])
  let mut fuel := 96
  for t in tries do
    let sel := units ++ goals ++ t
    let tagged := sel.filterMap fun i => cls[i]?.map (·.map (·, i))
    match (certCh tagged []).run fuel with
    | some ((ck, ts), _) =>
      let fsU := (used ++ ts).filterMap (factOf fs)
      return (sel, gk, ck, (List.range fs.length).filter fsU.contains)
    | none => fuel := fuel - 24; if fuel < 24 then none
  none

def natsE (ks : List (List Nat)) : Expr :=
  listE (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)) (ks.map fun k => listE (mkConst ``Nat) (k.map mkNatLit))

/-- Reify the target and the facts `(type, proof)`; facts outside the fragment are dropped. -/
def reifyAll (tgt : Expr) (facts : Array (Expr × Expr)) :
    MetaM (Option (Fm × Array Expr × Array Fm × Array (Expr × Expr))) := do
  let (some gf, as0) ← (reifyF tgt).run #[] | return none
  let mut st := as0
  let mut fs : Array Fm := #[]
  let mut kept : Array (Expr × Expr) := #[]
  for (ty, pf) in facts do
    let (r, st') ← (reifyF ty).run st
    if let some f := r then st := st'; fs := fs.push f; kept := kept.push (ty, pf)
  return some (gf, st, fs, kept)

/-- The proof term of `tgt` from a checked certificate. -/
def mkPf (tgt : Expr) (gf : Fm) (st : Array Expr) (fs : Array Fm) (kept : Array (Expr × Expr))
    (sel : List Nat) (gk ck : List (List Nat)) : MetaM Expr := do
  let tys := kept.map (·.1)
  let pfs := kept.map (·.2)
  let nat := mkConst ``Nat
  withLocalDeclsDND (st.mapIdx fun i _ => ((`x).appendIndexAfter i, nat)) fun xs => do
    let abst : Expr → Expr := fun e => e.replace fun t =>
      match st.findIdx? (· == t) with
      | some i => some xs[i]!
      | none => none
    withLocalDeclsDND (tys.mapIdx fun i t => ((`h).appendIndexAfter i, abst t)) fun hv => do
      let ρ := listE nat xs.toList
      let fsE := listE (mkConst ``Fm) (fs.toList.map fmE)
      let mut hs : Expr := mkConst ``True.intro
      let mut rest := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Fm)
      for i in (List.range fs.size).reverse do
        let fE := fmE fs[i]!
        hs := mkApp4 (mkConst ``And.intro) (mkApp2 (mkConst ``Fm.den) ρ fE)
          (mkApp2 (mkConst ``Fm.all) ρ rest) hv[i]! hs
        rest := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Fm) fE rest
      let body := mkAppN (mkConst ``check_sound) #[ρ, fsE, fmE gf, listE nat (sel.map mkNatLit), natsE gk, natsE ck,
        mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true), hs]
      let lam ← mkLambdaFVars (xs ++ hv) (mkApp2 (mkConst ``id [Level.zero]) (abst tgt) body)
      return mkAppN lam (st ++ pfs)

def maxAtoms : Nat := 40

def dbmCore (g : MVarId) : MetaM Bool := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let (some _, as0) ← (reifyF tgt).run #[] | return false
  let mut info : Array (Expr × Expr × Array Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``LE.le || ty.isAppOf ``LT.lt || ty.isAppOf ``GE.ge || ty.isAppOf ``GT.gt ||
      ty.isAppOf ``Eq || ty.isAppOf ``Ne || ty.isAppOf ``Or || ty.isAppOf ``And || ty.isAppOf ``Not then
      let (r, as) ← (reifyF ty).run #[]
      if let some f := r then
        if (cnf true f).length ≤ 8 then info := info.push (ty, d.toExpr, as)
  let mut allA : Array Expr := as0
  for (_, _, as) in info do
    for a in as do unless allA.contains a do allA := allA.push a
  for e in allA do
    if let (``HAdd.hAdd, #[t, _, _, _, a, b]) := e.getAppFnArgs then
      if isNat t && (← natLit? b).isNone && (← natLit? a).isNone then
        for pf in [mkApp2 (mkConst ``Nat.le_add_right) a b, mkApp2 (mkConst ``Nat.le_add_left) b a] do
          let ty ← instantiateMVars (← inferType pf)
          let (r, as) ← (reifyF ty).run #[]
          if r.isSome then info := info.push (ty, pf, as)
  let mut live : Array Expr := as0
  let mut chosen : Array Bool := info.map fun _ => false
  let mut changed := true
  while changed do
    changed := false
    for i in [:info.size] do
      if chosen[i]! then continue
      let (_, _, as) := info[i]!
      if as.any (fun a => live.contains a) then
        chosen := chosen.set! i true; changed := true
        for a in as do unless live.contains a do live := live.push a
  if live.size > maxAtoms then return false
  let mut facts : Array (Expr × Expr) := #[]
  for i in [:info.size] do
    if chosen[i]! then facts := facts.push (info[i]!.1, info[i]!.2.1)
  let mut wrap := false
  for a in live do
    if let (``HMod.hMod, _) := a.getAppFnArgs then wrap := true
  for (ty, _) in facts do
    if (ty.find? fun e => e.isAppOf ``HMod.hMod).isSome then wrap := true
  if wrap || (tgt.find? fun e => e.isAppOf ``HMod.hMod).isSome then
    for a in live do
      if let (``BitVec.toNat, #[w, x]) := a.getAppFnArgs then
        if (← natLit? w) == some 64 then
          let pf := mkApp2 (mkConst ``BitVec.isLt) w x
          facts := facts.push (← instantiateMVars (← inferType pf), pf)
  let some (gf, st, fs, kept) ← reifyAll tgt facts | return false
  let some (sel, gk, ck, used) := certs fs.toList gf | return false
  -- re-solve over the facts the certificate uses: the kernel re-walks only those
  let small := used.toArray.map fun i => kept[i]!
  if small.size < kept.size then
    if let some (gf', st', fs', kept') ← reifyAll tgt small then
      if let some (sel', gk', ck', _) := certs fs'.toList gf' then
        if check fs'.toList gf' sel' gk' ck' then
          g.assign (← mkPf tgt gf' st' fs' kept' sel' gk' ck')
          return true
  if !(check fs.toList gf sel gk ck) then return false
  g.assign (← mkPf tgt gf st fs kept sel gk ck)
  return true

/-- First pass of an arithmetic side goal: the reflective difference-constraint checker. -/
def dbmClose (g : MVarId) : MetaM Bool := do
  let s ← saveState
  try
    let (_, g') ← g.intros
    let g' ← g'.withContext do
      if (← whnfR (← instantiateMVars (← g'.getType))).isConstOf ``False then
        let m ← mkFreshExprSyntheticOpaqueMVar
          (mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat) (mkConst ``instLTNat) (mkNatLit 0) (mkNatLit 0))
        g'.assign (mkApp2 (mkConst ``Nat.lt_irrefl) (mkNatLit 0) m)
        pure m.mvarId!
      else pure g'
    if ← dbmCore g' then return true
    s.restore; return false
  catch _ => s.restore; return false

elab "dbm" : tactic => do
  unless ← dbmClose (← getMainGoal) do throwError "dbm: not closed by a difference-constraint certificate"
  replaceMainGoal []

/-- `omega` with the difference-constraint checker as first pass. -/
macro "omega_dc" : tactic => `(tactic| first | dbm | omega)

/-- Fails on `x.toNat + k < 2 ^ 64` with a literal `k ≥ 2 ^ 63` (the no-wrap side goal of
`toNat_add_lit` at a negative offset, which holds only for `x.toNat < 2 ^ 64 - k`). -/
elab "dc_nowrap_neg" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  if let (``LT.lt, #[ty, _, l, r]) := t.getAppFnArgs then
    if ty.isConstOf ``Nat then
      if let (``HAdd.hAdd, #[_, _, _, _, a, k]) := l.getAppFnArgs then
        if a.isAppOf ``BitVec.toNat then
          if let some k ← natLit? k then
            if let some r ← natLit? r then
              if r == 18446744073709551616 && 9223372036854775808 ≤ k then
                throwError "dc_nowrap_neg: negative offset"
            else if let (``HPow.hPow, #[_, _, _, _, b, e]) := r.getAppFnArgs then
              if (← natLit? b) == some 2 && (← natLit? e) == some 64 && 9223372036854775808 ≤ k then
                throwError "dc_nowrap_neg: negative offset"

/-- `omega_dc` for the side goals of the `toNat_add_lit`/`toNat_add_neg` rewrites: skips the
no-wrap goal of a negative offset (there `toNat_add_neg` applies). -/
macro "omega_dcn" : tactic => `(tactic| (dc_nowrap_neg; first | dbm | omega))

end VsaIris.Dbm
