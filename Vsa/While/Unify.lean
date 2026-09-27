/-!
# First-order unification

Terms over variables `V` (program names and auxiliary variables), leaves and
binary nodes. `unifyTop σ E` extends an idempotent substitution `σ` by a most
general solution of the equations `E`:

* `unifyTop_sound`: every assignment satisfying the result satisfies `σ` and
  `E`;
* `unifyTop_complete`: any assignment satisfying `σ` and `E` satisfies the
  result, which exists;
* `unifyTop_idem`, `unifyTop_vars`: the result is idempotent and mentions only
  variables of `σ` and `E`;
* `canon_sat`: an idempotent substitution has a ground solution `canon σ`.

The worklist algorithm terminates by the lexicographic measure (unsolved
variables, size of the worklist).
-/

namespace Vsa.While.Unify

/-- Variables: program names and auxiliary variables. -/
inductive V where
  | name (x : String)
  | aux (n : Nat)
  deriving DecidableEq, Repr

/-- Terms. -/
inductive Tm where
  | var (v : V)
  | leaf (c : Nat)
  | node (c : Nat) (a b : Tm)
  deriving DecidableEq, Repr

namespace Tm

def size : Tm → Nat
  | var _ => 1
  | leaf _ => 1
  | node _ a b => a.size + b.size + 1

def vars : Tm → List V
  | var v => [v]
  | leaf _ => []
  | node _ a b => a.vars ++ b.vars

/-- Apply an assignment. -/
def bind (θ : V → Tm) : Tm → Tm
  | var v => θ v
  | leaf c => leaf c
  | node c a b => node c (a.bind θ) (b.bind θ)

/-- Replace one variable. -/
def sub1 (t : Tm) (v : V) (s : Tm) : Tm := t.bind fun w => if w = v then s else var w

theorem size_pos (t : Tm) : 0 < t.size := by cases t <;> simp [size]

theorem bind_bind (θ θ' : V → Tm) (t : Tm) :
    (t.bind θ).bind θ' = t.bind fun v => (θ v).bind θ' := by
  induction t with
  | var v => rfl
  | leaf c => rfl
  | node c a b iha ihb => simp [bind, iha, ihb]

theorem bind_congr {θ θ' : V → Tm} {t : Tm} (h : ∀ v ∈ t.vars, θ v = θ' v) :
    t.bind θ = t.bind θ' := by
  induction t with
  | var v => exact h v (by simp [vars])
  | leaf c => rfl
  | node c a b iha ihb =>
    simp only [bind]
    rw [iha fun v hv => h v (by simp [vars, hv]), ihb fun v hv => h v (by simp [vars, hv])]

theorem bind_var (t : Tm) : t.bind var = t := by
  induction t with
  | var v => rfl
  | leaf c => rfl
  | node c a b iha ihb => simp [bind, iha, ihb]

theorem sub1_bind {θ : V → Tm} {v : V} {s : Tm} (h : θ v = s.bind θ) (t : Tm) :
    (t.sub1 v s).bind θ = t.bind θ := by
  unfold sub1
  rw [bind_bind]
  apply bind_congr
  intro w _
  by_cases hw : w = v
  · subst hw; simp [h]
  · simp [hw, bind]

theorem mem_vars_bind {θ : V → Tm} {t : Tm} {w : V} (h : w ∈ (t.bind θ).vars) :
    ∃ u ∈ t.vars, w ∈ (θ u).vars := by
  induction t with
  | var u => exact ⟨u, by simp [vars], h⟩
  | leaf c => simp [bind, vars] at h
  | node c a b iha ihb =>
    simp only [bind, vars, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨u, hu, hw⟩ := iha h; exact ⟨u, by simp [vars, hu], hw⟩
    · obtain ⟨u, hu, hw⟩ := ihb h; exact ⟨u, by simp [vars, hu], hw⟩

theorem mem_vars_sub1 {v w : V} {s t : Tm} (h : w ∈ (t.sub1 v s).vars) :
    (w ∈ t.vars ∧ w ≠ v) ∨ w ∈ s.vars := by
  obtain ⟨u, hu, hw⟩ := mem_vars_bind h
  by_cases huv : u = v
  · subst huv; simp at hw; exact .inr hw
  · simp [huv, vars] at hw; subst hw; exact .inl ⟨hu, huv⟩

/-- The occurs check is sound: a variable strictly inside a term is smaller. -/
theorem size_lt_of_occurs {θ : V → Tm} {v : V} {t : Tm} (hv : v ∈ t.vars) (ht : t ≠ var v) :
    (θ v).size < (t.bind θ).size := by
  induction t with
  | var u =>
    simp [vars] at hv; subst hv; exact absurd rfl ht
  | leaf c => simp [vars] at hv
  | node c a b iha ihb =>
    simp only [vars, List.mem_append] at hv
    simp only [bind, size]
    rcases hv with hv | hv
    · by_cases ha : a = var v
      · subst ha; simp [bind]; omega
      · have := iha hv ha; omega
    · by_cases hb : b = var v
      · subst hb; simp [bind]; omega
      · have := ihb hv hb; omega

end Tm

/-- Substitutions: bindings, first match wins. -/
abbrev Subst := List (V × Tm)

def find : Subst → V → Option Tm
  | [], _ => none
  | (w, t) :: σ, v => if w = v then some t else find σ v

def get (σ : Subst) (v : V) : Tm := (find σ v).getD (.var v)

def dom (σ : Subst) : List V := σ.map (·.1)

/-- Apply a substitution. -/
def app (σ : Subst) (t : Tm) : Tm := t.bind (get σ)

/-- An assignment satisfies a substitution. -/
def Sat (θ : V → Tm) (σ : Subst) : Prop := ∀ p ∈ σ, θ p.1 = p.2.bind θ

/-- An assignment satisfies equations. -/
def SatE (θ : V → Tm) (E : List (Tm × Tm)) : Prop := ∀ e ∈ E, e.1.bind θ = e.2.bind θ

/-- Distinct domain. -/
def Distinct : Subst → Prop
  | [] => True
  | (v, _) :: σ => v ∉ dom σ ∧ Distinct σ

/-- Idempotent: distinct domain, and no domain variable in any range term. -/
structure Idem (σ : Subst) : Prop where
  distinct : Distinct σ
  range : ∀ p ∈ σ, ∀ w ∈ p.2.vars, w ∉ dom σ

def varsS (σ : Subst) : List V := σ.flatMap fun p => p.1 :: p.2.vars

def varsE (E : List (Tm × Tm)) : List V := E.flatMap fun e => e.1.vars ++ e.2.vars

def sizeE : List (Tm × Tm) → Nat
  | [] => 0
  | (a, b) :: E => a.size + b.size + sizeE E

def bindS (v : V) (t : Tm) (σ : Subst) : Subst :=
  (v, t) :: σ.map fun p => (p.1, p.2.sub1 v t)

def bindE (v : V) (t : Tm) (E : List (Tm × Tm)) : List (Tm × Tm) :=
  E.map fun e => (e.1.sub1 v t, e.2.sub1 v t)

/-- Variables of `W` not yet solved. -/
def cnt (W : List V) (σ : Subst) : Nat := (W.filter fun w => !(dom σ).contains w).length

theorem dom_bindS (v : V) (t : Tm) (σ : Subst) : dom (bindS v t σ) = v :: dom σ := by
  simp [bindS, dom, Function.comp_def]

theorem length_filter_lt {α : Type} {p q : α → Bool} :
    ∀ (W : List α) {v : α}, (∀ w ∈ W, p w = true → q w = true) → v ∈ W → q v = true →
      p v = false → (W.filter p).length < (W.filter q).length
  | [], _, _, hv, _, _ => by cases hv
  | w :: W, v, hpq, hv, hq, hp => by
    have hle : ∀ (W : List α), (∀ w ∈ W, p w = true → q w = true) →
        (W.filter p).length ≤ (W.filter q).length := by
      intro W h
      induction W with
      | nil => simp
      | cons x W ih =>
        have ih := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
        by_cases hpx : p x = true
        · have hqx := h x (List.mem_cons_self) hpx
          simp [hpx, hqx]; omega
        · by_cases hqx : q x = true
          · simp [hpx, hqx]; omega
          · simp [hpx, hqx]; omega
    rcases List.mem_cons.mp hv with rfl | hv
    · have h := hle W fun w hw => hpq w (List.mem_cons_of_mem _ hw)
      simp [hp, hq]; omega
    · have h := length_filter_lt W (fun w hw => hpq w (List.mem_cons_of_mem _ hw)) hv hq hp
      by_cases hpw : p w = true
      · have hqw := hpq w List.mem_cons_self hpw
        simp [hpw, hqw]; omega
      · by_cases hqw : q w = true
        · simp [hpw, hqw]; omega
        · simp [hpw, hqw]; omega

theorem cnt_bindS_lt {W : List V} {σ : Subst} {v : V} (t : Tm) (hv : v ∈ W)
    (hd : v ∉ dom σ) : cnt W (bindS v t σ) < cnt W σ := by
  unfold cnt
  rw [dom_bindS]
  apply length_filter_lt W _ hv
  · simpa using hd
  · simp
  · intro w _ h; simp at h ⊢; exact h.2

/-- Worklist unification. -/
def unifyW (W : List V) (σ : Subst) : List (Tm × Tm) → Option Subst
  | [] => some σ
  | (.leaf c, .leaf d) :: E => if c = d then unifyW W σ E else none
  | (.node c a₁ a₂, .node d b₁ b₂) :: E =>
    if c = d then unifyW W σ ((a₁, b₁) :: (a₂, b₂) :: E) else none
  | (.var v, t) :: E =>
    if t = .var v then unifyW W σ E
    else if v ∈ t.vars then none
    else if h : v ∈ W ∧ v ∉ dom σ then unifyW W (bindS v t σ) (bindE v t E) else none
  | (t, .var v) :: E =>
    if v ∈ t.vars then none
    else if h : v ∈ W ∧ v ∉ dom σ then unifyW W (bindS v t σ) (bindE v t E) else none
  | (.leaf _, .node _ _ _) :: _ => none
  | (.node _ _ _, .leaf _) :: _ => none
termination_by E => (cnt W σ, sizeE E)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; exact cnt_bindS_lt _ h.1 h.2)
    | (apply Prod.Lex.right; simp only [sizeE, Tm.size]; omega)

/-! ## Unfolding -/

theorem unifyW_var_left {W : List V} {σ : Subst} {v : V} {t : Tm} {E : List (Tm × Tm)}
    (ht : t ≠ .var v) :
    unifyW W σ ((.var v, t) :: E) =
      if v ∈ t.vars then none
      else if v ∈ W ∧ v ∉ dom σ then unifyW W (bindS v t σ) (bindE v t E) else none := by
  rw [unifyW.eq_def]
  simp only [ht, ↓reduceIte, dite_eq_ite]

theorem unifyW_var_right {W : List V} {σ : Subst} {v : V} {t : Tm} {E : List (Tm × Tm)}
    (ht : ∀ w, t ≠ .var w) :
    unifyW W σ ((t, .var v) :: E) =
      if v ∈ t.vars then none
      else if v ∈ W ∧ v ∉ dom σ then unifyW W (bindS v t σ) (bindE v t E) else none := by
  cases t with
  | var w => exact absurd rfl (ht w)
  | leaf c => rw [unifyW.eq_def]; simp [dite_eq_ite]
  | node c a b => rw [unifyW.eq_def]; simp [dite_eq_ite]

/-! ## One binding -/

theorem sat_bindS {θ : V → Tm} {v : V} {t : Tm} {σ : Subst} :
    Sat θ (bindS v t σ) ↔ θ v = t.bind θ ∧ Sat θ σ := by
  constructor
  · intro h
    have hv : θ v = t.bind θ := h (v, t) (by simp [bindS])
    refine ⟨hv, fun p hp => ?_⟩
    have := h (p.1, p.2.sub1 v t) (by simp only [bindS, List.mem_cons, List.mem_map]; exact .inr ⟨p, hp, rfl⟩)
    rw [this, Tm.sub1_bind hv]
  · rintro ⟨hv, h⟩ p hp
    simp only [bindS, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact hv
    · rw [Tm.sub1_bind hv]; exact h q hq

theorem satE_bindE {θ : V → Tm} {v : V} {t : Tm} {E : List (Tm × Tm)} (hv : θ v = t.bind θ) :
    SatE θ (bindE v t E) ↔ SatE θ E := by
  constructor
  · intro h e he
    have := h (e.1.sub1 v t, e.2.sub1 v t) (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa [Tm.sub1_bind hv] using this
  · intro h e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp only [Tm.sub1_bind hv]
    exact h e' he'

theorem satE_cons {θ : V → Tm} {a b : Tm} {E : List (Tm × Tm)} :
    SatE θ ((a, b) :: E) ↔ a.bind θ = b.bind θ ∧ SatE θ E := by
  simp [SatE]

theorem mem_varsE_cons {w : V} {a b : Tm} {E : List (Tm × Tm)} :
    w ∈ varsE ((a, b) :: E) ↔ w ∈ a.vars ∨ w ∈ b.vars ∨ w ∈ varsE E := by
  simp [varsE, or_assoc]

theorem mem_varsE_bindE {w v : V} {t : Tm} {E : List (Tm × Tm)} (h : w ∈ varsE (bindE v t E)) :
    (w ∈ varsE E ∧ w ≠ v) ∨ w ∈ t.vars := by
  simp only [varsE, bindE, List.flatMap_map, List.mem_flatMap, List.mem_append] at h
  obtain ⟨e, he, h | h⟩ := h
  · rcases Tm.mem_vars_sub1 h with ⟨h, hne⟩ | h
    · exact .inl ⟨List.mem_flatMap.mpr ⟨e, he, List.mem_append_left _ h⟩, hne⟩
    · exact .inr h
  · rcases Tm.mem_vars_sub1 h with ⟨h, hne⟩ | h
    · exact .inl ⟨List.mem_flatMap.mpr ⟨e, he, List.mem_append_right _ h⟩, hne⟩
    · exact .inr h

/-! ## Soundness -/

theorem unifyW_sound (W : List V) :
    ∀ σ E σ', unifyW W σ E = some σ' → ∀ θ, Sat θ σ' → Sat θ σ ∧ SatE θ E := by
  intro σ E
  induction σ, E using unifyW.induct W with
  | case1 σ =>
    intro σ' h θ hs
    rw [unifyW.eq_def] at h; cases h; exact ⟨hs, fun _ h => by cases h⟩
  | case2 σ d E ih =>
    intro σ' h θ hs
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    obtain ⟨h1, h2⟩ := ih σ' h θ hs
    exact ⟨h1, satE_cons.mpr ⟨rfl, h2⟩⟩
  | case3 σ c d E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case4 σ a₁ a₂ d b₁ b₂ E ih =>
    intro σ' h θ hs
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    obtain ⟨h1, h2⟩ := ih σ' h θ hs
    rw [satE_cons, satE_cons] at h2
    exact ⟨h1, satE_cons.mpr ⟨by simp [Tm.bind, h2.1, h2.2.1], h2.2.2⟩⟩
  | case5 σ c a₁ a₂ d b₁ b₂ E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case6 σ v E ih =>
    intro σ' h θ hs
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    obtain ⟨h1, h2⟩ := ih σ' h θ hs
    exact ⟨h1, satE_cons.mpr ⟨rfl, h2⟩⟩
  | case7 σ v t E ht hv => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv] at h
  | case8 σ v t E ht hv hW ih =>
    intro σ' h θ hs
    rw [unifyW_var_left ht] at h; simp only [hv, hW, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := ih σ' h θ hs
    obtain ⟨hθv, h1⟩ := sat_bindS.mp h1
    exact ⟨h1, satE_cons.mpr ⟨hθv, (satE_bindE hθv).mp h2⟩⟩
  | case9 σ v t E ht hv hW => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv, hW] at h
  | case10 σ t v E ht hv => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv] at h
  | case11 σ t v E ht hv hW ih =>
    intro σ' h θ hs
    rw [unifyW_var_right ht] at h; simp only [hv, hW, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := ih σ' h θ hs
    obtain ⟨hθv, h1⟩ := sat_bindS.mp h1
    exact ⟨h1, satE_cons.mpr ⟨hθv.symm, (satE_bindE hθv).mp h2⟩⟩
  | case12 σ t v E ht hv hW => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv, hW] at h
  | case13 => intro σ' h; rw [unifyW.eq_def] at h; cases h
  | case14 => intro σ' h; rw [unifyW.eq_def] at h; cases h

/-! ## Completeness -/

theorem unifyW_complete (W : List V) (θ : V → Tm) :
    ∀ σ E, Sat θ σ → SatE θ E → (∀ w ∈ varsE E, w ∈ W ∧ w ∉ dom σ) →
      ∃ σ', unifyW W σ E = some σ' ∧ Sat θ σ' := by
  intro σ E
  induction σ, E using unifyW.induct W with
  | case1 σ => intro hs _ _; exact ⟨σ, by rw [unifyW.eq_def], hs⟩
  | case2 σ d E ih =>
    intro hs hE hW
    rw [unifyW.eq_def]; simp only [↓reduceIte]
    exact ih hs (satE_cons.mp hE).2 fun w hw => hW w (mem_varsE_cons.mpr (.inr (.inr hw)))
  | case3 σ c d E hcd =>
    intro _ hE _
    have := (satE_cons.mp hE).1; simp [Tm.bind] at this; exact absurd this hcd
  | case4 σ a₁ a₂ d b₁ b₂ E ih =>
    intro hs hE hW
    rw [unifyW.eq_def]; simp only [↓reduceIte]
    obtain ⟨h1, h2⟩ := satE_cons.mp hE
    simp only [Tm.bind, Tm.node.injEq, true_and] at h1
    refine ih hs (satE_cons.mpr ⟨h1.1, satE_cons.mpr ⟨h1.2, h2⟩⟩) fun w hw => hW w ?_
    simp only [mem_varsE_cons, Tm.vars, List.mem_append] at hw ⊢
    rcases hw with h | h | h | h | h <;> simp [h]
  | case5 σ c a₁ a₂ d b₁ b₂ E hcd =>
    intro _ hE _
    have := (satE_cons.mp hE).1; simp [Tm.bind] at this; exact absurd this.1 hcd
  | case6 σ v E ih =>
    intro hs hE hW
    rw [unifyW.eq_def]; simp only [↓reduceIte]
    exact ih hs (satE_cons.mp hE).2 fun w hw => hW w (mem_varsE_cons.mpr (.inr (.inr hw)))
  | case7 σ v t E ht hv =>
    intro _ hE _
    have h := (satE_cons.mp hE).1
    have := Tm.size_lt_of_occurs (θ := θ) hv ht
    simp only [Tm.bind] at h; rw [h] at this; omega
  | case8 σ v t E ht hv hW' ih =>
    intro hs hE hW
    rw [unifyW_var_left ht]; simp only [hv, hW', ↓reduceIte]
    obtain ⟨h1, h2⟩ := satE_cons.mp hE
    refine ih (sat_bindS.mpr ⟨h1, hs⟩) ((satE_bindE h1).mpr h2) fun w hw => ?_
    rcases mem_varsE_bindE hw with ⟨hw, hne⟩ | hw
    · have := hW w (mem_varsE_cons.mpr (.inr (.inr hw)))
      exact ⟨this.1, by rw [dom_bindS]; simp [hne, this.2]⟩
    · have := hW w (mem_varsE_cons.mpr (.inr (.inl hw)))
      refine ⟨this.1, ?_⟩
      rw [dom_bindS]; simp only [List.mem_cons, not_or]
      exact ⟨fun h => hv (h ▸ hw), this.2⟩
  | case9 σ v t E ht hv hW' =>
    intro _ _ hW
    exact absurd (hW v (mem_varsE_cons.mpr (.inl (by simp [Tm.vars])))) hW'
  | case10 σ t v E ht hv =>
    intro _ hE _
    have h := (satE_cons.mp hE).1
    have := Tm.size_lt_of_occurs (θ := θ) hv (ht v)
    simp only [Tm.bind] at h; rw [← h] at this; omega
  | case11 σ t v E ht hv hW' ih =>
    intro hs hE hW
    rw [unifyW_var_right ht]; simp only [hv, hW', ↓reduceIte]
    obtain ⟨h1, h2⟩ := satE_cons.mp hE
    have h1 : θ v = t.bind θ := h1.symm
    refine ih (sat_bindS.mpr ⟨h1, hs⟩) ((satE_bindE h1).mpr h2) fun w hw => ?_
    rcases mem_varsE_bindE hw with ⟨hw, hne⟩ | hw
    · have := hW w (mem_varsE_cons.mpr (.inr (.inr hw)))
      exact ⟨this.1, by rw [dom_bindS]; simp [hne, this.2]⟩
    · have := hW w (mem_varsE_cons.mpr (.inl hw))
      refine ⟨this.1, ?_⟩
      rw [dom_bindS]; simp only [List.mem_cons, not_or]
      exact ⟨fun h => hv (h ▸ hw), this.2⟩
  | case12 σ t v E ht hv hW' =>
    intro _ _ hW
    exact absurd (hW v (mem_varsE_cons.mpr (.inr (.inl (by simp [Tm.vars]))))) hW'
  | case13 =>
    intro _ hE _
    have := (satE_cons.mp hE).1; simp [Tm.bind] at this
  | case14 =>
    intro _ hE _
    have := (satE_cons.mp hE).1; simp [Tm.bind] at this

/-! ## Idempotence and variables -/

theorem dom_map_snd (f : V × Tm → Tm) (σ : Subst) :
    dom (σ.map fun p => (p.1, f p)) = dom σ := by
  simp [dom, Function.comp_def]

theorem distinct_map_snd (f : V × Tm → Tm) : ∀ σ : Subst,
    Distinct (σ.map fun p => (p.1, f p)) ↔ Distinct σ
  | [] => Iff.rfl
  | (v, t) :: σ => by
    simp only [List.map_cons, Distinct, dom_map_snd, distinct_map_snd f σ]

theorem idem_bindS {σ : Subst} {v : V} {t : Tm} (hσ : Idem σ) (hv : v ∉ dom σ)
    (hvt : v ∉ t.vars) (ht : ∀ w ∈ t.vars, w ∉ dom σ) : Idem (bindS v t σ) := by
  refine ⟨?_, ?_⟩
  · simp only [bindS, Distinct, dom_map_snd, distinct_map_snd]
    exact ⟨hv, hσ.distinct⟩
  · intro p hp w hw
    rw [dom_bindS]
    simp only [List.mem_cons, not_or]
    simp only [bindS, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨fun h => hvt (h ▸ hw), ht w hw⟩
    · rcases Tm.mem_vars_sub1 hw with ⟨hw, hne⟩ | hw
      · exact ⟨hne, hσ.range q hq w hw⟩
      · exact ⟨fun h => hvt (h ▸ hw), ht w hw⟩

theorem mem_varsS_bindS {σ : Subst} {v w : V} {t : Tm} (h : w ∈ varsS (bindS v t σ)) :
    w = v ∨ w ∈ t.vars ∨ w ∈ varsS σ := by
  simp only [varsS, bindS, List.flatMap_cons, List.flatMap_map, List.mem_append,
    List.mem_cons, List.mem_flatMap] at h
  rcases h with (h | h) | ⟨q, hq, h | h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (List.mem_flatMap.mpr ⟨q, hq, by simp [h]⟩))
  · rcases Tm.mem_vars_sub1 h with ⟨h, _⟩ | h
    · exact .inr (.inr (List.mem_flatMap.mpr ⟨q, hq, by simp [h]⟩))
    · exact .inr (.inl h)

theorem unifyW_idem (W : List V) :
    ∀ σ E σ', unifyW W σ E = some σ' → Idem σ → (∀ w ∈ varsE E, w ∉ dom σ) → Idem σ' := by
  intro σ E
  induction σ, E using unifyW.induct W with
  | case1 σ => intro σ' h hσ _; rw [unifyW.eq_def] at h; cases h; exact hσ
  | case2 σ d E ih =>
    intro σ' h hσ hE
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    exact ih σ' h hσ fun w hw => hE w (mem_varsE_cons.mpr (.inr (.inr hw)))
  | case3 σ c d E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case4 σ a₁ a₂ d b₁ b₂ E ih =>
    intro σ' h hσ hE
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    refine ih σ' h hσ fun w hw => hE w ?_
    simp only [mem_varsE_cons, Tm.vars, List.mem_append] at hw ⊢
    rcases hw with h | h | h | h | h <;> simp [h]
  | case5 σ c a₁ a₂ d b₁ b₂ E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case6 σ v E ih =>
    intro σ' h hσ hE
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    exact ih σ' h hσ fun w hw => hE w (mem_varsE_cons.mpr (.inr (.inr hw)))
  | case7 σ v t E ht hv => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv] at h
  | case8 σ v t E ht hv hW ih =>
    intro σ' h hσ hE
    rw [unifyW_var_left ht] at h; simp only [hv, hW, ↓reduceIte] at h
    have htv : ∀ w ∈ t.vars, w ∉ dom σ := fun w hw => hE w (mem_varsE_cons.mpr (.inr (.inl hw)))
    refine ih σ' h (idem_bindS hσ hW.2 hv htv) fun w hw => ?_
    rw [dom_bindS]; simp only [List.mem_cons, not_or]
    rcases mem_varsE_bindE hw with ⟨hw, hne⟩ | hw
    · exact ⟨hne, hE w (mem_varsE_cons.mpr (.inr (.inr hw)))⟩
    · exact ⟨fun h => hv (h ▸ hw), htv w hw⟩
  | case9 σ v t E ht hv hW => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv, hW] at h
  | case10 σ t v E ht hv => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv] at h
  | case11 σ t v E ht hv hW ih =>
    intro σ' h hσ hE
    rw [unifyW_var_right ht] at h; simp only [hv, hW, ↓reduceIte] at h
    have htv : ∀ w ∈ t.vars, w ∉ dom σ := fun w hw => hE w (mem_varsE_cons.mpr (.inl hw))
    refine ih σ' h (idem_bindS hσ hW.2 hv htv) fun w hw => ?_
    rw [dom_bindS]; simp only [List.mem_cons, not_or]
    rcases mem_varsE_bindE hw with ⟨hw, hne⟩ | hw
    · exact ⟨hne, hE w (mem_varsE_cons.mpr (.inr (.inr hw)))⟩
    · exact ⟨fun h => hv (h ▸ hw), htv w hw⟩
  | case12 σ t v E ht hv hW => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv, hW] at h
  | case13 => intro σ' h; rw [unifyW.eq_def] at h; cases h
  | case14 => intro σ' h; rw [unifyW.eq_def] at h; cases h

theorem unifyW_vars (W : List V) :
    ∀ σ E σ', unifyW W σ E = some σ' → ∀ w ∈ varsS σ', w ∈ varsS σ ∨ w ∈ varsE E := by
  intro σ E
  induction σ, E using unifyW.induct W with
  | case1 σ => intro σ' h w hw; rw [unifyW.eq_def] at h; cases h; exact .inl hw
  | case2 σ d E ih =>
    intro σ' h w hw
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    rcases ih σ' h w hw with h | h
    · exact .inl h
    · exact .inr (mem_varsE_cons.mpr (.inr (.inr h)))
  | case3 σ c d E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case4 σ a₁ a₂ d b₁ b₂ E ih =>
    intro σ' h w hw
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    rcases ih σ' h w hw with h | h
    · exact .inl h
    · refine .inr ?_
      simp only [mem_varsE_cons, Tm.vars, List.mem_append] at h ⊢
      rcases h with h | h | h | h | h <;> simp [h]
  | case5 σ c a₁ a₂ d b₁ b₂ E hcd => intro σ' h; rw [unifyW.eq_def] at h; simp [hcd] at h
  | case6 σ v E ih =>
    intro σ' h w hw
    rw [unifyW.eq_def] at h; simp only [↓reduceIte] at h
    rcases ih σ' h w hw with h | h
    · exact .inl h
    · exact .inr (mem_varsE_cons.mpr (.inr (.inr h)))
  | case7 σ v t E ht hv => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv] at h
  | case8 σ v t E ht hv hW ih =>
    intro σ' h w hw
    rw [unifyW_var_left ht] at h; simp only [hv, hW, ↓reduceIte] at h
    rcases ih σ' h w hw with h | h
    · rcases mem_varsS_bindS h with rfl | h | h
      · exact .inr (mem_varsE_cons.mpr (.inl (by simp [Tm.vars])))
      · exact .inr (mem_varsE_cons.mpr (.inr (.inl h)))
      · exact .inl h
    · rcases mem_varsE_bindE h with ⟨h, _⟩ | h
      · exact .inr (mem_varsE_cons.mpr (.inr (.inr h)))
      · exact .inr (mem_varsE_cons.mpr (.inr (.inl h)))
  | case9 σ v t E ht hv hW => intro σ' h; rw [unifyW_var_left ht] at h; simp [hv, hW] at h
  | case10 σ t v E ht hv => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv] at h
  | case11 σ t v E ht hv hW ih =>
    intro σ' h w hw
    rw [unifyW_var_right ht] at h; simp only [hv, hW, ↓reduceIte] at h
    rcases ih σ' h w hw with h | h
    · rcases mem_varsS_bindS h with rfl | h | h
      · exact .inr (mem_varsE_cons.mpr (.inr (.inl (by simp [Tm.vars]))))
      · exact .inr (mem_varsE_cons.mpr (.inl h))
      · exact .inl h
    · rcases mem_varsE_bindE h with ⟨h, _⟩ | h
      · exact .inr (mem_varsE_cons.mpr (.inr (.inr h)))
      · exact .inr (mem_varsE_cons.mpr (.inl h))
  | case12 σ t v E ht hv hW => intro σ' h; rw [unifyW_var_right ht] at h; simp [hv, hW] at h
  | case13 => intro σ' h; rw [unifyW.eq_def] at h; cases h
  | case14 => intro σ' h; rw [unifyW.eq_def] at h; cases h

/-! ## Lookup -/

theorem find_mem : ∀ {σ : Subst} {v : V} {t : Tm}, find σ v = some t → (v, t) ∈ σ
  | [], _, _, h => by cases h
  | (w, u) :: σ, v, t, h => by
    simp only [find] at h
    split at h
    · rename_i hw; cases h; subst hw; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (find_mem h)

theorem find_none : ∀ {σ : Subst} {v : V}, find σ v = none → v ∉ dom σ
  | [], _, _ => by simp [dom]
  | (w, u) :: σ, v, h => by
    simp only [find] at h
    split at h
    · cases h
    · rename_i hw
      simp only [dom, List.map_cons, List.mem_cons, not_or]
      exact ⟨fun e => hw e.symm, find_none h⟩

theorem find_of_mem : ∀ {σ : Subst} {v : V} {t : Tm}, Distinct σ → (v, t) ∈ σ → find σ v = some t
  | [], _, _, _, h => by cases h
  | (w, u) :: σ, v, t, hd, h => by
    simp only [find]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have hvw : w ≠ v := by
        rintro rfl
        exact hd.1 (List.mem_map.mpr ⟨(w, t), h, rfl⟩)
      simp only [hvw, ↓reduceIte]
      exact find_of_mem hd.2 h

theorem get_bind {θ : V → Tm} {σ : Subst} (hs : Sat θ σ) (v : V) : (get σ v).bind θ = θ v := by
  unfold get
  cases h : find σ v with
  | none => rfl
  | some t => exact (hs (v, t) (find_mem h)).symm

/-! ## The unifier on a substitution -/

def appE (σ : Subst) (E : List (Tm × Tm)) : List (Tm × Tm) :=
  E.map fun e => (app σ e.1, app σ e.2)

/-- Extend `σ` by a most general solution of `E`. -/
def unifyTop (σ : Subst) (E : List (Tm × Tm)) : Option Subst :=
  unifyW (varsE (appE σ E)) σ (appE σ E)

theorem app_bind {θ : V → Tm} {σ : Subst} (hs : Sat θ σ) (t : Tm) :
    (app σ t).bind θ = t.bind θ := by
  unfold app
  rw [Tm.bind_bind]
  exact Tm.bind_congr fun v _ => get_bind hs v

theorem satE_appE {θ : V → Tm} {σ : Subst} (hs : Sat θ σ) (E : List (Tm × Tm)) :
    SatE θ (appE σ E) ↔ SatE θ E := by
  constructor
  · intro h e he
    have := h _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    simpa [app_bind hs] using this
  · intro h e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp only [app_bind hs]
    exact h e' he'

theorem mem_vars_app {σ : Subst} {t : Tm} {w : V} (h : w ∈ (app σ t).vars) :
    (w ∈ t.vars ∧ w ∉ dom σ) ∨ ∃ p ∈ σ, w ∈ p.2.vars := by
  obtain ⟨u, hu, hw⟩ := Tm.mem_vars_bind h
  unfold get at hw
  cases hf : find σ u with
  | none =>
    rw [hf] at hw; simp [Tm.vars] at hw; subst hw
    exact .inl ⟨hu, find_none hf⟩
  | some r =>
    rw [hf] at hw
    exact .inr ⟨(u, r), find_mem hf, hw⟩

theorem mem_varsE_appE {σ : Subst} {E : List (Tm × Tm)} {w : V} (h : w ∈ varsE (appE σ E)) :
    (w ∈ varsE E ∧ w ∉ dom σ) ∨ ∃ p ∈ σ, w ∈ p.2.vars := by
  simp only [varsE, appE, List.flatMap_map, List.mem_flatMap, List.mem_append] at h
  obtain ⟨e, he, h | h⟩ := h
  · rcases mem_vars_app h with ⟨h, hd⟩ | h
    · exact .inl ⟨List.mem_flatMap.mpr ⟨e, he, List.mem_append_left _ h⟩, hd⟩
    · exact .inr h
  · rcases mem_vars_app h with ⟨h, hd⟩ | h
    · exact .inl ⟨List.mem_flatMap.mpr ⟨e, he, List.mem_append_right _ h⟩, hd⟩
    · exact .inr h

theorem unifyTop_sound {σ σ' : Subst} {E : List (Tm × Tm)} (h : unifyTop σ E = some σ')
    {θ : V → Tm} (hs : Sat θ σ') : Sat θ σ ∧ SatE θ E := by
  obtain ⟨h1, h2⟩ := unifyW_sound _ _ _ σ' h θ hs
  exact ⟨h1, (satE_appE h1 E).mp h2⟩

theorem unifyTop_complete {σ : Subst} {E : List (Tm × Tm)} (hσ : Idem σ) {θ : V → Tm}
    (hs : Sat θ σ) (hE : SatE θ E) : ∃ σ', unifyTop σ E = some σ' ∧ Sat θ σ' := by
  refine unifyW_complete _ θ σ _ hs ((satE_appE hs E).mpr hE) fun w hw => ⟨hw, ?_⟩
  rcases mem_varsE_appE hw with ⟨_, hd⟩ | ⟨p, hp, hw⟩
  · exact hd
  · exact hσ.range p hp w hw

theorem unifyTop_idem {σ σ' : Subst} {E : List (Tm × Tm)} (hσ : Idem σ)
    (h : unifyTop σ E = some σ') : Idem σ' := by
  refine unifyW_idem _ _ _ σ' h hσ fun w hw => ?_
  rcases mem_varsE_appE hw with ⟨_, hd⟩ | ⟨p, hp, hw⟩
  · exact hd
  · exact hσ.range p hp w hw

theorem unifyTop_vars {σ σ' : Subst} {E : List (Tm × Tm)} (h : unifyTop σ E = some σ')
    {w : V} (hw : w ∈ varsS σ') : w ∈ varsS σ ∨ w ∈ varsE E := by
  rcases unifyW_vars _ _ _ σ' h w hw with h | h
  · exact .inl h
  · rcases mem_varsE_appE h with ⟨h, _⟩ | ⟨p, hp, h⟩
    · exact .inr h
    · exact .inl (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ h⟩)

/-! ## A ground solution -/

/-- The solution of an idempotent substitution that sends free variables to
`leaf 0`. -/
def canon (σ : Subst) (v : V) : Tm := (get σ v).bind fun _ => .leaf 0

theorem canon_sat {σ : Subst} (hσ : Idem σ) : Sat (canon σ) σ := by
  intro p hp
  have hf := find_of_mem hσ.distinct hp
  simp only [canon, get, hf, Option.getD_some]
  apply Tm.bind_congr
  intro w hw
  have hn : find σ w = none := by
    cases h : find σ w with
    | none => rfl
    | some r => exact absurd (List.mem_map.mpr ⟨(w, r), find_mem h, rfl⟩) (hσ.range p hp w hw)
  simp [canon, get, hn, Tm.bind]

end Vsa.While.Unify
