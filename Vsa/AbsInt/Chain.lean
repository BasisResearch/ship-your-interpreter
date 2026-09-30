import Vsa.AbsInt.State

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

variable {A : Type} [AbsDom A]

theorem frameAt_iff {s : Store} {a : Addr} {P : Frame → Prop} :
    FrameAt s a P ↔ ∃ f, s.frames[a]? = some f ∧ P f := by
  unfold FrameAt
  cases s.frames[a]? <;> simp

theorem FrameAt.congr {s s' : Store} {a : Addr} {P : Frame → Prop}
    (h : s'.frames[a]? = s.frames[a]?) (hp : FrameAt s a P) : FrameAt s' a P := by
  unfold FrameAt at *
  rw [h]
  exact hp

theorem FrameAt.mono {s : Store} {a : Addr} {P Q : Frame → Prop}
    (h : ∀ f, P f → Q f) (hp : FrameAt s a P) : FrameAt s a Q := by
  unfold FrameAt at *
  cases hf : s.frames[a]? with
  | none => rw [hf] at hp; exact hp
  | some f => rw [hf] at hp; exact h f hp

theorem FrameAt.lt_size {s : Store} {a : Addr} {P : Frame → Prop}
    (hp : FrameAt s a P) : a < s.frames.size := by
  obtain ⟨f, hf, _⟩ := frameAt_iff.mp hp
  exact (Array.getElem?_eq_some_iff.mp hf).1

omit [AbsDom A] in
theorem Scope.get_cons (k : String) (b : Bind A) (S : Scope A) (y : String) :
    Scope.get ((k, b) :: S) y = if k = y then some b else S.get y := rfl

theorem ScopeOK.update {S : Scope A} {vars vars' : List (String × Value)}
    {x : String} {b : Bind A} (hb : BindOK (some b) (vfind vars' x))
    (hS : ScopeOK S vars) (hrest : ∀ y, x ≠ y → vfind vars' y = vfind vars y) :
    ScopeOK ((x, b) :: S) vars' := by
  intro y
  rw [Scope.get_cons]
  by_cases hxy : x = y
  · subst hxy
    simpa using hb
  · simp only [hxy, ↓reduceIte, hrest y hxy]
    exact hS y

theorem ScopeOK.nil : ScopeOK ([] : Scope A) [] := by
  intro y
  rfl

theorem get_eq_none_of_not_mem {S : Scope A} {y : String} (h : y ∉ keys S) :
    S.get y = none := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    obtain ⟨k, b⟩ := p
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    rw [Scope.get_cons, if_neg (Ne.symm h.1)]
    exact ih h.2

theorem mem_dedup {x : String} : ∀ {l : List String}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: ys => by
    unfold dedup
    have ih := @mem_dedup x ys
    split
    · rename_i h
      rw [ih]
      constructor
      · exact List.mem_cons_of_mem y
      · intro hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ih.mp h
        · exact hm
    · simp [ih]

theorem build_get (ks : List String) (g : String → Option (Bind A)) (y : String) :
    (build ks g).get y = if y ∈ ks then g y else none := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    unfold build
    rw [List.filterMap_cons]
    cases hk : g k with
    | none =>
      simp only [Option.map_none]
      rw [show List.filterMap (fun x => (g x).map fun b => (x, b)) ks = build ks g from rfl, ih]
      by_cases hyk : y = k
      · subst hyk; simp [hk]
      · simp [hyk]
    | some b =>
      simp only [Option.map_some]
      rw [Scope.get_cons,
        show List.filterMap (fun x => (g x).map fun b => (x, b)) ks = build ks g from rfl, ih]
      by_cases hyk : k = y
      · subst hyk; simp [hk]
      · simp [hyk, Ne.symm hyk]

theorem zipScope_get (op : A → A → A) (S T : Scope A) (y : String) :
    (zipScope op S T).get y = combB op (S.get y) (T.get y) := by
  unfold zipScope
  rw [build_get]
  split
  · rfl
  · rename_i h
    rw [mem_dedup, List.mem_append, not_or] at h
    rw [get_eq_none_of_not_mem h.1, get_eq_none_of_not_mem h.2]
    rfl

theorem leScope_get {S T : Scope A} (h : leScope S T = true) (y : String) :
    leB (S.get y) (T.get y) = true := by
  unfold leScope at h
  rw [List.all_eq_true] at h
  by_cases hy : y ∈ keys S ++ keys T
  · exact h y hy
  · rw [List.mem_append, not_or] at hy
    rw [get_eq_none_of_not_mem hy.1, get_eq_none_of_not_mem hy.2]
    rfl

theorem BindOK.combB_l {op : A → A → A} (hop : ∀ {a b v}, Gam a v → Gam (op a b) v)
    {b c : Option (Bind A)} {o : Option Value} (h : BindOK b o) :
    BindOK (combB op b c) o := by
  cases b with
  | none =>
    cases c with
    | none => exact h
    | some c =>
      simp only [BindOK] at h
      subst h
      simp [combB, BindOK]
  | some b =>
    cases c with
    | none => exact ⟨by simp, h.2⟩
    | some c =>
      refine ⟨fun hm => h.1 (by simp at hm; exact hm.1), fun v hv => hop (h.2 v hv)⟩

theorem BindOK.combB_r {op : A → A → A} (hop : ∀ {a b v}, Gam b v → Gam (op a b) v)
    {b c : Option (Bind A)} {o : Option Value} (h : BindOK c o) :
    BindOK (combB op b c) o := by
  cases c with
  | none =>
    cases b with
    | none => exact h
    | some b =>
      simp only [BindOK] at h
      subst h
      simp [combB, BindOK]
  | some c =>
    cases b with
    | none => exact ⟨by simp, h.2⟩
    | some b =>
      refine ⟨fun hm => h.1 (by simp at hm; exact hm.2), fun v hv => hop (h.2 v hv)⟩

theorem BindOK.leB {b c : Option (Bind A)} {o : Option Value}
    (hle : leB b c = true) (h : BindOK b o) : BindOK c o := by
  cases b with
  | none =>
    cases c with
    | none => exact h
    | some c =>
      simp only [BindOK] at h
      subst h
      simp only [AbsInt.leB, Bool.not_eq_eq_eq_not, Bool.not_true] at hle
      exact ⟨by simp [hle], by simp⟩
  | some b =>
    cases c with
    | none => simp [AbsInt.leB] at hle
    | some c =>
      simp only [AbsInt.leB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hle
      refine ⟨fun hm => h.1 ?_, fun v hv => le_sound hle.1 (h.2 v hv)⟩
      rcases hle.2 with h' | h'
      · rw [h'] at hm; cases hm
      · exact h'

def ScopeImp (S T : Scope A) : Prop := ∀ vars, ScopeOK S vars → ScopeOK T vars

theorem Chain.bounds {s : Store} :
    ∀ {as : List Addr} {a : Addr} {l : List (Scope A)}, Chain s (a :: as) l →
      a < s.frames.size ∧ as.length ≤ a ∧ ∀ i ∈ as, i < a
  | [], a, l, h => by
    cases l with
    | nil => simp [Chain] at h
    | cons S l => exact ⟨h.1.lt_size, by simp, by simp⟩
  | b :: as, a, l, h => by
    cases l with
    | nil => simp [Chain] at h
    | cons S l =>
      obtain ⟨hf, hlt, hc⟩ := h
      have hba : b < a := hlt b rfl
      obtain ⟨_, hlen, hmem⟩ := Chain.bounds hc
      refine ⟨hf.lt_size, by simp only [List.length_cons]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hlen hba), ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hba
      · exact Nat.lt_trans (hmem i hi) hba

theorem Chain.congr {s s' : Store} :
    ∀ {as : List Addr} {l : List (Scope A)},
      (∀ i ∈ as, s'.frames[i]? = s.frames[i]?) → Chain s as l → Chain s' as l
  | [], l, _, h => by
    cases l with
    | nil => trivial
    | cons _ _ => exact h.elim
  | a :: as, l, hs, h => by
    cases l with
    | nil => exact h
    | cons S l =>
      obtain ⟨hf, hlt, hc⟩ := h
      exact ⟨hf.congr (hs a (by simp)), hlt,
        Chain.congr (fun i hi => hs i (List.mem_cons_of_mem a hi)) hc⟩

theorem Chain.congr_le {s s' : Store} {a : Addr} {as : List Addr}
    {l : List (Scope A)} (hs : ∀ i, i ≤ a → s'.frames[i]? = s.frames[i]?)
    (h : Chain s (a :: as) l) : Chain s' (a :: as) l := by
  have hb := Chain.bounds h
  apply Chain.congr _ h
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact hs i (Nat.le_refl _)
  · exact hs i (Nat.le_of_lt (hb.2.2 i hi))

theorem Chain.mono {s : Store} :
    ∀ {as : List Addr} {l m : List (Scope A)}, Pw ScopeImp l m →
      Chain s as l → Chain s as m
  | [], [], [], _, h => h
  | [], [], _ :: _, hp, _ => by simp [Pw] at hp
  | [], _ :: _, _, _, h => by simp [Chain] at h
  | _ :: _, [], _, _, h => by simp [Chain] at h
  | a :: as, S :: l, [], hp, _ => by simp [Pw] at hp
  | a :: as, S :: l, T :: m, hp, h => by
    obtain ⟨hf, hlt, hc⟩ := h
    exact ⟨hf.mono (fun f hf' => ⟨hf'.1, hp.1 _ hf'.2⟩), hlt, Chain.mono hp.2 hc⟩

theorem pw_zipWith_l {f : Scope A → Scope A → Scope A} (hf : ∀ S T, ScopeImp S (f S T)) :
    ∀ {l m : List (Scope A)}, l.length = m.length → Pw ScopeImp l (List.zipWith f l m)
  | [], [], _ => trivial
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | S :: l, T :: m, h => ⟨hf S T, pw_zipWith_l hf (by simpa using h)⟩

theorem pw_zipWith_r {f : Scope A → Scope A → Scope A} (hf : ∀ S T, ScopeImp T (f S T)) :
    ∀ {l m : List (Scope A)}, l.length = m.length → Pw ScopeImp m (List.zipWith f l m)
  | [], [], _ => trivial
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | S :: l, T :: m, h => ⟨hf S T, pw_zipWith_r hf (by simpa using h)⟩

theorem pw_leScope :
    ∀ {l m : List (Scope A)}, l.length = m.length →
      (List.zipWith leScope l m).all id = true → Pw ScopeImp l m
  | [], [], _, _ => trivial
  | _ :: _, [], h, _ => by simp at h
  | [], _ :: _, h, _ => by simp at h
  | S :: l, T :: m, h, hall => by
    simp only [List.zipWith_cons_cons, List.all_cons, id, Bool.and_eq_true] at hall
    refine ⟨fun vars hS y => BindOK.leB (leScope_get hall.1 y) (hS y),
      pw_leScope (by simpa using h) hall.2⟩

theorem SGam.comb_l {op : A → A → A} (hop : ∀ {a b v}, Gam a v → Gam (op a b) v)
    {as : List Addr} {s : Store} {σ : AState A} (τ : AState A) (h : SGam as s σ) :
    SGam as s (σ.comb op τ) := by
  cases σ with
  | bot => exact h.elim
  | top => cases τ <;> trivial
  | sc l =>
    cases τ with
    | bot => exact h
    | top => trivial
    | sc m =>
      simp only [AState.comb]
      split
      · rename_i hlen
        exact Chain.mono (pw_zipWith_l (fun S T vars hS y => by
          rw [zipScope_get]; exact BindOK.combB_l hop (hS y)) hlen) h
      · trivial

theorem SGam.comb_r {op : A → A → A} (hop : ∀ {a b v}, Gam b v → Gam (op a b) v)
    {as : List Addr} {s : Store} {τ : AState A} (σ : AState A) (h : SGam as s τ) :
    SGam as s (σ.comb op τ) := by
  cases τ with
  | bot => exact h.elim
  | top => cases σ <;> trivial
  | sc m =>
    cases σ with
    | bot => exact h
    | top => trivial
    | sc l =>
      simp only [AState.comb]
      split
      · rename_i hlen
        exact Chain.mono (pw_zipWith_r (fun S T vars hS y => by
          rw [zipScope_get]; exact BindOK.combB_r hop (hS y)) hlen) h
      · trivial

theorem SGam.join_l {as : List Addr} {s : Store} {σ : AState A} (τ : AState A)
    (h : SGam as s σ) : SGam as s (σ.join τ) := SGam.comb_l AbsDom.join_l τ h

theorem SGam.join_r {as : List Addr} {s : Store} {τ : AState A} (σ : AState A)
    (h : SGam as s τ) : SGam as s (σ.join τ) := SGam.comb_r AbsDom.join_r σ h

theorem SGam.widen_l {as : List Addr} {s : Store} {σ : AState A} (τ : AState A)
    (h : SGam as s σ) : SGam as s (σ.widen τ) := SGam.comb_l AbsDom.widen_l τ h

theorem SGam.widen_r {as : List Addr} {s : Store} {τ : AState A} (σ : AState A)
    (h : SGam as s τ) : SGam as s (σ.widen τ) := SGam.comb_r AbsDom.widen_r σ h

theorem SGam.le {as : List Addr} {s : Store} {σ τ : AState A}
    (hle : σ.le τ = true) (h : SGam as s σ) : SGam as s τ := by
  cases σ with
  | bot => exact h.elim
  | top => cases τ <;> first | trivial | simp [AState.le] at hle
  | sc l =>
    cases τ with
    | bot => simp [AState.le] at hle
    | top => trivial
    | sc m =>
      simp only [AState.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact Chain.mono (pw_leScope hle.1 hle.2) h

theorem OptGam.joinOpt_l {a : A} {o : Option A} {v : Value} (h : Gam a v) :
    OptGam (joinOpt (some a) o) v := by
  cases o with
  | none => exact h
  | some b => exact AbsDom.join_l h

theorem OptGam.joinOpt_r {p o : Option A} {v : Value} (h : OptGam o v) :
    OptGam (joinOpt p o) v := by
  cases p with
  | none => exact h
  | some a =>
    cases o with
    | none => exact h.elim
    | some b => exact AbsDom.join_r h

theorem lookupL_sound {s : Store} {x : String} :
    ∀ {as : List Addr} {l : List (Scope A)} {a : Addr} {g : Nat},
      Chain s (a :: as) l → as.length < g →
      (∀ v, s.lookup g a x = some v → OptGam (lookupL x l).1 v) ∧
        (s.lookup g a x = none → (lookupL x l).2 = true)
  | as, [], a, g, h, _ => h.elim
  | as, S :: l, a, 0, _, hg => absurd hg (Nat.not_lt_zero _)
  | as, S :: l, a, g + 1, h, hg => by
    obtain ⟨hf, hlt, hc⟩ := h
    obtain ⟨f, hfa, hpar, hS⟩ := frameAt_iff.mp hf
    have hx := hS x
    rw [lookup_succ, hfa]

    have hcont : (∀ v, (match f.parent with
          | some p => s.lookup g p x
          | none => none) = some v → OptGam (lookupL x l).1 v) ∧
        ((match f.parent with
          | some p => s.lookup g p x
          | none => none) = none → (lookupL x l).2 = true) := by
      rw [hpar]
      cases as with
      | nil =>
        cases l with
        | nil => exact ⟨fun v hv => (by simp at hv), fun _ => rfl⟩
        | cons _ _ => exact hc.elim
      | cons b as =>
        exact lookupL_sound hc (by simp at hg ⊢; omega)
    simp only [lookupL]
    cases hb : S.get x with
    | none =>
      rw [hb] at hx
      simp only [BindOK] at hx
      simp only [hx]
      exact hcont
    | some bd =>
      rw [hb] at hx
      dsimp only
      by_cases hm : bd.must = true
      · rw [if_pos hm]
        have hsome := hx.1 hm
        cases hv : vfind f.vars x with
        | none => rw [hv] at hsome; cases hsome
        | some w =>
          exact ⟨fun v h => by cases h; exact hx.2 _ hv, fun h => by cases h⟩
      · rw [if_neg hm]
        cases hv : vfind f.vars x with
        | none =>
          exact ⟨fun v h => OptGam.joinOpt_r (hcont.1 v h), hcont.2⟩
        | some w =>
          exact ⟨fun v h => by
            cases h; exact OptGam.joinOpt_l (hx.2 _ hv), fun h => by cases h⟩

theorem SGam.lookup {as : List Addr} {env : Addr} {s : Store} {σ : AState A}
    {x : String} (hd : as.head? = some env) (h : SGam as s σ) :
    (∀ v, s.get? env x = some v → Gam (σ.lookup x).1 v) ∧
      (s.get? env x = none → (σ.lookup x).2 = true) := by
  cases σ with
  | bot => exact h.elim
  | top => exact ⟨fun _ _ => AbsDom.top_sound, fun _ => rfl⟩
  | sc l =>
    cases as with
    | nil => cases hd
    | cons e as =>
      cases hd
      have hb := Chain.bounds h
      have hsz : as.length < s.frames.size := Nat.lt_of_le_of_lt hb.2.1 hb.1
      obtain ⟨h1, h2⟩ := lookupL_sound (x := x) h hsz
      refine ⟨fun v hv => ?_, h2⟩
      have := h1 v hv
      simp only [AState.lookup]
      cases hr : (lookupL x l).1 with
      | none => rw [hr] at this; exact this.elim
      | some a => rw [hr] at this; exact this

theorem SGam.define {as : List Addr} {env : Addr} {s : Store} {σ : AState A}
    {x : String} {a : A} {v : Value} (hd : as.head? = some env)
    (h : SGam as s σ) (hv : Gam a v) : SGam as (s.define env x v) (σ.define x a) := by
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l =>
    cases as with
    | nil => cases hd
    | cons e as =>
      cases hd
      cases l with
      | nil => exact h.elim
      | cons S l =>
        have hb := Chain.bounds h
        obtain ⟨hf, hlt, hc⟩ := h
        obtain ⟨f, hfa, hpar, hS⟩ := frameAt_iff.mp hf
        refine ⟨?_, hlt, Chain.congr (fun i hi => ?_) hc⟩
        · rw [frameAt_iff]
          refine ⟨{ f with vars := defineVars f.vars x v }, ?_, hpar, ?_⟩
          · rw [define_frames, if_pos rfl, hfa]
            rfl
          · refine ScopeOK.update ?_ hS (fun y hxy => by
              rw [vfind_defineVars, if_neg hxy])
            rw [vfind_defineVars, if_pos rfl]
            exact ⟨fun _ => rfl, fun w hw => by cases hw; exact hv⟩
        · rw [define_frames, if_neg (Nat.ne_of_gt (hb.2.2 i hi))]

theorem set_succ (s : Store) (g : Nat) (a : Addr) (x : String) (v : Value) :
    s.set (g + 1) a x v =
      match s.frames[a]? with
      | none => none
      | some f =>
        if f.vars.any (·.1 == x) then
          some { s with frames := s.frames.modify a fun f =>
            { f with vars := setVars f.vars x v } }
        else match f.parent with
          | some p => s.set g p x v
          | none => none := by
  rw [Store.set]
  cases s.frames[a]? with
  | none => rfl
  | some f => rfl

theorem assignL_weak {s : Store} {x : String} {a : A} :
    ∀ {as : List Addr} {l : List (Scope A)}, Chain s as l →
      Chain s as (assignL x a true l).1
  | [], [], h => h
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | e :: as, S :: l, h => by
    obtain ⟨hf, hlt, hc⟩ := h
    simp only [assignL]
    cases hb : S.get x with
    | none => exact ⟨hf, hlt, assignL_weak hc⟩
    | some bd =>
      have upd : ∀ (m : Bool), bd.must = true ∨ m = false →
          FrameAt s e (fun f => f.parent = as.head? ∧
            ScopeOK ((x, (⟨join bd.val a, m⟩ : Bind A)) :: S) f.vars) := by
        intro m hm
        refine hf.mono (fun f hf' => ⟨hf'.1, ScopeOK.update ?_ hf'.2 (fun _ _ => rfl)⟩)
        have hx := hf'.2 x
        rw [hb] at hx
        refine ⟨fun hm' => hx.1 ?_, fun w hw => AbsDom.join_l (hx.2 w hw)⟩
        rcases hm with hm | hm
        · exact hm
        · rw [hm] at hm'; cases hm'
      dsimp only
      by_cases hm : bd.must = true
      · rw [if_pos hm]
        exact ⟨upd true (Or.inl hm), hlt, hc⟩
      · rw [if_neg hm]
        exact ⟨upd false (Or.inr rfl), hlt, assignL_weak hc⟩

theorem assignL_set {x : String} {av : A} {v : Value} (hv : Gam av v) :
    ∀ {as : List Addr} {l : List (Scope A)} {a : Addr} {g : Nat} {weak : Bool}
      {s s' : Store}, s.set g a x v = some s' → Chain s (a :: as) l →
      Chain s' (a :: as) (assignL x av weak l).1 ∧
        ∀ i, a < i → s'.frames[i]? = s.frames[i]?
  | _, [], _, _, _, _, _, _, h => h.elim
  | _, _ :: _, _, 0, _, _, _, hset, _ => by simp [Store.set] at hset
  | as, S :: l, a, g + 1, weak, s, s', hset, h => by
    have hbd := Chain.bounds h
    obtain ⟨hf, hlt, hc⟩ := h
    obtain ⟨f, hfa, hpar, hS⟩ := frameAt_iff.mp hf
    have hx := hS x
    rw [set_succ, hfa] at hset
    simp only at hset
    by_cases hany : f.vars.any (·.1 == x) = true
    ·
      rw [if_pos hany] at hset
      cases hset
      have hfr : ∀ i, (s.frames.modify a fun f =>
          { f with vars := setVars f.vars x v })[i]? =
          if a = i then (s.frames[i]?).map (fun f => { f with vars := setVars f.vars x v })
          else s.frames[i]? := fun i => Array.getElem?_modify
      have hhead : ∀ (b : Bind A), b.must = true → (∀ w, w = v → Gam b.val w) →
          FrameAt { s with frames := s.frames.modify a fun f =>
            { f with vars := setVars f.vars x v } } a
            (fun f => f.parent = as.head? ∧ ScopeOK ((x, b) :: S) f.vars) := by
        intro b hbm hbv
        rw [frameAt_iff]
        refine ⟨{ f with vars := setVars f.vars x v }, ?_, hpar, ?_⟩
        · simp only [hfr, hfa]
          rfl
        · refine ScopeOK.update ?_ hS (fun y hxy => by rw [vfind_setVars hany, if_neg hxy])
          rw [vfind_setVars hany, if_pos rfl]
          exact ⟨fun _ => rfl, fun w hw => hbv w (by cases hw; rfl)⟩
      have hrest : ∀ i ∈ as, ({ s with frames := s.frames.modify a fun f =>
          { f with vars := setVars f.vars x v } } : Store).frames[i]? = s.frames[i]? := by
        intro i hi
        simp only [hfr, if_neg (Nat.ne_of_gt (hbd.2.2 i hi))]
      refine ⟨?_, fun i hi => by simp only [hfr, if_neg (Nat.ne_of_lt hi)]⟩
      simp only [assignL]
      cases hb : S.get x with
      | none =>
        rw [hb] at hx
        have := vfind_isSome_of_any hany
        simp only [BindOK] at hx
        rw [hx] at this
        cases this
      | some bd =>
        rw [hb] at hx
        dsimp only
        by_cases hm : bd.must = true
        · rw [if_pos hm]
          refine ⟨hhead _ rfl (fun w hw => ?_), hlt, Chain.congr hrest hc⟩
          subst hw
          cases weak
          · exact hv
          · exact AbsDom.join_r hv
        · rw [if_neg hm]
          refine ⟨?_, hlt, Chain.congr hrest (assignL_weak hc)⟩

          rw [frameAt_iff]
          refine ⟨{ f with vars := setVars f.vars x v }, ?_, hpar, ?_⟩
          · simp only [hfr, hfa]
            rfl
          · refine ScopeOK.update ?_ hS (fun y hxy => by rw [vfind_setVars hany, if_neg hxy])
            rw [vfind_setVars hany, if_pos rfl]
            exact ⟨fun h => (by cases h), fun w hw => by cases hw; exact AbsDom.join_r hv⟩
    ·
      have hnone : vfind f.vars x = none :=
        vfind_none_of_not_any (Bool.eq_false_iff.mpr hany)
      rw [if_neg hany, hpar] at hset
      cases as with
      | nil => cases hset
      | cons p as =>
        simp only [List.head?_cons] at hset
        have hpa : p < a := hlt p rfl
        cases l with
        | nil => exact hc.elim
        | cons T l =>
        have hkeep : ∀ (weak' : Bool),
            Chain s' (p :: as) (assignL x av weak' (T :: l)).1 ∧
              ∀ i, p < i → s'.frames[i]? = s.frames[i]? :=
          fun weak' => assignL_set hv hset hc
        have hfa' : s'.frames[a]? = s.frames[a]? := (hkeep false).2 a hpa
        refine ⟨?_, fun i hi => (hkeep false).2 i (Nat.lt_trans hpa hi)⟩
        simp only [assignL]
        cases hb : S.get x with
        | none =>
          exact ⟨hf.congr hfa', hlt, (hkeep weak).1⟩
        | some bd =>
          rw [hb, hnone] at hx
          dsimp only
          by_cases hm : bd.must = true
          · have := hx.1 hm
            simp at this
          · rw [if_neg hm]
            refine ⟨?_, hlt, (hkeep true).1⟩
            refine (hf.mono (fun f' hf' => ⟨hf'.1, ScopeOK.update ?_ hf'.2 (fun _ _ => rfl)⟩)).congr hfa'
            have hy := hf'.2 x
            rw [hb] at hy
            exact ⟨fun h => (by cases h), fun w hw => AbsDom.join_l (hy.2 w hw)⟩

theorem assignL_none {x : String} {av : A} {v : Value} {s : Store} :
    ∀ {as : List Addr} {l : List (Scope A)} {a : Addr} {g : Nat} {weak : Bool},
      s.set g a x v = none → Chain s (a :: as) l → as.length < g →
      (assignL x av weak l).2 = true
  | _, [], _, _, _, _, h, _ => h.elim
  | _, _ :: _, _, 0, _, _, _, hg => absurd hg (Nat.not_lt_zero _)
  | as, S :: l, a, g + 1, weak, hset, h, hg => by
    obtain ⟨hf, hlt, hc⟩ := h
    obtain ⟨f, hfa, hpar, hS⟩ := frameAt_iff.mp hf
    have hx := hS x
    rw [set_succ, hfa] at hset
    simp only at hset
    by_cases hany : f.vars.any (·.1 == x) = true
    · rw [if_pos hany] at hset
      cases hset
    · have hnone : vfind f.vars x = none :=
        vfind_none_of_not_any (Bool.eq_false_iff.mpr hany)
      rw [if_neg hany, hpar] at hset

      have hrest : ∀ weak', (assignL x av weak' l).2 = true := by
        intro weak'
        cases as with
        | nil =>
          cases l with
          | nil => rfl
          | cons _ _ => exact hc.elim
        | cons p as =>
          exact assignL_none hset hc (by simp at hg ⊢; omega)
      simp only [assignL]
      cases hb : S.get x with
      | none => exact hrest weak
      | some bd =>
        rw [hb, hnone] at hx
        dsimp only
        by_cases hm : bd.must = true
        · have := hx.1 hm
          simp at this
        · rw [if_neg hm]
          exact hrest true

theorem SGam.assign {as : List Addr} {env : Addr} {s : Store} {σ : AState A}
    {x : String} {a : A} {v : Value} (hd : as.head? = some env)
    (h : SGam as s σ) (hv : Gam a v) :
    (∀ s', s.set? env x v = some s' → SGam as s' (σ.assign x a).1) ∧
      (s.set? env x v = none → (σ.assign x a).2 = true) := by
  cases σ with
  | bot => exact h.elim
  | top => exact ⟨fun _ _ => trivial, fun _ => rfl⟩
  | sc l =>
    cases as with
    | nil => cases hd
    | cons e as =>
      cases hd
      have hb := Chain.bounds h
      refine ⟨fun s' hs => (assignL_set hv hs h).1, fun hs => assignL_none hs h ?_⟩
      exact Nat.lt_of_le_of_lt hb.2.1 hb.1

theorem strengthenL_sound {s : Store} {x : String} {av : A} {w : Value} :
    ∀ {as : List Addr} {l : List (Scope A)} {a : Addr} {g : Nat},
      Chain s (a :: as) l → s.lookup g a x = some w → Gam av w →
      Chain s (a :: as) (strengthenL x av l)
  | _, [], _, _, h, _, _ => h.elim
  | _, _ :: _, _, 0, _, hl, _ => by simp [Store.lookup] at hl
  | as, S :: l, a, g + 1, h, hl, hw => by
    obtain ⟨hf, hlt, hc⟩ := h
    obtain ⟨f, hfa, hpar, hS⟩ := frameAt_iff.mp hf
    have hx := hS x
    rw [lookup_succ, hfa] at hl
    simp only at hl
    simp only [strengthenL]
    cases hb : S.get x with
    | none =>
      rw [hb] at hx
      simp only [BindOK] at hx
      rw [hx, hpar] at hl
      refine ⟨hf, hlt, ?_⟩
      cases as with
      | nil => cases hl
      | cons p as => exact strengthenL_sound hc hl hw
    | some bd =>
      rw [hb] at hx
      dsimp only
      by_cases hm : bd.must = true
      · rw [if_pos hm]
        have hsome := hx.1 hm
        cases hv : vfind f.vars x with
        | none => rw [hv] at hsome; cases hsome
        | some w' =>
          rw [hv] at hl
          cases hl
          refine ⟨?_, hlt, hc⟩
          rw [frameAt_iff]
          refine ⟨f, hfa, hpar, ScopeOK.update ?_ hS (fun _ _ => rfl)⟩
          rw [hv]
          exact ⟨fun _ => rfl, fun u hu => by cases hu; exact hw⟩
      · rw [if_neg hm]
        exact ⟨hf, hlt, hc⟩

theorem SGam.strengthen {as : List Addr} {env : Addr} {s : Store} {σ : AState A}
    {x : String} {av : A} {w : Value} (hd : as.head? = some env)
    (h : SGam as s σ) (hl : s.get? env x = some w) (hw : Gam av w) :
    SGam as s (σ.strengthen x av) := by
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l =>
    cases as with
    | nil => cases hd
    | cons e as =>
      cases hd
      exact strengthenL_sound h hl hw

theorem SGam.push {as : List Addr} {env : Addr} {s s' : Store} {inner : Addr}
    {σ : AState A} (hd : as.head? = some env) (h : SGam as s σ)
    (halloc : s.allocFrame (some env) = (s', inner)) :
    SGam (inner :: as) s' σ.push := by
  simp only [Store.allocFrame, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l =>
    cases as with
    | nil => cases hd
    | cons e as =>
      cases hd
      have hb := Chain.bounds h
      refine ⟨?_, fun b hb' => by cases hb'; exact hb.1, Chain.congr (fun i hi => ?_) h⟩
      · rw [frameAt_iff]
        refine ⟨⟨some _, []⟩, ?_, rfl, ScopeOK.nil⟩
        simp [Array.getElem?_push]
      · have hi' : i < s.frames.size := by
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hb.1
          · exact Nat.lt_trans (hb.2.2 i hi) hb.1
        simp [Array.getElem?_push, Nat.ne_of_lt hi']

theorem SGam.pop {as : List Addr} {inner : Addr} {s : Store} {σ : AState A}
    (h : SGam (inner :: as) s σ) : SGam as s σ.pop := by
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l =>
    cases l with
    | nil => exact h.elim
    | cons S l => exact h.2.2

theorem SGam.frames_eq {as : List Addr} {s s' : Store} {σ : AState A}
    (hfr : s'.frames = s.frames) (h : SGam as s σ) : SGam as s' σ := by
  cases σ with
  | bot => exact h.elim
  | top => trivial
  | sc l => exact Chain.congr (fun i _ => by rw [hfr]) h

end Vsa.AbsInt
