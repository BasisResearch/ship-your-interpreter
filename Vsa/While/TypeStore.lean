import Vsa.While.Types

/-!
# Store lemmas for type soundness

Store growth (`Ext`), typed lookup, allocation, definition, assignment and
parameter binding, each preserving `StoreOK`.
-/

namespace Vsa.While.Types

open Vsa.While

/-! ## Store growth -/

theorem Ext.refl (s : Store) : Ext s s :=
  ⟨Nat.le_refl _, fun _ f h => ⟨f, h, rfl, fun _ hx => hx⟩, fun _ _ h => h⟩

theorem Ext.trans {s₁ s₂ s₃ : Store} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ := by
  refine ⟨Nat.le_trans h₁.size_le h₂.size_le, ?_, fun a cd h => h₂.closures a cd (h₁.closures a cd h)⟩
  intro a f hf
  obtain ⟨f₂, hf₂, hp₂, hn₂⟩ := h₁.frames a f hf
  obtain ⟨f₃, hf₃, hp₃, hn₃⟩ := h₂.frames a f₂ hf₂
  exact ⟨f₃, hf₃, hp₃.trans hp₂, fun x hx => hn₃ x (hn₂ x hx)⟩

theorem find?_isSome_of_any {vars : List (String × Value)} {x : String}
    (h : vars.any (·.1 == x) = true) : ∃ p, vars.find? (·.1 == x) = some p := by
  cases hf : vars.find? (·.1 == x) with
  | some p => exact ⟨p, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp h
    exact absurd hqx (hf q hq)

theorem any_of_find? {vars : List (String × Value)} {x : String} {p : String × Value}
    (h : vars.find? (·.1 == x) = some p) : vars.any (·.1 == x) = true :=
  List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some h, List.find?_some (p := fun (q : String × Value) => q.1 == x) h⟩

/-- Unfolding one step of `Store.lookup`. -/
theorem lookup_succ (s : Store) (g : Nat) (a : Addr) (x : String) :
    s.lookup (g + 1) a x =
      match s.frames[a]? with
      | none => none
      | some f => match f.vars.find? (·.1 == x) with
        | some (_, v) => some v
        | none => match f.parent with
          | some p => s.lookup g p x
          | none => none := by
  simp only [Store.lookup]
  cases s.frames[a]? <;> rfl

theorem lookup_ext {s s' : Store} (hE : Ext s s') (x : String) :
    ∀ g a v g', s.lookup g a x = some v → g ≤ g' → ∃ v', s'.lookup g' a x = some v' := by
  intro g
  induction g with
  | zero => intro a v g' h; simp [Store.lookup] at h
  | succ g ih =>
    intro a v g' h hg
    obtain ⟨g'', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    rw [lookup_succ] at h ⊢
    cases hf : s.frames[a]? with
    | none => simp [hf] at h
    | some f =>
      obtain ⟨f', hf', hpar, hnames⟩ := hE.frames a f hf
      rw [hf] at h
      dsimp only at h
      rw [hf']
      dsimp only at h ⊢
      cases hfind : f.vars.find? (·.1 == x) with
      | some p =>
        obtain ⟨q, hq⟩ := find?_isSome_of_any (hnames x (any_of_find? hfind))
        rw [hq]
        exact ⟨q.2, rfl⟩
      | none =>
        rw [hfind] at h
        cases hfind' : f'.vars.find? (·.1 == x) with
        | some q => exact ⟨q.2, rfl⟩
        | none =>
          simp only [hpar]
          cases hp : f.parent with
          | none => simp [hp] at h
          | some p =>
            simp only [hp] at h
            exact ih p v g'' h (by omega)

theorem Defined.ext {s s' : Store} {a : Addr} {x : String} (h : Defined s a x)
    (hE : Ext s s') : Defined s' a x := by
  obtain ⟨v, hv⟩ := h
  exact lookup_ext hE x _ a v _ hv hE.size_le

theorem DefAll.ext {s s' : Store} {a : Addr} {S : List String} (h : DefAll s a S)
    (hE : Ext s s') : DefAll s' a S :=
  fun x hx => (h x hx).ext hE

theorem ValTy.ext {Δ : TyEnv} {s s' : Store} {v : Value} {t : Ty} (h : ValTy Δ s v t)
    (hE : Ext s s') : ValTy Δ s' v t := by
  cases h with
  | null => exact .null
  | bool b => exact .bool b
  | int n => exact .int n
  | str x => exact .str x
  | native f => exact .native f
  | closure a cd S S' r hcd hb hr hd =>
    exact .closure a cd S S' r (hE.closures a cd hcd) hb hr (hd.ext hE)

theorem ValTys.ext {Δ : TyEnv} {s s' : Store} {vs : List Value} {ts : List Ty}
    (h : ValTys Δ s vs ts) (hE : Ext s s') : ValTys Δ s' vs ts := by
  induction h with
  | nil => exact .nil
  | cons v vs t ts hv _ ih => exact .cons v vs t ts (hv.ext hE) ih

theorem StatusOK.ext {Δ : TyEnv} {s s' : Store} {R : Option Ty} {L : Bool}
    {st : Status} (h : StatusOK Δ s R L st) (hE : Ext s s') : StatusOK Δ s' R L st := by
  cases st with
  | normal => trivial
  | brk => exact h
  | cont => exact h
  | ret v =>
    obtain ⟨t, hR, hv⟩ := h
    exact ⟨t, hR, hv.ext hE⟩

/-- A found binding has its name's type. -/
theorem lookup_typed {Δ : TyEnv} {s : Store} (hS : StoreOK Δ s) (x : String) :
    ∀ g a v, s.lookup g a x = some v → ValTy Δ s v (Δ x) := by
  intro g
  induction g with
  | zero => intro a v h; simp [Store.lookup] at h
  | succ g ih =>
    intro a v h
    rw [lookup_succ] at h
    cases hf : s.frames[a]? with
    | none => simp [hf] at h
    | some f =>
      rw [hf] at h
      dsimp only at h
      cases hfind : f.vars.find? (·.1 == x) with
      | some p =>
        rw [hfind] at h
        obtain ⟨y, w⟩ := p
        simp only [Option.some.injEq] at h
        subst h
        have hy : y = x := by simpa using List.find?_some hfind
        subst hy
        exact hS a f hf _ (List.mem_of_find?_eq_some hfind)
      | none =>
        rw [hfind] at h
        cases hp : f.parent with
        | none => simp [hp] at h
        | some p => simp only [hp] at h; exact ih p v h

theorem get?_typed {Δ : TyEnv} {s : Store} (hS : StoreOK Δ s) {a : Addr} {x : String}
    {v : Value} (h : s.get? a x = some v) : ValTy Δ s v (Δ x) :=
  lookup_typed hS x _ a v h

/-! ## Allocation -/

theorem allocFrame_eq {s s' : Store} {p : Option Addr} {a : Addr}
    (h : s.allocFrame p = (s', a)) :
    s' = { s with frames := s.frames.push ⟨p, []⟩ } ∧ a = s.frames.size := by
  simp only [Store.allocFrame, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem allocFrame_ext {s s' : Store} {p : Option Addr} {a : Addr}
    (h : s.allocFrame p = (s', a)) : Ext s s' := by
  obtain ⟨rfl, rfl⟩ := allocFrame_eq h
  refine ⟨by simp, ?_, fun _ _ h => h⟩
  intro b f hf
  refine ⟨f, ?_, rfl, fun _ hx => hx⟩
  have hb : b < s.frames.size := (Array.getElem?_eq_some_iff.mp hf).1
  simp [Array.getElem?_push, Nat.ne_of_lt hb, hf]

theorem allocFrame_size {s s' : Store} {p : Option Addr} {a : Addr}
    (h : s.allocFrame p = (s', a)) : a < s'.frames.size := by
  obtain ⟨rfl, rfl⟩ := allocFrame_eq h
  simp

theorem allocFrame_storeOK {Δ : TyEnv} {s s' : Store} {p : Option Addr} {a : Addr}
    (h : s.allocFrame p = (s', a)) (hS : StoreOK Δ s) : StoreOK Δ s' := by
  have hE := allocFrame_ext h
  obtain ⟨rfl, rfl⟩ := allocFrame_eq h
  intro b f hf q hq
  rw [Array.getElem?_push] at hf
  split at hf
  · simp only [Option.some.injEq] at hf
    subst hf
    simp at hq
  · exact (hS b f hf q hq).ext hE

/-- A fresh frame sees every name bound along its parent's chain. -/
theorem allocFrame_defined {s s' : Store} {p a : Addr} {x : String}
    (h : s.allocFrame (some p) = (s', a)) (hd : Defined s p x) : Defined s' a x := by
  have hE := allocFrame_ext h
  obtain ⟨v, hv⟩ := hd
  obtain ⟨v', hv'⟩ := lookup_ext hE x _ p v _ hv (Nat.le_refl _)
  obtain ⟨rfl, rfl⟩ := allocFrame_eq h
  refine ⟨v', ?_⟩
  unfold Store.get?
  simp only [Array.size_push]
  rw [lookup_succ]
  simp only [Array.getElem?_push]
  exact hv'

theorem allocFrame_defAll {s s' : Store} {p a : Addr} {S : List String}
    (h : s.allocFrame (some p) = (s', a)) (hd : DefAll s p S) : DefAll s' a S :=
  fun x hx => allocFrame_defined h (hd x hx)

theorem allocClosure_eq {s s' : Store} {cd : ClosureData} {a : Addr}
    (h : s.allocClosure cd = (s', a)) :
    s' = { s with closures := s.closures.push cd } ∧ a = s.closures.size := by
  simp only [Store.allocClosure, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem allocClosure_ext {s s' : Store} {cd : ClosureData} {a : Addr}
    (h : s.allocClosure cd = (s', a)) : Ext s s' ∧ s'.closures[a]? = some cd := by
  obtain ⟨rfl, rfl⟩ := allocClosure_eq h
  refine ⟨⟨Nat.le_refl _, fun b f hf => ⟨f, hf, rfl, fun _ hx => hx⟩, ?_⟩, by simp⟩
  intro b c hc
  have hb : b < s.closures.size := (Array.getElem?_eq_some_iff.mp hc).1
  simp [Array.getElem?_push, Nat.ne_of_lt hb, hc]

theorem allocClosure_storeOK {Δ : TyEnv} {s s' : Store} {cd : ClosureData} {a : Addr}
    (h : s.allocClosure cd = (s', a)) (hS : StoreOK Δ s) : StoreOK Δ s' := by
  have hE := (allocClosure_ext h).1
  obtain ⟨rfl, rfl⟩ := allocClosure_eq h
  intro b f hf q hq
  exact (hS b f hf q hq).ext hE

/-! ## Definition and assignment -/

/-- The frame update performed by `Store.define`. -/
def defineFrame (x : String) (v : Value) (f : Frame) : Frame :=
  { f with vars :=
      if f.vars.any (·.1 == x) then
        f.vars.map fun p => if p.1 == x then (x, v) else p
      else f.vars ++ [(x, v)] }

theorem define_frames (s : Store) (a : Addr) (x : String) (v : Value) :
    (s.define a x v).frames = s.frames.modify a (defineFrame x v) := rfl

theorem defineFrame_any (x : String) (v : Value) (f : Frame) (y : String)
    (h : f.vars.any (·.1 == y) = true) : (defineFrame x v f).vars.any (·.1 == y) = true := by
  obtain ⟨q, hq, hqy⟩ := List.any_eq_true.mp h
  unfold defineFrame
  split
  · refine List.any_eq_true.mpr ⟨if q.1 == x then (x, v) else q, List.mem_map_of_mem hq, ?_⟩
    split
    · rename_i hx
      simp only [beq_iff_eq] at hx hqy ⊢
      exact hx ▸ hqy
    · exact hqy
  · exact List.any_eq_true.mpr ⟨q, List.mem_append_left _ hq, hqy⟩

theorem defineFrame_self (x : String) (v : Value) (f : Frame) :
    (defineFrame x v f).vars.any (·.1 == x) = true := by
  unfold defineFrame
  split
  · rename_i h
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp h
    refine List.any_eq_true.mpr ⟨(x, v), ?_, by simp⟩
    refine List.mem_map.mpr ⟨q, hq, ?_⟩
    simp [hqx]
  · simp

theorem define_ext (s : Store) (a : Addr) (x : String) (v : Value) :
    Ext s (s.define a x v) := by
  refine ⟨by simp [define_frames], ?_, fun _ _ h => h⟩
  intro b f hf
  rw [define_frames, Array.getElem?_modify]
  split
  · subst b
    refine ⟨defineFrame x v f, by simp [hf], rfl, defineFrame_any x v f⟩
  · exact ⟨f, hf, rfl, fun _ hx => hx⟩

theorem define_defined (s : Store) (a : Addr) (x : String) (v : Value)
    (ha : a < s.frames.size) : Defined (s.define a x v) a x := by
  obtain ⟨f, hf⟩ : ∃ f, s.frames[a]? = some f := ⟨s.frames[a], by simp [ha]⟩
  have hf' : (s.define a x v).frames[a]? = some (defineFrame x v f) := by
    rw [define_frames, Array.getElem?_modify]; simp [hf]
  obtain ⟨q, hq⟩ := find?_isSome_of_any (defineFrame_self x v f)
  refine ⟨q.2, ?_⟩
  unfold Store.get?
  obtain ⟨n, hn⟩ : ∃ n, (s.define a x v).frames.size = n + 1 :=
    ⟨s.frames.size - 1, by
      rw [define_frames, Array.size_modify]
      exact (Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) ha)).symm⟩
  rw [hn, lookup_succ, hf']
  dsimp only
  rw [hq]

theorem defineFrame_mem {x : String} {v : Value} {f : Frame} {p : String × Value}
    (hp : p ∈ (defineFrame x v f).vars) : p = (x, v) ∨ p ∈ f.vars := by
  unfold defineFrame at hp
  split at hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    split
    · exact Or.inl rfl
    · exact Or.inr hq
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inr h
    · simp at h; exact Or.inl h

theorem define_storeOK {Δ : TyEnv} {s : Store} {a : Addr} {x : String} {v : Value}
    (hS : StoreOK Δ s) (hv : ValTy Δ (s.define a x v) v (Δ x)) :
    StoreOK Δ (s.define a x v) := by
  have hE := define_ext s a x v
  intro b f hf q hq
  rw [define_frames, Array.getElem?_modify] at hf
  split at hf
  · subst b
    cases hf0 : s.frames[a]? with
    | none => simp [hf0] at hf
    | some f0 =>
      rw [hf0] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      rcases defineFrame_mem hq with rfl | hq
      · exact hv
      · exact (hS a f0 hf0 q hq).ext hE
  · exact (hS b f hf q hq).ext hE

/-- The frame update performed by a successful `Store.set` step. -/
def setFrame (x : String) (v : Value) (f : Frame) : Frame :=
  { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p }

theorem setFrame_any (x : String) (v : Value) (f : Frame) (y : String)
    (h : f.vars.any (·.1 == y) = true) : (setFrame x v f).vars.any (·.1 == y) = true := by
  obtain ⟨q, hq, hqy⟩ := List.any_eq_true.mp h
  refine List.any_eq_true.mpr ⟨if q.1 == x then (x, v) else q, List.mem_map_of_mem hq, ?_⟩
  split
  · rename_i hx
    simp only [beq_iff_eq] at hx hqy ⊢
    exact hx ▸ hqy
  · exact hqy

theorem set_spec {Δ : TyEnv} {x : String} {v : Value} :
    ∀ g (s s' : Store) (a : Addr), s.set g a x v = some s' →
      Ext s s' ∧ (StoreOK Δ s → ValTy Δ s' v (Δ x) → StoreOK Δ s') := by
  intro g
  induction g with
  | zero => intro s s' a h; simp [Store.set] at h
  | succ g ih =>
    intro s s' a h
    unfold Store.set at h
    cases hf : s.frames[a]? with
    | none => simp [hf] at h
    | some f =>
      rw [hf] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · have h := (Option.some.inj h).symm
        subst h
        change Ext s { s with frames := s.frames.modify a (setFrame x v) } ∧
          (StoreOK Δ s → ValTy Δ { s with frames := s.frames.modify a (setFrame x v) } v (Δ x) →
            StoreOK Δ { s with frames := s.frames.modify a (setFrame x v) })
        have hmod : ∀ b, ({ s with frames := s.frames.modify a (setFrame x v) } : Store).frames[b]?
            = if a = b then s.frames[b]?.map (setFrame x v) else s.frames[b]? :=
          fun b => Array.getElem?_modify
        have hE : Ext s { s with frames := s.frames.modify a (setFrame x v) } := by
          refine ⟨by simp, ?_, fun _ _ h => h⟩
          intro b f' hf'
          rw [hmod]
          split
          · subst b
            rw [hf] at hf'
            simp only [Option.some.injEq] at hf'
            subst hf'
            exact ⟨setFrame x v f, by simp [hf], rfl, setFrame_any x v f⟩
          · exact ⟨f', hf', rfl, fun _ hx => hx⟩
        refine ⟨hE, fun hS hv => ?_⟩
        intro b f' hf' q hq
        rw [hmod] at hf'
        split at hf'
        · subst b
          rw [hf] at hf'
          simp only [Option.map_some, Option.some.injEq] at hf'
          subst hf'
          obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
          split
          · exact hv
          · exact (hS a f hf q0 hq0).ext hE
        · exact (hS b f' hf' q hq).ext hE
      · cases hp : f.parent with
        | none => simp [hp] at h
        | some p => simp only [hp] at h; exact ih s s' p h

/-- Assignment succeeds on a bound name. -/
theorem set_of_lookup {x : String} {v : Value} :
    ∀ g (s : Store) (a : Addr) w, s.lookup g a x = some w → ∃ s', s.set g a x v = some s' := by
  intro g
  induction g with
  | zero => intro s a w h; simp [Store.lookup] at h
  | succ g ih =>
    intro s a w h
    rw [lookup_succ] at h
    unfold Store.set
    cases hf : s.frames[a]? with
    | none => simp [hf] at h
    | some f =>
      rw [hf] at h
      dsimp only at h
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hfind : f.vars.find? (·.1 == x) with
      | some q => simp only [any_of_find? hfind, ite_true]; exact ⟨_, rfl⟩
      | none =>
        rw [hfind] at h
        have hany : ¬ f.vars.any (·.1 == x) = true := by
          intro hany
          obtain ⟨q, hq⟩ := find?_isSome_of_any hany
          rw [hq] at hfind; cases hfind
        simp only [hany, ite_false, Bool.false_eq_true]
        cases hp : f.parent with
        | none => simp [hp] at h
        | some p => simp only [hp] at h ⊢; exact ih s p w h

theorem set?_of_defined {s : Store} {a : Addr} {x : String} (v : Value)
    (h : Defined s a x) : ∃ s', s.set? a x v = some s' := by
  obtain ⟨w, hw⟩ := h
  exact set_of_lookup _ s a w hw

/-! ## Parameter binding -/

theorem foldDefine_spec {Δ : TyEnv} {fr : Addr} :
    ∀ (ps : List String) (vs : List Value) (s : Store),
      fr < s.frames.size → StoreOK Δ s →
      ValTys Δ s vs (ps.map Δ) →
      let s' := (ps.zip vs).foldl (fun s (x, v) => s.define fr x v) s
      Ext s s' ∧ StoreOK Δ s' ∧ DefAll s' fr ps := by
  intro ps
  induction ps with
  | nil =>
    intro vs s _ hS hvs
    exact ⟨Ext.refl s, hS, fun _ h => by cases h⟩
  | cons x ps ih =>
    intro vs s hfr hS hvs
    cases hvs with
    | cons v vs _ _ hv hvs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      have hE1 := define_ext s fr x v
      have hS1 : StoreOK Δ (s.define fr x v) := define_storeOK hS (hv.ext hE1)
      have hfr1 : fr < (s.define fr x v).frames.size := Nat.lt_of_lt_of_le hfr hE1.size_le
      obtain ⟨hE2, hS2, hD2⟩ := ih vs (s.define fr x v) hfr1 hS1 (ValTys.ext hvs hE1)
      refine ⟨hE1.trans hE2, hS2, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (define_defined s fr y v hfr).ext hE2
      · exact hD2 y hy

end Vsa.While.Types
