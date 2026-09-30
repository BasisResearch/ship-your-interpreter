import Vsa.While.Semantics

namespace Vsa.While

def Frame.defVar (F : Frame) (x : String) (v : Value) : Frame :=
  { F with vars :=
      if F.vars.any (·.1 == x) then
        F.vars.map fun p => if p.1 == x then (x, v) else p
      else
        F.vars ++ [(x, v)] }

def Frame.setVar (F : Frame) (x : String) (v : Value) : Frame :=
  { F with vars := F.vars.map fun p => if p.1 == x then (x, v) else p }

def Frame.find (F : Frame) (x : String) : Option Value :=
  (F.vars.find? (·.1 == x)).map (·.2)

theorem Store.define_eq (s : Store) (a : Nat) (x : String) (v : Value) :
    s.define a x v = { s with frames := s.frames.modify a (·.defVar x v) } := rfl

structure Store.WF (s : Store) : Prop where
  parent_lt : ∀ (a : Nat) (F : Frame) (p : Nat),
    s.frames[a]? = some F → F.parent = some p → p < a
  closure_env : ∀ (c : Nat) (cd : ClosureData),
    s.closures[c]? = some cd → cd.env < s.frames.size

namespace Store

theorem find?_eq_none_iff_any {l : List (String × Value)} {x : String} :
    l.find? (·.1 == x) = none ↔ l.any (·.1 == x) = false := by
  simp [List.find?_eq_none, List.any_eq_false]

theorem lookup_succ (s : Store) (g a : Nat) (x : String) :
    s.lookup (g+1) a x = (s.frames[a]?).bind (fun F => match F.find x with
      | some v => some v | none => F.parent.bind (fun p => s.lookup g p x)) := by
  rw [Store.lookup]
  cases s.frames[a]? with
  | none => rfl
  | some F =>
    simp only [Option.bind_some, Frame.find]
    show (match F.vars.find? (·.1 == x) with | some (_, v) => some v | none => _) = _
    cases F.vars.find? (·.1 == x) with
    | some p => rfl
    | none => cases F.parent <;> rfl
theorem set_succ (s : Store) (g a : Nat) (x : String) (v : Value) :
    s.set (g+1) a x v = (s.frames[a]?).bind (fun F =>
      if F.vars.any (·.1 == x) then
        some { s with frames := s.frames.modify a fun f =>
          { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } }
      else F.parent.bind (fun p => s.set g p x v)) := by
  rw [Store.set]
  cases s.frames[a]? with
  | none => rfl
  | some F =>
    simp only [Option.bind_some]
    show (if _ then _ else _) = _
    split
    · rfl
    · cases F.parent <;> rfl

theorem lt_size_of_getElem? {s : Store} {a : Nat} {F : Frame}
    (h : s.frames[a]? = some F) : a < s.frames.size := by
  rcases Array.getElem?_eq_some_iff.mp h with ⟨ha, _⟩; exact ha

theorem lookup_gas {s : Store} (hs : s.WF) :
    ∀ (g g' : Nat) (a : Nat) (x : String), a < g → a < g' →
      s.lookup g a x = s.lookup g' a x := by
  intro g
  induction g with
  | zero => intro _ _ _ hg _; omega
  | succ k ih =>
    intro g' a x hg hg'
    cases g' with
    | zero => omega
    | succ k' =>
      rw [lookup_succ, lookup_succ]
      cases hF : s.frames[a]? with
      | none => rfl
      | some F =>
        simp only [Option.bind_some]
        cases F.find x with
        | some p => rfl
        | none =>
          cases hp : F.parent with
          | none => rfl
          | some p =>
            have := hs.parent_lt a F p hF hp
            simp only [Option.bind_some]
            exact ih k' p x (by omega) (by omega)

theorem set_gas {s : Store} (hs : s.WF) :
    ∀ (g g' : Nat) (a : Nat) (x : String) (v : Value), a < g → a < g' →
      s.set g a x v = s.set g' a x v := by
  intro g
  induction g with
  | zero => intro _ _ _ _ hg _; omega
  | succ k ih =>
    intro g' a x v hg hg'
    cases g' with
    | zero => omega
    | succ k' =>
      rw [set_succ, set_succ]
      cases hF : s.frames[a]? with
      | none => rfl
      | some F =>
        simp only [Option.bind_some]
        split
        · rfl
        · cases hp : F.parent with
          | none => rfl
          | some p =>
            have := hs.parent_lt a F p hF hp
            simp only [Option.bind_some]
            exact ih k' p x v (by omega) (by omega)

theorem size_pos {s : Store} {a : Nat} {F : Frame} (hF : s.frames[a]? = some F) :
    ∃ k, s.frames.size = k + 1 ∧ a ≤ k :=
  ⟨s.frames.size - 1, by have := lt_size_of_getElem? hF; omega, by
    have := lt_size_of_getElem? hF; omega⟩

theorem get?_here {s : Store} {a : Nat} {F : Frame} {x : String} {v : Value}
    (hF : s.frames[a]? = some F) (hx : F.find x = some v) : s.get? a x = some v := by
  obtain ⟨k, hk, _⟩ := size_pos hF
  unfold Store.get?; rw [hk, lookup_succ, hF]
  simp [hx]

theorem get?_parent {s : Store} (hs : s.WF) {a p : Nat} {F : Frame} {x : String}
    (hF : s.frames[a]? = some F) (hx : F.find x = none) (hp : F.parent = some p) :
    s.get? a x = s.get? p x := by
  obtain ⟨k, hk, hak⟩ := size_pos hF
  have hpa := hs.parent_lt a F p hF hp
  unfold Store.get?; rw [hk, lookup_succ, hF]
  simp only [Option.bind_some, hx, hp]
  exact lookup_gas hs k (k + 1) p x (by omega) (by omega)

theorem any_of_find {F : Frame} {x : String} {v : Value} (h : F.find x = some v) :
    F.vars.any (·.1 == x) = true := by
  unfold Frame.find at h
  cases hf : F.vars.find? (·.1 == x) with
  | none => simp [hf] at h
  | some p =>
    have := List.find?_some hf
    exact List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hf, this⟩

theorem any_false_of_find {F : Frame} {x : String} (h : F.find x = none) :
    F.vars.any (·.1 == x) = false := by
  unfold Frame.find at h
  exact find?_eq_none_iff_any.mp (by cases hf : F.vars.find? (·.1 == x) <;> simp_all)

theorem set?_here {s : Store} {a : Nat} {F : Frame} {x : String} {v0 v : Value}
    (hF : s.frames[a]? = some F) (hx : F.find x = some v0) :
    s.set? a x v = some { s with frames := s.frames.modify a (·.setVar x v) } := by
  obtain ⟨k, hk, _⟩ := size_pos hF
  unfold Store.set?; rw [hk, set_succ, hF]
  simp only [Option.bind_some, any_of_find hx, ite_true]
  rfl

theorem set?_parent {s : Store} (hs : s.WF) {a p : Nat} {F : Frame} {x : String}
    {v : Value} (hF : s.frames[a]? = some F) (hx : F.find x = none)
    (hp : F.parent = some p) : s.set? a x v = s.set? p x v := by
  obtain ⟨k, hk, hak⟩ := size_pos hF
  have hpa := hs.parent_lt a F p hF hp
  unfold Store.set?; rw [hk, set_succ, hF]
  simp only [Option.bind_some, any_false_of_find hx, hp]
  simp only [Bool.false_eq_true, ite_false]
  exact set_gas hs k (k + 1) p x v (by omega) (by omega)

theorem WF.modify {s : Store} (hs : s.WF) (a : Nat) (f : Frame → Frame)
    (hf : ∀ F, (f F).parent = F.parent) :
    ({ s with frames := s.frames.modify a f } : Store).WF where
  parent_lt b F p hb hp := by
    simp only [Array.getElem?_modify] at hb
    split at hb
    · cases h : s.frames[b]? with
      | none => simp [h] at hb
      | some G =>
        simp [h] at hb; subst hb
        exact hs.parent_lt b G p h (by rw [← hf]; exact hp)
    · exact hs.parent_lt b F p hb hp
  closure_env c cd hc := by simpa using hs.closure_env c cd hc

theorem WF.allocFrame {s : Store} (hs : s.WF) {e : Nat} (he : e < s.frames.size) :
    (s.allocFrame (some e)).1.WF where
  parent_lt b F p hb hp := by
    simp only [Store.allocFrame, Array.getElem?_push] at hb
    split at hb
    · rename_i hbs; cases hb; cases hp; subst hbs; exact he
    · exact hs.parent_lt b F p hb hp
  closure_env c cd hc := by
    have := hs.closure_env c cd hc
    show cd.env < (s.frames.push _).size
    rw [Array.size_push]; exact Nat.lt_succ_of_lt this

theorem WF.allocClosure {s : Store} (hs : s.WF) {cd : ClosureData}
    (he : cd.env < s.frames.size) : (s.allocClosure cd).1.WF where
  parent_lt b F p hb hp := hs.parent_lt b F p hb hp
  closure_env c cd' hc := by
    simp only [Store.allocClosure, Array.getElem?_push] at hc
    split at hc
    · cases hc; exact he
    · exact hs.closure_env c cd' hc

theorem WF.define {s : Store} (hs : s.WF) (a : Nat) (x : String) (v : Value) :
    (s.define a x v).WF := by
  rw [define_eq]; exact hs.modify a _ (fun _ => rfl)

theorem frames_define (s : Store) (a b : Nat) (x : String) (v : Value) :
    (s.define a x v).frames[b]? =
      if a = b then (s.frames[b]?).map (·.defVar x v) else s.frames[b]? := by
  rw [define_eq]; exact Array.getElem?_modify

theorem size_define (s : Store) (a : Nat) (x : String) (v : Value) :
    (s.define a x v).frames.size = s.frames.size := by
  rw [define_eq]; exact Array.size_modify

theorem closures_define (s : Store) (a : Nat) (x : String) (v : Value) :
    (s.define a x v).closures = s.closures := rfl

end Store

def Frame.bindAll (F : Frame) (l : List (String × Value)) : Frame :=
  l.foldl (fun F (x, v) => F.defVar x v) F

namespace Store

theorem foldl_define (a : Nat) (l : List (String × Value)) : ∀ (s : Store),
    (∀ b, (l.foldl (fun s (x, v) => s.define a x v) s).frames[b]? =
      if a = b then (s.frames[b]?).map (·.bindAll l) else s.frames[b]?) ∧
    (l.foldl (fun s (x, v) => s.define a x v) s).closures = s.closures ∧
    (l.foldl (fun s (x, v) => s.define a x v) s).frames.size = s.frames.size ∧
    (s.WF → (l.foldl (fun s (x, v) => s.define a x v) s).WF) := by
  induction l with
  | nil =>
    intro s
    refine ⟨fun b => ?_, rfl, rfl, id⟩
    show s.frames[b]? = _
    split
    · cases s.frames[b]? <;> rfl
    · rfl
  | cons p l ih =>
    intro s
    obtain ⟨x, v⟩ := p
    obtain ⟨h1, h2, h3, h4⟩ := ih (s.define a x v)
    simp only [List.foldl_cons]
    refine ⟨fun b => ?_, h2, by rw [h3, size_define], fun hs => h4 (hs.define a x v)⟩
    rw [h1 b, frames_define]
    split
    · rw [Option.map_map]; rfl
    · rfl

end Store

theorem initSt_wf : initSt.store.WF where
  parent_lt a F p h hp := by
    rcases a with _ | a
    · simp [initSt] at h; subst h; simp at hp
    · simp [initSt] at h
  closure_env c cd h := by simp [initSt] at h

end Vsa.While
