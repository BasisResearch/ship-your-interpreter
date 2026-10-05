import Vsa.CT.Typing

namespace Vsa.CT

open Vsa.While

def VarRel (sec : String → Bool) (p q : String × Value) : Prop :=
  p.1 = q.1 ∧ (sec p.1 = false → p.2 = q.2)

inductive VarsRel (sec : String → Bool) : List (String × Value) → List (String × Value) → Prop where
  | nil : VarsRel sec [] []
  | cons {p q : String × Value} {l1 l2 : List (String × Value)} :
    VarRel sec p q → VarsRel sec l1 l2 → VarsRel sec (p :: l1) (q :: l2)

theorem VarsRel.append {sec : String → Bool} :
    ∀ {l1 l2 m1 m2 : List (String × Value)}, VarsRel sec l1 l2 → VarsRel sec m1 m2 →
      VarsRel sec (l1 ++ m1) (l2 ++ m2)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hpq hr, h => .cons hpq (VarsRel.append hr h)

def LowF (sec : String → Bool) (f1 f2 : Frame) : Prop :=
  f1.parent = f2.parent ∧ VarsRel sec f1.vars f2.vars

def LowS (sec : String → Bool) (s1 s2 : Store) : Prop :=
  s1.frames.size = s2.frames.size ∧
    ∀ (a : Nat) (f1 f2 : Frame), s1.frames[a]? = some f1 → s2.frames[a]? = some f2 → LowF sec f1 f2

def NatOK (v : Value) (x : String) : Prop :=
  (isNat x = false → ∃ n, v = .int n) ∧ (x = "print" → v = .native .print) ∧
    (x = "println" → v = .native .println)

def Good (s : Store) : Prop :=
  s.closures.size = 0 ∧
    ∀ (a : Nat) (f : Frame), s.frames[a]? = some f → ∀ p ∈ f.vars, NatOK p.2 p.1

def Low (sec : String → Bool) (st1 st2 : St) : Prop :=
  LowS sec st1.store st2.store ∧ Good st1.store ∧ Good st2.store

theorem frame_some {s1 s2 : Store} {a : Nat} {f1 : Frame} (hs : s1.frames.size = s2.frames.size)
    (h : s1.frames[a]? = some f1) : ∃ f2, s2.frames[a]? = some f2 := by
  have ha : a < s1.frames.size := by
    rcases Nat.lt_or_ge a s1.frames.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  exact ⟨s2.frames[a]'(hs ▸ ha), Array.getElem?_eq_getElem (hs ▸ ha)⟩

theorem find_rel {sec : String → Bool} {x : String} :
    ∀ {l1 l2 : List (String × Value)}, VarsRel sec l1 l2 →
      (∀ p1, l1.find? (·.1 == x) = some p1 →
        ∃ p2, l2.find? (·.1 == x) = some p2 ∧ VarRel sec p1 p2 ∧ p2 ∈ l2) ∧
      (l1.find? (·.1 == x) = none → l2.find? (·.1 == x) = none)
  | [], [], .nil => ⟨fun _ h => by simp at h, fun _ => rfl⟩
  | p :: l1, q :: l2, .cons hpq hr => by
    obtain ⟨ih1, ih2⟩ := find_rel hr
    have hn : p.1 = q.1 := hpq.1
    by_cases hx : p.1 = x
    · have hq : q.1 = x := hn ▸ hx
      refine ⟨fun p1 h => ?_, fun h => ?_⟩
      · simp [List.find?, hx] at h
        subst h
        exact ⟨q, by simp [List.find?, hq], hpq, List.mem_cons_self ..⟩
      · simp [List.find?, hx] at h
    · have hq : ¬ q.1 = x := fun e => hx (hn ▸ e)
      have hb1 : (p.1 == x) = false := by simpa using hx
      have hb2 : (q.1 == x) = false := by simpa using hq
      refine ⟨fun p1 h => ?_, fun h => ?_⟩
      · simp only [List.find?, hb1] at h
        obtain ⟨p2, h2, hr2, hm⟩ := ih1 p1 h
        refine ⟨p2, ?_, hr2, List.mem_cons_of_mem _ hm⟩
        simp only [List.find?, hb2]; exact h2
      · simp only [List.find?, hb1] at h
        simp only [List.find?, hb2]; exact ih2 h

theorem any_rel {sec : String → Bool} {x : String} :
    ∀ {l1 l2 : List (String × Value)}, VarsRel sec l1 l2 →
      l1.any (·.1 == x) = l2.any (·.1 == x)
  | [], [], .nil => rfl
  | p :: l1, q :: l2, .cons hpq hr => by
    simp only [List.any_cons, hpq.1, any_rel hr]

theorem map_rel {sec : String → Bool} {x : String} {v1 v2 : Value} (hv : sec x = false → v1 = v2) :
    ∀ {l1 l2 : List (String × Value)}, VarsRel sec l1 l2 →
      VarsRel sec (l1.map fun p => if p.1 == x then (x, v1) else p)
        (l2.map fun p => if p.1 == x then (x, v2) else p)
  | [], [], .nil => .nil
  | p :: l1, q :: l2, .cons hpq hr => by
    refine .cons ?_ (map_rel hv hr)
    have hn : p.1 = q.1 := hpq.1
    by_cases hx : p.1 = x
    · have hq : q.1 = x := hn ▸ hx
      simp only [hx, hq, beq_self_eq_true, ite_true]
      exact ⟨rfl, hv⟩
    · have hq : ¬ q.1 = x := fun e => hx (hn ▸ e)
      simp only [beq_iff_eq, hx, hq, ite_false]
      exact hpq

theorem lookup_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) (g2 : Good s2) :
    ∀ (g : Nat) (a : Nat) (x : String) (v1 : Value), s1.lookup g a x = some v1 →
      ∃ v2, s2.lookup g a x = some v2 ∧ (sec x = false → v1 = v2) ∧ NatOK v2 x
  | 0, _, _, _, hl => by simp [Store.lookup] at hl
  | g + 1, a, x, v1, hl => by
    simp only [Store.lookup] at hl
    cases hf1 : s1.frames[a]? with
    | none => rw [hf1] at hl; cases hl
    | some f1 =>
      rw [hf1] at hl
      obtain ⟨f2, hf2⟩ := frame_some h.1 hf1
      obtain ⟨hpar, hvars⟩ := h.2 a f1 f2 hf1 hf2
      obtain ⟨fr1, fr2⟩ := find_rel (x := x) hvars
      simp only [Option.bind_eq_bind, Option.bind_some] at hl
      cases hfd : f1.vars.find? (·.1 == x) with
      | some p1 =>
        rw [hfd] at hl
        obtain ⟨y, w⟩ := p1
        simp only [Option.some.injEq] at hl
        subst hl
        obtain ⟨p2, hp2, hr, hm⟩ := fr1 _ hfd
        have hy : y = x := by simpa using List.find?_some hfd
        refine ⟨p2.2, ?_, fun hs => hr.2 (by simpa [hy] using hs), ?_⟩
        · simp only [Store.lookup, hf2, Option.bind_eq_bind, Option.bind_some, hp2]
        · have := g2.2 a f2 hf2 p2 hm
          have hx2 : p2.1 = x := by
            have := List.find?_some hp2; simpa using this
          rw [hx2] at this; exact this
      | none =>
        rw [hfd] at hl
        have hfd2 := fr2 hfd
        cases hp : f1.parent with
        | none => rw [hp] at hl; cases hl
        | some p =>
          rw [hp] at hl
          obtain ⟨v2, h1, h2, h3⟩ := lookup_low h g2 g p x v1 hl
          refine ⟨v2, ?_, h2, h3⟩
          simp only [Store.lookup, hf2, Option.bind_eq_bind, Option.bind_some, hfd2, ← hpar, hp]
          exact h1

theorem get_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) (g2 : Good s2)
    {a : Nat} {x : String} {v1 : Value} (hl : s1.get? a x = some v1) :
    ∃ v2, s2.get? a x = some v2 ∧ (sec x = false → v1 = v2) ∧ NatOK v2 x := by
  unfold Store.get? at hl ⊢
  rw [← h.1]
  exact lookup_low h g2 _ a x v1 hl

theorem get_good {s : Store} (g : Good s) : ∀ (n : Nat) {a : Nat} {x : String} {v : Value},
    s.lookup n a x = some v → NatOK v x
  | 0, _, _, _, hl => by simp [Store.lookup] at hl
  | n + 1, a, x, v, hl => by
    simp only [Store.lookup, Option.bind_eq_bind] at hl
    cases hf : s.frames[a]? with
    | none => rw [hf] at hl; cases hl
    | some f =>
      rw [hf, Option.bind_some] at hl
      cases hfd : f.vars.find? (·.1 == x) with
      | some p =>
        rw [hfd] at hl
        obtain ⟨y, w⟩ := p
        simp only [Option.some.injEq] at hl
        subst hl
        have hy : y = x := by simpa using List.find?_some hfd
        have := g.2 a f hf (y, w) (List.mem_of_find?_eq_some hfd)
        rw [hy] at this; exact this
      | none =>
        rw [hfd] at hl
        cases hp : f.parent with
        | none => rw [hp] at hl; cases hl
        | some p => rw [hp] at hl; exact get_good g n hl

theorem modify_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) (a : Nat)
    (g1 g2 : Frame → Frame) (hg : ∀ f1 f2, LowF sec f1 f2 → LowF sec (g1 f1) (g2 f2)) :
    LowS sec { s1 with frames := s1.frames.modify a g1 } { s2 with frames := s2.frames.modify a g2 } := by
  refine ⟨by simp [h.1], fun b f1 f2 h1 h2 => ?_⟩
  simp only [Array.getElem?_modify] at h1 h2
  by_cases hab : a = b
  · subst hab
    simp only [ite_true] at h1 h2
    cases e1 : s1.frames[a]? with
    | none => rw [e1] at h1; cases h1
    | some q1 =>
      cases e2 : s2.frames[a]? with
      | none => rw [e2] at h2; cases h2
      | some q2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        exact hg _ _ (h.2 a q1 q2 e1 e2)
  · simp only [hab, ite_false] at h1 h2
    exact h.2 b f1 f2 h1 h2

theorem modify_good {s : Store} (g : Good s) (a : Nat) (gf : Frame → Frame)
    (hg : ∀ f, (∀ p ∈ f.vars, NatOK p.2 p.1) → ∀ p ∈ (gf f).vars, NatOK p.2 p.1) :
    Good { s with frames := s.frames.modify a gf } := by
  refine ⟨g.1, fun b f h => ?_⟩
  simp only [Array.getElem?_modify] at h
  by_cases hab : a = b
  · subst hab
    simp only [ite_true] at h
    cases e : s.frames[a]? with
    | none => rw [e] at h; cases h
    | some q =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hg q (g.2 a q e)
  · simp only [hab, ite_false] at h
    exact g.2 b f h

theorem natOK_upd {x : String} {v : Value} (hx : NatOK v x) :
    ∀ (l : List (String × Value)), (∀ p ∈ l, NatOK p.2 p.1) →
      ∀ p ∈ l.map (fun p => if p.1 == x then (x, v) else p), NatOK p.2 p.1 := by
  intro l hl p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  by_cases h : q.1 = x
  · simp only [h, beq_self_eq_true, ite_true]; exact hx
  · simp only [beq_iff_eq, h, ite_false]; exact hl q hq

theorem define_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) (a : Addr) (x : String)
    {v1 v2 : Value} (hv : sec x = false → v1 = v2) :
    LowS sec (s1.define a x v1) (s2.define a x v2) := by
  unfold Store.define
  refine modify_low h a _ _ fun f1 f2 hf => ⟨hf.1, ?_⟩
  simp only [any_rel (x := x) hf.2]
  split
  · exact map_rel hv hf.2
  · exact hf.2.append (.cons ⟨rfl, hv⟩ .nil)

theorem define_good {s : Store} (g : Good s) (a : Addr) (x : String) {v : Value} (hx : NatOK v x) :
    Good (s.define a x v) := by
  unfold Store.define
  refine modify_good g a _ fun f hf => ?_
  simp only
  split
  · exact natOK_upd hx _ hf
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hf p hp
    · simp at hp; subst hp; exact hx

theorem set_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) {x : String}
    {v1 v2 : Value} (hv : sec x = false → v1 = v2) :
    ∀ (g : Nat) (a : Addr) {s1' : Store}, s1.set g a x v1 = some s1' →
      ∃ s2', s2.set g a x v2 = some s2' ∧ LowS sec s1' s2'
  | 0, _, _, hs => by simp [Store.set] at hs
  | g + 1, a, s1', hs => by
    simp only [Store.set, Option.bind_eq_bind] at hs
    cases hf1 : s1.frames[a]? with
    | none => rw [hf1] at hs; cases hs
    | some f1 =>
      rw [hf1, Option.bind_some] at hs
      obtain ⟨f2, hf2⟩ := frame_some h.1 hf1
      have hr := h.2 a f1 f2 hf1 hf2
      have hany := any_rel (x := x) hr.2
      by_cases ha : f1.vars.any (·.1 == x) = true
      · rw [if_pos ha] at hs
        cases hs
        refine ⟨{ s2 with frames := s2.frames.modify a fun f =>
            { f with vars := f.vars.map fun p => if p.1 == x then (x, v2) else p } }, ?_,
          modify_low h a _ _ fun q1 q2 hq => ⟨hq.1, map_rel hv hq.2⟩⟩
        simp only [Store.set, hf2, Option.bind_eq_bind, Option.bind_some, ← hany, ha, ite_true]
      · rw [if_neg ha] at hs
        cases hp : f1.parent with
        | none => rw [hp] at hs; cases hs
        | some p =>
          rw [hp] at hs
          obtain ⟨s2', h1, h2⟩ := set_low h hv g p hs
          refine ⟨s2', ?_, h2⟩
          simp only [Store.set, hf2, Option.bind_eq_bind, Option.bind_some, ← hany, ha, ← hr.1, hp]
          exact h1

theorem set_good {s : Store} (g : Good s) {x : String} {v : Value} (hx : NatOK v x) :
    ∀ (n : Nat) (a : Addr) {s' : Store}, s.set n a x v = some s' → Good s'
  | 0, _, _, hs => by simp [Store.set] at hs
  | n + 1, a, s', hs => by
    simp only [Store.set, Option.bind_eq_bind] at hs
    cases hf : s.frames[a]? with
    | none => rw [hf] at hs; cases hs
    | some f =>
      rw [hf, Option.bind_some] at hs
      by_cases ha : f.vars.any (·.1 == x) = true
      · rw [if_pos ha] at hs
        cases hs
        exact modify_good g a _ fun q hq => natOK_upd hx _ hq
      · rw [if_neg ha] at hs
        cases hp : f.parent with
        | none => rw [hp] at hs; cases hs
        | some p => rw [hp] at hs; exact set_good g hx n p hs

theorem set_size {s : Store} {x : String} {v : Value} :
    ∀ (n : Nat) (a : Addr) {s' : Store}, s.set n a x v = some s' → s'.frames.size = s.frames.size
  | 0, _, _, hs => by simp [Store.set] at hs
  | n + 1, a, s', hs => by
    simp only [Store.set, Option.bind_eq_bind] at hs
    cases hf : s.frames[a]? with
    | none => rw [hf] at hs; cases hs
    | some f =>
      rw [hf, Option.bind_some] at hs
      by_cases ha : f.vars.any (·.1 == x) = true
      · rw [if_pos ha] at hs; cases hs; simp
      · rw [if_neg ha] at hs
        cases hp : f.parent with
        | none => rw [hp] at hs; cases hs
        | some p => rw [hp] at hs; exact set_size n p hs

theorem set?_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) {a : Addr} {x : String}
    {v1 v2 : Value} (hv : sec x = false → v1 = v2) {s1' : Store} (hs : s1.set? a x v1 = some s1') :
    ∃ s2', s2.set? a x v2 = some s2' ∧ LowS sec s1' s2' := by
  unfold Store.set? at hs ⊢
  rw [← h.1]
  exact set_low h hv _ a hs

theorem alloc_low {sec : String → Bool} {s1 s2 : Store} (h : LowS sec s1 s2) (p : Option Addr) :
    LowS sec (s1.allocFrame p).1 (s2.allocFrame p).1 ∧ (s1.allocFrame p).2 = (s2.allocFrame p).2 := by
  refine ⟨⟨by simp [Store.allocFrame, h.1], fun b f1 f2 h1 h2 => ?_⟩, by simp [Store.allocFrame, h.1]⟩
  simp only [Store.allocFrame, Array.getElem?_push] at h1 h2
  rw [h.1] at h1
  by_cases hb : b = s2.frames.size
  · simp only [hb, ite_true, Option.some.injEq] at h1 h2
    subst h1 h2
    exact ⟨rfl, .nil⟩
  · simp only [hb, ite_false] at h1 h2
    exact h.2 b f1 f2 h1 h2

theorem alloc_good {s : Store} (g : Good s) (p : Option Addr) : Good (s.allocFrame p).1 := by
  refine ⟨g.1, fun b f h => ?_⟩
  simp only [Store.allocFrame, Array.getElem?_push] at h
  by_cases hb : b = s.frames.size
  · simp only [hb, ite_true, Option.some.injEq] at h
    subst h
    intro q hq; simp at hq
  · simp only [hb, ite_false] at h
    exact g.2 b f h

end Vsa.CT
