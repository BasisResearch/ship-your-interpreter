import Vsa.While.Semantics

open Vsa Vsa.While

namespace Vsa.Sim

def ValueClosuresBounded (size : Nat) : Value → Prop
  | .closure ca => ca < size
  | _ => True

structure StoreClosuresBounded (s : Store) : Prop where
  bounded : ∀ fa, (h : fa < s.frames.size) →
    ∀ i, (hi : i < s.frames[fa].vars.length) →
      ValueClosuresBounded s.closures.size (s.frames[fa].vars[i].2)

def FrameNamesUnique (vars : List (String × Value)) : Prop :=
  (vars.map Prod.fst).Nodup

def StoreUnique (s : Store) : Prop :=
  ∀ fa, (h : fa < s.frames.size) → FrameNamesUnique s.frames[fa].vars

def StoreParents (s : Store) : Prop :=
  ∀ fa, (h : fa < s.frames.size) → ∀ parent,
    s.frames[fa].parent = some parent → parent < fa

structure StoreInvariant (s : Store) : Prop where
  unique : StoreUnique s
  parents : StoreParents s

inductive FirstMatch (vars : List (String × Value)) (x : String) (v : Value) : Prop where
  | intro (before after : List (String × Value)) :
      vars = before ++ (x, v) :: after →
      (∀ p ∈ before, p.1 ≠ x) →
      FirstMatch vars x v

def FrameMiss (vars : List (String × Value)) (x : String) : Prop :=
  ∀ p ∈ vars, p.1 ≠ x

theorem FirstMatch.find?_eq_some {vars : List (String × Value)} {x : String} {v : Value}
    (h : FirstMatch vars x v) :
    vars.find? (fun p => p.1 == x) = some (x, v) := by
  obtain ⟨before, after, hsplit, hbefore⟩ := h
  rw [hsplit, List.find?_append]
  have hnone : before.find? (fun p => p.1 == x) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [beq_iff_eq]
    exact hbefore p hp
  rw [hnone]
  simp

theorem FrameMiss.find?_eq_none {vars : List (String × Value)} {x : String}
    (h : FrameMiss vars x) :
    vars.find? (fun p => p.1 == x) = none := by
  rw [List.find?_eq_none]
  intro p hp
  simp only [beq_iff_eq]
  exact h p hp

theorem FrameMiss.any_eq_false {vars : List (String × Value)} {x : String}
    (h : FrameMiss vars x) :
    vars.any (fun p => p.1 == x) = false := by
  rw [List.any_eq_false]
  intro p hp
  simp only [beq_iff_eq]
  exact h p hp

theorem FirstMatch.any_eq_true {vars : List (String × Value)} {x : String} {v : Value}
    (h : FirstMatch vars x v) :
    vars.any (fun p => p.1 == x) = true := by
  obtain ⟨before, after, hsplit, _⟩ := h
  rw [List.any_eq_true]
  refine ⟨(x, v), ?_, by simp⟩
  rw [hsplit]
  simp

theorem firstMatch_iff_find? {vars : List (String × Value)} {x : String} {v : Value} :
    FirstMatch vars x v ↔ vars.find? (fun p => p.1 == x) = some (x, v) := by
  constructor
  · exact FirstMatch.find?_eq_some
  · intro h
    induction vars with
    | nil => simp at h
    | cons hd tl ih =>
      simp only [List.find?_cons] at h
      by_cases heq : hd.1 = x
      · have hp : (hd.1 == x) = true := by simpa only [beq_iff_eq]
        rw [hp] at h
        have : hd = (x, v) := by simpa using h
        subst hd
        exact ⟨[], tl, by simp, by simp⟩
      · have hp : (hd.1 == x) = false := by simpa only [beq_eq_false_iff_ne]
        rw [hp] at h
        obtain ⟨before, after, hsplit, hbefore⟩ := ih h
        refine ⟨hd :: before, after, ?_, ?_⟩
        · simp only [List.cons_append, hsplit]
        · intro p hp'
          simp only [List.mem_cons] at hp'
          rcases hp' with rfl | hp'
          · exact heq
          · exact hbefore p hp'

theorem frameMiss_iff_find? {vars : List (String × Value)} {x : String} :
    FrameMiss vars x ↔ vars.find? (fun p => p.1 == x) = none := by
  constructor
  · exact FrameMiss.find?_eq_none
  · intro h p hp heq
    have hfalse := (List.find?_eq_none.mp h) p hp
    apply hfalse
    simpa only [beq_iff_eq]

theorem frameMiss_iff_any {vars : List (String × Value)} {x : String} :
    FrameMiss vars x ↔ vars.any (fun p => p.1 == x) = false := by
  constructor
  · exact FrameMiss.any_eq_false
  · intro h p hp heq
    have hfalse := (List.any_eq_false.mp h) p hp
    apply hfalse
    simpa only [beq_iff_eq]

theorem exists_firstMatch_iff_any {vars : List (String × Value)} {x : String} :
    (∃ v, FirstMatch vars x v) ↔ vars.any (fun p => p.1 == x) = true := by
  constructor
  · rintro ⟨v, h⟩
    exact h.any_eq_true
  · intro hany
    cases hfind : vars.find? (fun p => p.1 == x) with
    | none =>
      have hmiss : FrameMiss vars x := frameMiss_iff_find?.mpr hfind
      rw [hmiss.any_eq_false] at hany
      contradiction
    | some p =>
      obtain ⟨name, value⟩ := p
      have hname : name = x := by
        have := List.find?_some hfind
        simpa only [beq_iff_eq] using this
      subst name
      exact ⟨value, firstMatch_iff_find?.mpr hfind⟩

inductive SetChain (s : Store) (x : String) (newValue : Value) :
    Nat → Addr → Store → Prop where
  | hit {gas a f oldValue} :
      s.frames[a]? = some f → FirstMatch f.vars x oldValue →
      SetChain s x newValue (gas + 1) a
        { s with frames := s.frames.modify a fun frame =>
            { frame with vars := frame.vars.map fun p =>
                if p.1 == x then (x, newValue) else p } }
  | parent {gas a f parent s'} :
      s.frames[a]? = some f → FrameMiss f.vars x → f.parent = some parent →
      SetChain s x newValue gas parent s' →
      SetChain s x newValue (gas + 1) a s'

theorem set_eq_some_iff_chain (s : Store) (x : String) (newValue : Value) :
    ∀ gas a s', s.set gas a x newValue = some s' ↔
      SetChain s x newValue gas a s' := by
  intro gas
  induction gas with
  | zero =>
    intro a s'
    constructor
    · intro h
      simp [Store.set] at h
    · intro h
      cases h
  | succ gas ih =>
    intro a s'
    constructor
    · intro h
      unfold Store.set at h
      cases hframe : s.frames[a]? with
      | none => simp [hframe] at h
      | some frame =>
        rw [hframe] at h
        simp only [bind, Option.bind] at h
        by_cases hany : frame.vars.any (fun p => p.1 == x)
        · rw [if_pos hany] at h
          injection h with hresult
          subst s'
          obtain ⟨oldValue, hfirst⟩ := exists_firstMatch_iff_any.mpr hany
          exact SetChain.hit hframe hfirst
        · rw [if_neg hany] at h
          cases hparent : frame.parent with
          | none => simp [hparent] at h
          | some parent =>
            rw [hparent] at h
            have hanyFalse : frame.vars.any (fun p => p.1 == x) = false := by
              cases heq : frame.vars.any (fun p => p.1 == x) <;> simp_all
            exact SetChain.parent hframe (frameMiss_iff_any.mpr hanyFalse)
              hparent ((ih parent s').mp h)
    · intro h
      cases h with
      | hit hframe hfirst =>
        unfold Store.set
        rw [hframe]
        simp only [bind, Option.bind]
        rw [if_pos hfirst.any_eq_true]
      | parent hframe hmiss hparent htail =>
        unfold Store.set
        rw [hframe]
        simp only [bind, Option.bind]
        rw [hmiss.any_eq_false, hparent]
        exact (ih _ _).mpr htail

def replaceBindingValue (x : String) (newValue : Value) (p : String × Value) :
    String × Value :=
  if p.1 == x then (x, newValue) else p

theorem replaceBindingValue_name (x : String) (newValue : Value) (p : String × Value) :
    (replaceBindingValue x newValue p).1 = p.1 := by
  unfold replaceBindingValue
  by_cases h : p.1 = x
  · simp [h]
  · have hb : (p.1 == x) = false := by simpa only [beq_eq_false_iff_ne]
    simp [hb]

theorem replaceBindingValue_names (vars : List (String × Value)) (x : String)
    (newValue : Value) :
    (vars.map (replaceBindingValue x newValue)).map Prod.fst = vars.map Prod.fst := by
  induction vars with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons]
    rw [replaceBindingValue_name, ih]

theorem FrameNamesUnique.replaceBindingValue {vars : List (String × Value)}
    (h : FrameNamesUnique vars) (x : String) (newValue : Value) :
    FrameNamesUnique (vars.map (replaceBindingValue x newValue)) := by
  unfold FrameNamesUnique at h ⊢
  rw [replaceBindingValue_names]
  exact h

theorem FrameNamesUnique.append_of_miss {vars : List (String × Value)}
    (h : FrameNamesUnique vars) {x : String} (v : Value) (hmiss : FrameMiss vars x) :
    FrameNamesUnique (vars ++ [(x, v)]) := by
  unfold FrameNamesUnique at h ⊢
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨h, by simp, ?_⟩
  intro name hname other hother
  simp only [List.mem_singleton] at hother
  subst other
  obtain ⟨p, hp, hpname⟩ := List.mem_map.mp hname
  subst name
  exact hmiss p hp

theorem FrameNamesUnique.defineBindings {vars : List (String × Value)}
    (h : FrameNamesUnique vars) (x : String) (v : Value) :
    FrameNamesUnique
      (if vars.any (fun p => p.1 == x) then
        vars.map (Vsa.Sim.replaceBindingValue x v)
       else vars ++ [(x, v)]) := by
  by_cases hany : vars.any (fun p => p.1 == x)
  · rw [if_pos hany]
    exact FrameNamesUnique.replaceBindingValue h x v
  · rw [if_neg hany]
    have hfalse : vars.any (fun p => p.1 == x) = false := by
      cases heq : vars.any (fun p => p.1 == x) <;> simp_all
    exact h.append_of_miss v (frameMiss_iff_any.mpr hfalse)

theorem StoreUnique.allocFrame (s : Store) (parent : Option Addr)
    (h : StoreUnique s) : StoreUnique (s.allocFrame parent).1 := by
  intro fa hfa
  simp only [Store.allocFrame] at hfa ⊢
  by_cases hold : fa < s.frames.size
  · have heq := Array.getElem_push_lt
        (xs := s.frames) (x := ({ parent := parent, vars := [] } : Frame)) hold
    rw [heq]
    exact h fa hold
  · have hnew : fa = s.frames.size := by
      rw [Array.size_push] at hfa
      omega
    subst fa
    have heq : (s.frames.push { parent := parent, vars := [] })[s.frames.size]'hfa =
        ({ parent := parent, vars := [] } : Frame) := Array.getElem_push_eq
    rw [heq]
    simp [FrameNamesUnique]

theorem StoreParents.allocFrame (s : Store) (parent : Option Addr)
    (h : StoreParents s)
    (hparent : ∀ p, parent = some p → p < s.frames.size) :
    StoreParents (s.allocFrame parent).1 := by
  intro fa hfa p hp
  simp only [Store.allocFrame] at hfa hp ⊢
  by_cases hold : fa < s.frames.size
  · have heq := Array.getElem_push_lt
        (xs := s.frames) (x := ({ parent := parent, vars := [] } : Frame)) hold
    rw [heq] at hp
    exact h fa hold p hp
  · have hnew : fa = s.frames.size := by
      rw [Array.size_push] at hfa
      omega
    subst fa
    have heq : (s.frames.push { parent := parent, vars := [] })[s.frames.size]'hfa =
        ({ parent := parent, vars := [] } : Frame) := Array.getElem_push_eq
    rw [heq] at hp
    exact hparent p hp

theorem StoreInvariant.allocFrame (s : Store) (parent : Option Addr)
    (h : StoreInvariant s)
    (hparent : ∀ p, parent = some p → p < s.frames.size) :
    StoreInvariant (s.allocFrame parent).1 :=
  ⟨h.unique.allocFrame s parent, h.parents.allocFrame s parent hparent⟩

theorem StoreUnique.define (s : Store) (a : Addr) (x : String) (v : Value)
    (h : StoreUnique s) : StoreUnique (s.define a x v) := by
  intro fa hfa
  unfold Store.define at hfa ⊢
  have hfa' : fa < s.frames.size := by simpa using hfa
  rw [Array.getElem_modify]
  by_cases ha : a = fa
  · rw [if_pos ha]
    subst a
    change FrameNamesUnique
      (if (s.frames[fa]'hfa').vars.any (fun p => p.1 == x) then
        (s.frames[fa]'hfa').vars.map (replaceBindingValue x v)
       else (s.frames[fa]'hfa').vars ++ [(x, v)])
    exact FrameNamesUnique.defineBindings (h fa hfa') x v
  · rw [if_neg ha]
    exact h fa hfa'

theorem StoreParents.define (s : Store) (a : Addr) (x : String) (v : Value)
    (h : StoreParents s) : StoreParents (s.define a x v) := by
  intro fa hfa parent hparent
  unfold Store.define at hfa hparent
  have hfa' : fa < s.frames.size := by simpa using hfa
  rw [Array.getElem_modify] at hparent
  by_cases ha : a = fa
  · rw [if_pos ha] at hparent
    exact h fa hfa' parent hparent
  · rw [if_neg ha] at hparent
    exact h fa hfa' parent hparent

theorem StoreInvariant.define (s : Store) (a : Addr) (x : String) (v : Value)
    (h : StoreInvariant s) : StoreInvariant (s.define a x v) :=
  ⟨h.unique.define s a x v, h.parents.define s a x v⟩

theorem SetChain.unique {s s' : Store} {x : String} {newValue : Value}
    {gas : Nat} {a : Addr} (hchain : SetChain s x newValue gas a s')
    (hunique : StoreUnique s) : StoreUnique s' := by
  induction hchain with
  | @hit gas a frame oldValue hframe hfirst =>
    intro fa hfa
    have hfa' : fa < s.frames.size := by simpa using hfa
    rw [Array.getElem_modify]
    by_cases ha : a = fa
    · rw [if_pos ha]
      subst a
      change FrameNamesUnique
        ((s.frames[fa]'hfa').vars.map (replaceBindingValue x newValue))
      exact FrameNamesUnique.replaceBindingValue (hunique fa hfa') x newValue
    · rw [if_neg ha]
      exact hunique fa hfa'
  | parent _ _ _ _ ih =>
    exact ih

theorem SetChain.parents {s s' : Store} {x : String} {newValue : Value}
    {gas : Nat} {a : Addr} (hchain : SetChain s x newValue gas a s')
    (hparents : StoreParents s) : StoreParents s' := by
  induction hchain with
  | @hit gas a frame oldValue hframe hfirst =>
    intro fa hfa parent hparent
    have hfa' : fa < s.frames.size := by simpa using hfa
    rw [Array.getElem_modify] at hparent
    by_cases ha : a = fa
    · rw [if_pos ha] at hparent
      exact hparents fa hfa' parent hparent
    · rw [if_neg ha] at hparent
      exact hparents fa hfa' parent hparent
  | parent _ _ _ _ ih =>
    exact ih

theorem StoreInvariant.set {s s' : Store} {gas : Nat} {a : Addr}
    {x : String} {newValue : Value} (hinv : StoreInvariant s)
    (hset : s.set gas a x newValue = some s') : StoreInvariant s' := by
  have hchain := (set_eq_some_iff_chain s x newValue gas a s').mp hset
  exact ⟨hchain.unique hinv.unique, hchain.parents hinv.parents⟩

theorem StoreInvariant.set? {s s' : Store} {a : Addr}
    {x : String} {newValue : Value} (hinv : StoreInvariant s)
    (hset : s.set? a x newValue = some s') : StoreInvariant s' :=
  hinv.set hset

theorem FirstMatch.index {vars : List (String × Value)} {x : String}
    {value : Value} (hfirst : FirstMatch vars x value) :
    ∃ (i : Nat) (hi : i < vars.length),
      vars[i] = (x, value) ∧
      ∀ j, (hj : j < i) → (vars[j]'(Nat.lt_trans hj hi)).1 ≠ x := by
  obtain ⟨before, after, hsplit, hbefore⟩ := hfirst
  subst vars
  refine ⟨before.length, by simp, ?_, ?_⟩
  · rw [List.getElem_append_right (by omega)]
    simp
  · intro j hj
    have hjall : j < (before ++ (x, value) :: after).length := by simp; omega
    have hget : (before ++ (x, value) :: after)[j]'hjall = before[j] :=
      List.getElem_append_left hj
    rw [hget]
    exact hbefore before[j] (List.getElem_mem hj)

theorem storeInvariant_initSt : StoreInvariant initSt.store := by
  constructor
  · intro fa hfa
    have hfa0 : fa = 0 := by simpa [initSt] using hfa
    subst fa
    simp [FrameNamesUnique, initSt]
  · intro fa hfa parent hparent
    have hfa0 : fa = 0 := by simpa [initSt] using hfa
    subst fa
    simp [initSt] at hparent

end Vsa.Sim
