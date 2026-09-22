import Vsa.While.Semantics

/-!
# Store invariants and first-match chain witnesses

This module isolates the pure specification facts needed by `env_get` and
`env_set`.  The witnesses follow the C implementation's order: scan one frame
from index zero, then follow its parent.
-/

open Vsa Vsa.While

namespace Vsa.Sim

/-- A closure reference bound on a spec value: if `v` is `.closure ca`, then
`ca < size`.  (Every other variant carries no closure index.) -/
def ValueClosuresBounded (size : Nat) : Value → Prop
  | .closure ca => ca < size
  | _ => True

/-- **`StoreClosuresBounded s`** — every closure address stored in any frame
binding of `s` is `< s.closures.size` (it was returned by an earlier
`allocClosure`).  This is the well-formedness invariant that makes the closures
map monotone on the store's *own* references, so a `PhiExtends`-widening of `φc`
leaves `StoreRepr` intact.  Named-field structure per CLAUDE.md. -/
structure StoreClosuresBounded (s : Store) : Prop where
  bounded : ∀ fa, (h : fa < s.frames.size) →
    ∀ i, (hi : i < s.frames[fa].vars.length) →
      ValueClosuresBounded s.closures.size (s.frames[fa].vars[i].2)

/-- No frame contains two bindings with the same name. -/
def FrameNamesUnique (vars : List (String × Value)) : Prop :=
  (vars.map Prod.fst).Nodup

/-- Every represented frame has unique binding names. -/
def StoreUnique (s : Store) : Prop :=
  ∀ fa, (h : fa < s.frames.size) → FrameNamesUnique s.frames[fa].vars

/-- Parent pointers are valid and point to older frames. -/
def StoreParents (s : Store) : Prop :=
  ∀ fa, (h : fa < s.frames.size) → ∀ parent,
    s.frames[fa].parent = some parent → parent < fa

/-- The store-shape invariant required by the C environment operations. -/
structure StoreInvariant (s : Store) : Prop where
  unique : StoreUnique s
  parents : StoreParents s

/-- A decomposition at the first binding named `x`.  `before.length` is the
machine scan index. -/
inductive FirstMatch (vars : List (String × Value)) (x : String) (v : Value) : Prop where
  | intro (before after : List (String × Value)) :
      vars = before ++ (x, v) :: after →
      (∀ p ∈ before, p.1 ≠ x) →
      FirstMatch vars x v

/-- No binding in this frame is named `x`. -/
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

/-- `List.find?` exposes exactly a first-match decomposition. -/
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

/-- A successful lookup path: first-match hit in this frame, or a full-frame
miss followed by the parent path. -/
inductive LookupChain (s : Store) (x : String) : Nat → Addr → Value → Prop where
  | hit {gas a f v} :
      s.frames[a]? = some f → FirstMatch f.vars x v →
      LookupChain s x (gas + 1) a v
  | parent {gas a f parent v} :
      s.frames[a]? = some f → FrameMiss f.vars x → f.parent = some parent →
      LookupChain s x gas parent v →
      LookupChain s x (gas + 1) a v

/-- A successful assignment path.  The hit result is definitionally the Lean
store update; uniqueness later reduces that update to one C slot. -/
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

/-- The exact terminal frame selected by a successful assignment path.  Unlike
`SetTerminal`, this retains every missed parent edge from the starting frame. -/
inductive SetTarget (s : Store) (x : String) : Nat → Addr → Addr → Frame → Value → Prop where
  | hit {gas a f oldValue} :
      s.frames[a]? = some f → FirstMatch f.vars x oldValue →
      SetTarget s x (gas + 1) a a f oldValue
  | parent {gas a f parent target targetFrame oldValue} :
      s.frames[a]? = some f → FrameMiss f.vars x → f.parent = some parent →
      SetTarget s x gas parent target targetFrame oldValue →
      SetTarget s x (gas + 1) a target targetFrame oldValue

/-- A `SetChain` determines the actual first-match target and its old value,
while retaining the exact result-store equation. -/
theorem SetChain.selected {s s' : Store} {x : String} {newValue : Value}
    {gas : Nat} {a : Addr} (h : SetChain s x newValue gas a s') :
    ∃ target frame oldValue,
      SetTarget s x gas a target frame oldValue ∧
      s.frames[target]? = some frame ∧ FirstMatch frame.vars x oldValue ∧
      s' = { s with frames := s.frames.modify target fun current =>
        { current with vars := current.vars.map fun p =>
          if p.1 == x then (x, newValue) else p } } := by
  induction h with
  | hit hframe hfirst =>
      exact ⟨_, _, _, SetTarget.hit hframe hfirst, hframe, hfirst, rfl⟩
  | parent hframe hmiss hparent _ ih =>
      obtain ⟨target, targetFrame, oldValue, hpath, htarget, hfirst, hresult⟩ := ih
      exact ⟨target, targetFrame, oldValue,
        SetTarget.parent hframe hmiss hparent hpath, htarget, hfirst, hresult⟩

theorem SetTarget.headFrame {s : Store} {x : String} {gas : Nat}
    {a target : Addr} {targetFrame : Frame} {oldValue : Value}
    (h : SetTarget s x gas a target targetFrame oldValue) :
    ∃ frame, s.frames[a]? = some frame := by
  cases h with
  | hit hframe _ => exact ⟨_, hframe⟩
  | parent hframe _ _ _ => exact ⟨_, hframe⟩

/-- The chain witness is exactly the successful result of the Lean lookup. -/
theorem lookup_eq_some_iff_chain (s : Store) (x : String) :
    ∀ gas a v, s.lookup gas a x = some v ↔ LookupChain s x gas a v := by
  intro gas
  induction gas with
  | zero =>
    intro a v
    constructor
    · intro h
      simp [Store.lookup] at h
    · intro h
      cases h
  | succ gas ih =>
    intro a v
    constructor
    · intro h
      unfold Store.lookup at h
      cases hframe : s.frames[a]? with
      | none => simp [hframe] at h
      | some frame =>
        rw [hframe] at h
        simp only [bind, Option.bind] at h
        cases hfind : frame.vars.find? (fun p => p.1 == x) with
        | none =>
          rw [hfind] at h
          cases hparent : frame.parent with
          | none => simp [hparent] at h
          | some parent =>
            rw [hparent] at h
            exact LookupChain.parent hframe (frameMiss_iff_find?.mpr hfind) hparent
              ((ih parent v).mp h)
        | some pair =>
          obtain ⟨name, foundValue⟩ := pair
          rw [hfind] at h
          have hvalue : foundValue = v := by simpa using h
          have hname : name = x := by
            have := List.find?_some hfind
            simpa only [beq_iff_eq] using this
          subst name
          subst foundValue
          exact LookupChain.hit hframe (firstMatch_iff_find?.mpr hfind)
    · intro h
      cases h with
      | hit hframe hfirst =>
        unfold Store.lookup
        rw [hframe]
        simp only [bind, Option.bind, hfirst.find?_eq_some]
      | parent hframe hmiss hparent htail =>
        unfold Store.lookup
        rw [hframe]
        simp only [bind, Option.bind, hmiss.find?_eq_none, hparent]
        exact (ih _ _).mpr htail

/-- `Store.get?` form used directly by the variable rule. -/
theorem get?_eq_some_iff_chain (s : Store) (a : Addr) (x : String) (v : Value) :
    s.get? a x = some v ↔ LookupChain s x s.frames.size a v :=
  lookup_eq_some_iff_chain s x s.frames.size a v

/-- The assignment chain witness is exactly the successful Lean update. -/
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

/-- `Store.set?` form used directly by the assignment rule. -/
theorem set?_eq_some_iff_chain (s : Store) (a : Addr) (x : String)
    (newValue : Value) (s' : Store) :
    s.set? a x newValue = some s' ↔
      SetChain s x newValue s.frames.size a s' :=
  set_eq_some_iff_chain s x newValue s.frames.size a s'

/-! ## Preservation of the store-shape invariant -/

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

theorem StoreUnique.allocClosure (s : Store) (closure : ClosureData)
    (h : StoreUnique s) : StoreUnique (s.allocClosure closure).1 := by
  simpa [Store.allocClosure, StoreUnique] using h

theorem StoreParents.allocClosure (s : Store) (closure : ClosureData)
    (h : StoreParents s) : StoreParents (s.allocClosure closure).1 := by
  simpa [Store.allocClosure, StoreParents] using h

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

theorem StoreInvariant.allocClosure (s : Store) (closure : ClosureData)
    (h : StoreInvariant s) : StoreInvariant (s.allocClosure closure).1 :=
  ⟨h.unique.allocClosure s closure, h.parents.allocClosure s closure⟩

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

theorem StoreInvariant.foldDefine (bindings : List (String × Value))
    (frame : Addr) {s : Store} (hinv : StoreInvariant s) :
    StoreInvariant
      (bindings.foldl (fun current binding =>
        current.define frame binding.1 binding.2) s) := by
  induction bindings generalizing s with
  | nil => exact hinv
  | cons binding rest ih =>
    simp only [List.foldl_cons]
    exact ih (hinv.define s frame binding.1 binding.2)

/-- Legal store mutations.  This is the operation-level reachability relation
used to seed stronger simulation entry predicates without changing WHILE's
language semantics. -/
inductive StoreStep : Store → Store → Prop where
  | allocFrame (s : Store) (parent : Option Addr)
      (hparent : ∀ p, parent = some p → p < s.frames.size) :
      StoreStep s (s.allocFrame parent).1
  | allocClosure (s : Store) (closure : ClosureData) :
      StoreStep s (s.allocClosure closure).1
  | define (s : Store) (frame : Addr) (x : String) (v : Value) :
      StoreStep s (s.define frame x v)
  | set (s s' : Store) (gas : Nat) (frame : Addr) (x : String) (v : Value) :
      s.set gas frame x v = some s' → StoreStep s s'

theorem StoreStep.preserves {s s' : Store} (hstep : StoreStep s s')
    (hinv : StoreInvariant s) : StoreInvariant s' := by
  cases hstep with
  | allocFrame parent hparent => exact hinv.allocFrame _ parent hparent
  | allocClosure closure => exact hinv.allocClosure _ closure
  | define frame x v => exact hinv.define _ frame x v
  | set _ _ _ _ _ hset => exact hinv.set hset

/-- Stores constructible from `initSt` by legal environment operations. -/
inductive ReachableStore : Store → Prop where
  | init : ReachableStore initSt.store
  | step {s s'} : ReachableStore s → StoreStep s s' → ReachableStore s'

/-- Terminal target of a successful first-match lookup chain. -/
def LookupTerminal (s : Store) (x : String) (v : Value) : Prop :=
    ∃ (target : Addr) (frame : Frame),
      s.frames[target]? = some frame ∧ FirstMatch frame.vars x v

/-- Terminal target and result equation of a successful assignment chain. -/
def SetTerminal (s s' : Store) (x : String) (newValue : Value) : Prop :=
  ∃ target frame oldValue,
    s.frames[target]? = some frame ∧ FirstMatch frame.vars x oldValue ∧
    s' = { s with frames := s.frames.modify target fun current =>
      { current with vars := current.vars.map (replaceBindingValue x newValue) } }

/-- A lookup chain exposes the exact terminal frame and first-match slot. -/
theorem LookupChain.terminal {s : Store} {x : String} {gas : Nat} {a : Addr}
    {v : Value} (h : LookupChain s x gas a v) : LookupTerminal s x v := by
  unfold LookupTerminal
  induction h with
  | hit hframe hfirst => exact ⟨_, _, hframe, hfirst⟩
  | parent _ _ _ _ ih => exact ih

/-- A set chain exposes the one target frame.  The Lean result is its mapped
update; `FirstMatch.single_update` below reduces that map to one slot when the
store is unique. -/
theorem SetChain.terminal {s s' : Store} {x : String} {newValue : Value}
    {gas : Nat} {a : Addr} (h : SetChain s x newValue gas a s') :
    SetTerminal s s' x newValue := by
  unfold SetTerminal
  induction h with
  | hit hframe hfirst => exact ⟨_, _, _, hframe, hfirst, rfl⟩
  | parent _ _ _ _ ih => exact ih

theorem map_replaceBindingValue_of_miss {vars : List (String × Value)} {x : String}
    (newValue : Value) (hmiss : FrameMiss vars x) :
    vars.map (replaceBindingValue x newValue) = vars := by
  induction vars with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.1 ≠ x := hmiss p (by simp)
    have hrest : FrameMiss rest x := by
      intro q hq
      exact hmiss q (by simp [hq])
    simp only [List.map_cons, replaceBindingValue]
    have hb : (p.1 == x) = false := by simpa only [beq_eq_false_iff_ne]
    rw [hb, ih hrest]
    simp

theorem FirstMatch.after_miss {vars : List (String × Value)} {x : String}
    {oldValue : Value} (hfirst : FirstMatch vars x oldValue)
    (hunique : FrameNamesUnique vars) :
    ∃ before after,
      vars = before ++ (x, oldValue) :: after ∧
      FrameMiss before x ∧ FrameMiss after x := by
  obtain ⟨before, after, hsplit, hbefore⟩ := hfirst
  refine ⟨before, after, hsplit, hbefore, ?_⟩
  unfold FrameNamesUnique at hunique
  rw [hsplit, List.map_append] at hunique
  simp only [List.map_cons] at hunique
  have htail : (x :: after.map Prod.fst).Nodup := (List.nodup_append.mp hunique).2.1
  have hxnot : x ∉ after.map Prod.fst := (List.nodup_cons.mp htail).1
  intro p hp heq
  apply hxnot
  have : p.1 ∈ after.map Prod.fst := List.mem_map_of_mem hp
  simpa [heq] using this

/-- Under `FrameNamesUnique`, the spec's map-based assignment changes exactly the
first C scan slot and leaves both surrounding slices unchanged. -/
theorem FirstMatch.single_update {vars : List (String × Value)} {x : String}
    {oldValue newValue : Value} (hfirst : FirstMatch vars x oldValue)
    (hunique : FrameNamesUnique vars) :
    ∃ before after,
      vars = before ++ (x, oldValue) :: after ∧
      vars.map (replaceBindingValue x newValue) =
        before ++ (x, newValue) :: after := by
  obtain ⟨before, after, hsplit, hbefore, hafter⟩ := hfirst.after_miss hunique
  refine ⟨before, after, hsplit, ?_⟩
  rw [hsplit, List.map_append, map_replaceBindingValue_of_miss newValue hbefore]
  simp only [List.map_cons]
  rw [map_replaceBindingValue_of_miss newValue hafter]
  simp [replaceBindingValue]

/-- Index form consumed by the C scan loop. -/
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

/-- Direct hVar hook: a semantic `Store.get?` premise yields the recursive C
scan witness and its terminal first-match frame. -/
theorem get?_terminal_first {s : Store} {a : Addr} {x : String} {v : Value}
    (hget : s.get? a x = some v) :
    LookupChain s x s.frames.size a v ∧
      LookupTerminal s x v := by
  have hchain := (get?_eq_some_iff_chain s a x v).mp hget
  exact ⟨hchain, hchain.terminal⟩

/-- Direct hAssign hook: a semantic `Store.set?` premise yields the recursive C
scan witness, terminal first-match frame, and exact result-store equation. -/
theorem set?_terminal_first {s s' : Store} {a : Addr} {x : String}
    {newValue : Value} (hset : s.set? a x newValue = some s') :
    SetChain s x newValue s.frames.size a s' ∧
      SetTerminal s s' x newValue := by
  have hchain := (set?_eq_some_iff_chain s a x newValue s').mp hset
  exact ⟨hchain, hchain.terminal⟩

/-- hAssign's strongest pure hook: under store uniqueness, `set?` identifies
one first-match list cell and the spec result is exactly that one-cell update. -/
theorem set?_single_update {s s' : Store} {a : Addr} {x : String}
    {newValue : Value} (hunique : StoreUnique s)
    (hset : s.set? a x newValue = some s') :
    ∃ (target : Addr) (frame : Frame) (oldValue : Value)
      (before after : List (String × Value)),
      s.frames[target]? = some frame ∧
      frame.vars = before ++ (x, oldValue) :: after ∧
      frame.vars.map (replaceBindingValue x newValue) =
        before ++ (x, newValue) :: after ∧
      s' = { s with frames := s.frames.modify target fun current =>
        { current with vars := current.vars.map (replaceBindingValue x newValue) } } := by
  obtain ⟨_, target, frame, oldValue, hframe, hfirst, hresult⟩ :=
    set?_terminal_first hset
  obtain ⟨htarget, htargetGet⟩ := Array.getElem?_eq_some_iff.mp hframe
  have hframeEq : s.frames[target]'htarget = frame := htargetGet
  have hframeUnique : FrameNamesUnique frame.vars := by
    rw [← hframeEq]
    exact hunique target htarget
  obtain ⟨before, after, hsplit, hupdate⟩ :=
    hfirst.single_update hframeUnique
  exact ⟨target, frame, oldValue, before, after, hframe, hsplit, hupdate, hresult⟩

/-- The concrete initial interpreter store satisfies the environment invariant. -/
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

theorem ReachableStore.invariant {s : Store} (h : ReachableStore s) :
    StoreInvariant s := by
  induction h with
  | init => exact storeInvariant_initSt
  | step _ hstep ih => exact hstep.preserves ih

/-! ## Constructor-facing semantic bridges -/

/-- Exact semantic certificate for a successful variable lookup. -/
structure VarStoreBridge (s : Store) (a : Addr) (x : String) (v : Value) : Prop where
  invariant : StoreInvariant s
  chain : LookupChain s x s.frames.size a v
  terminal : LookupTerminal s x v

/-- Exact semantic certificate for a successful assignment.  `oneSlot` states
that the map-based Lean update is the single-slot update performed by C. -/
structure AssignStoreBridge
    (s s' : Store) (a : Addr) (x : String) (newValue : Value) : Prop where
  before : StoreInvariant s
  chain : SetChain s x newValue s.frames.size a s'
  terminal : SetTerminal s s' x newValue
  oneSlot :
    ∃ (target : Addr) (frame : Frame) (oldValue : Value)
      (beforeVars afterVars : List (String × Value)),
      s.frames[target]? = some frame ∧
      frame.vars = beforeVars ++ (x, oldValue) :: afterVars ∧
      frame.vars.map (replaceBindingValue x newValue) =
        beforeVars ++ (x, newValue) :: afterVars ∧
      s' = { s with frames := s.frames.modify target fun current =>
        { current with vars := current.vars.map (replaceBindingValue x newValue) } }
  after : StoreInvariant s'
  reachable : ReachableStore s'

/-- The bridge's target is selected by the same recursive parent path used by
the machine scan, with the one-slot list decomposition derived from uniqueness. -/
theorem AssignStoreBridge.selected {s s' : Store} {a : Addr} {x : String}
    {newValue : Value} (h : AssignStoreBridge s s' a x newValue) :
    ∃ target frame oldValue beforeVars afterVars,
      SetTarget s x s.frames.size a target frame oldValue ∧
      s.frames[target]? = some frame ∧
      FirstMatch frame.vars x oldValue ∧
      frame.vars = beforeVars ++ (x, oldValue) :: afterVars ∧
      frame.vars.map (replaceBindingValue x newValue) =
        beforeVars ++ (x, newValue) :: afterVars ∧
      s' = { s with frames := s.frames.modify target fun current =>
        { current with vars := current.vars.map (replaceBindingValue x newValue) } } := by
  obtain ⟨target, frame, oldValue, hpath, hframe, hfirst, hresult⟩ := h.chain.selected
  obtain ⟨htarget, htargetGet⟩ := Array.getElem?_eq_some_iff.mp hframe
  have hframeEq : s.frames[target]'htarget = frame := htargetGet
  have hunique : FrameNamesUnique frame.vars := by
    rw [← hframeEq]
    exact h.before.unique target htarget
  obtain ⟨beforeVars, afterVars, hsplit, hupdate⟩ :=
    hfirst.single_update hunique
  exact ⟨target, frame, oldValue, beforeVars, afterVars, hpath, hframe,
    hfirst, hsplit, hupdate, by unfold replaceBindingValue; exact hresult⟩

/-- A reachable store plus the constructor's `get?` premise determines the
complete first-match parent-chain certificate. -/
theorem ReachableStore.varBridge {s : Store} (hreach : ReachableStore s)
    {a : Addr} {x : String} {v : Value} (hget : s.get? a x = some v) :
    VarStoreBridge s a x v := by
  have hinv := hreach.invariant
  obtain ⟨hchain, hterminal⟩ := get?_terminal_first hget
  exact ⟨hinv, hchain, hterminal⟩

/-- A reachable store plus the constructor's `set?` premise determines the
single C slot updated, preserves the invariant, and remains reachable. -/
theorem ReachableStore.assignBridge {s s' : Store} (hreach : ReachableStore s)
    {a : Addr} {x : String} {newValue : Value}
    (hset : s.set? a x newValue = some s') :
    AssignStoreBridge s s' a x newValue := by
  have hinv := hreach.invariant
  obtain ⟨hchain, hterminal⟩ := set?_terminal_first hset
  have hone := set?_single_update hinv.unique hset
  have hafter := hinv.set? hset
  have hreach' : ReachableStore s' := by
    apply ReachableStore.step hreach
    exact StoreStep.set s s' s.frames.size a x newValue hset
  exact ⟨hinv, hchain, hterminal, hone, hafter, hreach'⟩

end Vsa.Sim
