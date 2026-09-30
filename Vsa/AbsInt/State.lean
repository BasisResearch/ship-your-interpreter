import Vsa.AbsInt.Domain

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

structure Bind (A : Type) where
  val : A
  must : Bool
  deriving Repr

abbrev Scope (A : Type) := List (String × Bind A)

def Scope.get {A : Type} : Scope A → String → Option (Bind A)
  | [], _ => none
  | (k, b) :: S, x => if k = x then some b else Scope.get S x

inductive AState (A : Type) where
  | bot
  | top
  | sc (l : List (Scope A))
  deriving Repr

def Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: m => R a b ∧ Pw R l m
  | _, _ => False

section Concrete

variable {A : Type} [AbsDom A]

def vfind (vars : List (String × Value)) (x : String) : Option Value :=
  (vars.find? (·.1 == x)).map Prod.snd

def OptGam : Option A → Value → Prop
  | none, _ => False
  | some a, v => Gam a v

def BindOK : Option (Bind A) → Option Value → Prop
  | none, o => o = none
  | some b, o => (b.must = true → o.isSome = true) ∧ ∀ v, o = some v → Gam b.val v

def ScopeOK (S : Scope A) (vars : List (String × Value)) : Prop :=
  ∀ x, BindOK (S.get x) (vfind vars x)

def FrameAt (s : Store) (a : Addr) (P : Frame → Prop) : Prop :=
  match s.frames[a]? with
  | some f => P f
  | none => False

def Chain (s : Store) : List Addr → List (Scope A) → Prop
  | [], [] => True
  | a :: as, S :: l =>
      FrameAt s a (fun f => f.parent = as.head? ∧ ScopeOK S f.vars) ∧
        (∀ b, as.head? = some b → b < a) ∧ Chain s as l
  | _, _ => False

def SGam (as : List Addr) (s : Store) : AState A → Prop
  | .bot => False
  | .top => True
  | .sc l => Chain s as l

theorem vfind_nil (y : String) : vfind [] y = none := rfl

theorem vfind_cons (k : String) (w : Value) (r : List (String × Value))
    (y : String) : vfind ((k, w) :: r) y = if k = y then some w else vfind r y := by
  by_cases h : k = y
  · subst h; simp [vfind]
  · simp [vfind, h]

theorem any_cons (k : String) (w : Value) (r : List (String × Value)) (x : String) :
    ((k, w) :: r).any (·.1 == x) = (k == x || r.any (·.1 == x)) := rfl

theorem vfind_isSome_of_any {vars : List (String × Value)} {x : String}
    (h : vars.any (·.1 == x) = true) : (vfind vars x).isSome = true := by
  induction vars with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [vfind_cons]
    rw [any_cons] at h
    by_cases hk : k = x
    · simp [hk]
    · simp only [hk, beq_false_of_ne, Bool.false_or, ne_eq, not_false_eq_true] at h
      simp only [hk, ↓reduceIte]
      exact ih h

theorem vfind_none_of_not_any {vars : List (String × Value)} {x : String}
    (h : vars.any (·.1 == x) = false) : vfind vars x = none := by
  induction vars with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [vfind_cons]
    rw [any_cons] at h
    by_cases hk : k = x
    · simp [hk] at h
    · simp only [hk, beq_false_of_ne, Bool.false_or, ne_eq, not_false_eq_true] at h
      simp only [hk, ↓reduceIte]
      exact ih h

def setVars (vars : List (String × Value)) (x : String) (v : Value) :
    List (String × Value) :=
  vars.map fun p => if p.1 == x then (x, v) else p

theorem setVars_cons (k : String) (w : Value) (r : List (String × Value))
    (x : String) (v : Value) :
    setVars ((k, w) :: r) x v = (if k = x then (x, v) else (k, w)) :: setVars r x v := by
  by_cases hk : k = x <;> simp [setVars, hk]

theorem vfind_setVars_ne {vars : List (String × Value)} {x y : String}
    (v : Value) (hxy : x ≠ y) : vfind (setVars vars x v) y = vfind vars y := by
  induction vars with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [setVars_cons]
    by_cases hk : k = x
    · subst hk
      simp only [↓reduceIte, vfind_cons, hxy, ih]
    · simp only [hk, ↓reduceIte, vfind_cons, ih]

theorem vfind_setVars_eq {vars : List (String × Value)} {x : String}
    (v : Value) (h : vars.any (·.1 == x) = true) :
    vfind (setVars vars x v) x = some v := by
  induction vars with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [setVars_cons]
    rw [any_cons] at h
    by_cases hk : k = x
    · simp [hk, vfind_cons]
    · simp only [hk, beq_false_of_ne, Bool.false_or, ne_eq, not_false_eq_true] at h
      simp only [hk, ↓reduceIte, vfind_cons]
      exact ih h

theorem vfind_setVars {vars : List (String × Value)} {x : String} {v : Value}
    (h : vars.any (·.1 == x) = true) (y : String) :
    vfind (setVars vars x v) y = if x = y then some v else vfind vars y := by
  by_cases hxy : x = y
  · subst hxy; simp [vfind_setVars_eq v h]
  · simp [hxy, vfind_setVars_ne v hxy]

theorem vfind_append_ne {vars : List (String × Value)} {x y : String}
    (v : Value) (hxy : x ≠ y) : vfind (vars ++ [(x, v)]) y = vfind vars y := by
  induction vars with
  | nil => simp [vfind_cons, hxy, vfind_nil]
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.cons_append, vfind_cons, ih]

theorem vfind_append_eq {vars : List (String × Value)} {x : String}
    (v : Value) (h : vars.any (·.1 == x) = false) :
    vfind (vars ++ [(x, v)]) x = some v := by
  induction vars with
  | nil => simp [vfind_cons]
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [any_cons] at h
    by_cases hk : k = x
    · simp [hk] at h
    · simp only [hk, beq_false_of_ne, Bool.false_or, ne_eq, not_false_eq_true] at h
      simp only [List.cons_append, vfind_cons, hk, ↓reduceIte]
      exact ih h

def defineVars (vars : List (String × Value)) (x : String) (v : Value) :
    List (String × Value) :=
  if vars.any (·.1 == x) then setVars vars x v else vars ++ [(x, v)]

theorem vfind_defineVars (vars : List (String × Value)) (x : String)
    (v : Value) (y : String) :
    vfind (defineVars vars x v) y = if x = y then some v else vfind vars y := by
  unfold defineVars
  cases h : vars.any (·.1 == x)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hxy : x = y
    · subst hxy; simp [vfind_append_eq v h]
    · simp [hxy, vfind_append_ne v hxy]
  · simp only [↓reduceIte]
    exact vfind_setVars h y

theorem define_frames (s : Store) (a : Addr) (x : String) (v : Value) (i : Nat) :
    (s.define a x v).frames[i]? =
      if a = i then (s.frames[i]?).map (fun f => { f with vars := defineVars f.vars x v })
      else s.frames[i]? := by
  simp only [Store.define, Array.getElem?_modify]
  rfl

theorem lookup_succ (s : Store) (g : Nat) (a : Addr) (x : String) :
    s.lookup (g + 1) a x =
      match s.frames[a]? with
      | none => none
      | some f => match vfind f.vars x with
        | some v => some v
        | none => match f.parent with
          | some p => s.lookup g p x
          | none => none := by
  rw [Store.lookup]
  cases hf : s.frames[a]? with
  | none => rfl
  | some f =>
    cases hq : f.vars.find? (·.1 == x) with
    | none => simp only [bind, Option.bind, hq, vfind, Option.map_none]; cases f.parent <;> rfl
    | some q =>
      obtain ⟨k, w⟩ := q
      simp [hq, vfind]

end Concrete

section Ops

variable {A : Type} [AbsOps A]

def joinOpt : Option A → Option A → Option A
  | none, o => o
  | some a, none => some a
  | some a, some b => some (join a b)

def combB (op : A → A → A) : Option (Bind A) → Option (Bind A) → Option (Bind A)
  | none, none => none
  | some b, none => some ⟨b.val, false⟩
  | none, some c => some ⟨c.val, false⟩
  | some b, some c => some ⟨op b.val c.val, b.must && c.must⟩

def leB : Option (Bind A) → Option (Bind A) → Bool
  | none, none => true
  | none, some c => !c.must
  | some _, none => false
  | some b, some c => le b.val c.val && (!c.must || b.must)

def keys (S : Scope A) : List String := S.map (·.1)

def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

def build (ks : List String) (g : String → Option (Bind A)) : Scope A :=
  ks.filterMap fun x => (g x).map fun b => (x, b)

def zipScope (op : A → A → A) (S T : Scope A) : Scope A :=
  build (dedup (keys S ++ keys T)) fun x => combB op (S.get x) (T.get x)

def leScope (S T : Scope A) : Bool :=
  (keys S ++ keys T).all fun x => leB (S.get x) (T.get x)

def AState.comb (op : A → A → A) : AState A → AState A → AState A
  | .bot, t => t
  | t, .bot => t
  | .sc l, .sc m =>
      if l.length = m.length then .sc (List.zipWith (zipScope op) l m) else .top
  | _, _ => .top

def AState.join (σ τ : AState A) : AState A := AState.comb AbsOps.join σ τ

def AState.widen (σ τ : AState A) : AState A := AState.comb AbsOps.widen σ τ

def AState.le : AState A → AState A → Bool
  | .bot, _ => true
  | _, .top => true
  | .sc l, .sc m => l.length == m.length && (List.zipWith leScope l m).all id
  | _, _ => false

def lookupL (x : String) : List (Scope A) → Option A × Bool
  | [] => (none, true)
  | S :: l => match S.get x with
    | some b => if b.must then (some b.val, false)
      else ((joinOpt (some b.val) (lookupL x l).1), (lookupL x l).2)
    | none => lookupL x l

def AState.lookup (σ : AState A) (x : String) : A × Bool :=
  match σ with
  | .bot => (AbsOps.top, false)
  | .top => (AbsOps.top, true)
  | .sc l => ((lookupL x l).1.getD AbsOps.top, (lookupL x l).2)

def AState.define (σ : AState A) (x : String) (a : A) : AState A :=
  match σ with
  | .sc (S :: l) => .sc (((x, ⟨a, true⟩) :: S) :: l)
  | σ => σ

def assignL (x : String) (a : A) : Bool → List (Scope A) → List (Scope A) × Bool
  | _, [] => ([], true)
  | weak, S :: l => match S.get x with
    | some b =>
      if b.must then
        (((x, ⟨if weak then join b.val a else a, true⟩) :: S) :: l, false)
      else
        (((x, ⟨join b.val a, false⟩) :: S) :: (assignL x a true l).1,
          (assignL x a true l).2)
    | none => (S :: (assignL x a weak l).1, (assignL x a weak l).2)

def AState.assign (σ : AState A) (x : String) (a : A) : AState A × Bool :=
  match σ with
  | .bot => (.bot, false)
  | .top => (.top, true)
  | .sc l => (.sc (assignL x a false l).1, (assignL x a false l).2)

def strengthenL (x : String) (a : A) : List (Scope A) → List (Scope A)
  | [] => []
  | S :: l => match S.get x with
    | some b => if b.must then ((x, ⟨a, true⟩) :: S) :: l else S :: l
    | none => S :: strengthenL x a l

def AState.strengthen (σ : AState A) (x : String) (a : A) : AState A :=
  match σ with
  | .sc l => .sc (strengthenL x a l)
  | σ => σ

def AState.push : AState A → AState A
  | .sc l => .sc ([] :: l)
  | σ => σ

def AState.pop : AState A → AState A
  | .sc (_ :: l) => .sc l
  | .sc [] => .top
  | σ => σ

def AState.isBot : AState A → Bool
  | .bot => true
  | _ => false

end Ops

end Vsa.AbsInt
