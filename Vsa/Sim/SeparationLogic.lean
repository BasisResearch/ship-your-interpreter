import Vsa.Sim.ReprSurvival

/-! Permission resources and local memory assertions. Writable ownership is
exclusive. Read-only ownership can be shared. Every assertion depends only
on bytes in its resource, which supplies the semantic basis of framing. -/

open Vsa.MemRepr

namespace Vsa.Sim.SeparationLogic

structure Resource where
  write : Nat → Prop
  read : Nat → Prop
  disjoint : ∀ k, write k → read k → False

def Resource.support (r : Resource) (k : Nat) : Prop := r.write k ∨ r.read k

/-- Cross-resource exclusion; read/read sharing is permitted. -/
structure Compatible (r s : Resource) : Prop where
  write_write : ∀ k, r.write k → s.write k → False
  write_read : ∀ k, r.write k → s.read k → False
  read_write : ∀ k, r.read k → s.write k → False

def Resource.empty : Resource := ⟨fun _ => False, fun _ => False, fun _ h => h.elim⟩
def Resource.exclusive (P : Nat → Prop) : Resource :=
  ⟨P, fun _ => False, fun _ _ h => h.elim⟩
def Resource.shared (P : Nat → Prop) : Resource :=
  ⟨fun _ => False, P, fun _ h => h.elim⟩

theorem Resource.ext {r s : Resource}
    (hw : ∀ k, r.write k ↔ s.write k) (hr : ∀ k, r.read k ↔ s.read k) : r = s := by
  have ew : r.write = s.write := funext (fun k => propext (hw k))
  have er : r.read = s.read := funext (fun k => propext (hr k))
  cases r
  cases s
  cases ew
  cases er
  rfl

theorem Compatible.symm {r s : Resource} (h : Compatible r s) : Compatible s r :=
  ⟨fun k hs hr => h.write_write k hr hs,
   fun k hs hr => h.read_write k hr hs,
   fun k hs hr => h.write_read k hr hs⟩

theorem Compatible.empty_right (r : Resource) : Compatible r Resource.empty :=
  ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim⟩

theorem Compatible.shared (P Q : Nat → Prop) :
    Compatible (Resource.shared P) (Resource.shared Q) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ _ h => h.elim⟩

def Resource.join (r s : Resource) (h : Compatible r s) : Resource where
  write k := r.write k ∨ s.write k
  read k := r.read k ∨ s.read k
  disjoint k hw hr := by
    rcases hw with hw | hw <;> rcases hr with hr | hr
    · exact r.disjoint k hw hr
    · exact h.write_read k hw hr
    · exact h.read_write k hr hw
    · exact s.disjoint k hw hr

/-- A split records both permission compatibility and exact resource coverage. -/
structure Split (left right whole : Resource) : Prop where
  compatible : Compatible left right
  write : ∀ k, whole.write k ↔ left.write k ∨ right.write k
  read : ∀ k, whole.read k ↔ left.read k ∨ right.read k

theorem Split.join {r s : Resource} (h : Compatible r s) :
    Split r s (r.join s h) := ⟨h, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem Split.symm {r s whole : Resource} (h : Split r s whole) : Split s r whole :=
  ⟨h.compatible.symm, fun k => (h.write k).trans or_comm,
    fun k => (h.read k).trans or_comm⟩

theorem Split.support_left {r s whole : Resource} (h : Split r s whole)
    {k : Nat} (hk : r.support k) : whole.support k := by
  rcases hk with hw | hr
  · exact Or.inl ((h.write k).mpr (Or.inl hw))
  · exact Or.inr ((h.read k).mpr (Or.inl hr))

theorem Split.support_right {r s whole : Resource} (h : Split r s whole)
    {k : Nat} (hk : s.support k) : whole.support k := h.symm.support_left hk

/-- Memory locality is part of an assertion's type. Predicates that inspect
unowned bytes cannot be introduced without proving this property. -/
structure Assertion where
  holds : Mem → Resource → Prop
  stable : ∀ {m m' : Mem} {r : Resource}, AgreeP r.support m m' → holds m r → holds m' r

instance : CoeFun Assertion (fun _ => Mem → Resource → Prop) := ⟨Assertion.holds⟩

theorem Assertion.ext {P Q : Assertion}
    (h : ∀ m r, P m r ↔ Q m r) : P = Q := by
  have he : P.holds = Q.holds := funext (fun m => funext (fun r => propext (h m r)))
  cases P
  cases Q
  cases he
  rfl

def Entails (P Q : Assertion) : Prop := ∀ m r, P m r → Q m r

def emp : Assertion where
  holds _ r := r = Resource.empty
  stable _ h := h

/-- Separating conjunction splits permissions over the same concrete memory. -/
def sep (P Q : Assertion) : Assertion where
  holds m r := ∃ left right, Split left right r ∧ P m left ∧ Q m right
  stable hag h := by
    obtain ⟨left, right, hs, hp, hq⟩ := h
    exact ⟨left, right, hs,
      P.stable (fun k hk => hag k (hs.support_left hk)) hp,
      Q.stable (fun k hk => hag k (hs.support_right hk)) hq⟩

scoped infixr:70 " ∗ " => sep
scoped infix:50 " ⊢ₛ " => Entails

/-- Exact exclusive ownership of a byte footprint. -/
def owns (P : Nat → Prop) : Assertion where
  holds _ r := r = Resource.exclusive P
  stable _ h := h

/-- Exact shared read ownership of a byte footprint. -/
def reads (P : Nat → Prop) : Assertion where
  holds _ r := r = Resource.shared P
  stable _ h := h

/-- One writable byte with its concrete value. -/
def pointsTo (a : Nat) (b : BitVec 8) : Assertion where
  holds m r := r = Resource.exclusive (fun k => k = a) ∧ m[a]? = some b
  stable hag h := by
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, ?_⟩
    have ha : _ := hag a (by rw [hr]; exact Or.inl rfl)
    exact ha.symm.trans hb

/-- One immutable byte with its concrete value. -/
def readPointsTo (a : Nat) (b : BitVec 8) : Assertion where
  holds m r := r = Resource.shared (fun k => k = a) ∧ m[a]? = some b
  stable hag h := by
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, ?_⟩
    have ha : _ := hag a (by rw [hr]; exact Or.inr rfl)
    exact ha.symm.trans hb

#print axioms Resource.ext
#print axioms Compatible.symm
#print axioms Compatible.empty_right
#print axioms Compatible.shared
#print axioms Split.join
#print axioms Split.symm
#print axioms Split.support_left
#print axioms Split.support_right
#print axioms Assertion.ext

end Vsa.Sim.SeparationLogic
