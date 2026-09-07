import Vsa.Sim.SeparationLogic

/-! Algebra derived from exact permission splitting. Assertions are identified
through Assertion.ext; no algebraic laws are extra axioms or assumptions. -/

open Vsa.MemRepr

namespace Vsa.Sim.SeparationLogic

/-- Reassociate ((a,b),c) to (a,(b,c)), constructing the intermediate resource. -/
theorem Split.reassoc {a b ab c whole : Resource}
    (hab : Split a b ab) (hwhole : Split ab c whole) :
    ∃ bc, Split b c bc ∧ Split a bc whole := by
  have hbc : Compatible b c := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun k hb hc => hwhole.compatible.write_write k
        ((hab.write k).mpr (Or.inr hb)) hc
    · exact fun k hb hc => hwhole.compatible.write_read k
        ((hab.write k).mpr (Or.inr hb)) hc
    · exact fun k hb hc => hwhole.compatible.read_write k
        ((hab.read k).mpr (Or.inr hb)) hc
  let bc := b.join c hbc
  have ha : Compatible a bc := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hr
      rcases hr with hb | hc
      · exact hab.compatible.write_write k hk hb
      · exact hwhole.compatible.write_write k ((hab.write k).mpr (Or.inl hk)) hc
    · intro k hk hr
      rcases hr with hb | hc
      · exact hab.compatible.write_read k hk hb
      · exact hwhole.compatible.write_read k ((hab.write k).mpr (Or.inl hk)) hc
    · intro k hk hr
      rcases hr with hb | hc
      · exact hab.compatible.read_write k hk hb
      · exact hwhole.compatible.read_write k ((hab.read k).mpr (Or.inl hk)) hc
  refine ⟨bc, Split.join hbc, ⟨ha, ?_, ?_⟩⟩
  · intro k
    exact (hwhole.write k).trans ((or_congr (hab.write k) Iff.rfl).trans or_assoc)
  · intro k
    exact (hwhole.read k).trans ((or_congr (hab.read k) Iff.rfl).trans or_assoc)

/-- Reverse reassociation follows from the same construction and symmetry. -/
theorem Split.reassoc_left {a b c bc whole : Resource}
    (hbc : Split b c bc) (hwhole : Split a bc whole) :
    ∃ ab, Split a b ab ∧ Split ab c whole := by
  obtain ⟨ba, hba, hc⟩ := Split.reassoc hbc.symm hwhole.symm
  exact ⟨ba, hba.symm, hc.symm⟩

theorem Split.empty_right (r : Resource) : Split r Resource.empty r :=
  ⟨Compatible.empty_right r, fun _ => by simp [Resource.empty], fun _ => by simp [Resource.empty]⟩

theorem Split.eq_of_empty_right {r whole : Resource}
    (h : Split r Resource.empty whole) : whole = r := by
  apply Resource.ext
  · intro k
    exact (h.write k).trans (by simp [Resource.empty])
  · intro k
    exact (h.read k).trans (by simp [Resource.empty])

theorem sep_comm (P Q : Assertion) : sep P Q = sep Q P := by
  apply Assertion.ext
  intro m r
  constructor
  · rintro ⟨a, b, hs, hp, hq⟩
    exact ⟨b, a, hs.symm, hq, hp⟩
  · rintro ⟨b, a, hs, hq, hp⟩
    exact ⟨a, b, hs.symm, hp, hq⟩

theorem sep_assoc (P Q R : Assertion) : sep (sep P Q) R = sep P (sep Q R) := by
  apply Assertion.ext
  intro m r
  constructor
  · rintro ⟨ab, c, hw, ⟨a, b, hab, hp, hq⟩, hr⟩
    obtain ⟨bc, hbc, ha⟩ := hab.reassoc hw
    exact ⟨a, bc, ha, hp, b, c, hbc, hq, hr⟩
  · rintro ⟨a, bc, hw, hp, ⟨b, c, hbc, hq, hr⟩⟩
    obtain ⟨ab, hab, hc⟩ := hbc.reassoc_left hw
    exact ⟨ab, c, hc, ⟨a, b, hab, hp, hq⟩, hr⟩

theorem sep_emp (P : Assertion) : sep P emp = P := by
  apply Assertion.ext
  intro m r
  constructor
  · rintro ⟨a, b, hs, hp, hb⟩
    change b = Resource.empty at hb
    subst b
    have he := hs.eq_of_empty_right
    subst r
    exact hp
  · intro hp
    exact ⟨r, Resource.empty, Split.empty_right r, hp, rfl⟩

theorem emp_sep (P : Assertion) : sep emp P = P := by
  rw [sep_comm, sep_emp]

theorem Entails.refl (P : Assertion) : Entails P P := fun _ _ hp => hp

theorem Entails.trans {P Q R : Assertion} (hpq : Entails P Q) (hqr : Entails Q R) :
    Entails P R := fun m r hp => hqr m r (hpq m r hp)

theorem sep_mono {P P' Q Q' : Assertion} (hp : Entails P P') (hq : Entails Q Q') :
    Entails (sep P Q) (sep P' Q') := by
  rintro m r ⟨a, b, hs, hpa, hqb⟩
  exact ⟨a, b, hs, hp m a hpa, hq m b hqb⟩

/-- Read/read overlap is permitted, with exact union equal to the same resource. -/
theorem Split.shared_self (P : Nat → Prop) :
    Split (Resource.shared P) (Resource.shared P) (Resource.shared P) :=
  ⟨Compatible.shared P P, fun _ => or_self_iff.symm, fun _ => or_self_iff.symm⟩

theorem Split.eq_shared {P : Nat → Prop} {r : Resource}
    (h : Split (Resource.shared P) (Resource.shared P) r) :
    r = Resource.shared P := by
  apply Resource.ext
  · exact fun k => (h.write k).trans or_self_iff
  · exact fun k => (h.read k).trans or_self_iff

/-- Exact shared ownership is duplicable and contractible. -/
theorem reads_dup (P : Nat → Prop) : sep (reads P) (reads P) = reads P := by
  apply Assertion.ext
  intro m r
  constructor
  · rintro ⟨a, b, hs, ha, hb⟩
    change a = Resource.shared P at ha
    change b = Resource.shared P at hb
    subst a
    subst b
    exact hs.eq_shared
  · intro hr
    change r = Resource.shared P at hr
    subst r
    exact ⟨Resource.shared P, Resource.shared P, Split.shared_self P, rfl, rfl⟩

/-- Immutable byte facts duplicate together with their read permission. -/
theorem readPointsTo_dup (a : Nat) (b : BitVec 8) :
    sep (readPointsTo a b) (readPointsTo a b) = readPointsTo a b := by
  apply Assertion.ext
  intro m r
  constructor
  · rintro ⟨left, right, hs, ⟨hl, hb⟩, ⟨hr, _⟩⟩
    subst left
    subst right
    exact ⟨hs.eq_shared, hb⟩
  · rintro ⟨hr, hb⟩
    subst r
    exact ⟨_, _, Split.shared_self _, ⟨rfl, hb⟩, ⟨rfl, hb⟩⟩

/-- Nonempty exclusive ownership cannot occur on both sides of one split. -/
theorem not_exclusive_self {P : Nat → Prop} (hne : ∃ a, P a) (r : Resource) :
    ¬ Split (Resource.exclusive P) (Resource.exclusive P) r := by
  intro hs
  obtain ⟨a, ha⟩ := hne
  exact hs.compatible.write_write a ha ha

/-- A writable singleton cannot be owned twice in separating conjunction. -/
theorem owns_singleton_not_sep (a : Nat) (m : Mem) (r : Resource) :
    ¬ sep (owns (fun k => k = a)) (owns (fun k => k = a)) m r := by
  rintro ⟨left, right, hs, hl, hr⟩
  change left = Resource.exclusive (fun k => k = a) at hl
  change right = Resource.exclusive (fun k => k = a) at hr
  subst left
  subst right
  exact not_exclusive_self (P := fun k => k = a) ⟨a, rfl⟩ r hs

/-- In particular, concrete writable byte facts cannot self-separate. -/
theorem pointsTo_not_sep (a : Nat) (b c : BitVec 8) (m : Mem) (r : Resource) :
    ¬ sep (pointsTo a b) (pointsTo a c) m r := by
  rintro ⟨left, right, hs, ⟨hl, _⟩, ⟨hr, _⟩⟩
  subst left
  subst right
  exact not_exclusive_self (P := fun k => k = a) ⟨a, rfl⟩ r hs

#print axioms Split.empty_right
#print axioms Split.eq_of_empty_right
#print axioms Split.shared_self
#print axioms Split.eq_shared
#print axioms not_exclusive_self
#print axioms Split.reassoc
#print axioms Split.reassoc_left
#print axioms sep_comm
#print axioms sep_assoc
#print axioms sep_emp
#print axioms emp_sep
#print axioms Entails.refl
#print axioms Entails.trans
#print axioms sep_mono
#print axioms reads_dup
#print axioms readPointsTo_dup
#print axioms owns_singleton_not_sep
#print axioms pointsTo_not_sep

end Vsa.Sim.SeparationLogic
