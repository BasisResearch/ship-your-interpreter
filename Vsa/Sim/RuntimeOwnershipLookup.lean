import Vsa.Sim.EnvGetSpec5
import Vsa.Sim.RuntimeOwnershipCopy
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- The first matching binding and its represented, owned source slot.
The frame may be any terminal frame of the lookup's parent chain. -/
structure EnvGetOwnedSource
    (m : Mem) (N : NativeAddrs) (φf φc : Addr → Nat) (shared : Nat → Prop)
    (s : Store) (x : String) (v : Value) (fa : Addr) (f : Vsa.While.Frame)
    (i pv : Nat) : Prop where
  frame : s.frames[fa]? = some f
  index : i < f.vars.length
  binding : f.vars[i] = (x, v)
  first : ∀ j, (hj : j < i) → (f.vars[j]'(Nat.lt_trans hj index)).1 ≠ x
  values : read64 m (φf fa + 16) = some pv
  repr : ValueRepr m N φc (pv + 24 * i) v
  owned : ValueOwned m shared (pv + 24 * i) v

/-- Store ownership supplies the payload at the semantic lookup's terminal
source slot. No machine execution or payload geometry is assumed. -/
theorem RuntimeOwnership.StoreOwned.lookupSource
    {m : Mem} {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {alloc : Allocations} {shared : Nat → Prop} {s : Store}
    (hown : StoreOwned m φf φc alloc shared s)
    (hrepr : StoreRepr m N A φf φc s)
    {env : Addr} {x : String} {v : Value}
    (hget : s.get? env x = some v) :
    ∃ fa f i pv, EnvGetOwnedSource m N φf φc shared s x v fa f i pv := by
  obtain ⟨_, fa, f, hframe, hfirst⟩ := get?_terminal_first hget
  obtain ⟨hfa, helem⟩ := Array.getElem?_eq_some_iff.mp hframe
  have hfr : FrameRepr m N φf φc (φf fa) f := by
    simpa only [helem] using hrepr.frames fa hfa
  have hfo : FrameOwned m φf alloc shared fa f := by
    simpa only [helem] using hown.frames fa hfa
  obtain ⟨i, hi, hpair, hbefore⟩ := hfirst.index
  obtain ⟨pv, hpv, hvalue⟩ := frame_slot_valueRepr m N φf φc (φf fa) f i hfr hi
  have howned := hfo.values pv hpv i hi
  refine ⟨fa, f, i, pv, hframe, hi, hpair, hbefore, hpv, ?_, ?_⟩
  · simpa only [hpair] using hvalue
  · simpa only [hpair] using howned

/-- The actual copy preserves the selected binding's owned payload. -/
theorem EnvGetOwnedSource.copy_owned
    {m m' : Mem} {N : NativeAddrs} {φf φc : Addr → Nat} {shared : Nat → Prop}
    {s : Store} {x : String} {v : Value} {fa : Addr} {f : Vsa.While.Frame} {i pv dst : Nat}
    (h : EnvGetOwnedSource m N φf φc shared s x v fa f i pv)
    (hcopy : ∀ k, k < 24 → m'[dst + k]? = some ((m[pv + 24 * i + k]?).getD 0))
    (hag : AgreeP shared m m') : ValueOwned m' shared dst v :=
  h.owned.copy_total hcopy hag

/-- Ownership supplies the guarded payload premise of the copy contracts. -/
theorem RuntimeOwnership.ValueOwned.payload_disjoint
    {m : Mem} {shared : Nat → Prop} {src dst : Nat} {v : Value}
    (h : ValueOwned m shared src v)
    (hoff : ∀ k, shared k → k < dst ∨ dst + 24 ≤ k)
    (p : Nat) (s : String) (hp : read64 m (src + 8) = some p)
    (hps : ValuePayload v s) :
    ∀ k, k ≤ s.length → p + k < dst ∨ dst + 24 ≤ p + k := by
  have hcovered := h.covered hoff
  cases v <;> simp only [ValuePayload] at hps
  all_goals subst s; exact hcovered p hp

/-- The selected terminal binding supplies the hit-tail payload separation. -/
theorem EnvGetOwnedSource.payload_disjoint
    {m : Mem} {N : NativeAddrs} {φf φc : Addr → Nat} {shared : Nat → Prop}
    {s : Store} {x : String} {v : Value} {fa : Addr} {f : Vsa.While.Frame} {i pv dst : Nat}
    (h : EnvGetOwnedSource m N φf φc shared s x v fa f i pv)
    (hoff : ∀ k, shared k → k < dst ∨ dst + 24 ≤ k) :
    ∀ p t, read64 m (pv + 24 * i + 8) = some p → ValuePayload v t →
      ∀ k, k ≤ t.length → p + k < dst ∨ dst + 24 ≤ p + k :=
  h.owned.payload_disjoint hoff

/-- An occupied array slot lies inside its allocation's arena. -/
theorem RuntimeOwnership.ArrayOwned.slot_in_arena
    {A : Arena} {exts : List Extent} {alloc : Allocations} {role : Role}
    {p width cap i : Nat} (h : ArrayOwned alloc role p width cap)
    (hl : Ledger A exts alloc) (hi : i < cap) :
    A.contains (p + width * i) width := by
  have ha := h.nonempty (Nat.zero_lt_of_lt hi)
  have hb := (hl.arena.1 _ (hl.live _ _ _ ha)).2
  have hs : width * i + width ≤ width * cap := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      Nat.mul_le_mul_left width (show i + 1 ≤ cap by omega)
  change A.lo ≤ p ∧ p + width * cap ≤ A.hi at hb
  exact ⟨by omega, by omega⟩

/-- A represented frame's actual values pointer selects an arena-resident slot. -/
theorem RuntimeOwnership.FrameOwned.value_slot_in_arena
    {m : Mem} {φf : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame} {A : Arena} {exts : List Extent} {pv i : Nat}
    (h : FrameOwned m φf alloc shared fa f) (hl : Ledger A exts alloc)
    (hpv : read64 m (φf fa + 16) = some pv) (hi : i < f.vars.length) :
    A.contains (pv + 24 * i) 24 := by
  obtain ⟨a, ha⟩ := h.arrays
  have he : a.values = pv := Option.some.inj (ha.valuesRead.symm.trans hpv)
  have hfit : i < a.cap := Nat.lt_of_lt_of_le hi ha.bound
  simpa only [he] using ha.values.slot_in_arena hl hfit

/-- The semantic binding count fits the signed machine scan bound. -/
theorem RuntimeOwnership.FrameOwned.length_signed
    {m : Mem} {φf : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame} {A : Arena} {exts : List Extent}
    (h : FrameOwned m φf alloc shared fa f) (hl : Ledger A exts alloc)
    (hhi : A.hi ≤ 2^32) : f.vars.length < 2^31 := by
  obtain ⟨a, ha⟩ := h.arrays
  exact Nat.lt_of_le_of_lt ha.bound (h.capSigned hl ha.capRead hhi)

/-- Source-word access used by the hit-tail copy. The selected slot is the
same one represented and owned by `EnvGetOwnedSource`. -/
structure EnvGetSourceAccess (m : Mem) (A : Arena) (pv i : Nat) : Prop where
  words : ValueWordsTotal m (pv + 24 * i)
  arena : A.contains (pv + 24 * i) 24
  aligned : (pv + 24 * i) % 8 = 0
  indexSigned : i < 2^31

theorem EnvGetOwnedSource.access
    {m : Mem} {N : NativeAddrs} {φf φc : Addr → Nat} {shared : Nat → Prop}
    {s : Store} {x : String} {v : Value} {fa : Addr} {f : Vsa.While.Frame} {i pv : Nat}
    {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : EnvGetOwnedSource m N φf φc shared s x v fa f i pv)
    (hown : StoreOwned m φf φc alloc shared s)
    (hl : Ledger A exts alloc) (hready : StoreArraysReady m φf s)
    (hhi : A.hi ≤ 2^32) : EnvGetSourceAccess m A pv i := by
  obtain ⟨hfa, helem⟩ := Array.getElem?_eq_some_iff.mp h.frame
  have hfo : FrameOwned m φf alloc shared fa f := by
    simpa only [helem] using hown.frames fa hfa
  have hi : i < s.frames[fa].vars.length := by
    simpa only [helem] using h.index
  have halign := hready.valuesAligned fa hfa pv h.values
  exact
    { words := hready.valueWords fa hfa pv h.values i hi
      arena := hfo.value_slot_in_arena hl h.values h.index
      aligned := by omega
      indexSigned := Nat.lt_trans h.index (hfo.length_signed hl hhi) }

#print axioms EnvGetOwnedSource.access
#print axioms RuntimeOwnership.FrameOwned.length_signed
#print axioms RuntimeOwnership.StoreOwned.lookupSource
#print axioms EnvGetOwnedSource.copy_owned
#print axioms RuntimeOwnership.ValueOwned.payload_disjoint
#print axioms EnvGetOwnedSource.payload_disjoint
#print axioms RuntimeOwnership.ArrayOwned.slot_in_arena
#print axioms RuntimeOwnership.FrameOwned.value_slot_in_arena

end Vsa.Sim
