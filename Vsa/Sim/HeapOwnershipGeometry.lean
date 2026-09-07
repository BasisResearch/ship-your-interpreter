import Vsa.Alloc
import Vsa.Sim.AstTransport

/-! Data-only live extent geometry and representation footprints.
These definitions do not depend on interpreter entries or allocator operations. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

abbrev Extent := Nat × Nat

/-- Live extents are nonempty, inside the arena, and pairwise disjoint. -/
def HeapArena (A : Arena) (exts : List Extent) : Prop :=
  (∀ e ∈ exts, 0 < e.2 ∧ A.contains e.1 e.2) ∧
  exts.Pairwise ExtDisjoint

/-- A byte-level representation footprint is covered by the live allocator
ledger.  Pairwise disjointness of that ledger then turns allocation ownership
into the non-aliasing facts required by mutable runtime operations. -/
def ExtentsCover (exts : List Extent) (P : Nat → Prop) : Prop :=
  ∀ a, P a → ∃ e ∈ exts, e.1 ≤ a ∧ a < e.1 + e.2

/-- The indirect bytes read by a represented value are allocator-owned.
Only strings and native names dereference the payload word; closure values
only compare the represented closure pointer stored in their value header. -/
def ValueHeapOwned (m : Vsa.MemRepr.Mem) (exts : List Extent)
    (a : Nat) : Vsa.While.Value → Prop
  | .str s => ∃ p, read64 m (a + 8) = some p ∧ (p, s.length + 1) ∈ exts
  | .native f => ∃ p, read64 m (a + 8) = some p ∧
      (p, (nativeName f).length + 1) ∈ exts
  | _ => True

/-- Heap ownership for a contiguous runtime value vector. -/
def ValuesHeapOwned (m : Vsa.MemRepr.Mem) (exts : List Extent)
    (base : Nat) (vs : List Vsa.While.Value) : Prop :=
  ∀ i, (hi : i < vs.length) → ValueHeapOwned m exts (base + 24 * i) vs[i]

/-- Complement of the three mutable windows used by an in-capacity
`env_define` append. -/
def AppendOutside (env names vals count a : Nat) : Prop :=
  (a < names + 8 * count ∨ names + 8 * count + 8 ≤ a) ∧
  (a < vals + 24 * count ∨ vals + 24 * count + 24 ≤ a) ∧
  (a < env ∨ env + 4 ≤ a)

/-- Complement of one mutable 24-byte value slot used by `env_define`'s
existing-name update arm. -/
def SetOutside (slot a : Nat) : Prop :=
  a < slot ∨ slot + 24 ≤ a

/-- Exact byte footprint of one represented frame, stated against an
arbitrary protected-address predicate. -/
structure FrameFootprintCovered (m : Vsa.MemRepr.Mem)
    (phiF : Addr → Nat) (fa : Addr) (f : Vsa.While.Frame)
    (P : Nat → Prop) : Prop where
  header : ∀ k, envHeader (phiF fa) k → P k
  slots : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv → ∀ i, i < f.vars.length →
      (∀ k, k < 8 → P (pn + 8 * i + k)) ∧
      (∀ k, valHeader (pv + 24 * i) k → P k)
  names : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ∀ q,
      read64 m (pn + 8 * i) = some q →
      ∀ k, k ≤ f.vars[i].1.length → P (q + k)
  values : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) →
      ValuePayloadCovered P m (pv + 24 * i) f.vars[i].2

/-- Exact footprint of the target frame except for one value slot. -/
structure TargetFrameFootprintCovered (m : Vsa.MemRepr.Mem)
    (phiF : Addr → Nat) (fa : Addr) (f : Vsa.While.Frame)
    (hit : Nat) (P : Nat → Prop) : Prop where
  header : ∀ k, envHeader (phiF fa) k → P k
  nameSlots : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv → ∀ i, i < f.vars.length →
      ∀ k, k < 8 → P (pn + 8 * i + k)
  names : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → ∀ q,
      read64 m (pn + 8 * i) = some q →
      ∀ k, k ≤ f.vars[i].1.length → P (q + k)
  otherValueHeaders : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv → ∀ i, i < f.vars.length →
      i ≠ hit → ∀ k, valHeader (pv + 24 * i) k → P k
  otherValues : ∀ pn pv, read64 m (phiF fa + 8) = some pn →
    read64 m (phiF fa + 16) = some pv →
    ∀ i, (hi : i < f.vars.length) → i ≠ hit →
      ValuePayloadCovered P m (pv + 24 * i) f.vars[i].2

/-- Exact byte footprint of one represented closure. -/
structure ClosureFootprintCovered (m : Vsa.MemRepr.Mem)
    (phiC : Addr → Nat) (ca : Addr) (cd : Vsa.While.ClosureData)
    (P : Nat → Prop) : Prop where
  header : ∀ k, closHeader (phiC ca) k → P k
  ast : ∀ q, read64 m (phiC ca) = some q →
    ∀ a, ExprFp m q (.fn cd.name cd.params cd.body) a → P a

end Vsa.Sim
