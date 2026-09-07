import Vsa.RuntimeRepr
import Vsa.Sim.Regions

/-!
Bytes excluded from immutable AST ownership at interpreter entry.

The ELF interval covers its writable sections for the fixed proof binary
(SHA256 b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0).
The remaining intervals are the supplied stack, arena, and initial global
environment, including both arrays through their full capacity.

The memory parameter is the initial snapshot: array bounds remain frozen
when transporting AST reads to later memories. This predicate states only
data separation; it does not assert that execution respects these bounds.
-/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim

/-- The concrete union of mutable bytes excluded from AST read footprints.
Array membership requires successful reads of the initial capacity and base;
the representation invariant separately supplies those reads. -/
def AstMutableByte (m : Mem) (SL : StackLayout) (A : Arena)
    (globalEnv k : Nat) : Prop :=
  (0x8001ad00 ≤ k ∧ k < 0x8001c168) ∨
  (SL.lo ≤ k ∧ k < SL.hi) ∨
  (A.lo ≤ k ∧ k < A.hi) ∨
  mem_region k (globalEnv, 32) ∨
  (∃ cap names, read32 m (globalEnv + 4) = some cap ∧
    read64 m (globalEnv + 8) = some names ∧
    mem_region k (names, 8 * cap)) ∨
  (∃ cap values, read32 m (globalEnv + 4) = some cap ∧
    read64 m (globalEnv + 16) = some values ∧
    mem_region k (values, 24 * cap))

namespace AstMutableByte

variable {m : Mem} {SL : StackLayout} {A : Arena} {globalEnv k : Nat}

theorem of_elf (h : 0x8001ad00 ≤ k ∧ k < 0x8001c168) :
    AstMutableByte m SL A globalEnv k :=
  Or.inl h

theorem of_stack (h : SL.lo ≤ k ∧ k < SL.hi) :
    AstMutableByte m SL A globalEnv k :=
  Or.inr (Or.inl h)

theorem of_arena (h : A.lo ≤ k ∧ k < A.hi) :
    AstMutableByte m SL A globalEnv k :=
  Or.inr (Or.inr (Or.inl h))

theorem of_global_header (h : mem_region k (globalEnv, 32)) :
    AstMutableByte m SL A globalEnv k :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem of_global_names {cap names : Nat}
    (hcap : read32 m (globalEnv + 4) = some cap)
    (hnames : read64 m (globalEnv + 8) = some names)
    (hk : mem_region k (names, 8 * cap)) :
    AstMutableByte m SL A globalEnv k :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cap, names, hcap, hnames, hk⟩))))

theorem of_global_values {cap values : Nat}
    (hcap : read32 m (globalEnv + 4) = some cap)
    (hvalues : read64 m (globalEnv + 16) = some values)
    (hk : mem_region k (values, 24 * cap)) :
    AstMutableByte m SL A globalEnv k :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨cap, values, hcap, hvalues, hk⟩))))

/-- A reached memory frame restricts to any owned byte predicate. The mutable
set is evaluated in the initial snapshot `m`, not in either later memory. -/
theorem agree_on_owned {P : Nat → Prop} {before after : Mem}
    (hframe : ∀ a, ¬ AstMutableByte m SL A globalEnv a →
      before[a]? = after[a]?)
    (howned : ∀ a, P a → ¬ AstMutableByte m SL A globalEnv a) :
    ∀ a, P a → before[a]? = after[a]? :=
  fun a ha => hframe a (howned a ha)

/-- Region form of ownership-based byte agreement. -/
theorem agreeOn_of_owned {r : Region} {before after : Mem}
    (hframe : ∀ a, ¬ AstMutableByte m SL A globalEnv a →
      before[a]? = after[a]?)
    (howned : ∀ a, mem_region a r → ¬ AstMutableByte m SL A globalEnv a) :
    AgreeOn r before after :=
  agree_on_owned hframe howned

end AstMutableByte

end Vsa.Sim
