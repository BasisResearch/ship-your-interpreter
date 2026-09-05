import Vsa.Sim.ErrorSimFull

/-!
# Impossible dangling closure at call entry

`CallEntryI` requires every closure-valued callee to be bounded by the semantic
closure array.  A bounded array index cannot simultaneously have lookup
`none`, so the specification's dangling-closure error constructor is
unreachable at the indexed machine boundary.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr (Mem)
open Vsa.RuntimeRepr (NativeAddrs Arena)
open Vsa.Alloc (StackLayout)
open Vsa.While (Addr Value)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- The exact `ErrorCasesI.hBadClosure` field, discharged because its indexed
machine entry contradicts the missing semantic closure. -/
theorem callErr_badClosure_impossible
    (g : (R : Register) → Option (RegisterType R)) (m0 : Mem) :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (vs : List Value),
      st.store.closures[a]? = none →
      CallErrI g m0 st d (.closure a) vs := by
  intro st d a vs hMissing N A SL φf φc dLeft aLeft sp sret c hEntry
  have ha : a < st.store.closures.size := by
    simpa only [ValueClosuresBounded] using hEntry.valueBounded
  have hPresent : st.store.closures[a]? = some st.store.closures[a] :=
    Array.getElem?_eq_getElem ha
  rw [hPresent] at hMissing
  simp at hMissing

#print axioms callErr_badClosure_impossible

end Vsa.Sim
