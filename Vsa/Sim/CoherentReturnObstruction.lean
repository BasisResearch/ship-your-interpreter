import Vsa.Sim.CoherentReturn
import Vsa.Sim.EqualityReturnMapObstruction

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.EqualityReturnMapObstruction

/-- The new return contract rejects the two incompatible closure boxes even
when ownership and the entry-prefix constraints carry no extra information. -/
theorem reject_incoherent_return (N : NativeAddrs) (A : Arena)
    (entryF entryC : Addr → Nat) (store : Store) (writes : Nat → Prop) :
    ¬ ∃ resultF resultC, ReturnRepr N A entryF entryC resultF resultC 0 0 store
      [(0, .closure 0), (24, .closure 0)] (fun _ _ _ => True) writes memory := by
  obtain ⟨_, _, _, _, _, _, hno⟩ := separate_maps_without_common_map N
  rintro ⟨_, resultC, h⟩
  exact hno ⟨resultC, h.values _ _ (by simp), h.values _ _ (by simp)⟩

#print axioms reject_incoherent_return

end Vsa.Sim.EqualityReturnMapObstruction
