import Vsa.Sim.EqualityMapObstruction
import Vsa.Sim.OutputAliasMemory

/-! Independent operand-map witnesses do not imply a common representation
map. This finite-memory component example is not a loaded execution. -/

namespace Vsa.Sim.EqualityReturnMapObstruction

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While
open Vsa.Sim.OutputAliasLoaded

/-- Two closure boxes with different nonzero pointer words. -/
def byte (k : Nat) : BitVec 8 :=
  if k = 0 ∨ k = 24 then 4#8
  else if k = 8 then 8#8
  else if k = 32 then 16#8
  else 0#8

def memory : Mem := finiteMemory byte 0 48

theorem read_memory (a width : Nat) (hbound : a + width ≤ 48) :
    readLE memory a width = some (byteRead byte a width) :=
  finiteMemory_readLE byte 0 48 a width (Nat.zero_le _) hbound

/-- The same source index can be represented in either box by choosing its
map independently. The finite-memory read theorem supplies every byte. -/
theorem closure_box (N : NativeAddrs) (a pointer : Nat)
    (hbound : a + 16 ≤ 48)
    (htag : byteRead byte a 4 = 4)
    (hptr : byteRead byte (a + 8) 8 = pointer) (hnz : pointer ≠ 0) :
    ValueRepr memory N (fun _ => pointer) a (.closure 0) := by
  refine ⟨?_, ?_, hnz⟩
  · exact (read_memory a 4 (by omega)).trans (congrArg some htag)
  · exact (read_memory (a + 8) 8 (by omega)).trans (congrArg some hptr)

/-- Empty-prefix extensions and separate operand representations hold, but
there is no single map representing both copies of source closure zero. -/
theorem separate_maps_without_common_map (N : NativeAddrs) :
    ∃ left right : Addr → Nat,
      PhiExtends (fun _ => 0) left 0 ∧ PhiExtends (fun _ => 0) right 0 ∧
      ValueRepr memory N left 0 (.closure 0) ∧
      ValueRepr memory N right 24 (.closure 0) ∧
      ¬ (∃ common : Addr → Nat,
        ValueRepr memory N common 0 (.closure 0) ∧
        ValueRepr memory N common 24 (.closure 0)) := by
  have hl := closure_box N 0 8 (by decide) (by decide) (by decide) (by decide)
  have hr := closure_box N 24 16 (by decide) (by decide) (by decide) (by decide)
  refine ⟨(fun _ => 8), (fun _ => 16), (fun _ h => by omega),
    (fun _ h => by omega), hl, hr, ?_⟩
  rintro ⟨common, hleft, hright⟩
  obtain ⟨_, hleftRead, _⟩ := hleft
  obtain ⟨_, hrightRead, _⟩ := hright
  obtain ⟨_, hlRead, _⟩ := hl
  obtain ⟨_, hrRead, _⟩ := hr
  have h8 : 8 = common 0 := Option.some.inj (hlRead.symm.trans hleftRead)
  have h16 : 16 = common 0 := Option.some.inj (hrRead.symm.trans hrightRead)
  omega

end Vsa.Sim.EqualityReturnMapObstruction
