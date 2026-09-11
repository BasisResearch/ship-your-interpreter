import Vsa.Sim.MemcpyCopyDispatch

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- Execute memcpy for the actual aligned allocation, every source alignment,
and every positive length within the supplied RAM regions. -/
theorem run {dst src r : BitVec 64} {n : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : Input dst src r n bs m0 before)
    (align : dst.toNat % 8 = 0) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned dst src r n bs m0) before after := by
  by_cases matching : (src.toNat ^^^ dst.toNat) % 8 = 0
  · obtain ⟨matched, matchSteps, matchState⟩ := matchedEntry h matching
    obtain ⟨tested, testSteps, testState⟩ := lengthTest matchState.state
    by_cases small : n < 8
    · obtain ⟨selected, selectSteps, selectState⟩ := smallEntry testState.state small
      obtain ⟨entered, entrySteps, entryState⟩ := byteEntry selectState.state
      obtain ⟨after, copySteps, returned⟩ := bytesReturn entryState.state retAlign
      exact ⟨after, matchSteps.trans (testSteps.trans (selectSteps.trans (entrySteps.trans copySteps))),
        matchState.then (testState.then (selectState.then (entryState.then returned)))⟩
    · obtain ⟨entered, entrySteps, entryState⟩ := largeEntry testState.state (by omega) align
      obtain ⟨after, copySteps, returned⟩ := bulkReturn entryState.state retAlign
      exact ⟨after, matchSteps.trans (testSteps.trans (entrySteps.trans copySteps)),
        matchState.then (testState.then (entryState.then returned))⟩
  · exact misaligned h matching retAlign

#print axioms run

end Vsa.Sim.MemcpyCopy
