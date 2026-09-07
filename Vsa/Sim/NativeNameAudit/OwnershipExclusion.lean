import Vsa.Sim.NativeNameAudit.Admission
import Vsa.Sim.RuntimeOwnership

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.NativeNameAudit

open Vsa.Sim.OutputAliasLoaded RuntimeOwnership

/-- Every ownership witness rejects the binding name overlapping the output
byte. Only the global-frame address and actual writable byte are fixed. -/
theorem nativeName_frame_not_owned
    {phiF : Addr → Nat} {fa : Addr} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (hlink : phiF fa = 0x81000000) (hw : writes 0x8001bb97)
    (hi : Immutable alloc shared readable writes) :
    ¬ FrameOwned nativeNameMem phiF alloc shared fa globalFrame := by
  intro h
  obtain ⟨a, ha⟩ := h.arrays
  have hn : a.names = 0x81000040 := Option.some.inj
    ((show read64 nativeNameMem 0x81000008 = some a.names by
      simpa only [hlink] using ha.namesRead).symm.trans nativeName_names)
  obtain ⟨q, hq, hs⟩ := ha.keys 1 (by decide)
  have hr : read64 nativeNameMem 0x81000048 = some 0x8001bb91 := by
    simp only [read64, readLE, nativeName_lookup]
    decide
  have hq' : read64 nativeNameMem 0x81000048 = some q := by
    simpa only [hn] using hq
  have he : q = 0x8001bb91 := Option.some.inj (hq'.symm.trans hr)
  have hb := hs.immutable.bytes 6 (by decide)
  have hb' : shared 0x8001bb97 := by simpa only [he] using hb
  exact hi.outsideWrites _ hb' hw

#print axioms nativeName_frame_not_owned

end Vsa.Sim.NativeNameAudit
