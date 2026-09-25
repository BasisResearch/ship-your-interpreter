import VsaIris.Interp.TopBoundary
import VsaIris.Interp.CallNative

/-!
# The boundary's facts the case lemmas take (lane A)

`TermSupply`/`StuckSupply` (`TermSim.lean`, `StuckSim.lean`) name a few facts
about the native table and `struct Interp`'s placement. All of them are read
off `Loaded`: the natives' entries (`InterpRunPhysicalFacts.native_addrs`) and
`in = interpObject` (`interp_local`).
-/

namespace VsaIris.Interp

open Vsa.While Vsa.RuntimeRepr Vsa.Sim.LayoutInstance

theorem nativeEntries_of {N : NativeAddrs}
    (h : N.print = 0x80002ed4 ∧ N.println = 0x80002f7c ∧ N.assert = 0x80002df4) :
    NativeEntries N := ⟨h.1, h.2.1, h.2.2⟩

theorem nativeInj_of {N : NativeAddrs} (h : NativeEntries N) : NativeInj N := by
  intro f g hfg
  have hp := h.print; have hl := h.println; have ha := h.assert
  cases f <;> cases g <;> simp only [NativeAddrs.addr] at hfg <;> first | rfl | omega

/-- `struct Interp`'s placement at the boundary. -/
theorem interpObject_toNat : (BitVec.ofNat 64 interpObject).toNat = interpObject := by decide

theorem inpGeom_top : Newlib.RtErr.InpGeom (BitVec.ofNat 64 interpObject) :=
  ⟨by rw [interpObject_toNat]; decide, by rw [interpObject_toNat]; decide⟩

theorem inpLt_top : interpObject < 2 ^ 64 := by decide

theorem inpAl_top : interpObject % 8 = 0 := by decide

end VsaIris.Interp
