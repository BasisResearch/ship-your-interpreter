import Vsa.Sim.RuntimeOwnership
import Vsa.Sim.EnvNewSuccessSuffix

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.RuntimeOwnership

/-- The actual env_new initialization stores produce canonical NULL arrays.
The caller supplies only the allocated record and its semantic address map. -/
theorem frameOwned_of_envNewSuccess
    {esp p par r savedS0 : BitVec 64} {before after : Config}
    {phiF : Vsa.While.Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Vsa.While.Addr} {parent : Option Vsa.While.Addr}
    (h : EnvNewSuccessPost esp p par r savedS0 before after)
    (hlink : phiF fa = p.toNat)
    (hr : Allocated alloc (.frame fa) p.toNat 32) :
    FrameOwned after.σ.mem phiF alloc shared fa ⟨parent, []⟩ := by
  have hm : after.σ.mem = writeMap8 (writeMap8 (writeMap8
      (writeMap8 before.σ.mem (p.toNat + 24) (sdData_val par))
      p.toNat (sdData_val 0#64)) (p.toNat + 8) (sdData_val 0#64))
      (p.toNat + 16) (sdData_val 0#64) := by
    simpa [envNewSuccessLog, writeLog, applyW] using h.mem
  apply FrameOwned.empty (by simpa only [hlink] using hr) rfl
  · rw [hlink, hm, read32_writeMap8_disjoint _ _ _ _ (by omega),
      read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap8_hi,
      sdData_val_zero_toNat]
  · rw [hlink, hm, read64_writeMap8_disjoint _ _ _ _ (by omega),
      read64_writeMap8, sdData_val_zero_toNat]
  · rw [hlink, hm, read64_writeMap8, sdData_val_zero_toNat]

#print axioms frameOwned_of_envNewSuccess

end Vsa.Sim.RuntimeOwnership
