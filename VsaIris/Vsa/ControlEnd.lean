import VsaIris.Vsa.ControlWitness
import VsaIris.Vsa.Malloc

/-!
# The control heap's `malloc(64)` meets the assumed end condition

`MallocLocalRun` (the remaining allocator assumption) asks every malloc run to
end in `MallocEnd`, and `MallocRoomRun` in `MallocRoomEnd`. This module checks
both are satisfied by the concrete behaviour of the eb73d8c control heap: the
memory after `malloc(64)`'s top split (`Control.m64`), read as the owned image,
with the returned pointer `0x82000210` in `a0` and the ABI frame restored,
satisfies `MallocEnd` from the control's live blocks, and `MallocRoomEnd` at
zero remaining credits. Together with `live_relative_frame_admits_both` (the
write set lies in `heapFoot vsaLayout controlBlocks`, which contains the byte
`malloc(32)` writes), this is the case `no_fixed_privFoot` shows the old
contract cannot admit.
-/

namespace VsaIris.VsaHeap.Control

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap Vsa.Sim.NativeNameAudit.Control VsaIris.Inst

/-- The owned image after `malloc(64)`. -/
def img64 (a : Nat) : BitVec 8 := (m64[a]?).getD 0

theorem shape64 : vsaLayout.Shape img64 H64 :=
  (imgShape_iff (imgOn_of_getD
    (fun a ha => by
      obtain ⟨b, hb⟩ := heap_present a (foot_ram ha).1 (foot_ram ha).2
      exact writeLog_present heapMem w64 a (by rw [hb]; rfl))
    (fun _ _ => rfl))).2 ⟨_, _, _, _, post64⟩

theorem ret64_toNat : (0x82000210#64 : BitVec 64).toNat = 0x82000210 := by decide

/-- The concrete `malloc(64)` return satisfies the assumed end condition. -/
theorem malloc64_end (rv' : Nat → BitVec 64) (r s : BitVec 64) (saved : List (Nat × BitVec 64))
    (hframe : RetFrame rv' r s saved) (ha0 : rv' a0 = 0x82000210#64) :
    MallocEnd vsaLayout controlBlocks 64#64 r s saved rv' img64 where
  frame := hframe
  result := by
    right
    rw [ha0, ret64_toNat]
    exact ⟨fresh64, by decide, shape64⟩

/-- And the capacity end condition, at zero remaining credits. -/
theorem malloc64_roomEnd (maxReq : Nat) (rv' : Nat → BitVec 64) (r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (hframe : RetFrame rv' r s saved)
    (ha0 : rv' a0 = 0x82000210#64) :
    MallocRoomEnd vsaLayout (vsaRoom maxReq) controlBlocks 64#64 r s saved 0 rv' img64 := by
  have hp : (rv' a0).toNat = 0x82000210 := by rw [ha0, ret64_toNat]
  have hfresh := fresh64
  refine ⟨hframe, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact hfresh
  · rw [hp]
  · rw [hp]; exact shape64
  · rw [hp]
    obtain ⟨m, hm, _⟩ := shape64
    exact ⟨m, hm, AllocationReserve.zero _ _ _ _⟩

/-- The old contract's obstruction, at the control's live blocks. -/
theorem control_no_fixed_privFoot :
    ¬ ∃ F : Nat → Prop, F 0x82000238 ∧
      ∀ H ∈ [controlBlocks, (0x82000210, 64) :: controlBlocks], ∀ e ∈ H, ∀ a, InExt e a → ¬ F a :=
  no_fixed_privFoot controlBlocks

end VsaIris.VsaHeap.Control
