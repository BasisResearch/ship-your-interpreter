import Vsa.Sim.Code.FixedImage
import Vsa.Sim.BinopChainGen
import Vsa.Sim.EvalBinSim4
import Vsa.Sim.EvalMulChain
import Vsa.Sim.EvalDivChain
import Vsa.Sim.EvalGeChain

namespace Vsa.Sim.Code
open Vsa.MemRepr Vsa.Sim.Code

/-- A bounded byte image supplies a complete four-byte slot. -/
theorem FixedBytesLoaded.slotPinned {m : Mem} {base size : Nat}
    {byte : Nat → BitVec 8} (h : FixedBytesLoaded base size byte m)
    (a : BitVec 64) (hlo : base ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ base + size) :
    SlotPinned a (byte (a.toNat - base)) (byte (a.toNat - base + 1))
      (byte (a.toNat - base + 2)) (byte (a.toNat - base + 3)) m := by
  have pin (i : Nat) (hi : i < 4) :
      m[a.toNat + i]? = some (byte (a.toNat - base + i)) := by
    have hb := h (a.toNat - base + i) (by omega)
    have ha : base + (a.toNat - base + i) = a.toNat + i := by omega
    rw [ha] at hb
    exact hb
  have hzero := pin 0 (by decide)
  simp only [Nat.add_zero] at hzero
  exact ⟨hzero, pin 1 (by decide), pin 2 (by decide), pin 3 (by decide)⟩

/-- Project a complete slot contained in the fixed read-only image. -/
theorem FixedRodataLoaded.slotPinned {m : Mem} (h : FixedRodataLoaded m)
    (a : BitVec 64) (hlo : 0x80018be0 ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ 0x8001acf0) :
    SlotPinned a
      (fixedRodataByte (a.toNat - 0x80018be0))
      (fixedRodataByte (a.toNat - 0x80018be0 + 1))
      (fixedRodataByte (a.toNat - 0x80018be0 + 2))
      (fixedRodataByte (a.toNat - 0x80018be0 + 3)) m :=
  FixedBytesLoaded.slotPinned h a hlo hhi

theorem FixedRodataLoaded.addSlot {m : Mem} (h : FixedRodataLoaded m) :
    AddSlotPinned m := h.slotPinned 0x80019f84#64 (by decide) (by decide)

theorem FixedRodataLoaded.subSlot {m : Mem} (h : FixedRodataLoaded m) :
    SubSlotPinned m := h.slotPinned 0x80019f88#64 (by decide) (by decide)

theorem FixedRodataLoaded.mulSlot {m : Mem} (h : FixedRodataLoaded m) :
    MulSlotPinned m := h.slotPinned 0x80019f8c#64 (by decide) (by decide)

theorem FixedRodataLoaded.divSlot {m : Mem} (h : FixedRodataLoaded m) :
    DivSlotPinned m := h.slotPinned 0x80019f90#64 (by decide) (by decide)

theorem FixedRodataLoaded.modSlot {m : Mem} (h : FixedRodataLoaded m) :
    SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8 m :=
  h.slotPinned 0x80019f94#64 (by decide) (by decide)

theorem FixedRodataLoaded.ltSlot {m : Mem} (h : FixedRodataLoaded m) :
    LtSlotPinned m := h.slotPinned 0x80019fa8#64 (by decide) (by decide)

theorem FixedRodataLoaded.leSlot {m : Mem} (h : FixedRodataLoaded m) :
    LeSlotPinned m := h.slotPinned 0x80019fac#64 (by decide) (by decide)

theorem FixedRodataLoaded.gtSlot {m : Mem} (h : FixedRodataLoaded m) :
    GtSlotPinned m := h.slotPinned 0x80019fb0#64 (by decide) (by decide)

theorem FixedRodataLoaded.geSlot {m : Mem} (h : FixedRodataLoaded m) :
    GeSlotPinned m := h.slotPinned 0x80019fb4#64 (by decide) (by decide)

#print axioms FixedBytesLoaded.slotPinned
#print axioms FixedRodataLoaded.slotPinned
#print axioms FixedRodataLoaded.addSlot
#print axioms FixedRodataLoaded.subSlot
#print axioms FixedRodataLoaded.mulSlot
#print axioms FixedRodataLoaded.divSlot
#print axioms FixedRodataLoaded.modSlot
#print axioms FixedRodataLoaded.ltSlot
#print axioms FixedRodataLoaded.leSlot
#print axioms FixedRodataLoaded.gtSlot
#print axioms FixedRodataLoaded.geSlot
end Vsa.Sim.Code
