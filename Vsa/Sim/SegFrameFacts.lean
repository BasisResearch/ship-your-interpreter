import Vsa.Sim.BlockMem
import Vsa.Sim.BlockPilot

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

theorem memFacts_ld_frame (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hk : a.kind = .ld)
    (hlo : 0x80000000 ≤ (eaddrM a L).toNat)
    (hhi : (eaddrM a L).toNat + 8 ≤ 0x100000000)
    (hht : (eaddrM a L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)
    (p0 : (m[(eaddrM a L).toNat]?).getD 0 = b0) (p1 : (m[(eaddrM a L).toNat + 1]?).getD 0 = b1)
    (p2 : (m[(eaddrM a L).toNat + 2]?).getD 0 = b2) (p3 : (m[(eaddrM a L).toNat + 3]?).getD 0 = b3)
    (p4 : (m[(eaddrM a L).toNat + 4]?).getD 0 = b4) (p5 : (m[(eaddrM a L).toNat + 5]?).getD 0 = b5)
    (p6 : (m[(eaddrM a L).toNat + 6]?).getD 0 = b6) (p7 : (m[(eaddrM a L).toNat + 7]?).getD 0 = b7) :
    MemFacts m L [b0, b1, b2, b3, b4, b5, b6, b7] a := by
  unfold MemFacts; rw [hk]
  exact ⟨⟨hlo, hhi, hht⟩, p0, p1,
    p2, p3, p4,
    p5, p6, p7⟩

theorem memFacts_sd_frame (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (bs : List (BitVec 8)) (hk : a.kind = .sd)
    (hlo : 0x80000000 ≤ (eaddrM a L).toNat)
    (hhi : (eaddrM a L).toNat + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ (eaddrM a L).toNat)
    (hal : (eaddrM a L).toNat % 8 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts; rw [hk]; exact ⟨hlo, hhi, hht, hal⟩

structure FrameBundle (m : Std.ExtHashMap Nat (BitVec 8)) (base : BitVec 64) : Prop where
  lo   : 0x80000000 ≤ base.toNat
  hi   : base.toNat + 0x108 ≤ 0x100000000
  htif : tohostAddr + 16 ≤ base.toNat
  al   : base.toNat % 8 = 0

theorem frame_ea (a : MInstr) (L : GRegs) (base : BitVec 64) (off : Nat)
    (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off ≤ 0x108) (fb : FrameBundle m base) :
    (eaddrM a L).toNat = base.toNat + off := by
  unfold eaddrM
  rw [hsrc, BitVec.toNat_add, himm]
  have := fb.hi
  rw [Nat.mod_eq_of_lt (by omega)]

end Vsa.Sim
