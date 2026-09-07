import Vsa.Sim.RamReadVirtual
import Vsa.Sim.Frame

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- The fetch prelude and next-PC write preserve the load's control-state pins. -/
theorem GoodState.at_load_site {σ : Vsa.Machine.MState} (hg : GoodState σ) (pc : BitVec 64) :
    GoodState (afterNextPC (afterPrelude σ) pc) :=
  (hg.insert_nonpinned (r := Register.minstret_increment) (by decide) _).insert_nonpinned
    (r := Register.nextPC) (by decide) _

/-- Execute any scalar signed or unsigned load with its total byte value.
The destination-register write is supplied by the existing write semantics. -/
theorem execute_load_ram_scalar {σ σ' : Vsa.Machine.MState} (hg : GoodState σ)
    (off : BitVec 12) (rs rd : regidx) (unsigned : Bool) (vbase : BitVec 64)
    (k : Nat) (hk : k ≤ 3)
    (hrs : (rX_bits rs).run σ = .ok vbase σ)
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhi : (vbase + sign_extend (m := 64) off).toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ^ k ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hwr : (wX_bits rd (extend_value unsigned
      (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat (2 ^ k)))).run σ = .ok () σ') :
    (execute (instruction.LOAD (off, rs, rd, unsigned, 2 ^ k))).run σ =
      .ok RETIRE_SUCCESS σ' := by
  have hw : 2 ^ k ≤ 8 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  exact execute_load_char off rs rd unsigned (2 ^ k) _ σ σ' (by simpa [Functions.xlen_bytes] using hw)
    (vmem_read_ram_scalar hg rs (sign_extend (m := 64) off) vbase k hk hrs hlo hhi hhtif) hwr

/-- Generic total words agree with the existing four-byte load representation. -/
theorem bytesT_four_eq (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesT m a 4 = bytesT4 m a := by
  simp [bytesT, bytesT4, BitVec.append_eq, Nat.add_assoc]
  erw [BitVec.zero_width_append]
  rfl

/-- Generic total words agree with the existing eight-byte load representation. -/
theorem bytesT_eight_eq (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesT m a 8 = bytesT8 m a := by
  simp [bytesT, bytesT8, BitVec.append_eq, Nat.add_assoc]
  erw [BitVec.zero_width_append]
  rfl

/-- `ld` with total bytes, including misalignment and page crossings. -/
theorem exec_ld_ram (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (bytesT8 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 8)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, false, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply execute_load_ram_scalar (hG.at_load_site pc) off rs1 rd false vbase 3
    (by decide) hrs1 hlo hhiram hhtif
  change (wX_bits rd (sign_extend (m := 64)
    (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 8))).run
    (afterNextPC (afterPrelude σ) pc) = .ok () σ'
  rw [bytesT_eight_eq]
  exact hwr

/-- `lw` with total bytes, including misalignment and page crossings. -/
theorem exec_lw_ram (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (sign_extend (m := 64)
        (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply execute_load_ram_scalar (hG.at_load_site pc) off rs1 rd false vbase 2
    (by decide) hrs1 hlo hhiram hhtif
  change (wX_bits rd (sign_extend (m := 64)
    (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 4))).run
    (afterNextPC (afterPrelude σ) pc) = .ok () σ'
  rw [bytesT_four_eq]
  exact hwr

#print axioms exec_ld_ram
#print axioms exec_lw_ram
#print axioms GoodState.at_load_site
#print axioms execute_load_ram_scalar
#print axioms bytesT_four_eq
#print axioms bytesT_eight_eq
end Vsa.Sim
