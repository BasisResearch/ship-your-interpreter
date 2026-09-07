import Vsa.Sim.RamReadLoad

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Generic total words agree with the existing halfword representation. -/
theorem bytesT_two_eq (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) :
    bytesT m a 2 = bytesT2 m a := by
  simp [bytesT, bytesT2, BitVec.append_eq]
  erw [BitVec.zero_width_append]
  rfl

/-- Name the scalar load result without imposing data alignment. -/
theorem exec_load_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12)
    (rs rd : regidx) (unsigned : Bool) (k : Nat) (hk : k ≤ 3)
    (σ' : Vsa.Machine.MState) (vbase value : BitVec 64) (hg : GoodState σ)
    (hrs : (rX_bits rs).run (afterNextPC (afterPrelude σ) pc) =
      .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : extend_value unsigned
      (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat (2 ^ k)) = value)
    (hwr : (wX_bits rd value).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhi : (vbase + sign_extend (m := 64) off).toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ^ k ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs, rd, unsigned, 2 ^ k))).run
      (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ' := by
  apply execute_load_ram_scalar (hg.at_load_site pc) off rs rd unsigned vbase k hk hrs hlo hhi hhtif
  change (wX_bits rd (extend_value unsigned
    (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat (2 ^ k)))).run
    (afterNextPC (afterPrelude σ) pc) = .ok () σ'
  rw [hv]
  exact hwr

/-- `ld` with a named loaded value and unrestricted data alignment. -/
theorem exec_ld_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT8 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 8)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, false, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_load_ramv σ pc off rs1 rd false 3 (by decide) σ' vbase v hG hrs1 ?_ hwr hlo hhiram hhtif
  change (sign_extend (m := 64) (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 8) : BitVec 64) = v
  rw [bytesT_eight_eq]
  exact hv

#print axioms exec_ld_ramv
/-- `lw` with a named loaded value and unrestricted data alignment. -/
theorem exec_lw_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, false, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_load_ramv σ pc off rs1 rd false 2 (by decide) σ' vbase v hG hrs1 ?_ hwr hlo hhiram hhtif
  change (sign_extend (m := 64) (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 4) : BitVec 64) = v
  rw [bytesT_four_eq]
  exact hv

#print axioms exec_lw_ramv
/-- `lwu` with a named loaded value and unrestricted data alignment. -/
theorem exec_lwu_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (zero_extend (m := 64)
      (bytesT4 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 4)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_load_ramv σ pc off rs1 rd true 2 (by decide) σ' vbase v hG hrs1 ?_ hwr hlo hhiram hhtif
  change (zero_extend (m := 64) (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 4) : BitVec 64) = v
  rw [bytesT_four_eq]
  exact hv

#print axioms exec_lwu_ramv
/-- `lh` with a named loaded value and unrestricted data alignment. -/
theorem exec_lh_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (sign_extend (m := 64)
      (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, false, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_load_ramv σ pc off rs1 rd false 1 (by decide) σ' vbase v hG hrs1 ?_ hwr hlo hhiram hhtif
  change (sign_extend (m := 64) (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 2) : BitVec 64) = v
  rw [bytesT_two_eq]
  exact hv

#print axioms exec_lh_ramv
/-- `lhu` with a named loaded value and unrestricted data alignment. -/
theorem exec_lhu_ramv (σ : Vsa.Machine.MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : Vsa.Machine.MState) (vbase : BitVec 64) (v : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hv : (zero_extend (m := 64)
      (bytesT2 σ.mem (vbase + sign_extend (m := 64) off).toNat : BitVec (8 * 2)) : BitVec 64) = v)
    (hwr : (wX_bits rd v).run (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat) :
    (execute (instruction.LOAD (off, rs1, rd, true, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
  apply exec_load_ramv σ pc off rs1 rd true 1 (by decide) σ' vbase v hG hrs1 ?_ hwr hlo hhiram hhtif
  change (zero_extend (m := 64) (bytesT σ.mem (vbase + sign_extend (m := 64) off).toNat 2) : BitVec 64) = v
  rw [bytesT_two_eq]
  exact hv

#print axioms exec_lhu_ramv

#print axioms bytesT_two_eq
#print axioms exec_load_ramv
end Vsa.Sim
