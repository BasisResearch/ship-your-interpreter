import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part25
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part24
import Vsa.Sim.DecodeTable.Batch05Part23
import Vsa.Sim.DecodeTable.Batch07Part02
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part18
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites

/-!
# Layer 3 — per-site observational step lemmas for `memcpy`'s small word-copy loop

One observational-step (`StepObs`) lemma per instruction of the **small word-copy
loop** at `[0x80006bfc, 0x80006c38]` (the 8-byte-granularity copy used when the
source and destination are congruent mod 8, both aligned, and `n` is not large
enough to hit the unrolled ×8 loop).

Loop body / prologue (little-endian byte order noted per word):

| pc  | word     | mnemonic       | AST | class |
|-----|----------|----------------|-----|-------|
| bfc | 00058693 | mv a3,a1       | ITYPE(0x000,x11,x13,ADDI) | ALU |
| c00 | 00070793 | mv a5,a4       | ITYPE(0x000,x14,x15,ADDI) | ALU |
| c04 | 02c77a63 | bgeu a4,a2     | BTYPE(0x0034,x12,x14,BGEU) | BRANCH |
| c08 | 0005b683 | ld a6,0(a3)    | LOAD(0x000,x13,x16,false,8) | LOAD |
| c0c | 00878793 | addi a5,a5,8   | ITYPE(0x008,x15,x15,ADDI) | ALU |
| c10 | 00868693 | addi a3,a3,8   | ITYPE(0x008,x13,x13,ADDI) | ALU |
| c14 | ff07bc23 | sd a6,-8(a5)   | STORE(0xff8,x16,x15,8) | STORE |
| c18 | fec7e8e3 | bltu a5,a2     | BTYPE(0x1ff0,x12,x15,BLTU) | BRANCH |
| c38 | 01176863 | bltu a4,a7     | BTYPE(0x0010,x17,x14,BLTU) | BRANCH |

The `ld`/`sd` sites reuse the width-8 `DemoLoad`/`DemoStore` recipe
(`vmem_read_data_eight` + `execute_load_signed_char`; `vmem_write_addr_8` +
`execute_STORE_char`). BLTU characters come from `ExecuteBranch.lean`
(`execute_btype_bltu_{taken,nottaken}`); BGEU from `Vsa.Sim.DivSites` (as in
`MemcpySites.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bfc memcpy_at_80006c00 memcpy_at_80006c04
  memcpy_at_80006c08 memcpy_at_80006c0c memcpy_at_80006c10 memcpy_at_80006c14
  memcpy_at_80006c18 memcpy_at_80006c38)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts (little-endian) -/

theorem w_bfc_word : (((0x00#8).append (0x05#8)).append (0x86#8)).append (0x93#8) = (0x00058693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_bfc_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x86#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c00_word : (((0x00#8).append (0x07#8)).append (0x07#8)).append (0x93#8) = (0x00070793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c00_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c04_word : (((0x02#8).append (0xc7#8)).append (0x7a#8)).append (0x63#8) = (0x02c77a63#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c04_notrvc : Sail.BitVec.extractLsb ((((0x02#8).append (0xc7#8)).append (0x7a#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c08_word : (((0x00#8).append (0x06#8)).append (0xb8#8)).append (0x03#8) = (0x0006b803#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c08_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0xb8#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c0c_word : (((0x00#8).append (0x87#8)).append (0x87#8)).append (0x93#8) = (0x00878793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c0c_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x87#8)).append (0x87#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c10_word : (((0x00#8).append (0x86#8)).append (0x86#8)).append (0x93#8) = (0x00868693#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c10_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x86#8)).append (0x86#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c14_word : (((0xff#8).append (0x07#8)).append (0xbc#8)).append (0x23#8) = (0xff07bc23#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c14_notrvc : Sail.BitVec.extractLsb ((((0xff#8).append (0x07#8)).append (0xbc#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c18_word : (((0xfe#8).append (0xc7#8)).append (0xe8#8)).append (0xe3#8) = (0xfec7e8e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c18_notrvc : Sail.BitVec.extractLsb ((((0xfe#8).append (0xc7#8)).append (0xe8#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_c38_word : (((0x01#8).append (0x17#8)).append (0x68#8)).append (0x63#8) = (0x01176863#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem w_c38_notrvc : Sail.BitVec.extractLsb ((((0x01#8).append (0x17#8)).append (0x68#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Width-8 load/store helpers (little-endian 8-byte value and byte-insert chain) -/

/-- The 8-byte little-endian loaded value at `[a, a+8)`: `b0` is the byte at `a`.
Mirrors `DemoLoad.ldData` (kept local; `DemoLoad` is not imported here). -/
abbrev ldData8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec (8 * 8) :=
  ((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0

/-- The store-data slice for a width-8 `sd` (the `extractLsb` argument
`execute_STORE_char`'s `hwrite` demands). Mirrors `DemoStore.sdData`. -/
abbrev sdData8 (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

/-- Effective store address for `sd a6,-8(a5)`: `vbase + sign_extend 0xff8` (= `vbase - 8`). -/
abbrev sdAddrM8 (vbase : BitVec 64) : BitVec 64 :=
  vbase + sign_extend (m := 64) (0xff8#12)

/-- The 8-byte little-endian byte-insert chain produced by `vmem_write_addr_8`. -/
abbrev sdMem8 (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (vdata : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert a.toNat ((sdData8 vdata).extractLsb' 0 8)).insert
      (a.toNat + 1) ((sdData8 vdata).extractLsb' 8 8)).insert
      (a.toNat + 2) ((sdData8 vdata).extractLsb' 16 8)).insert
      (a.toNat + 3) ((sdData8 vdata).extractLsb' 24 8)).insert
      (a.toNat + 4) ((sdData8 vdata).extractLsb' 32 8)).insert
      (a.toNat + 5) ((sdData8 vdata).extractLsb' 40 8)).insert
      (a.toNat + 6) ((sdData8 vdata).extractLsb' 48 8)).insert
      (a.toNat + 7) ((sdData8 vdata).extractLsb' 56 8))

/-! ## Site 0x80006bfc — `mv a3,a1` = `addi a3,a1,0` (rd = x13, rs1 = x11) -/

theorem exec_bfc (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (v11 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0d#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v11 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x11 _ v11 h₂)
    (wX_bits_x13 _ (v11 + sign_extend (m := 64) (0x000#12)))

/-- **Observational step at 0x80006bfc** (`mv a3,a1`). Writes `x13 := v11`. -/
theorem site_80006bfc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bfc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bfc hmem
  exact stepObs_alu σ i u (0x80006bfc#64) vminstret (0x00058693#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (v11 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x86#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_bfc_word w_bfc_notrvc
    (Vsa.Sim.DecodeTable.decode_00058693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bfc σ (0x80006bfc#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c00 — `mv a5,a4` = `addi a5,a4,0` (rd = x15, rs1 = x14) -/

theorem exec_c00 (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v14 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v14 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x14 _ v14 h₂)
    (wX_bits_x15 _ (v14 + sign_extend (m := 64) (0x000#12)))

/-- **Observational step at 0x80006c00** (`mv a5,a4`). Writes `x15 := v14`. -/
theorem site_80006c00
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c00#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v14 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c00 hmem
  exact stepObs_alu σ i u (0x80006c00#64) vminstret (0x00070793#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v14 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x07#8) (0x07#8) (0x00#8)
    hG hpc hminstret w_c00_word w_c00_notrvc
    (Vsa.Sim.DecodeTable.decode_00070793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c00 σ (0x80006c00#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c0c — `addi a5,a5,8` (rd = x15, rs1 = x15) -/

theorem exec_c0c (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0x008#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0x008#12)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (v15 + sign_extend (m := 64) (0x008#12)))

/-- **Observational step at 0x80006c0c** (`addi a5,a5,8`). Writes `x15 := a5 + 8`. -/
theorem site_80006c0c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c0c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v15 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c0c hmem
  exact stepObs_alu σ i u (0x80006c0c#64) vminstret (0x00878793#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 (v15 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x87#8) (0x87#8) (0x00#8)
    hG hpc hminstret w_c0c_word w_c0c_notrvc
    (Vsa.Sim.DecodeTable.decode_00878793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c0c σ (0x80006c0c#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c10 — `addi a3,a3,8` (rd = x13, rs1 = x13) -/

theorem exec_c10 (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x13 (v13 + sign_extend (m := 64) (0x008#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5) v13
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v13 + sign_extend (m := 64) (0x008#12)))
    (rX_bits_x13 _ v13 h₂)
    (wX_bits_x13 _ (v13 + sign_extend (m := 64) (0x008#12)))

/-- **Observational step at 0x80006c10** (`addi a3,a3,8`). Writes `x13 := a3 + 8`. -/
theorem site_80006c10
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c10#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13 (v13 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c10 hmem
  exact stepObs_alu σ i u (0x80006c10#64) vminstret (0x00868693#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, iop.ADDI))
    Register.x13 (v13 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x86#8) (0x86#8) (0x00#8)
    hG hpc hminstret w_c10_word w_c10_notrvc
    (Vsa.Sim.DecodeTable.decode_00868693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c10 σ (0x80006c10#64) v13 hx13)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c08 — `ld a6,0(a3)` (LOAD signed width 8, rd = x16, rs1 = x13)

Effective address `a3 + sext 0x000 = a3`. Loads the 8-byte little-endian value
into `x16 := sign_extend (ldData8 …)` (width-preserving at width 8). Recipe from
`DemoLoad.exec_ld_x11_x2`. -/

theorem exec_c08 (σ : MState) (pc : BitVec 64) (v13 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hlo : 0x80000000 ≤ v13.toNat)
    (hhiram : v13.toNat + 8 ≤ 0x100000000)
    (hhtif : v13.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ v13.toNat)
    (halign : v13.toNat % 8 = 0)
    (hm0 : σ.mem[v13.toNat]? = some b0)
    (hm1 : σ.mem[v13.toNat + 1]? = some b1)
    (hm2 : σ.mem[v13.toNat + 2]? = some b2)
    (hm3 : σ.mem[v13.toNat + 3]? = some b3)
    (hm4 : σ.mem[v13.toNat + 4]? = some b4)
    (hm5 : σ.mem[v13.toNat + 5]? = some b5)
    (hm6 : σ.mem[v13.toNat + 6]? = some b6)
    (hm7 : σ.mem[v13.toNat + 7]? = some b7) :
    (execute (instruction.LOAD (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, false, 8))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x16
            (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hrs1 : (rX_bits (regidx.Regidx 0x0d#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v13 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x13 _ v13 hx13₂
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  -- effective address is `v13 + sext 0x000 = v13`
  have haddr_eq : v13 + sign_extend (m := 64) (0x000#12) = v13 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    exact BitVec.add_zero v13
  have hread := vmem_read_data_eight (afterNextPC (afterPrelude σ) pc)
    (regidx.Regidx 0x0d#5) (sign_extend (m := 64) (0x000#12)) v13
    b0 b1 b2 b3 b4 b5 b6 b7 initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase' hrs1
    (by rw [haddr_eq]; exact hlo) (by rw [haddr_eq]; exact hhiram)
    (by rw [haddr_eq]; exact hhtif) (by rw [haddr_eq]; exact halign)
    (by rw [haddr_eq, mem_afterNextPC]; exact hm0) (by rw [haddr_eq, mem_afterNextPC]; exact hm1)
    (by rw [haddr_eq, mem_afterNextPC]; exact hm2) (by rw [haddr_eq, mem_afterNextPC]; exact hm3)
    (by rw [haddr_eq, mem_afterNextPC]; exact hm4) (by rw [haddr_eq, mem_afterNextPC]; exact hm5)
    (by rw [haddr_eq, mem_afterNextPC]; exact hm6) (by rw [haddr_eq, mem_afterNextPC]; exact hm7)
  have hwr : (wX_bits (regidx.Regidx 0x10#5)
        (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok () (sigma3_alu σ pc Register.x16
          (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))) :=
    wX_bits_x16 _ (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))
  exact execute_load_signed_char (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x10#5)
    8 (ldData8 b0 b1 b2 b3 b4 b5 b6 b7) (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x16 (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7)))
    (by decide) hread hwr

/-- **Observational step at 0x80006c08** (`ld a6,0(a3)`). Writes
`x16 := sign_extend (ldData8 …)`, the 8-byte word at `a3`. -/
theorem site_80006c08
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c08#64 : BitVec 64))
    (hlo : 0x80000000 ≤ v13.toNat)
    (hhiram : v13.toNat + 8 ≤ 0x100000000)
    (hhtif : v13.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ v13.toNat)
    (halign : v13.toNat % 8 = 0)
    (hm0 : σ.mem[v13.toNat]? = some b0) (hm1 : σ.mem[v13.toNat + 1]? = some b1)
    (hm2 : σ.mem[v13.toNat + 2]? = some b2) (hm3 : σ.mem[v13.toNat + 3]? = some b3)
    (hm4 : σ.mem[v13.toNat + 4]? = some b4) (hm5 : σ.mem[v13.toNat + 5]? = some b5)
    (hm6 : σ.mem[v13.toNat + 6]? = some b6) (hm7 : σ.mem[v13.toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x16
          (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))) := by
  subst hpcv
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := memcpy_at_80006c08 hmem
  exact stepObs_alu σ i u (0x80006c08#64) vminstret (0x0006b803#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x10#5, false, 8))
    Register.x16 (sign_extend (m := 64) (ldData8 b0 b1 b2 b3 b4 b5 b6 b7))
    (0x03#8) (0xb8#8) (0x06#8) (0x00#8)
    hG hpc hminstret w_c08_word w_c08_notrvc
    (Vsa.Sim.DecodeTable.decode_0006b803 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c08 σ (0x80006c08#64) v13 b0 b1 b2 b3 b4 b5 b6 b7 hG hx13
      hlo hhiram hhtif halign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hbb0 hbb1 hbb2 hbb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c14 — `sd a6,-8(a5)` (STORE width 8, rs2 = x16, rs1 = x15)

Effective address `a5 + sext 0xff8 = a5 - 8` (`sdAddrM8`). Stores the 8 low bytes
of `a6` (= `x16`) little-endian. Post memory is the 8-byte insert chain
`sdMem8 σ₂.mem (sdAddrM8 v15) v16`. Recipe from `DemoStore.exec_sd_x11_x2`. -/

theorem exec_c14 (σ : MState) (pc : BitVec 64) (v15 v16 : BitVec 64)
    (hG : GoodState σ)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hlo : 0x80000000 ≤ (sdAddrM8 v15).toNat)
    (hhiram : (sdAddrM8 v15).toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (sdAddrM8 v15).toNat)
    (halign : (sdAddrM8 v15).toNat % 8 = 0) :
    (execute (instruction.STORE (0xff8#12, regidx.Regidx 0x10#5, regidx.Regidx 0x0f#5, 8))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (sdMem8 (afterNextPC (afterPrelude σ) pc).mem (sdAddrM8 v15) v16)) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx16₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x16 = some v16 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx16
  have hrs1 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v15 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x15 _ v15 hx15₂
  have hrs2 : (rX_bits (regidx.Regidx 0x10#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v16 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x16 _ v16 hx16₂
  have hwrite := vmem_write_addr_8 (afterNextPC (afterPrelude σ) pc) (sdAddrM8 v15) (sdData8 v16)
    initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  have hchar := execute_STORE_char (0xff8#12) (regidx.Regidx 0x10#5) (regidx.Regidx 0x0f#5) 8
    v15 v16 (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc (sdMem8 (afterNextPC (afterPrelude σ) pc).mem (sdAddrM8 v15) v16))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (sdAddrM8 v15)) 8
          (sdData8 v16) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc (sdMem8 (afterNextPC (afterPrelude σ) pc).mem (sdAddrM8 v15) v16))
      exact hwrite)
  show (execute (instruction.STORE (0xff8#12, regidx.Regidx 0x10#5, regidx.Regidx 0x0f#5, 8))).run
      (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-- **Observational step at 0x80006c14** (`sd a6,-8(a5)`). Stores the 8-byte word
`a6` at `a5-8`; post memory is `sdMem8 σ.mem (a5-8) a6`. -/
theorem site_80006c14
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c14#64 : BitVec 64))
    (halo : 0x80000000 ≤ (sdAddrM8 v15).toNat)
    (hahiram : (sdAddrM8 v15).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (sdAddrM8 v15).toNat)
    (haalign : (sdAddrM8 v15).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = sdMem8 (afterNextPC (afterPrelude σ) (0x80006c14#64)).mem (sdAddrM8 v15) v16 ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (sdMem8 (afterNextPC (afterPrelude σ) (0x80006c14#64)).mem (sdAddrM8 v15) v16)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c14 hmem
  exact stepObs_store σ i u (0x80006c14#64) vminstret (0xff07bc23#32)
    (instruction.STORE (0xff8#12, regidx.Regidx 0x10#5, regidx.Regidx 0x0f#5, 8))
    (sdMem8 (afterNextPC (afterPrelude σ) (0x80006c14#64)).mem (sdAddrM8 v15) v16)
    (0x23#8) (0xbc#8) (0x07#8) (0xff#8)
    hG hpc hminstret w_c14_word w_c14_notrvc
    (Vsa.Sim.DecodeTable.decode_ff07bc23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c14 σ (0x80006c14#64) v15 v16 hG hx15 hx16 halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c04 — `bgeu a4,a2` = BTYPE(0x0034, x12, x14, BGEU)

rs1 = x14, rs2 = x12. Taken (a4 ≥u a2) ⇒ `pc + sext 0x0034 = 0x80006c38`. Not-taken
(a4 <u a2) ⇒ fall through to `0x80006c08` (word-loop head). -/

theorem exec_c04_taken (σ : MState) (pc : BitVec 64) (v14 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x0034#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v14 v12 = true) :
    (execute (instruction.BTYPE (0x0034#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0034#13)) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bgeu_taken (0x0034#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5)
    v14 v12 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x12 _ v12 hx12₂) hpc₂ hmisa₂ htgt hv

theorem exec_c04_nottaken (σ : MState) (pc : BitVec 64) (v14 v12 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : zopz0zKzJ_u v14 v12 = false) :
    (execute (instruction.BTYPE (0x0034#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_bgeu_nottaken (0x0034#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5)
    v14 v12 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x12 _ v12 hx12₂) hv

/-- **Observational step at 0x80006c04, not taken** (`bgeu a4,a2`, a4 <u a2): fall to
word-loop head 0x80006c08. -/
theorem site_80006c04_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c04#64 : BitVec 64)) (hv : zopz0zKzJ_u v14 v12 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c04 hmem
  exact stepObs_branch_nottaken σ i u (0x80006c04#64) vminstret (0x0034#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) bop.BGEU (0x02c77a63#32)
    (0x63#8) (0x7a#8) (0xc7#8) (0x02#8)
    hG hpc hminstret w_c04_word w_c04_notrvc
    (Vsa.Sim.DecodeTable.decode_02c77a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c04_nottaken σ (0x80006c04#64) v14 v12 hx14 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006c04, taken** (`bgeu a4,a2`, a4 ≥u a2): skip the
word loop, branch to 0x80006c38. -/
theorem site_80006c04_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c04#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0034#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v14 v12 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0034#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c04 hmem
  exact stepObs_branch_taken σ i u (0x80006c04#64) vminstret (0x0034#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) bop.BGEU (0x02c77a63#32)
    (0x63#8) (0x7a#8) (0xc7#8) (0x02#8)
    hG hpc hminstret w_c04_word w_c04_notrvc
    (Vsa.Sim.DecodeTable.decode_02c77a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c04_taken σ (0x80006c04#64) v14 v12 hG hpc hx14 hx12 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c18 — `bltu a5,a2` = BTYPE(0x1ff0, x12, x15, BLTU)

rs1 = x15, rs2 = x12. Taken (a5 <u a2) ⇒ `pc + sext 0x1ff0 = 0x80006c08` (loop back).
Not-taken (a5 ≥u a2) ⇒ fall through to `0x80006c1c` (loop epilogue). -/

theorem exec_c18_taken (σ : MState) (pc : BitVec 64) (v15 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v15 v12 = true) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1ff0#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bltu_taken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5)
    v15 v12 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x12 _ v12 hx12₂) hpc₂ hmisa₂ htgt hv

theorem exec_c18_nottaken (σ : MState) (pc : BitVec 64) (v15 v12 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : zopz0zI_u v15 v12 = false) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_bltu_nottaken (0x1ff0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5)
    v15 v12 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x12 _ v12 hx12₂) hv

/-- **Observational step at 0x80006c18, taken** (`bltu a5,a2`, a5 <u a2): loop back to
0x80006c08. -/
theorem site_80006c18_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c18#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v15 v12 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c18 hmem
  exact stepObs_branch_taken σ i u (0x80006c18#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) bop.BLTU (0xfec7e8e3#32)
    (0xe3#8) (0xe8#8) (0xc7#8) (0xfe#8)
    hG hpc hminstret w_c18_word w_c18_notrvc
    (Vsa.Sim.DecodeTable.decode_fec7e8e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c18_taken σ (0x80006c18#64) v15 v12 hG hpc hx15 hx12 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006c18, not taken** (`bltu a5,a2`, a5 ≥u a2): fall to
loop epilogue 0x80006c1c. -/
theorem site_80006c18_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c18#64 : BitVec 64)) (hv : zopz0zI_u v15 v12 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c18 hmem
  exact stepObs_branch_nottaken σ i u (0x80006c18#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0c#5) bop.BLTU (0xfec7e8e3#32)
    (0xe3#8) (0xe8#8) (0xc7#8) (0xfe#8)
    hG hpc hminstret w_c18_word w_c18_notrvc
    (Vsa.Sim.DecodeTable.decode_fec7e8e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c18_nottaken σ (0x80006c18#64) v15 v12 hx15 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c38 — `bltu a4,a7` = BTYPE(0x0010, x17, x14, BLTU)

rs1 = x14, rs2 = x17. Taken (a4 <u a7) ⇒ `pc + sext 0x0010 = 0x80006c48` (byte loop).
Not-taken (a4 ≥u a7) ⇒ fall through to `0x80006c3c` (ret). -/

theorem exec_c38_taken (σ : MState) (pc : BitVec 64) (v14 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (htgt : (pc + sign_extend (m := 64) (0x0010#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v14 v17 = true) :
    (execute (instruction.BTYPE (0x0010#13, regidx.Regidx 0x11#5, regidx.Regidx 0x0e#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0010#13)) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bltu_taken (0x0010#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x11#5)
    v14 v17 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x17 _ v17 hx17₂) hpc₂ hmisa₂ htgt hv

theorem exec_c38_nottaken (σ : MState) (pc : BitVec 64) (v14 v17 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hv : zopz0zI_u v14 v17 = false) :
    (execute (instruction.BTYPE (0x0010#13, regidx.Regidx 0x11#5, regidx.Regidx 0x0e#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  exact execute_btype_bltu_nottaken (0x0010#13) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x11#5)
    v14 v17 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x14 _ v14 hx14₂) (rX_bits_x17 _ v17 hx17₂) hv

/-- **Observational step at 0x80006c38, taken** (`bltu a4,a7`, a4 <u a7): enter the
byte loop 0x80006c48. -/
theorem site_80006c38_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c38#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0010#13)).toNat % 4 = 0)
    (hv : zopz0zI_u v14 v17 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0010#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c38 hmem
  exact stepObs_branch_taken σ i u (0x80006c38#64) vminstret (0x0010#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x11#5) bop.BLTU (0x01176863#32)
    (0x63#8) (0x68#8) (0x17#8) (0x01#8)
    hG hpc hminstret w_c38_word w_c38_notrvc
    (Vsa.Sim.DecodeTable.decode_01176863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c38_taken σ (0x80006c38#64) v14 v17 hG hpc hx14 hx17 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006c38, not taken** (`bltu a4,a7`, a4 ≥u a7): fall to
ret 0x80006c3c. -/
theorem site_80006c38_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c38#64 : BitVec 64)) (hv : zopz0zI_u v14 v17 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c38 hmem
  exact stepObs_branch_nottaken σ i u (0x80006c38#64) vminstret (0x0010#13)
    (regidx.Regidx 0x0e#5) (regidx.Regidx 0x11#5) bop.BLTU (0x01176863#32)
    (0x63#8) (0x68#8) (0x17#8) (0x01#8)
    hG hpc hminstret w_c38_word w_c38_notrvc
    (Vsa.Sim.DecodeTable.decode_01176863 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c38_nottaken σ (0x80006c38#64) v14 v17 hx14 hx17 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
