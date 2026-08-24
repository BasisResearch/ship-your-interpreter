import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch16Part15
import Vsa.Sim.DecodeTable.Batch16Part16
import Vsa.Sim.DecodeTable.Batch16Part19
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites

/-!
# Layer 3 — per-site observational step lemmas for `memcpy` (byte-copy path)

One observational-step (`StepObs`) lemma per instruction of newlib `memcpy`'s
**byte-copy path** — the branch the binary takes when the alignment fast-path
does not apply (`(src ^ dst) & 7 ≠ 0` at `0x80006bd4`, jumping to the byte loop
at `0x80006c40`).

The byte path (addresses in `[0x80006c40, 0x80006c60)`):

| pc | word | mnemonic | AST | class |
|----|------|----------|-----|-------|
| c40 | 00050713 | mv a4,a0    | ITYPE(0x000,x10,x14,ADDI) | ALU |
| c44 | ff157ce3 | bgeu a0,a7  | BTYPE(0x1ff8,x17,x10,BGEU) | BRANCH |
| c48 | 0005c783 | lbu a5,0(a1)| LOAD(0x000,x11,x15,unsigned,1) | LOAD |
| c4c | 00170713 | addi a4,a4,1| ITYPE(0x001,x14,x14,ADDI) | ALU |
| c50 | 00158593 | addi a1,a1,1| ITYPE(0x001,x11,x11,ADDI) | ALU |
| c54 | fef70fa3 | sb a5,-1(a4)| STORE(0xfff,x15,x14,1) | STORE |
| c58 | fee898e3 | bne a7,a4   | BTYPE(0x1ff0,x14,x17,BNE) | BRANCH |
| c5c | 00008067 | ret         | JALR(0x000,x1,x0) | JUMP |

BGEU has no generic execute char in `ExecuteBranch.lean` (only up to BLTU), so we
clone `execute_btype_bge_taken`/`_nottaken` here for `bop.BGEU` (guard
`zopz0zKzJ_u` = unsigned `≥`).

A `lbu`'s post-state is a single `x15` insert holding `zero_extend (m := 64) data`
(`data : BitVec (8*1)`, width-1 load); a `sb`'s post-state is a single byte insert
`σ₂.mem.insert a.toNat (extractLsb vdata 7 0)`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006c40 memcpy_at_80006c44 memcpy_at_80006c48
  memcpy_at_80006c4c memcpy_at_80006c50 memcpy_at_80006c54 memcpy_at_80006c58
  memcpy_at_80006c5c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! BGEU execute characters come from `Vsa.Sim.DivSites` (canonical home). -/

/-! ## Byte-word / non-RVC facts (all four bytes little-endian) -/

theorem c40_word : (((0x00#8).append (0x05#8)).append (0x07#8)).append (0x13#8) = (0x00050713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c40_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x07#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c44_word : (((0xff#8).append (0x15#8)).append (0x7c#8)).append (0xe3#8) = (0xff157ce3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c44_notrvc : Sail.BitVec.extractLsb ((((0xff#8).append (0x15#8)).append (0x7c#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c48_word : (((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x83#8) = (0x0005c783#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c48_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0xc7#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c4c_word : (((0x00#8).append (0x17#8)).append (0x07#8)).append (0x13#8) = (0x00170713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c4c_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x17#8)).append (0x07#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c50_word : (((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8) = (0x00158593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c50_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0x85#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c54_word : (((0xfe#8).append (0xf7#8)).append (0x0f#8)).append (0xa3#8) = (0xfef70fa3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c54_notrvc : Sail.BitVec.extractLsb ((((0xfe#8).append (0xf7#8)).append (0x0f#8)).append (0xa3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c58_word : (((0xfe#8).append (0xe8#8)).append (0x98#8)).append (0xe3#8) = (0xfee898e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c58_notrvc : Sail.BitVec.extractLsb ((((0xfe#8).append (0xe8#8)).append (0x98#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem c5c_word : (((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8) = (0x00008067#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem c5c_notrvc : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x80#8)).append (0x67#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Site 0x80006c40 — `mv a4,a0` = `addi a4,a0,0` (rd = x14, rs1 = x10) -/

theorem exec_c40 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x10 _ v10 hx10₂)
    (wX_bits_x14 _ (v10 + sign_extend (m := 64) (0x000#12)))

/-- **Observational step at 0x80006c40** (`mv a4,a0`). Writes `x14 := v10`. -/
theorem site_80006c40
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c40#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c40 hmem
  exact stepObs_alu σ i u (0x80006c40#64) vminstret (0x00050713#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret c40_word c40_notrvc
    (Vsa.Sim.DecodeTable.decode_00050713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c40 σ (0x80006c40#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c4c — `addi a4,a4,1` (rd = x14, rs1 = x14) -/

theorem exec_c4c (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x001#12))) := by
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x001#12)))
    (rX_bits_x14 _ v14 hx14₂)
    (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0x001#12)))

/-- **Observational step at 0x80006c4c** (`addi a4,a4,1`). Writes `x14 := a4 + 1`. -/
theorem site_80006c4c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c4c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c4c hmem
  exact stepObs_alu σ i u (0x80006c4c#64) vminstret (0x00170713#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x07#8) (0x17#8) (0x00#8)
    hG hpc hminstret c4c_word c4c_notrvc
    (Vsa.Sim.DecodeTable.decode_00170713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c4c σ (0x80006c4c#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c50 — `addi a1,a1,1` (rd = x11, rs1 = x11) -/

theorem exec_c50 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 (v11 + sign_extend (m := 64) (0x001#12))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 (v11 + sign_extend (m := 64) (0x001#12)))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x001#12)))

/-- **Observational step at 0x80006c50** (`addi a1,a1,1`). Writes `x11 := a1 + 1`. -/
theorem site_80006c50
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c50#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c50 hmem
  exact stepObs_alu σ i u (0x80006c50#64) vminstret (0x00158593#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x001#12)) (0x93#8) (0x85#8) (0x15#8) (0x00#8)
    hG hpc hminstret c50_word c50_notrvc
    (Vsa.Sim.DecodeTable.decode_00158593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c50 σ (0x80006c50#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c48 — `lbu a5,0(a1)` (LOAD unsigned width 1, rd = x15, rs1 = x11)

The effective address is `a1 + sext 0x000 = a1`. The loaded byte `b : BitVec 8`
(`= data : BitVec (8*1)`) is written to `x15` as `zero_extend (m := 64) b`. -/

theorem exec_c48 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64) (b : BitVec 8)
    (hG : GoodState σ)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hlo : 0x80000000 ≤ v11.toNat) (hhiram : v11.toNat + 1 ≤ 0x100000000)
    (hhtif : v11.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ v11.toNat)
    (hm0 : σ.mem[v11.toNat]? = some b) :
    (execute (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, true, 1))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (zero_extend (m := 64) (b : BitVec (8*1)))) := by
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
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hrs1 : (rX_bits (regidx.Regidx 0x0b#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v11 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x11 _ v11 hx11₂
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  -- effective address is `v11 + sext 0x000 = v11`
  have haddr_eq : v11 + sign_extend (m := 64) (0x000#12) = v11 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    exact BitVec.add_zero v11
  have hread := vmem_read_data_one (afterNextPC (afterPrelude σ) pc)
    (regidx.Regidx 0x0b#5) (sign_extend (m := 64) (0x000#12)) v11 b initMstatus initPmpaddr
    hpriv hmstatus hmprv hseccfg hpma hcfg haddr hbase' hrs1
    (by rw [haddr_eq]; exact hlo) (by rw [haddr_eq]; exact hhiram)
    (by rw [haddr_eq]; exact hhtif)
    (by rw [haddr_eq, mem_afterNextPC]; exact hm0)
  have hwr : (wX_bits (regidx.Regidx 0x0f#5)
        (zero_extend (m := 64) (b : BitVec (8*1)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () (sigma3_alu σ pc Register.x15 (zero_extend (m := 64) (b : BitVec (8*1)))) :=
    wX_bits_x15 _ (zero_extend (m := 64) (b : BitVec (8*1)))
  exact execute_load_unsigned_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
    1 (b : BitVec (8*1)) (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (zero_extend (m := 64) (b : BitVec (8*1))))
    (by decide) hread hwr

/-- **Observational step at 0x80006c48** (`lbu a5,0(a1)`). Writes
`x15 := zero_extend b`, where `b` is the byte at `a1`. -/
theorem site_80006c48
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64) (b : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c48#64 : BitVec 64))
    (hlo : 0x80000000 ≤ v11.toNat) (hhiram : v11.toNat + 1 ≤ 0x100000000)
    (hhtif : v11.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ v11.toNat)
    (hm0 : σ.mem[v11.toNat]? = some b) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (zero_extend (m := 64) (b : BitVec (8*1)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c48 hmem
  exact stepObs_alu σ i u (0x80006c48#64) vminstret (0x0005c783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, true, 1))
    Register.x15 (zero_extend (m := 64) (b : BitVec (8*1))) (0x83#8) (0xc7#8) (0x05#8) (0x00#8)
    hG hpc hminstret c48_word c48_notrvc
    (Vsa.Sim.DecodeTable.decode_0005c783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c48 σ (0x80006c48#64) v11 b hG hx11 hlo hhiram hhtif hm0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c54 — `sb a5,-1(a4)` (STORE width 1, rs2 = x15, rs1 = x14)

Effective address `a4 + sext 0xfff = a4 - 1`. Stores the low byte
`extractLsb v15 7 0` of `a5` (= `x15`). Post memory
`σ.mem.insert (a4-1).toNat (extractLsb v15 7 0)`. -/

/-- The store data slice for width 1: `extractLsb vdata 7 0` (auto-`setWidth (8*1)`). -/
abbrev sbData (vdata : BitVec 64) : BitVec (8 * 1) :=
  Sail.BitVec.extractLsb vdata ((1 *i 8) -i 1) 0

/-- The effective store address for `sb …,-1(a4)`: `vbase + sign_extend 0xfff`. -/
abbrev sbAddr (vbase : BitVec 64) : BitVec 64 :=
  vbase + sign_extend (m := 64) (0xfff#12)

theorem exec_c54 (σ : MState) (pc : BitVec 64) (v14 v15 : BitVec 64)
    (hG : GoodState σ)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hlo : 0x80000000 ≤ (sbAddr v14).toNat)
    (hhiram : (sbAddr v14).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (sbAddr v14).toNat) :
    (execute (instruction.STORE (0xfff#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, 1))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert (sbAddr v14).toNat (sbData v15))) := by
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
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hrs1 : (rX_bits (regidx.Regidx 0x0e#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v14 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x14 _ v14 hx14₂
  have hrs2 : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok v15 (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x15 _ v15 hx15₂
  have hwrite := vmem_write_addr_1 (afterNextPC (afterPrelude σ) pc) (sbAddr v14) (sbData v15)
    initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin
  have hchar := execute_STORE_char (0xfff#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) 1
    v14 v15 (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc ((afterNextPC (afterPrelude σ) pc).mem.insert (sbAddr v14).toNat (sbData v15)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (sbAddr v14)) 1
          (sbData v15) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc ((afterNextPC (afterPrelude σ) pc).mem.insert (sbAddr v14).toNat (sbData v15)))
      exact hwrite)
  show (execute (instruction.STORE (0xfff#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, 1))).run
      (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-- **Observational step at 0x80006c54** (`sb a5,-1(a4)`). Stores the low byte of
`a5` at `a4-1`; post memory is `σ.mem.insert (a4-1).toNat (low byte of a5)`. -/
theorem site_80006c54
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c54#64 : BitVec 64))
    (halo : 0x80000000 ≤ (sbAddr v14).toNat)
    (hahiram : (sbAddr v14).toNat + 1 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (sbAddr v14).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (afterNextPC (afterPrelude σ) (0x80006c54#64)).mem.insert (sbAddr v14).toNat (sbData v15) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          ((afterNextPC (afterPrelude σ) (0x80006c54#64)).mem.insert (sbAddr v14).toNat (sbData v15))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c54 hmem
  exact stepObs_store σ i u (0x80006c54#64) vminstret (0xfef70fa3#32)
    (instruction.STORE (0xfff#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, 1))
    ((afterNextPC (afterPrelude σ) (0x80006c54#64)).mem.insert (sbAddr v14).toNat (sbData v15))
    (0xa3#8) (0x0f#8) (0xf7#8) (0xfe#8)
    hG hpc hminstret c54_word c54_notrvc
    (Vsa.Sim.DecodeTable.decode_fef70fa3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c54 σ (0x80006c54#64) v14 v15 hG hx14 hx15 halo hahiram hahiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c44 — `bgeu a0,a7` = BTYPE(0x1ff8, x17, x10, BGEU)

Decode: `BTYPE (0x1ff8#13, x17, x10, BGEU)`, rs1 = x10, rs2 = x17. Taken (a0 ≥u a7)
⇒ branch to `pc + sext 0x1ff8 = pc - 8 = 0x80006c3c` (ret). Not-taken (a0 <u a7)
⇒ fall through to `pc + 4 = 0x80006c48` (byte loop). -/

theorem exec_c44_taken (σ : MState) (pc : BitVec 64) (v10 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (htgt : (pc + sign_extend (m := 64) (0x1ff8#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v10 v17 = true) :
    (execute (instruction.BTYPE (0x1ff8#13, regidx.Regidx 0x11#5, regidx.Regidx 0x0a#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1ff8#13)) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bgeu_taken (0x1ff8#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x11#5)
    v10 v17 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x17 _ v17 hx17₂) hpc₂ hmisa₂ htgt hv

theorem exec_c44_nottaken (σ : MState) (pc : BitVec 64) (v10 v17 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hv : zopz0zKzJ_u v10 v17 = false) :
    (execute (instruction.BTYPE (0x1ff8#13, regidx.Regidx 0x11#5, regidx.Regidx 0x0a#5, bop.BGEU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx10₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  exact execute_btype_bgeu_nottaken (0x1ff8#13) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x11#5)
    v10 v17 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x10 _ v10 hx10₂) (rX_bits_x17 _ v17 hx17₂) hv

/-- **Observational step at 0x80006c44, not taken** (`bgeu a0,a7`, a0 <u a7): fall
to byte loop 0x80006c48. -/
theorem site_80006c44_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c44#64 : BitVec 64)) (hv : zopz0zKzJ_u v10 v17 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c44 hmem
  exact stepObs_branch_nottaken σ i u (0x80006c44#64) vminstret (0x1ff8#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x11#5) bop.BGEU (0xff157ce3#32)
    (0xe3#8) (0x7c#8) (0x15#8) (0xff#8)
    hG hpc hminstret c44_word c44_notrvc
    (Vsa.Sim.DecodeTable.decode_ff157ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c44_nottaken σ (0x80006c44#64) v10 v17 hx10 hx17 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006c44, taken** (`bgeu a0,a7`, a0 ≥u a7): branch to
0x80006c3c (ret). -/
theorem site_80006c44_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c44#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff8#13)).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v10 v17 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff8#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c44 hmem
  exact stepObs_branch_taken σ i u (0x80006c44#64) vminstret (0x1ff8#13)
    (regidx.Regidx 0x0a#5) (regidx.Regidx 0x11#5) bop.BGEU (0xff157ce3#32)
    (0xe3#8) (0x7c#8) (0x15#8) (0xff#8)
    hG hpc hminstret c44_word c44_notrvc
    (Vsa.Sim.DecodeTable.decode_ff157ce3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c44_taken σ (0x80006c44#64) v10 v17 hG hpc hx10 hx17 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c58 — `bne a7,a4` = BTYPE(0x1ff0, x14, x17, BNE)

Decode: `BTYPE (0x1ff0#13, x14, x17, BNE)`, rs1 = x17, rs2 = x14. Taken (a7 ≠ a4)
⇒ branch to `pc + sext 0x1ff0 = pc - 16 = 0x80006c48` (loop back). Not-taken
(a7 = a4) ⇒ fall through to `pc + 4 = 0x80006c5c` (ret). -/

theorem exec_c58_taken (σ : MState) (pc : BitVec 64) (v17 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (htgt : (pc + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0)
    (hv : (v17 != v14) = true) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x0e#5, regidx.Regidx 0x11#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x1ff0#13)) := by
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x1ff0#13) (regidx.Regidx 0x11#5) (regidx.Regidx 0x0e#5)
    v17 v14 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x17 _ v17 hx17₂) (rX_bits_x14 _ v14 hx14₂) hpc₂ hmisa₂ htgt hv

theorem exec_c58_nottaken (σ : MState) (pc : BitVec 64) (v17 v14 : BitVec 64)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hv : (v17 != v14) = false) :
    (execute (instruction.BTYPE (0x1ff0#13, regidx.Regidx 0x0e#5, regidx.Regidx 0x11#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx17₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  have hx14₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_btype_bne_nottaken (0x1ff0#13) (regidx.Regidx 0x11#5) (regidx.Regidx 0x0e#5)
    v17 v14 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x17 _ v17 hx17₂) (rX_bits_x14 _ v14 hx14₂) hv

/-- **Observational step at 0x80006c58, taken** (`bne a7,a4`, a7 ≠ a4): loop back to
0x80006c48. -/
theorem site_80006c58_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v17 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c58#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0)
    (hv : (v17 != v14) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1ff0#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c58 hmem
  exact stepObs_branch_taken σ i u (0x80006c58#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x11#5) (regidx.Regidx 0x0e#5) bop.BNE (0xfee898e3#32)
    (0xe3#8) (0x98#8) (0xe8#8) (0xfe#8)
    hG hpc hminstret c58_word c58_notrvc
    (Vsa.Sim.DecodeTable.decode_fee898e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c58_taken σ (0x80006c58#64) v17 v14 hG hpc hx17 hx14 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006c58, not taken** (`bne a7,a4`, a7 = a4): fall to
ret 0x80006c5c. -/
theorem site_80006c58_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v17 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c58#64 : BitVec 64)) (hv : (v17 != v14) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c58 hmem
  exact stepObs_branch_nottaken σ i u (0x80006c58#64) vminstret (0x1ff0#13)
    (regidx.Regidx 0x11#5) (regidx.Regidx 0x0e#5) bop.BNE (0xfee898e3#32)
    (0xe3#8) (0x98#8) (0xe8#8) (0xfe#8)
    hG hpc hminstret c58_word c58_notrvc
    (Vsa.Sim.DecodeTable.decode_fee898e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c58_nottaken σ (0x80006c58#64) v17 v14 hx17 hx14 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c5c — `ret` = `jalr x0,ra,0` (rs1 = x1) -/

/-- **Observational step at 0x80006c5c** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_80006c5c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c5c#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c5c hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80006c5c#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80006c5c#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80006c5c#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80006c5c#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    c5c_notrvc c5c_word
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
