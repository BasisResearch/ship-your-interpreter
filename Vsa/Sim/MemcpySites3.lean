import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch04Part11
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites
import Vsa.Sim.MemcpySites2

/-!
# Layer 3 — per-site observational step lemmas for `memcpy`'s word-loop epilogue

One observational-step (`StepObs`) lemma per instruction of the **word-loop
epilogue** `[0x80006c1c, 0x80006c34]` — the straight-line pointer recomputation
after the small word loop that repositions `a1`/`a4` past the copied `p` words and
falls into the byte tail (`c38`).

| pc  | word     | mnemonic       | AST | class |
|-----|----------|----------------|-----|-------|
| c1c | fff60613 | addi a2,a2,-1  | ITYPE(0xfff,x12,x12,ADDI) | ALU |
| c20 | 40e60633 | sub  a2,a2,a4  | RTYPE(x14,x12,x12,SUB)    | ALU |
| c24 | ff867613 | andi a2,a2,-8  | ITYPE(0xff8,x12,x12,ANDI) | ALU |
| c28 | 00858593 | addi a1,a1,8   | ITYPE(0x008,x11,x11,ADDI) | ALU |
| c2c | 00870713 | addi a4,a4,8   | ITYPE(0x008,x14,x14,ADDI) | ALU |
| c30 | 00c585b3 | add  a1,a1,a2  | RTYPE(x12,x11,x11,ADD)    | ALU |
| c34 | 00c70733 | add  a4,a4,a2  | RTYPE(x12,x14,x14,ADD)    | ALU |

All sites are the plain ALU recipe (`MemcpySites` byte-path style): one `exec_*`
assembly (decode + one/two `rX_bits` reads + one `wX_bits`) and one `stepObs_alu`.
The site at `c38` (`bltu a4,a7`) already exists in `MemcpySites2.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006c1c memcpy_at_80006c20 memcpy_at_80006c24
  memcpy_at_80006c28 memcpy_at_80006c2c memcpy_at_80006c30 memcpy_at_80006c34)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site 0x80006c1c — `addi a2,a2,-1` (rd = x12, rs1 = x12) -/

theorem exec_c1c (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (v12 + sign_extend (m := 64) (0xfff#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v12 + sign_extend (m := 64) (0xfff#12)))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (v12 + sign_extend (m := 64) (0xfff#12)))

/-- **Observational step at 0x80006c1c** (`addi a2,a2,-1`). Writes `x12 := a2 - 1`. -/
theorem site_80006c1c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c1c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (v12 + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c1c hmem
  exact stepObs_alu σ i u (0x80006c1c#64) vminstret (0xfff60613#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ADDI))
    Register.x12 (v12 + sign_extend (m := 64) (0xfff#12)) (0x13#8) (0x06#8) (0xf6#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fff60613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c1c σ (0x80006c1c#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c20 — `sub a2,a2,a4` (rd = x12, rs1 = x12, rs2 = x14) -/

theorem exec_c20 (σ : MState) (pc : BitVec 64) (v12 v14 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x12 (v12 - v14)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_sub_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5)
    v12 v14 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v12 - v14))
    (rX_bits_x12 _ v12 h12) (rX_bits_x14 _ v14 h14)
    (wX_bits_x12 _ (v12 - v14))

/-- **Observational step at 0x80006c20** (`sub a2,a2,a4`). Writes `x12 := a2 - a4`. -/
theorem site_80006c20
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c20#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12 (v12 - v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c20 hmem
  exact stepObs_alu σ i u (0x80006c20#64) vminstret (0x40e60633#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, rop.SUB))
    Register.x12 (v12 - v14) (0x33#8) (0x06#8) (0xe6#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40e60633 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c20 σ (0x80006c20#64) v12 v14 hx12 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c24 — `andi a2,a2,-8` (rd = x12, rs1 = x12) -/

theorem exec_c24 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.ITYPE (0xff8#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (v12 &&& sign_extend (m := 64) (0xff8#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_itype_andi_char (0xff8#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v12 &&& sign_extend (m := 64) (0xff8#12)))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (v12 &&& sign_extend (m := 64) (0xff8#12)))

/-- **Observational step at 0x80006c24** (`andi a2,a2,-8`). Writes `x12 := a2 &&& ~7`. -/
theorem site_80006c24
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c24#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (v12 &&& sign_extend (m := 64) (0xff8#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c24 hmem
  exact stepObs_alu σ i u (0x80006c24#64) vminstret (0xff867613#32)
    (instruction.ITYPE (0xff8#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.ANDI))
    Register.x12 (v12 &&& sign_extend (m := 64) (0xff8#12)) (0x13#8) (0x76#8) (0x86#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_ff867613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c24 σ (0x80006c24#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c28 — `addi a1,a1,8` (rd = x11, rs1 = x11) -/

theorem exec_c28 (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x11 (v11 + sign_extend (m := 64) (0x008#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 (v11 + sign_extend (m := 64) (0x008#12)))
    (rX_bits_x11 _ v11 h₂)
    (wX_bits_x11 _ (v11 + sign_extend (m := 64) (0x008#12)))

/-- **Observational step at 0x80006c28** (`addi a1,a1,8`). Writes `x11 := a1 + 8`. -/
theorem site_80006c28
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c28#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 (v11 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c28 hmem
  exact stepObs_alu σ i u (0x80006c28#64) vminstret (0x00858593#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 (v11 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x85#8) (0x85#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00858593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c28 σ (0x80006c28#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c2c — `addi a4,a4,8` (rd = x14, rs1 = x14) -/

theorem exec_c2c (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x008#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0x008#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0x008#12)))
    (rX_bits_x14 _ v14 h₂)
    (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0x008#12)))

/-- **Observational step at 0x80006c2c** (`addi a4,a4,8`). Writes `x14 := a4 + 8`. -/
theorem site_80006c2c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c2c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c2c hmem
  exact stepObs_alu σ i u (0x80006c2c#64) vminstret (0x00870713#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0x008#12)) (0x13#8) (0x07#8) (0x87#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00870713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c2c σ (0x80006c2c#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c30 — `add a1,a1,a2` (rd = x11, rs1 = x11, rs2 = x12) -/

theorem exec_c30 (σ : MState) (pc : BitVec 64) (v11 v12 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x11 (v11 + v12)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_add_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5)
    v11 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x11 (v11 + v12))
    (rX_bits_x11 _ v11 h11) (rX_bits_x12 _ v12 h12)
    (wX_bits_x11 _ (v11 + v12))

/-- **Observational step at 0x80006c30** (`add a1,a1,a2`). Writes `x11 := a1 + a2`. -/
theorem site_80006c30
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c30#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v11 + v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c30 hmem
  exact stepObs_alu σ i u (0x80006c30#64) vminstret (0x00c585b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, rop.ADD))
    Register.x11 (v11 + v12) (0xb3#8) (0x85#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c585b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c30 σ (0x80006c30#64) v11 v12 hx11 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c34 — `add a4,a4,a2` (rd = x14, rs1 = x14, rs2 = x12) -/

theorem exec_c34 (σ : MState) (pc : BitVec 64) (v14 v12 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x14 (v14 + v12)) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_add_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5)
    v14 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v14 + v12))
    (rX_bits_x14 _ v14 h14) (rX_bits_x12 _ v12 h12)
    (wX_bits_x14 _ (v14 + v12))

/-- **Observational step at 0x80006c34** (`add a4,a4,a2`). Writes `x14 := a4 + a2`. -/
theorem site_80006c34
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c34#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 + v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c34 hmem
  exact stepObs_alu σ i u (0x80006c34#64) vminstret (0x00c70733#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, rop.ADD))
    Register.x14 (v14 + v12) (0x33#8) (0x07#8) (0xc7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c70733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_c34 σ (0x80006c34#64) v14 v12 hx14 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
