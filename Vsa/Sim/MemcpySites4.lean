import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part31
import Vsa.Sim.DecodeTable.Batch04Part09
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch08Part13
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch11Part23
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.Code.Memcpy
import Vsa.Sim.DivSites
import Vsa.Sim.MemcpySites
import Vsa.Sim.MemcpySites2
import Vsa.Sim.MemcpySites3

/-!
# Layer 3 — per-site observational step lemmas for `memcpy`'s dispatch prologue

One observational-step (`StepObs`) lemma per instruction of the **dispatch
prologue** `[0x80006bc8, 0x80006bf8]` — the alignment/size classification that
routes to the byte path (`0x80006c40`), the head-align peel (`0x80006cbc`,
excluded), the ×8 unrolled path (`0x80006c60`, excluded), or the small word loop
(fall through to `0x80006bfc`).  Plus the `c3c` `ret` (no-tail exit).

| pc  | word     | mnemonic       | AST | class |
|-----|----------|----------------|-----|-------|
| bc8 | 00a5c7b3 | xor  a5,a1,a0  | RTYPE(x10,x11,x15,XOR)   | ALU |
| bcc | 0077f793 | andi a5,a5,7   | ITYPE(0x007,x15,x15,ANDI)| ALU |
| bd0 | 00c508b3 | add  a7,a0,a2  | RTYPE(x12,x10,x17,ADD)   | ALU |
| bd4 | 06079663 | bnez a5,c40    | BTYPE(0x006c,x0,x15,BNE) | BR  |
| bd8 | 00863613 | sltiu a2,a2,8  | ITYPE(0x008,x12,x12,SLTIU)| ALU |
| bdc | 06061263 | bnez a2,c40    | BTYPE(0x0064,x0,x12,BNE) | BR  |
| be0 | 00757793 | andi a5,a0,7   | ITYPE(0x007,x10,x15,ANDI)| ALU |
| be4 | 00050713 | mv   a4,a0     | ITYPE(0x000,x10,x14,ADDI)| ALU |
| be8 | 0c079a63 | bnez a5,cbc    | BTYPE(0x00d4,x0,x15,BNE) | BR  |
| bec | ff88f613 | andi a2,a7,-8  | ITYPE(0xff8,x17,x12,ANDI)| ALU |
| bf0 | 40e606b3 | sub  a3,a2,a4  | RTYPE(x14,x12,x13,SUB)   | ALU |
| bf4 | 04000793 | li   a5,64     | ITYPE(0x040,x0,x15,ADDI) | ALU |
| bf8 | 06d7c463 | blt  a5,a3,c60 | BTYPE(0x0068,x13,x15,BLT)| BR  |
| c3c | 00008067 | ret            | JALR(0,x1,x0)            | JR  |

The `bfc`/`c00`/`c04` sites and the `c38` bltu pair already live in
`MemcpySites2.lean`; the epilogue ALU sites in `MemcpySites3.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bc8 memcpy_at_80006bcc memcpy_at_80006bd0
  memcpy_at_80006bd4 memcpy_at_80006bd8 memcpy_at_80006bdc memcpy_at_80006be0
  memcpy_at_80006be4 memcpy_at_80006be8 memcpy_at_80006bec memcpy_at_80006bf0
  memcpy_at_80006bf4 memcpy_at_80006bf8 memcpy_at_80006c3c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site 0x80006bc8 — `xor a5,a1,a0` (rd = x15, rs1 = x11, rs2 = x10) -/

theorem exec_bc8 (σ : MState) (pc : BitVec 64) (v11 v10 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, rop.XOR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v11 ^^^ v10)) := by
  have h11 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_rtype_xor_char (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
    v11 v10 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v11 ^^^ v10))
    (rX_bits_x11 _ v11 h11) (rX_bits_x10 _ v10 h10)
    (wX_bits_x15 _ (v11 ^^^ v10))

/-- **Observational step at 0x80006bc8** (`xor a5,a1,a0`). Writes `x15 := a1 ^^^ a0`. -/
theorem site_80006bc8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bc8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v11 ^^^ v10)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bc8 hmem
  exact stepObs_alu σ i u (0x80006bc8#64) vminstret (0x00a5c7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0a#5, regidx.Regidx 0x0b#5, regidx.Regidx 0x0f#5, rop.XOR))
    Register.x15 (v11 ^^^ v10) (0xb3#8) (0xc7#8) (0xa5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00a5c7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bc8 σ (0x80006bc8#64) v11 v10 hx11 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bcc — `andi a5,a5,7` (rd = x15, rs1 = x15) -/

theorem exec_bcc (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x007#12)))

/-- **Observational step at 0x80006bcc** (`andi a5,a5,7`). Writes `x15 := a5 &&& 7`. -/
theorem site_80006bcc
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bcc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bcc hmem
  exact stepObs_alu σ i u (0x80006bcc#64) vminstret (0x0077f793#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v15 &&& sign_extend (m := 64) (0x007#12)) (0x93#8) (0xf7#8) (0x77#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0077f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bcc σ (0x80006bcc#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bd0 — `add a7,a0,a2` (rd = x17, rs1 = x10, rs2 = x12) -/

theorem exec_bd0 (σ : MState) (pc : BitVec 64) (v10 v12 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x11#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x17 (v10 + v12)) := by
  have h10 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_rtype_add_char (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x11#5)
    v10 v12 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x17 (v10 + v12))
    (rX_bits_x10 _ v10 h10) (rX_bits_x12 _ v12 h12)
    (wX_bits_x17 _ (v10 + v12))

/-- **Observational step at 0x80006bd0** (`add a7,a0,a2`). Writes `x17 := a0 + a2`. -/
theorem site_80006bd0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bd0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x17 (v10 + v12)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bd0 hmem
  exact stepObs_alu σ i u (0x80006bd0#64) vminstret (0x00c508b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0c#5, regidx.Regidx 0x0a#5, regidx.Regidx 0x11#5, rop.ADD))
    Register.x17 (v10 + v12) (0xb3#8) (0x08#8) (0xc5#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c508b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd0 σ (0x80006bd0#64) v10 v12 hx10 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bd4 — `bnez a5,c40` = BTYPE(0x006c, x0, x15, BNE)

rs1 = x15, rs2 = x0.  Taken (a5 ≠ 0) ⇒ `pc + sext 0x006c = 0x80006c40` (byte path).
Not-taken (a5 = 0, i.e. aligned) ⇒ fall through to `0x80006bd8`. -/

theorem exec_bd4_taken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (htgt : (pc + sign_extend (m := 64) (0x006c#13)).toNat % 4 = 0)
    (hv : (v15 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x006c#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x006c#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x006c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bd4_nottaken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : (v15 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x006c#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_bne_nottaken (0x006c#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006bd4, taken** (`bnez a5`, a5 ≠ 0): route to byte path. -/
theorem site_80006bd4_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bd4#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x006c#13)).toNat % 4 = 0)
    (hv : (v15 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x006c#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bd4 hmem
  exact stepObs_branch_taken σ i u (0x80006bd4#64) vminstret (0x006c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x06079663#32)
    (0x63#8) (0x96#8) (0x07#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06079663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd4_taken σ (0x80006bd4#64) v15 hG hpc hx15 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006bd4, not taken** (`bnez a5`, a5 = 0): fall to bd8. -/
theorem site_80006bd4_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bd4#64 : BitVec 64)) (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bd4 hmem
  exact stepObs_branch_nottaken σ i u (0x80006bd4#64) vminstret (0x006c#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x06079663#32)
    (0x63#8) (0x96#8) (0x07#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06079663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd4_nottaken σ (0x80006bd4#64) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bd8 — `sltiu a2,a2,8` (rd = x12, rs1 = x12) -/

theorem exec_bd8 (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12) :
    (execute (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_itype_sltiu_char (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5) v12
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x12
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12))))))
    (rX_bits_x12 _ v12 h₂)
    (wX_bits_x12 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12))))))

/-- **Observational step at 0x80006bd8** (`sltiu a2,a2,8`). Writes `x12 := (a2 <u 8 ? 1 : 0)`. -/
theorem site_80006bd8
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bd8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bd8 hmem
  exact stepObs_alu σ i u (0x80006bd8#64) vminstret (0x00863613#32)
    (instruction.ITYPE (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, iop.SLTIU))
    Register.x12 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v12 (sign_extend (m := 64) (0x008#12)))))
    (0x13#8) (0x36#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00863613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bd8 σ (0x80006bd8#64) v12 hx12)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bdc — `bnez a2,c40` = BTYPE(0x0064, x0, x12, BNE)

rs1 = x12, rs2 = x0.  Taken (a2 ≠ 0, i.e. n < 8) ⇒ `pc + sext 0x0064 = 0x80006c40`
(byte path).  Not-taken (a2 = 0, i.e. n ≥ 8) ⇒ fall through to `0x80006be0`. -/

theorem exec_bdc_taken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (htgt : (pc + sign_extend (m := 64) (0x0064#13)).toNat % 4 = 0)
    (hv : (v12 != (0#64)) = true) :
    (execute (instruction.BTYPE (0x0064#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0c#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0064#13)) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_bne_taken (0x0064#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
    v12 (0#64) pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 hx12₂) (rX_bits_zero _) hpc₂ hmisa₂ htgt hv

theorem exec_bdc_nottaken (σ : MState) (pc : BitVec 64) (v12 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hv : (v12 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x0064#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0c#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx12₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  exact execute_btype_bne_nottaken (0x0064#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
    v12 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x12 _ v12 hx12₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006bdc, taken** (`bnez a2`, n < 8): route to byte path. -/
theorem site_80006bdc_taken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bdc#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0064#13)).toNat % 4 = 0)
    (hv : (v12 != (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0064#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bdc hmem
  exact stepObs_branch_taken σ i u (0x80006bdc#64) vminstret (0x0064#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BNE (0x06061263#32)
    (0x63#8) (0x12#8) (0x06#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06061263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bdc_taken σ (0x80006bdc#64) v12 hG hpc hx12 htgt hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- **Observational step at 0x80006bdc, not taken** (`bnez a2`, n ≥ 8): fall to be0. -/
theorem site_80006bdc_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bdc#64 : BitVec 64)) (hv : (v12 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bdc hmem
  exact stepObs_branch_nottaken σ i u (0x80006bdc#64) vminstret (0x0064#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BNE (0x06061263#32)
    (0x63#8) (0x12#8) (0x06#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06061263 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bdc_nottaken σ (0x80006bdc#64) v12 hx12 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006be0 — `andi a5,a0,7` (rd = x15, rs1 = x10) -/

theorem exec_be0 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x007#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_andi_char (0x007#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0f#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12)))
    (rX_bits_x10 _ v10 h₂)
    (wX_bits_x15 _ (v10 &&& sign_extend (m := 64) (0x007#12)))

/-- **Observational step at 0x80006be0** (`andi a5,a0,7`). Writes `x15 := a0 &&& 7`. -/
theorem site_80006be0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006be0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006be0 hmem
  exact stepObs_alu σ i u (0x80006be0#64) vminstret (0x00757793#32)
    (instruction.ITYPE (0x007#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v10 &&& sign_extend (m := 64) (0x007#12)) (0x93#8) (0x77#8) (0x75#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00757793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_be0 σ (0x80006be0#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006be4 — `mv a4,a0` = `addi a4,a0,0` (rd = x14, rs1 = x10) -/

theorem exec_be4 (σ : MState) (pc : BitVec 64) (v10 : BitVec 64)
    (hx10 : σ.regs.get? Register.x10 = some v10) :
    (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx10
  exact execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0e#5) v10
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x14 (v10 + sign_extend (m := 64) (0x000#12)))
    (rX_bits_x10 _ v10 h₂)
    (wX_bits_x14 _ (v10 + sign_extend (m := 64) (0x000#12)))

/-- **Observational step at 0x80006be4** (`mv a4,a0`). Writes `x14 := a0`. -/
theorem site_80006be4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006be4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006be4 hmem
  exact stepObs_alu σ i u (0x80006be4#64) vminstret (0x00050713#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x07#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_be4 σ (0x80006be4#64) v10 hx10)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006be8 — `bnez a5,cbc` = BTYPE(0x00d4, x0, x15, BNE)

rs1 = x15, rs2 = x0.  Taken (a5 ≠ 0, i.e. dst%8 ≠ 0) ⇒ head-align peel `0x80006cbc`
(EXCLUDED by the unified `P`).  Not-taken (a5 = 0, i.e. dst%8 = 0) ⇒ fall through
to `0x80006bec`. -/

theorem exec_be8_nottaken (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hv : (v15 != (0#64)) = false) :
    (execute (instruction.BTYPE (0x00d4#13, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, bop.BNE))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_btype_bne_nottaken (0x00d4#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5)
    v15 (0#64) (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_zero _) hv

/-- **Observational step at 0x80006be8, not taken** (`bnez a5`, dst%8 = 0): fall to bec. -/
theorem site_80006be8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006be8#64 : BitVec 64)) (hv : (v15 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006be8 hmem
  exact stepObs_branch_nottaken σ i u (0x80006be8#64) vminstret (0x00d4#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) bop.BNE (0x0c079a63#32)
    (0x63#8) (0x9a#8) (0x07#8) (0x0c#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0c079a63 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_be8_nottaken σ (0x80006be8#64) v15 hx15 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bec — `andi a2,a7,-8` (rd = x12, rs1 = x17) -/

theorem exec_bec (σ : MState) (pc : BitVec 64) (v17 : BitVec 64)
    (hx17 : σ.regs.get? Register.x17 = some v17) :
    (execute (instruction.ITYPE (0xff8#12, regidx.Regidx 0x11#5, regidx.Regidx 0x0c#5, iop.ANDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x12 (v17 &&& sign_extend (m := 64) (0xff8#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x17 = some v17 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx17
  exact execute_itype_andi_char (0xff8#12) (regidx.Regidx 0x11#5) (regidx.Regidx 0x0c#5) v17
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x12 (v17 &&& sign_extend (m := 64) (0xff8#12)))
    (rX_bits_x17 _ v17 h₂)
    (wX_bits_x12 _ (v17 &&& sign_extend (m := 64) (0xff8#12)))

/-- **Observational step at 0x80006bec** (`andi a2,a7,-8`). Writes `x12 := a7 &&& ~7`. -/
theorem site_80006bec
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v17 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bec#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x12 (v17 &&& sign_extend (m := 64) (0xff8#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bec hmem
  exact stepObs_alu σ i u (0x80006bec#64) vminstret (0xff88f613#32)
    (instruction.ITYPE (0xff8#12, regidx.Regidx 0x11#5, regidx.Regidx 0x0c#5, iop.ANDI))
    Register.x12 (v17 &&& sign_extend (m := 64) (0xff8#12)) (0x13#8) (0xf6#8) (0x88#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_ff88f613 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bec σ (0x80006bec#64) v17 hx17)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bf0 — `sub a3,a2,a4` (rd = x13, rs1 = x12, rs2 = x14) -/

theorem exec_bf0 (σ : MState) (pc : BitVec 64) (v12 v14 : BitVec 64)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0d#5, rop.SUB))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x13 (v12 - v14)) := by
  have h12 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx12
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_sub_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0d#5)
    v12 v14 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v12 - v14))
    (rX_bits_x12 _ v12 h12) (rX_bits_x14 _ v14 h14)
    (wX_bits_x13 _ (v12 - v14))

/-- **Observational step at 0x80006bf0** (`sub a3,a2,a4`). Writes `x13 := a2 - a4`. -/
theorem site_80006bf0
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bf0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (v12 - v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bf0 hmem
  exact stepObs_alu σ i u (0x80006bf0#64) vminstret (0x40e606b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0c#5, regidx.Regidx 0x0d#5, rop.SUB))
    Register.x13 (v12 - v14) (0xb3#8) (0x06#8) (0xe6#8) (0x40#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_40e606b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bf0 σ (0x80006bf0#64) v12 v14 hx12 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bf4 — `li a5,64` = `addi a5,x0,64` (rd = x15, rs1 = x0) -/

theorem exec_bf4 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.ITYPE (0x040#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) (0x040#12))) := by
  exact execute_itype_addi_char (0x040#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 ((0#64) + sign_extend (m := 64) (0x040#12)))
    (rX_bits_zero _)
    (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x040#12)))

/-- **Observational step at 0x80006bf4** (`li a5,64`). Writes `x15 := 64`. -/
theorem site_80006bf4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bf4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x040#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bf4 hmem
  exact stepObs_alu σ i u (0x80006bf4#64) vminstret (0x04000793#32)
    (instruction.ITYPE (0x040#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x040#12)) (0x93#8) (0x07#8) (0x00#8) (0x04#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_04000793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bf4 σ (0x80006bf4#64))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006bf8 — `blt a5,a3,c60` = BTYPE(0x0068, x13, x15, BLT)

rs1 = x15, rs2 = x13.  Taken (a5 <s a3, i.e. 64 <s (dst+n rounded − dst) = 8p) ⇒
`0x80006c60` (×8 unrolled path, EXCLUDED).  Not-taken (a5 ≥s a3, i.e. 8p ≤ 64) ⇒
fall through to `0x80006bfc` (small word-loop setup). -/

theorem exec_bf8_taken (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (htgt : (pc + sign_extend (m := 64) (0x0068#13)).toNat % 4 = 0)
    (hv : zopz0zI_s v15 v13 = true) :
    (execute (instruction.BTYPE (0x0068#13, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc (0x0068#13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  have hmisa₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some initMisa := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa
  exact execute_btype_blt_taken (0x0068#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5)
    v15 v13 pc initMisa (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂) hpc₂ hmisa₂ htgt hv

theorem exec_bf8_nottaken (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hv : zopz0zI_s v15 v13 = false) :
    (execute (instruction.BTYPE (0x0068#13, regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, bop.BLT))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_btype_blt_nottaken (0x0068#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂) hv

/-- **Observational step at 0x80006bf8, not taken** (`blt a5,a3`, 8p ≤ 64): fall to
the small word-loop setup at bfc. -/
theorem site_80006bf8_nottaken
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006bf8#64 : BitVec 64)) (hv : zopz0zI_s v15 v13 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006bf8 hmem
  exact stepObs_branch_nottaken σ i u (0x80006bf8#64) vminstret (0x0068#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) bop.BLT (0x06d7c463#32)
    (0x63#8) (0xc4#8) (0xd7#8) (0x06#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_06d7c463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bf8_nottaken σ (0x80006bf8#64) v15 v13 hx15 hx13 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## Site 0x80006c3c — `ret` = `jalr x0,ra,0` (rs1 = x1)

The no-tail exit: after the word loop when `8p = n` (whole copy word-aligned),
`c38 bltu a4,a7` is not-taken and falls to this `ret`. -/

/-- **Observational step at 0x80006c3c** (`ret`): PC → bit-0-cleared `ra`. -/
theorem site_80006c3c
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : MemcpyLoaded σ.mem)
    (hpcv : pc = (0x80006c3c#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := memcpy_at_80006c3c hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80006c3c#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80006c3c#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80006c3c#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80006c3c#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
