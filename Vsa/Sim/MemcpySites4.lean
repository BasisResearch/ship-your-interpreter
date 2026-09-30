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
open Vsa.Sim.Code (MemcpyLoaded memcpy_at_80006bc8 memcpy_at_80006bcc memcpy_at_80006bd0 memcpy_at_80006bd4 memcpy_at_80006bd8 memcpy_at_80006bdc memcpy_at_80006be0 memcpy_at_80006be4 memcpy_at_80006be8 memcpy_at_80006bec memcpy_at_80006bf0 memcpy_at_80006bf4 memcpy_at_80006bf8 memcpy_at_80006c3c)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Site 0x80006bc8 — `xor a5,a1,a0` (rd = x15, rs1 = x11, rs2 = x10) -/

/-! ## Site 0x80006bcc — `andi a5,a5,7` (rd = x15, rs1 = x15) -/

/-! ## Site 0x80006bd0 — `add a7,a0,a2` (rd = x17, rs1 = x10, rs2 = x12) -/

/-! ## Site 0x80006bd4 — `bnez a5,c40` = BTYPE(0x006c, x0, x15, BNE)

rs1 = x15, rs2 = x0.  Taken (a5 ≠ 0) ⇒ `pc + sext 0x006c = 0x80006c40` (byte path).
Not-taken (a5 = 0, i.e. aligned) ⇒ fall through to `0x80006bd8`. -/

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

/-! ## Site 0x80006be0 — `andi a5,a0,7` (rd = x15, rs1 = x10) -/

/-! ## Site 0x80006be4 — `mv a4,a0` = `addi a4,a0,0` (rd = x14, rs1 = x10) -/

/-! ## Site 0x80006be8 — `bnez a5,cbc` = BTYPE(0x00d4, x0, x15, BNE)

rs1 = x15, rs2 = x0.  Taken (a5 ≠ 0, i.e. dst%8 ≠ 0) ⇒ head-align peel `0x80006cbc`
(EXCLUDED by the unified `P`).  Not-taken (a5 = 0, i.e. dst%8 = 0) ⇒ fall through
to `0x80006bec`. -/

/-! ## Site 0x80006bec — `andi a2,a7,-8` (rd = x12, rs1 = x17) -/

/-! ## Site 0x80006bf0 — `sub a3,a2,a4` (rd = x13, rs1 = x12, rs2 = x14) -/

/-! ## Site 0x80006bf4 — `li a5,64` = `addi a5,x0,64` (rd = x15, rs1 = x0) -/

/-! ## Site 0x80006bf8 — `blt a5,a3,c60` = BTYPE(0x0068, x13, x15, BLT)

rs1 = x15, rs2 = x13.  Taken (a5 <s a3, i.e. 64 <s (dst+n rounded − dst) = 8p) ⇒
`0x80006c60` (×8 unrolled path, EXCLUDED).  Not-taken (a5 ≥s a3, i.e. 8p ≤ 64) ⇒
fall through to `0x80006bfc` (small word-loop setup). -/

/-! ## Site 0x80006c3c — `ret` = `jalr x0,ra,0` (rs1 = x1)

The no-tail exit: after the word loop when `8p = n` (whole copy word-aligned),
`c38 bltu a4,a7` is not-taken and falls to this `ret`. -/

end Vsa.Sim
