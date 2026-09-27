import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch03Part15
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part13
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part29
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part28
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch11Part20
import Vsa.Sim.DecodeTable.Batch13Part06
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part26
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch16Part13
import Vsa.Sim.DecodeTable.Batch16Part21
import Vsa.Sim.DecodeTable.Batch16Part22
import Vsa.Sim.DecodeTable.Batch16Part23
import Vsa.Sim.DecodeTable.Batch16Part24
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.Code.Strlen

/-!
# Layer 3 — per-site observational step lemmas for `strlen`

One observational-step (`StepObs`) lemma per instruction of `strlen`
(53 instructions at `[0x80006cf0, 0x80006dc4)`), following `Muldi3Sites.lean`
verbatim: each site = the fully-qualified `DecodeTable` decode lemma + the
`rX`/`wX` read-backs + the matching `ExecuteAlu`/`ExecuteBranch`/`ExecuteLoad`
character, assembled into the abstract `hexec` the generic `stepObs_*` wrapper
wants, and closed by one `stepObs_*` application.

Every lemma is **parity-agnostic** (`i < 2 ↦ ∃ σ' i', … ∧ i' < 2 ∧ … ∧
ReadsLikePost σ' (sigmaPost_…)`), folding the tick/notick split into the
`ReadsLikePost` observation.

Load handling follows `DemoLoad.lean`: an executed LOAD's post-state is a single
`rd` insert (`sigma3_alu`), so loads plug into `stepObs_alu`.
* The word-wise `ld a2,0(a4)` (`0x80006d10`) uses the **TOTAL** load chain
  (`vmem_read_data_eight_total`), so no per-byte `some`-hypotheses are needed —
  the trailing bytes of the NUL-containing word may be unmapped.
* The `lbu` sites read mapped string bytes, so the width-1 `some`-hyp chain
  (`vmem_read_data_one`) is used.

Segments (control flow):
* entry / alignment test (`0xcf0…cfc`)
* magic-constant setup (`0xd00…d0c`)
* word-scan loop (`0xd10…d28`)
* byte tail (`0xd2c…d70`)
* byte-at-a-time alignment head (`0xd74…d90`)
* exit blocks (`0xd94…dc0`)
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Entry / alignment test (`0x80006cf0 … 0x80006cfc`) -/

/-! ### Site 0x80006cf0 — `andi a5,a0,7` = `andi x15,x10,7` -/

/-! ### Site 0x80006cf4 — `mv a4,a0` = `addi x14,x10,0` -/

/-! ### Site 0x80006cf8 — `bnez a5,+0x80` = `bne x15,x0` (to 0x80006d78)

Decode: `BTYPE (0x0080#13, x0, x15, BNE)`. Taken (a5 ≠ 0): PC → pc + sext 0x0080.
Not-taken (a5 = 0): fall through to pc+4. -/

/-! ### Site 0x80006cfc — `lui a5,0x7f7f8` = `lui x15,0x7f7f8` -/

theorem exec_lui_a5 (σ : MState) (pc : BitVec 64) :
    (execute (instruction.UTYPE (0x7f7f8#20, regidx.Regidx 0x0f#5, uop.LUI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12))) :=
  execute_utype_lui_char (0x7f7f8#20) (regidx.Regidx 0x0f#5)
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))
    (wX_bits_x15 _ (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)))

theorem lui_a5_word :
    (((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8) = (0x7f7f87b7#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem lui_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x7f#8).append (0x7f#8)).append (0x87#8)).append (0xb7#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Magic-constant setup (`0x80006d00 … 0x80006d0c`) -/

/-! ### Site 0x80006d00 — `addi a5,a5,-129` = `addi x15,x15,0xf7f` -/

theorem exec_addi_a5_m129 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.ITYPE (0xf7f#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_itype_addi_char (0xf7f#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + sign_extend (m := 64) (0xf7f#12)))
    (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x15 _ (v15 + sign_extend (m := 64) (0xf7f#12)))

theorem addi_a5_m129_word :
    (((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8) = (0xf7f78793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem addi_a5_m129_notrvc :
    Sail.BitVec.extractLsb ((((0xf7#8).append (0xf7#8)).append (0x87#8)).append (0x93#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ### Site 0x80006d04 — `slli a3,a5,0x20` = `slli x13,x15,0x20` -/

/-! ### Site 0x80006d08 — `add a3,a3,a5` = `add x13,x13,x15` -/

theorem exec_add_a3_a3_a5 (σ : MState) (pc : BitVec 64) (v13 v15 : BitVec 64)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x13 (v13 + v15)) := by
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_add_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5)
    v13 v15 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x13 (v13 + v15))
    (rX_bits_x13 _ v13 hx13₂) (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x13 _ (v13 + v15))

/-! ### Site 0x80006d0c — `li a1,-1` = `addi x11,x0,0xfff` -/

/-! ## Word-scan loop (`0x80006d10 … 0x80006d28`)

The word-loop scans 8 aligned bytes at a time: `ld a2,0(a4)` then the magic
`a5 = ((a2 & a3) + a3) | a2 | a3`, and `beq a5,a1` (loop while `a5 = all-ones`,
i.e. no zero byte — see `StrlenMagic.detect_all_ones`). The `ld` uses the TOTAL
chain (`vmem_read_data_eight_total`), since the NUL-containing word's trailing
bytes may be unmapped. -/

/-! ### Site 0x80006d10 — `ld a2,0(a4)` = `ld x12, 0(x14)` (TOTAL 8-byte load)

Effective address `a := v14 + sext 0`; loads the eight little-endian bytes
`getD 0`. Value written to `x12` is `sign_extend (ldBytesT σ₂ a)`. -/

/-! ### Site 0x80006d14 — `addi a4,a4,8` = `addi x14,x14,8` -/

/-! ### Site 0x80006d18 — `and a5,a2,a3` = `and x15,x12,x13` -/

/-! ### Site 0x80006d1c — `add a5,a5,a3` = `add x15,x15,x13` -/

theorem exec_add_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + v13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_add_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 + v13))
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x15 _ (v15 + v13))

/-! ### Site 0x80006d20 — `or a5,a5,a2` = `or x15,x15,x12` -/

/-! ### Site 0x80006d24 — `or a5,a5,a3` = `or x15,x15,x13` -/

theorem exec_or_a5_a5_a3 (σ : MState) (pc : BitVec 64) (v15 v13 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0d#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.OR))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 ||| v13)) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx13
  exact execute_rtype_or_char (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v13 (afterNextPC (afterPrelude σ) pc) (sigma3_alu σ pc Register.x15 (v15 ||| v13))
    (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂)
    (wX_bits_x15 _ (v15 ||| v13))

/-! ### Site 0x80006d28 — `beq a5,a1,0x80006d10` = `beq x15,x11` (loop back-edge)

Decode: `BTYPE (0x1fe8#13, x11, x15, BEQ)`. Taken (a5 = a1 = all-ones ⟺ no zero
byte in the word): PC → pc + sext 0x1fe8 = pc - 24 = 0x80006d10 (loop back).
Not-taken (a5 ≠ a1 ⟺ zero byte found): fall through to pc+4 (byte tail). -/

/-! ## Byte tail (`0x80006d2c … 0x80006d70`)

Once the word-loop finds a word with a zero byte, the tail probes the eight
bytes `a4-8 … a4-1` with `lbu`+`beqz` to locate the exact NUL. These bytes are
all mapped (they lie within the just-loaded word), so the `lbu` sites use the
width-1 `some`-hypothesis chain (`vmem_read_data_one`).

Two shared parameterized executes serve the whole tail (and the alignment head):
`exec_lbu_a5_a4` (`lbu x15, imm(x14)`, over the byte offset `imm`) and
`exec_beqz_a5` (`beq x15,x0`, over the branch immediate). -/

/-! ### Site 0x80006d2c — `lbu a5,-8(a4)` = `lbu x15, 0xff8(x14)` -/

/-! ### Site 0x80006d30 — `sub a3,a4,a0` = `sub x13,x14,x10` -/

/-! ### Site 0x80006d34 — `beqz a5,0x80006d9c` = `beq x15,x0` (imm 0x0068) -/

/-! ### Site 0x80006d38 — `lbu a5,-7(a4)` = `lbu x15, 0xff9(x14)` -/

/-! ### Site 0x80006d3c — `beqz a5,0x80006d94` = `beq x15,x0` (imm 0x0058) -/

/-! ### Site 0x80006d40 — `lbu a5,-6(a4)` = `lbu x15, 0xffa(x14)` -/

/-! ### Site 0x80006d44 — `beqz a5,0x80006dac` = `beq x15,x0` (imm 0x0068) -/

/-! ### Site 0x80006d48 — `lbu a5,-5(a4)` = `lbu x15, 0xffb(x14)` -/

/-! ### Site 0x80006d4c — `beqz a5,0x80006da4` = `beq x15,x0` (imm 0x0058) -/

/-! ### Site 0x80006d50 — `lbu a5,-4(a4)` = `lbu x15, 0xffc(x14)` -/

/-! ### Site 0x80006d54 — `beqz a5,0x80006db4` = `beq x15,x0` (imm 0x0060) -/

/-! ### Site 0x80006d58 — `lbu a5,-3(a4)` = `lbu x15, 0xffd(x14)` -/

/-! ### Site 0x80006d5c — `beqz a5,0x80006dbc` = `beq x15,x0` (imm 0x0060) -/

/-! ### Site 0x80006d60 — `lbu a5,-2(a4)` = `lbu x15, 0xffe(x14)` -/

/-! ### Site 0x80006d64 — `snez a0,a5` = `sltu x10,x0,x15` -/

theorem exec_snez_a0_a5 (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  have hx15₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_sltu_char (regidx.Regidx 0x0f#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5)
    (0#64) v15 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))
    (rX_bits_zero _) (rX_bits_x15 _ v15 hx15₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15))))

theorem snez_a0_a5_word :
    (((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8) = (0x00f03533#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem snez_a0_a5_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xf0#8)).append (0x35#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Observational step at 0x80006d64** (`snez a0,a5`). Writes `x10 := (a5 ≠ 0 ? 1 : 0)`. -/
theorem site_80006d64
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : StrlenLoaded σ.mem)
    (hpcv : pc = (0x80006d64#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.strlen_at_80006d64 hmem
  exact stepObs_alu σ i u (0x80006d64#64) vminstret (0x00f03533#32)
    (instruction.RTYPE (regidx.Regidx 0x0f#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, rop.SLTU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v15)))
    (0x33#8) (0x35#8) (0xf0#8) (0x00#8)
    hG hpc hminstret snez_a0_a5_word snez_a0_a5_notrvc
    (Vsa.Sim.DecodeTable.decode_00f03533 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_snez_a0_a5 σ (0x80006d64#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### Site 0x80006d68 — `add a0,a0,a3` = `add x10,x10,x13` -/

/-! ### Site 0x80006d6c — `addi a0,a0,-2` = `addi x10,x10,0xffe` -/

/-! ### Site 0x80006d70 — `ret` = `jalr x0,ra,0` (rs1 = x1 = ra) -/

/-! ## Byte-at-a-time alignment head (`0x80006d74 … 0x80006d90`)

Reached from the entry `bnez a5` when `a0` is not 8-aligned: advance a byte at a
time until aligned, checking for NUL. `beqz a3` tests the alignment counter
`a3 = a4 & 7`; `bnez a5` tests the loaded byte. -/

/-! ### Site 0x80006d74 — `beqz a3,0x80006cfc` = `beq x13,x0` (imm 0x1f88) -/

/-! ### Site 0x80006d78 — `lbu a5,0(a4)` = `lbu x15, 0x000(x14)` -/

/-! ### Site 0x80006d7c — `addi a4,a4,1` = `addi x14,x14,1` -/

/-! ### Site 0x80006d80 — `andi a3,a4,7` = `andi x13,x14,7` -/

/-! ### Site 0x80006d84 — `bnez a5,0x80006d74` = `bne x15,x0` (imm 0x1ff0, loop back-edge) -/

/-! ### Site 0x80006d88 — `sub a4,a4,a0` = `sub x14,x14,x10` -/

/-! ### Site 0x80006d8c — `addi a0,a4,-1` = `addi x10,x14,0xfff` -/

/-! ### Site 0x80006d90 — `ret` = `jalr x0,ra,0` -/

/-! ## Exit blocks (`0x80006d94 … 0x80006dc0`)

Six `addi a0,a3,imm; ret` pairs — the word-loop tail jumps to the block matching
which byte held the NUL, computing `strlen = (a4 - a0) - k`. The `addi` sites all
share one execute (`exec_addi_a0_a3`, `addi x10,x13,imm`); the `ret` sites are the
`stepObs_jr` instantiation (identical to `site_80006d70`/`d90` at a different pc). -/

/-! ### Site 0x80006d94 — `addi a0,a3,-7` = `addi x10,x13,0xff9` -/

/-! ### Site 0x80006d98 — `ret` -/

/-! ### Site 0x80006d9c — `addi a0,a3,-8` = `addi x10,x13,0xff8` -/

/-! ### Site 0x80006da0 — `ret` -/

/-! ### Site 0x80006da4 — `addi a0,a3,-5` = `addi x10,x13,0xffb` -/

/-! ### Site 0x80006da8 — `ret` -/

/-! ### Site 0x80006dac — `addi a0,a3,-6` = `addi x10,x13,0xffa` -/

/-! ### Site 0x80006db0 — `ret` -/

/-! ### Site 0x80006db4 — `addi a0,a3,-4` = `addi x10,x13,0xffc` -/

/-! ### Site 0x80006db8 — `ret` -/

/-! ### Site 0x80006dbc — `addi a0,a3,-3` = `addi x10,x13,0xffd` -/

/-! ### Site 0x80006dc0 — `ret` -/

end Vsa.Sim
