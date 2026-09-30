import Vsa.Sim.ValueSites
import Vsa.Sim.DivSites
import Vsa.Sim.Code.Longjmp
import Vsa.Sim.DecodeTable.Batch08Part25
import Vsa.Sim.DecodeTable.Batch08Part17
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part05
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part19
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part15
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch06Part21
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch02Part23

/-!
# Layer 3 — per-site observational step lemmas for `setjmp` / `longjmp`

One `StepObs` lemma per instruction of newlib RV64 soft-float `setjmp`
(`0x80006ffc`, 16 insts: 14 `sd` + `li a0,0` + `ret`) and `longjmp`
(`0x8000703c`, 17 insts: 14 `ld` + `seqz`/`add` + `ret`).

Stores use `exec_sd_val` (width-8 `sd`, base = `a0`, offset = the slot). Loads
are **ALU-class** sites (`sign_extend` of the dword → `sigmaPost_alu`), via
`exec_ld` from `ValueSites`. `seqz a0,a1` is `SLTIU a0,a1,1`; `add a0,a0,a1` is
`RTYPE ADD`. Everything reuses the `stepObs_*` wrappers, `decode_*` table,
`writeMap8`/`sdData_val`.  Byte-word facts get an `_jmp` suffix (collision sweep).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts -/

theorem w_0015b513_jmp : ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) = (0x0015b513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0015b513_jmp : Sail.BitVec.extractLsb ((((0x00#8).append (0x15#8)).append (0xb5#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## setjmp: the 14 `sd rX, off(a0)` sites (base = a0 = x10) -/

/-! ## setjmp: `li a0,0` @ 0x80007034 (`addi a0,x0,0`, rd = x10). -/

/-! ## setjmp: `ret` @ 0x80007038 (`jalr x0,ra,0`). -/

/-! ## longjmp: the 14 `ld rX, off(a0)` ALU-class sites (base = a0 = x10) -/

/-! ## longjmp: `seqz a0,a1` @ 0x80007074 (`SLTIU a0,a1,1`, rd = x10, rs1 = x11). -/

theorem exec_seqz_jmp (σ : MState) (pc : BitVec 64) (v11 : BitVec 64)
    (hx11 : σ.regs.get? Register.x11 = some v11) :
    (execute (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x10
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  exact execute_itype_sltiu_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0a#5) v11
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x10
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))
    (rX_bits_x11 _ v11 hx11₂)
    (wX_bits_x10 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12))))))

theorem site_80007074_jmp
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : LongjmpLoaded σ.mem)
    (hpcv : pc = (0x80007074#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := longjmp_at_80007074 hmem
  exact stepObs_alu σ i u (0x80007074#64) vminstret (0x0015b513#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0a#5, iop.SLTIU))
    Register.x10 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v11 (sign_extend (m := 64) (0x001#12)))))
    (0x13#8) (0xb5#8) (0x15#8) (0x00#8)
    hG hpc hminstret w_0015b513_jmp nr_0015b513_jmp
    (Vsa.Sim.DecodeTable.decode_0015b513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_seqz_jmp σ (0x80007074#64) v11 hx11)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## longjmp: `add a0,a0,a1` @ 0x80007078 (`RTYPE ADD`, rs2 = x11, rs1 = x10, rd = x10). -/

/-! ## longjmp: `ret` @ 0x8000707c (`jalr x0,ra,0`). -/

end Vsa.Sim
