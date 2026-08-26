import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch03Part16

/-!
# Layer 4 — M4 `whileStmt` normal-exit tail sites

The two straight-line instructions on the `whileStmt` normal-exit fall-through
(condition falsy → `whileFalse`; body `.brk` → `whileBreak`), after the arm body
lands at `0x80004090`:

```
80004090:  li  a0,0        -- x10 := 0 = StatusCode .normal   (00000513)
80004094:  j   0x8000409c  -- into the shared epilogue         (0080006f)
```

These are IDENTICAL to the `expr`/`ifNone` `li a0,0` / `j 0x8000409c` tail; only
the PC and the `j` immediate differ. The rest of the `whileStmt` arm body (cond
eval + `value_truthy` + branch + optional body recursion + loop control) is
delivered as named glue residuals, so it needs no per-site battery here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- 0x80004090: `li a0,0` (`addi a0,x0,0`). -/
theorem site_80004090_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004090#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004090 hmem
  exact stepObs_alu σ i u (0x80004090#64) vminstret (0x00000513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12))
    (0x13#8) (0x05#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0a#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80004090#64))
      (sigma3_alu σ (0x80004090#64) Register.x10 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _)
      (wX_bits_x10 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80004094: `j 0x8000409c`. -/
theorem site_80004094_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004094#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x000008#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x000008#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004094 hmem
  exact stepObs_j σ i u (0x80004094#64) vminstret (0x0080006f#32) (0x000008#21)
    (0x6f#8) (0x00#8) (0x80#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0080006f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

end Vsa.Sim
