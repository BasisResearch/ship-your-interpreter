import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch16Part08
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Eval_expr

/-!
# Layer 3/4 — per-site observational step lemmas for the `EX_INT` path of `eval_expr`

The `EvalE.int` case walks `eval_expr` (@0x80003164) through:

* **prologue** — `lw a4,0(a2)` (kind), `addi sp,sp,-1088` (frame), 4 `sd` spills
  (`s0@1072`, `s2@1056`, `ra@1080`, `s1@1064`), `li a5,10`, `mv s0,a2`, `mv s2,a1`,
  `bltu a5,a4` (bounds; NOT taken for kind 0), `lwu a5,0(a2)` (kind again),
  `auipc a4,0x17; addi a4,a4,-568` (table base 0x80019f58), `mv s1,a0`,
  `slli a5,a5,2; add a5,a5,a4; lw a5,0(a5)` (jump-table read),
  `add a5,a5,a4; jr a5` (computed dispatch → 0x80003408);
* **arm** (@0x80003408) — `ld a1,8(a2)` (payload), `jal value_int` (@0x8000280c);
* **epilogue** (@0x800033ec) — `ld ra,1080(sp); ld s0,1072(sp); ld s2,1056(sp);
  mv a0,s1; ld s1,1064(sp); addi sp,sp,1088; ret`, reached via `j 0x800033ec`.

Each site follows the `ValueSites`/`ValueEqualSites` recipe: a `stepObs_*` wrapper
over a per-instruction `execute_*` characterization, discharging the fetch bytes
from `Eval_expr.lean`'s `eval_expr_at_*` and the decode from `DecodeTable`. All new
top-level names are suffixed `_ee` to avoid the generic-exec-helper collisions the
sites files have hit before.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Generic unsigned width-4 load `lwu rd,off(rs1)`

`lwu` is `LOAD (off, rs1, rd, true, 4)`. `extend_value true` zero-extends, so the
written value is `zero_extend (kind word)`. Mirrors `exec_lw` (signed) over
`execute_load_unsigned_char`. -/
theorem exec_lwu_ee (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64)
        ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))).run (afterNextPC (afterPrelude σ) pc)
      = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (halign : (vbase + sign_extend (m := 64) off).toNat % 4 = 0)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0)
    (h1 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 1]? = some b1)
    (h2 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 2]? = some b2)
    (h3 : σ.mem[(vbase + sign_extend (m := 64) off).toNat + 3]? = some b3) :
    (execute (instruction.LOAD (off, rs1, rd, true, 4))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
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
  have hread := vmem_read_data_four (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 b1 b2 b3 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif halign
    (by rw [mem_afterNextPC]; exact h0) (by rw [mem_afterNextPC]; exact h1)
    (by rw [mem_afterNextPC]; exact h2) (by rw [mem_afterNextPC]; exact h3)
  exact execute_load_unsigned_char off rs1 rd 4
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) (afterNextPC (afterPrelude σ) pc)
    σ' (by decide) hread hwr

/-! ## Prologue -/

/-! ### 0x80003164 — `lw a4,0(a2)` (kind of `e`). Writes `x14`. -/
theorem site_80003164_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003164#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003164 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003164#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x80003164#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003164#64) vminstret (0x00062703#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0e#5, false, 4))
    Register.x14 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x03#8) (0x27#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00062703 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80003164#64) (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0e#5)
      (sigma3_alu σ (0x80003164#64) Register.x14
        (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vexpr b0 b1 b2 b3 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x14 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003168 — `addi sp,sp,-1088` (0xbc0). Writes `x2 := sp + sext 0xbc0`. -/
theorem exec_addi_sp_m1088_ee (σ : MState) (pc : BitVec 64) (vsp : BitVec 64)
    (hx2 : σ.regs.get? Register.x2 = some vsp) :
    (execute (instruction.ITYPE (0xbc0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x2 (vsp + sign_extend (m := 64) (0xbc0#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx2
  exact execute_itype_addi_char (0xbc0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x2 (vsp + sign_extend (m := 64) (0xbc0#12)))
    (rX_bits_x2 _ vsp h₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0xbc0#12)))

theorem site_80003168_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003168#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0xbc0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003168 hmem
  exact stepObs_alu σ i u (0x80003168#64) vminstret (0xbc010113#32)
    (instruction.ITYPE (0xbc0#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0xbc0#12)) (0x13#8) (0x01#8) (0x01#8) (0xbc#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_bc010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_sp_m1088_ee σ (0x80003168#64) vsp hx2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### The 4 `sd` spills (0x8000316c/70/74/78). Generic over (rs2, off). -/

/-- 0x8000316c: `sd s0,1072(sp)` (off 0x430, rs2=x8). -/
theorem site_8000316c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp) (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000316c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x430#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x430#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000316c#64)).mem
        (vsp + sign_extend (m := 64) (0x430#12)).toNat (sdData_val v8) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000316c#64)).mem
            (vsp + sign_extend (m := 64) (0x430#12)).toNat (sdData_val v8))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000316c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000316c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000316c#64) _ (by decide) (by decide)]; exact hx2
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x8000316c#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x8000316c#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_store σ i u (0x8000316c#64) vminstret (0x42813823#32)
    (instruction.STORE (0x430#12, regidx.Regidx 0x08#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000316c#64)).mem
      (vsp + sign_extend (m := 64) (0x430#12)).toNat (sdData_val v8))
    (0x23#8) (0x38#8) (0x81#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42813823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000316c#64) (0x430#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      vsp v8 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x8 _ v8 hx8₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003170: `sd s2,1056(sp)` (off 0x420, rs2=x18). -/
theorem site_80003170_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp) (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003170#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x420#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x420#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80003170#64)).mem
        (vsp + sign_extend (m := 64) (0x420#12)).toNat (sdData_val v18) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80003170#64)).mem
            (vsp + sign_extend (m := 64) (0x420#12)).toNat (sdData_val v18))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003170 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003170#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003170#64) _ (by decide) (by decide)]; exact hx2
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80003170#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80003170#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_store σ i u (0x80003170#64) vminstret (0x43213023#32)
    (instruction.STORE (0x420#12, regidx.Regidx 0x12#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80003170#64)).mem
      (vsp + sign_extend (m := 64) (0x420#12)).toNat (sdData_val v18))
    (0x23#8) (0x30#8) (0x21#8) (0x43#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_43213023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80003170#64) (0x420#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x02#5)
      vsp v18 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x18 _ v18 hx18₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003174: `sd ra,1080(sp)` (off 0x438, rs2=x1). -/
theorem site_80003174_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp) (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003174#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x438#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x438#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80003174#64)).mem
        (vsp + sign_extend (m := 64) (0x438#12)).toNat (sdData_val v1) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80003174#64)).mem
            (vsp + sign_extend (m := 64) (0x438#12)).toNat (sdData_val v1))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003174 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003174#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003174#64) _ (by decide) (by decide)]; exact hx2
  have hx1₂ : (afterNextPC (afterPrelude σ) (0x80003174#64)).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ (0x80003174#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_store σ i u (0x80003174#64) vminstret (0x42113c23#32)
    (instruction.STORE (0x438#12, regidx.Regidx 0x01#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80003174#64)).mem
      (vsp + sign_extend (m := 64) (0x438#12)).toNat (sdData_val v1))
    (0x23#8) (0x3c#8) (0x11#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42113c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80003174#64) (0x438#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      vsp v1 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x1 _ v1 hx1₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003178: `sd s1,1064(sp)` (off 0x428, rs2=x9). -/
theorem site_80003178_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp) (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003178#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x428#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x428#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80003178#64)).mem
        (vsp + sign_extend (m := 64) (0x428#12)).toNat (sdData_val v9) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80003178#64)).mem
            (vsp + sign_extend (m := 64) (0x428#12)).toNat (sdData_val v9))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003178 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80003178#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80003178#64) _ (by decide) (by decide)]; exact hx2
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80003178#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x80003178#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_store σ i u (0x80003178#64) vminstret (0x42913423#32)
    (instruction.STORE (0x428#12, regidx.Regidx 0x09#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80003178#64)).mem
      (vsp + sign_extend (m := 64) (0x428#12)).toNat (sdData_val v9))
    (0x23#8) (0x34#8) (0x91#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42913423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80003178#64) (0x428#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x02#5)
      vsp v9 hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x9 _ v9 hx9₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000317c — `li a5,10` (addi x15,x0,10). Writes `x15 := 10`. -/
theorem site_8000317c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000317c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x00a#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000317c hmem
  exact stepObs_alu σ i u (0x8000317c#64) vminstret (0x00a00793#32)
    (instruction.ITYPE (0x00a#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x00a#12)) (0x93#8) (0x07#8) (0xa0#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00a00793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x00a#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000317c#64))
      (sigma3_alu σ (0x8000317c#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x00a#12)))
      (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x00a#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003180 — `mv s0,a2` (addi x8,x12,0). Writes `x8 := a2`. -/
theorem site_80003180_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003180#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v12 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003180 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003180#64)).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ (0x80003180#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003180#64) vminstret (0x00060413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v12 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00060413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x08#5) v12
      (afterNextPC (afterPrelude σ) (0x80003180#64))
      (sigma3_alu σ (0x80003180#64) Register.x8 (v12 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x12 _ v12 hx12₂) (wX_bits_x8 _ (v12 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003184 — `mv s2,a1` (addi x18,x11,0). Writes `x18 := a1`. -/
theorem site_80003184_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003184#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003184 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80003184#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80003184#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80003184#64) vminstret (0x00058913#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x12#5, iop.ADDI))
    Register.x18 (v11 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x89#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00058913 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x12#5) v11
      (afterNextPC (afterPrelude σ) (0x80003184#64))
      (sigma3_alu σ (0x80003184#64) Register.x18 (v11 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x11 _ v11 hx11₂) (wX_bits_x18 _ (v11 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003188 — `bltu a5,a4` (rs1=x15, rs2=x14), imm 0x9a0 → 0x80003b28.
For the `.int` case (kind 0 ≤ 10), the branch is NOT taken. -/
theorem exec_bltu_a5_a4_nottaken_ee (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hv : zopz0zI_u v15 v14 = false) :
    (execute (instruction.BTYPE (0x9a0#13, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, bop.BLTU))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_btype_bltu_nottaken (0x9a0#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc)
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) hv

theorem site_80003188_nottaken_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003188#64 : BitVec 64))
    (hv : zopz0zI_u v15 v14 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003188 hmem
  exact stepObs_branch_nottaken σ i u (0x80003188#64) vminstret (0x9a0#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) bop.BLTU (0x1ae7e0e3#32)
    (0xe3#8) (0xe0#8) (0xe7#8) (0x1a#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_1ae7e0e3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_bltu_a5_a4_nottaken_ee σ (0x80003188#64) v15 v14 hx15 hx14 hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000318c — `lwu a5,0(a2)` (kind, unsigned). Writes `x15`. -/
theorem site_8000318c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000318c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000318c hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x8000318c#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x8000318c#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x8000318c#64) vminstret (0x00066783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0f#5, true, 4))
    Register.x15 (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))
    (0x83#8) (0x67#8) (0x06#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00066783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lwu_ee σ (0x8000318c#64) (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x8000318c#64) Register.x15
        (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      vexpr b0 b1 b2 b3 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x15 _ (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003190 — `auipc a4,0x17`. Writes `x14 := pc + sext(0x17 <<< 12)`. -/
theorem exec_auipc_a4_ee (σ : MState) (pc : BitVec 64)
    (hpc : σ.regs.get? Register.PC = some pc) :
    (execute (instruction.UTYPE (0x00017#20, regidx.Regidx 0x0e#5, uop.AUIPC))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) := by
  have hpc₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc
  exact execute_utype_auipc_char (0x00017#20) (regidx.Regidx 0x0e#5) pc
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) hpc₂
    (wX_bits_x14 _ (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)))

theorem site_80003190_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003190#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003190 hmem
  exact stepObs_alu σ i u (0x80003190#64) vminstret (0x00017717#32)
    (instruction.UTYPE (0x00017#20, regidx.Regidx 0x0e#5, uop.AUIPC))
    Register.x14 ((0x80003190#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
    (0x17#8) (0x77#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00017717 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_auipc_a4_ee σ (0x80003190#64) hpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003194 — `addi a4,a4,-568` (0xdc8). Writes `x14 := v14 + sext 0xdc8`. -/
theorem exec_addi_a4_m568_ee (σ : MState) (pc : BitVec 64) (v14 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.ITYPE (0xdc8#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0xdc8#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_itype_addi_char (0xdc8#12) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (v14 + sign_extend (m := 64) (0xdc8#12)))
    (rX_bits_x14 _ v14 h₂) (wX_bits_x14 _ (v14 + sign_extend (m := 64) (0xdc8#12)))

theorem site_80003194_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003194#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14 (v14 + sign_extend (m := 64) (0xdc8#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003194 hmem
  exact stepObs_alu σ i u (0x80003194#64) vminstret (0xdc870713#32)
    (instruction.ITYPE (0xdc8#12, regidx.Regidx 0x0e#5, regidx.Regidx 0x0e#5, iop.ADDI))
    Register.x14 (v14 + sign_extend (m := 64) (0xdc8#12)) (0x13#8) (0x07#8) (0x87#8) (0xdc#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_dc870713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_a4_m568_ee σ (0x80003194#64) v14 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003198 — `mv s1,a0` (addi x9,x10,0). Writes `x9 := a0` (the sret buffer). -/
theorem site_80003198_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003198#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003198 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80003198#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80003198#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80003198#64) vminstret (0x00050493#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x09#5, iop.ADDI))
    Register.x9 (v10 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x04#8) (0x05#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050493 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x09#5) v10
      (afterNextPC (afterPrelude σ) (0x80003198#64))
      (sigma3_alu σ (0x80003198#64) Register.x9 (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x9 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000319c — `slli a5,a5,0x2` (rd=x15, rs1=x15, shamt=2). -/
theorem exec_slli_a5_ee (σ : MState) (pc : BitVec 64) (v15 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_shiftiop_slli_char (0x02#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))
    (rX_bits_x15 _ v15 h₂)
    (wX_bits_x15 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0)))

theorem site_8000319c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000319c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000319c hmem
  exact stepObs_alu σ i u (0x8000319c#64) vminstret (0x00279793#32)
    (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, sop.SLLI))
    Register.x15 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x02#6) 5 0))
    (0x93#8) (0x97#8) (0x27#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00279793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_slli_a5_ee σ (0x8000319c#64) v15 hx15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800031a0 / 0x800031a8 — `add a5,a5,a4` (rd=x15, rs1=x15, rs2=x14). -/
theorem exec_add_a5_a5_a4_ee (σ : MState) (pc : BitVec 64) (v15 v14 : BitVec 64)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_alu σ pc Register.x15 (v15 + v14)) := by
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  exact execute_rtype_add_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x15 (v15 + v14))
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14) (wX_bits_x15 _ (v15 + v14))

theorem site_800031a0_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031a0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800031a0 hmem
  exact stepObs_alu σ i u (0x800031a0#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a4_ee σ (0x800031a0#64) v15 v14 hx15 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

theorem site_800031a8_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15) (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031a8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800031a8 hmem
  exact stepObs_alu σ i u (0x800031a8#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_add_a5_a5_a4_ee σ (0x800031a8#64) v15 v14 hx15 hx14)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800031a4 — `lw a5,0(a5)` : the JUMP-TABLE read (in `.rodata`).
Four table-slot bytes `t0..t3` are explicit hypotheses. Writes
`x15 := sign_extend (t3 ++ t2 ++ t1 ++ t0)`. -/
theorem site_800031a4_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vtab : BitVec 64) (t0 t1 t2 t3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some vtab)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031a4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vtab + sign_extend (m := 64) (0x000#12)).toNat)
    (hhiram : (vtab + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (vtab + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vtab + sign_extend (m := 64) (0x000#12)).toNat)
    (halign : (vtab + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (h0 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat]? = some t0)
    (h1 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some t1)
    (h2 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some t2)
    (h3 : σ.mem[(vtab + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some t3) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800031a4 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x800031a4#64)).regs.get? Register.x15 = some vtab := by
    rw [get?_afterNextPC σ (0x800031a4#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x800031a4#64) vminstret (0x0007a783#32)
    (instruction.LOAD (0x000#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, false, 4))
    Register.x15 (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4)))
    (0x83#8) (0xa7#8) (0x07#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0007a783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x800031a4#64) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x800031a4#64) Register.x15
        (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))))
      vtab t0 t1 t2 t3 hG (rX_bits_x15 _ vtab hx15₂)
      (wX_bits_x15 _ (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))))
      hlo hhiram hhtif halign h0 h1 h2 h3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800031ac — `jr a5` : the computed dispatch (`jalr x0, 0(a5)`). -/
theorem site_800031ac_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vtgt : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some vtgt)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800031ac#64 : BitVec 64))
    (htgt : (BitVec.update (vtgt + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (vtgt + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800031ac hmem
  have hx15₂ : (rX_bits (regidx.Regidx 0x0f#5)).run (afterNextPC (afterPrelude σ) (0x800031ac#64))
      = .ok vtgt (afterNextPC (afterPrelude σ) (0x800031ac#64)) := by
    apply rX_bits_x15
    rw [get?_afterNextPC σ (0x800031ac#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_jr σ i u (0x800031ac#64) vminstret vtgt (0x00078067#32) (0x000#12)
    (regidx.Regidx 0x0f#5) (0x67#8) (0x80#8) (0x07#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00078067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx15₂ htgt hi

/-! ## The EX_INT arm (@0x80003408) -/

/-! ### 0x80003408 — `ld a1,8(a2)` (payload). Writes `x11`. -/
theorem site_80003408_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003408#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (h1 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003408 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003408#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x80003408#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003408#64) vminstret (0x00863583#32)
    (instruction.LOAD (0x008#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0b#5, false, 8))
    Register.x11 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x35#8) (0x86#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00863583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80003408#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x80003408#64) Register.x11
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vexpr b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x12 _ vexpr hx12₂)
      (wX_bits_x11 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000340c — `jal value_int` (imm 0x1ff400 → 0x8000280c, rd=x1=ra). -/
theorem site_8000340c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000340c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff400#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ff400#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000340c hmem
  exact stepObs_jal σ i u (0x8000340c#64) vminstret (0xc00ff0ef#32) (0x1ff400#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000340c#64) 4)
    (0xef#8) (0xf0#8) (0x0f#8) (0xc0#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_c00ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x8000340c#64) 4)) hi

/-! ### 0x80003410 — `j 0x800033ec` (jal x0, imm 0x1fffdc → epilogue). -/
theorem site_80003410_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003410#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fffdc#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fffdc#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003410 hmem
  exact stepObs_j σ i u (0x80003410#64) vminstret (0xfddff06f#32) (0x1fffdc#21)
    (0x6f#8) (0xf0#8) (0xdf#8) (0xfd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fddff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ## The shared epilogue (@0x800033ec) -/

/-! ### The 4 `ld` restores (0x800033ec/f0/f4/fc). Generic over (rd, off). -/

/-- 0x800033ec: `ld ra,1080(sp)` (off 0x438, rd=x1). -/
theorem site_800033ec_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800033ec#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x438#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x438#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x438#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x438#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x438#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x1
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800033ec hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800033ec#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800033ec#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800033ec#64) vminstret (0x43813083#32)
    (instruction.LOAD (0x438#12, regidx.Regidx 0x02#5, regidx.Regidx 0x01#5, false, 8))
    Register.x1 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x30#8) (0x81#8) (0x43#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_43813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800033ec#64) (0x438#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x800033ec#64) Register.x1
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x1 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800033f0: `ld s0,1072(sp)` (off 0x430, rd=x8). -/
theorem site_800033f0_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800033f0#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x430#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x430#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x430#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x430#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x430#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800033f0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800033f0#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800033f0#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800033f0#64) vminstret (0x43013403#32)
    (instruction.LOAD (0x430#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x01#8) (0x43#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_43013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800033f0#64) (0x430#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x800033f0#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800033f4: `ld s2,1056(sp)` (off 0x420, rd=x18). -/
theorem site_800033f4_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800033f4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x420#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x420#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x420#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x420#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x420#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x18
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800033f4 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800033f4#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800033f4#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800033f4#64) vminstret (0x42013903#32)
    (instruction.LOAD (0x420#12, regidx.Regidx 0x02#5, regidx.Regidx 0x12#5, false, 8))
    Register.x18 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x39#8) (0x01#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42013903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800033f4#64) (0x420#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x800033f4#64) Register.x18
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x18 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x800033f8 — `mv a0,s1` (addi x10,x9,0). Writes `x10 := s1` (the sret buffer). -/
theorem site_800033f8_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800033f8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v9 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800033f8 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x800033f8#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x800033f8#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_alu σ i u (0x800033f8#64) vminstret (0x00048513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v9 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x85#8) (0x04#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00048513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5) v9
      (afterNextPC (afterPrelude σ) (0x800033f8#64))
      (sigma3_alu σ (0x800033f8#64) Register.x10 (v9 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x9 _ v9 hx9₂) (wX_bits_x10 _ (v9 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800033fc: `ld s1,1064(sp)` (off 0x428, rd=x9). -/
theorem site_800033fc_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800033fc#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x428#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x428#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x428#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x428#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x428#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x9
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_800033fc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x800033fc#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x800033fc#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x800033fc#64) vminstret (0x42813483#32)
    (instruction.LOAD (0x428#12, regidx.Regidx 0x02#5, regidx.Regidx 0x09#5, false, 8))
    Register.x9 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x34#8) (0x81#8) (0x42#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_42813483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x800033fc#64) (0x428#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x800033fc#64) Register.x9
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x9 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003400 — `addi sp,sp,1088` (0x440). Restores `x2 := vsp + sext 0x440`. -/
theorem exec_addi_sp_p1088_ee (σ : MState) (pc : BitVec 64) (vsp : BitVec 64)
    (hx2 : σ.regs.get? Register.x2 = some vsp) :
    (execute (instruction.ITYPE (0x440#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))).run
        (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x2 (vsp + sign_extend (m := 64) (0x440#12))) := by
  have h₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx2
  exact execute_itype_addi_char (0x440#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) vsp
    (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x2 (vsp + sign_extend (m := 64) (0x440#12)))
    (rX_bits_x2 _ vsp h₂) (wX_bits_x2 _ (vsp + sign_extend (m := 64) (0x440#12)))

theorem site_80003400_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003400#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x2 (vsp + sign_extend (m := 64) (0x440#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003400 hmem
  exact stepObs_alu σ i u (0x80003400#64) vminstret (0x44010113#32)
    (instruction.ITYPE (0x440#12, regidx.Regidx 0x02#5, regidx.Regidx 0x02#5, iop.ADDI))
    Register.x2 (vsp + sign_extend (m := 64) (0x440#12)) (0x13#8) (0x01#8) (0x01#8) (0x44#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_44010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_addi_sp_p1088_ee σ (0x80003400#64) vsp hx2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80003404 — `ret` (jalr x0, 0(ra)). PC → bit-0-cleared `ra`. -/
theorem site_80003404_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vra : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx1 : σ.regs.get? Register.x1 = some vra)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003404#64 : BitVec 64))
    (htgt : (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (vra + sign_extend (m := 64) (0x000#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003404 hmem
  have hx1₂ : (rX_bits (regidx.Regidx 0x01#5)).run (afterNextPC (afterPrelude σ) (0x80003404#64))
      = .ok vra (afterNextPC (afterPrelude σ) (0x80003404#64)) := by
    apply rX_bits_x1
    rw [get?_afterNextPC σ (0x80003404#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_jr σ i u (0x80003404#64) vminstret vra (0x00008067#32) (0x000#12)
    (regidx.Regidx 0x01#5) (0x67#8) (0x80#8) (0x00#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00008067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    hx1₂ htgt hi

end Vsa.Sim
