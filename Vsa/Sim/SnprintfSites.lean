import Vsa.Sim.StepObs
import Vsa.Sim.StrcpySites
import Vsa.Sim.Code.SvfprintfSlice

/-!
# Layer 3 — per-site observational step lemmas for the `%lld` decimal loop of `_svfprintf_r`

`StepObs` site batteries (`_sn` suffix) for the executed integer-formatting slice
of `_svfprintf_r` (`experiments/M3-snprintf-lld.md` §1.4).  Per the task brief
these cover the **decimal-conversion loop body** `[0x800082fc, 0x8000833c)`
(quotient step + `bgeu` exit test + remainder/emit step, the two `jal`s into the
verified div cluster, the backward `sb`, cursor decrement, digit count) plus the
**sign-handling block** `[0x800080dc, 0x800080f4]` and the single-digit fast path
`[0x80008100, 0x8000810c]`.

Each site is one `stepObs_*` application (`Vsa/Sim/StepObs.lean`) against the
byte-pinned code region `SvfprintfSliceLoaded` (`Vsa/Sim/Code/SvfprintfSlice.lean`,
`svfprintfSlice_at_ADDR`) and the `DecodeTable.decode_WORD` shard lemmas — the
DemoStore/DemoLoad/EnvNewSites recipe unchanged.  Register map for the loop:
`s0=x8`, `s6=x22`, `s7=x23`, `s9=x25`, `s10=x26`, `s11=x27`, `a0=x10`, `a1=x11`,
`a5=x15`.

The two `jal` sites (`0x80008304 → __hidden___udivdi3`, `0x80008324 → __umoddi3`)
write `x1 := pc+4` and redirect the PC to the div-cluster entry; the div specs
(`udivdi3_spec`/`umoddi3_spec`) are composed at those successor states in
`SnprintfSpec2.lean` with the ghost frame threading the live set.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts for the loop / sign / fast-path instruction words -/

theorem w_00073683_sn : (((0x00#8).append (0x07#8)).append (0x36#8)).append (0x83#8) = (0x00073683#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00073683_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x07#8)).append (0x36#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00068713_sn : (((0x00#8).append (0x06#8)).append (0x87#8)).append (0x13#8) = (0x00068713#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00068713_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x87#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_f606d4e3_sn : (((0xf6#8).append (0x06#8)).append (0xd4#8)).append (0xe3#8) = (0xf606d4e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_f606d4e3_sn : Sail.BitVec.extractLsb ((((0xf6#8).append (0x06#8)).append (0xd4#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_02d00793_sn : (((0x02#8).append (0xd0#8)).append (0x07#8)).append (0x93#8) = (0x02d00793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_02d00793_sn : Sail.BitVec.extractLsb ((((0x02#8).append (0xd0#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0af103a3_sn : (((0x0a#8).append (0xf1#8)).append (0x03#8)).append (0xa3#8) = (0x0af103a3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0af103a3_sn : Sail.BitVec.extractLsb ((((0x0a#8).append (0xf1#8)).append (0x03#8)).append (0xa3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_40e00733_sn : (((0x40#8).append (0xe0#8)).append (0x07#8)).append (0x33#8) = (0x40e00733#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_40e00733_sn : Sail.BitVec.extractLsb ((((0x40#8).append (0xe0#8)).append (0x07#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00900793_sn : (((0x00#8).append (0x90#8)).append (0x07#8)).append (0x93#8) = (0x00900793#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00900793_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x90#8)).append (0x07#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_1ce7e263_sn : (((0x1c#8).append (0xe7#8)).append (0xe2#8)).append (0x63#8) = (0x1ce7e263#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_1ce7e263_sn : Sail.BitVec.extractLsb ((((0x1c#8).append (0xe7#8)).append (0xe2#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0307071b_sn : (((0x03#8).append (0x07#8)).append (0x07#8)).append (0x1b#8) = (0x0307071b#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0307071b_sn : Sail.BitVec.extractLsb ((((0x03#8).append (0x07#8)).append (0x07#8)).append (0x1b#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_14e10da3_sn : (((0x14#8).append (0xe1#8)).append (0x0d#8)).append (0xa3#8) = (0x14e10da3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_14e10da3_sn : Sail.BitVec.extractLsb ((((0x14#8).append (0xe1#8)).append (0x0d#8)).append (0xa3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00040513_sn : (((0x00#8).append (0x04#8)).append (0x05#8)).append (0x13#8) = (0x00040513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00040513_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0x05#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00a00593_sn : (((0x00#8).append (0xa0#8)).append (0x05#8)).append (0x93#8) = (0x00a00593#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00a00593_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0xa0#8)).append (0x05#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_ba8fc0ef_sn : (((0xba#8).append (0x8f#8)).append (0xc0#8)).append (0xef#8) = (0xba8fc0ef#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_ba8fc0ef_sn : Sail.BitVec.extractLsb ((((0xba#8).append (0x8f#8)).append (0xc0#8)).append (0xef#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_00040b13_sn : (((0x00#8).append (0x04#8)).append (0x0b#8)).append (0x13#8) = (0x00040b13#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_00040b13_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0x0b#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_000d0c93_sn : (((0x00#8).append (0x0d#8)).append (0x0c#8)).append (0x93#8) = (0x000d0c93#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_000d0c93_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x0d#8)).append (0x0c#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0567f063_sn : (((0x05#8).append (0x67#8)).append (0xf0#8)).append (0x63#8) = (0x0567f063#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0567f063_sn : Sail.BitVec.extractLsb ((((0x05#8).append (0x67#8)).append (0xf0#8)).append (0x63#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_bd0fc0ef_sn : (((0xbd#8).append (0x0f#8)).append (0xc0#8)).append (0xef#8) = (0xbd0fc0ef#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_bd0fc0ef_sn : Sail.BitVec.extractLsb ((((0xbd#8).append (0x0f#8)).append (0xc0#8)).append (0xef#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_0305051b_sn : (((0x03#8).append (0x05#8)).append (0x05#8)).append (0x1b#8) = (0x0305051b#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_0305051b_sn : Sail.BitVec.extractLsb ((((0x03#8).append (0x05#8)).append (0x05#8)).append (0x1b#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_feac8fa3_sn : (((0xfe#8).append (0xac#8)).append (0x8f#8)).append (0xa3#8) = (0xfeac8fa3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_feac8fa3_sn : Sail.BitVec.extractLsb ((((0xfe#8).append (0xac#8)).append (0x8f#8)).append (0xa3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_fffc8d13_sn : (((0xff#8).append (0xfc#8)).append (0x8d#8)).append (0x13#8) = (0xfffc8d13#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_fffc8d13_sn : Sail.BitVec.extractLsb ((((0xff#8).append (0xfc#8)).append (0x8d#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_001b8b9b_sn : (((0x00#8).append (0x1b#8)).append (0x8b#8)).append (0x9b#8) = (0x001b8b9b#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_001b8b9b_sn : Sail.BitVec.extractLsb ((((0x00#8).append (0x1b#8)).append (0x8b#8)).append (0x9b#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem w_fc0d82e3_sn : (((0xfc#8).append (0x0d#8)).append (0x82#8)).append (0xe3#8) = (0xfc0d82e3#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide
theorem nr_fc0d82e3_sn : Sail.BitVec.extractLsb ((((0xfc#8).append (0x0d#8)).append (0x82#8)).append (0xe3#8)) 1 0 = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Shared decode-prelude helper

Every `decode_*` shard lemma takes the three prelude side-conditions read off
`GoodState`.  This wraps them for a site. -/

private theorem misa_pre (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa
private theorem priv_pre (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege
private theorem sec_pre (σ : MState) (hG : GoodState σ) :
    (afterPrelude σ).regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) := by
  rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg

/-! ## Loop-body sites

Each site reads its source GPR (a `some`-hypothesis) and steps once, producing the
`sigmaPost_*` observation consumed by the `obs_*` frame lemmas in `SnprintfSpec2`.
The `mv`/`li`/`addi` sites are ITYPE-ADDI (`exec_addi_gen`); `addiw` is `ADDIW`
(`execute_addiw_char`); the `sb` is a width-1 STORE (`exec_sb`); the `bgeu`/`beqz`
are BTYPE (`stepObs_branch_*`); the two `jal`s write `x1 := pc+4` and redirect the
PC to the div-cluster entry (`stepObs_jal`). -/

/-! ### 0x800082fc — `mv a0,s0` = `addi x10,x8,0` (x10 := x8) -/
theorem site_800082fc_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800082fc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v8 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_800082fc hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x800082fc#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x800082fc#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x800082fc#64) vminstret (0x00040513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v8 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_00040513_sn nr_00040513_sn
    (Vsa.Sim.DecodeTable.decode_00040513 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5) v8
      (afterNextPC (afterPrelude σ) (0x800082fc#64))
      (sigma3_alu σ (0x800082fc#64) Register.x10 (v8 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x10 _ (v8 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008300 — `li a1,10` = `addi x11,x0,10` (x11 := 10) -/
theorem site_80008300_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008300#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008300 hmem
  exact stepObs_alu σ i u (0x80008300#64) vminstret (0x00a00593#32)
    (instruction.ITYPE (0x00a#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12)) (0x93#8) (0x05#8) (0xa0#8) (0x00#8)
    hG hpc hminstret w_00a00593_sn nr_00a00593_sn
    (Vsa.Sim.DecodeTable.decode_00a00593 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x00a#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80008300#64))
      (sigma3_alu σ (0x80008300#64) Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12)))
      (rX_bits_zero _) (wX_bits_x11 _ ((0#64) + sign_extend (m := 64) (0x00a#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008304 — `jal __hidden___udivdi3` : x1 := pc+4, PC := 0x800046ac -/
theorem site_80008304_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008304#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fc3a8#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008304 hmem
  refine stepObs_jal σ i u (0x80008304#64) vminstret (0xba8fc0ef#32) (0x1fc3a8#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008304#64) 4)
    (0xef#8) (0xc0#8) (0x8f#8) (0xba#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_ba8fc0ef_sn w_ba8fc0ef_sn
    (Vsa.Sim.DecodeTable.decode_ba8fc0ef (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x80008304#64) 4)

/-! ### 0x80008308 — `mv s6,s0` = `addi x22,x8,0` (x22 := x8) -/
theorem site_80008308_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008308#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22 (v8 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008308 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80008308#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80008308#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80008308#64) vminstret (0x00040b13#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x16#5, iop.ADDI))
    Register.x22 (v8 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x0b#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_00040b13_sn nr_00040b13_sn
    (Vsa.Sim.DecodeTable.decode_00040b13 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x16#5) v8
      (afterNextPC (afterPrelude σ) (0x80008308#64))
      (sigma3_alu σ (0x80008308#64) Register.x22 (v8 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x22 _ (v8 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000830c — `li a5,9` = `addi x15,x0,9` (x15 := 9) -/
theorem site_8000830c_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000830c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_8000830c hmem
  exact stepObs_alu σ i u (0x8000830c#64) vminstret (0x00900793#32)
    (instruction.ITYPE (0x009#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0f#5, iop.ADDI))
    Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12)) (0x93#8) (0x07#8) (0x90#8) (0x00#8)
    hG hpc hminstret w_00900793_sn nr_00900793_sn
    (Vsa.Sim.DecodeTable.decode_00900793 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x009#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000830c#64))
      (sigma3_alu σ (0x8000830c#64) Register.x15 ((0#64) + sign_extend (m := 64) (0x009#12)))
      (rX_bits_zero _) (wX_bits_x15 _ ((0#64) + sign_extend (m := 64) (0x009#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008310 — `mv s9,s10` = `addi x25,x26,0` (x25 := x26) -/
theorem site_80008310_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v26 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx26 : σ.regs.get? Register.x26 = some v26)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008310#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x25 (v26 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008310 hmem
  have hx26₂ : (afterNextPC (afterPrelude σ) (0x80008310#64)).regs.get? Register.x26 = some v26 := by
    rw [get?_afterNextPC σ (0x80008310#64) _ (by decide) (by decide)]; exact hx26
  exact stepObs_alu σ i u (0x80008310#64) vminstret (0x000d0c93#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x1a#5, regidx.Regidx 0x19#5, iop.ADDI))
    Register.x25 (v26 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x0c#8) (0x0d#8) (0x00#8)
    hG hpc hminstret w_000d0c93_sn nr_000d0c93_sn
    (Vsa.Sim.DecodeTable.decode_000d0c93 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x1a#5) (regidx.Regidx 0x19#5) v26
      (afterNextPC (afterPrelude σ) (0x80008310#64))
      (sigma3_alu σ (0x80008310#64) Register.x25 (v26 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x26 _ v26 hx26₂) (wX_bits_x25 _ (v26 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008314 — `mv s0,a0` = `addi x8,x10,0` (x8 := x10) -/
theorem site_80008314_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008314#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008314 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80008314#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80008314#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80008314#64) vminstret (0x00050413#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x08#5, iop.ADDI))
    Register.x8 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x05#8) (0x00#8)
    hG hpc hminstret
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00050413 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x08#5) v10
      (afterNextPC (afterPrelude σ) (0x80008314#64))
      (sigma3_alu σ (0x80008314#64) Register.x8 (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x8 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008318 — `bgeu a5,s6,0x80008358` = BTYPE(0x0040,x22,x15,BGEU) (exit test) -/
/-- Taken arm: `x15 ≥u x22` (`s6 ≤ 9`) ⇒ jump to `0x80008358`. -/
theorem site_80008318_taken_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008318#64 : BitVec 64))
    (hv : zopz0zKzJ_u v15 v22 = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x0040#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008318 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80008318#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hx15
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80008318#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_branch_taken σ i u (0x80008318#64) vminstret (0x0040#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x16#5) bop.BGEU (0x0567f063#32) (0x63#8) (0xf0#8) (0x67#8) (0x05#8)
    hG hpc hminstret w_0567f063_sn nr_0567f063_sn
    (Vsa.Sim.DecodeTable.decode_0567f063 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_btype_bgeu_taken (0x0040#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x16#5) v15 v22
      (0x80008318#64) (Vsa.Sim.initMisa) (afterNextPC (afterPrelude σ) (0x80008318#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x22 _ v22 hx22₂)
      (by rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Not-taken arm: `¬(x15 ≥u x22)` (`s6 > 9`) ⇒ fall through to `0x8000831c`. -/
theorem site_80008318_nottaken_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008318#64 : BitVec 64))
    (hv : zopz0zKzJ_u v15 v22 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008318 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80008318#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hx15
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80008318#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80008318#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_branch_nottaken σ i u (0x80008318#64) vminstret (0x0040#13)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x16#5) bop.BGEU (0x0567f063#32) (0x63#8) (0xf0#8) (0x67#8) (0x05#8)
    hG hpc hminstret w_0567f063_sn nr_0567f063_sn
    (Vsa.Sim.DecodeTable.decode_0567f063 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_btype_bgeu_nottaken (0x0040#13) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x16#5) v15 v22
      (afterNextPC (afterPrelude σ) (0x80008318#64))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x22 _ v22 hx22₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000831c — `li a1,10` = `addi x11,x0,10` (x11 := 10) -/
theorem site_8000831c_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000831c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_8000831c hmem
  exact stepObs_alu σ i u (0x8000831c#64) vminstret (0x00a00593#32)
    (instruction.ITYPE (0x00a#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, iop.ADDI))
    Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12)) (0x93#8) (0x05#8) (0xa0#8) (0x00#8)
    hG hpc hminstret w_00a00593_sn nr_00a00593_sn
    (Vsa.Sim.DecodeTable.decode_00a00593 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x00a#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000831c#64))
      (sigma3_alu σ (0x8000831c#64) Register.x11 ((0#64) + sign_extend (m := 64) (0x00a#12)))
      (rX_bits_zero _) (wX_bits_x11 _ ((0#64) + sign_extend (m := 64) (0x00a#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008320 — `mv a0,s0` = `addi x10,x8,0` (x10 := x8) -/
theorem site_80008320_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008320#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10 (v8 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008320 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80008320#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80008320#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80008320#64) vminstret (0x00040513#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x08#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v8 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x05#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_00040513_sn nr_00040513_sn
    (Vsa.Sim.DecodeTable.decode_00040513 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0a#5) v8
      (afterNextPC (afterPrelude σ) (0x80008320#64))
      (sigma3_alu σ (0x80008320#64) Register.x10 (v8 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x10 _ (v8 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008324 — `jal __umoddi3` : x1 := pc+4, PC := 0x800046f4 -/
theorem site_80008324_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008324#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1fc3d0#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008324 hmem
  refine stepObs_jal σ i u (0x80008324#64) vminstret (0xbd0fc0ef#32) (0x1fc3d0#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80008324#64) 4)
    (0xef#8) (0xc0#8) (0x0f#8) (0xbd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    nr_bd0fc0ef_sn w_bd0fc0ef_sn
    (Vsa.Sim.DecodeTable.decode_bd0fc0ef (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x80008324#64) 4)

/-! ### 0x80008328 — `addiw a0,a0,48` = ADDIW(0x030,x10,x10) : x10 := sext32(x10+48) -/
theorem site_80008328_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008328#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x10
          (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0x030#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008328 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80008328#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80008328#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80008328#64) vminstret (0x0305051b#32)
    (instruction.ADDIW (0x030#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x0a#5))
    Register.x10 (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0x030#12)) 31 0))
    (0x1b#8) (0x05#8) (0x05#8) (0x03#8)
    hG hpc hminstret w_0305051b_sn nr_0305051b_sn
    (Vsa.Sim.DecodeTable.decode_0305051b (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_addiw_char (0x030#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x0a#5) v10
      (afterNextPC (afterPrelude σ) (0x80008328#64))
      (sigma3_alu σ (0x80008328#64) Register.x10
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0x030#12)) 31 0)))
      (rX_bits_x10 _ v10 hx10₂)
      (wX_bits_x10 _ (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0x030#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x8000832c — `sb a0,-1(s9)` = STORE(0xfff,x10,x25,1) : mem[x25-1] := x10[7:0] -/
theorem site_8000832c_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v25 v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx25 : σ.regs.get? Register.x25 = some v25)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000832c#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v25 + sign_extend (m := 64) (0xfff#12)).toNat)
    (hhiram : (v25 + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (v25 + sign_extend (m := 64) (0xfff#12)).toNat) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = ((afterNextPC (afterPrelude σ) (0x8000832c#64)).mem.insert
        (v25 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v10)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret
        ((afterNextPC (afterPrelude σ) (0x8000832c#64)).mem.insert
          (v25 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v10))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_8000832c hmem
  exact stepObs_store σ i u (0x8000832c#64) vminstret (0xfeac8fa3#32)
    (instruction.STORE (0xfff#12, regidx.Regidx 0x0a#5, regidx.Regidx 0x19#5, 1))
    ((afterNextPC (afterPrelude σ) (0x8000832c#64)).mem.insert
      (v25 + sign_extend (m := 64) (0xfff#12)).toNat (stData 1 v10))
    (0xa3#8) (0x8f#8) (0xac#8) (0xfe#8)
    hG hpc hminstret w_feac8fa3_sn nr_feac8fa3_sn
    (Vsa.Sim.DecodeTable.decode_feac8fa3 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (exec_sb σ (0x8000832c#64) (0xfff#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x19#5) v25 v10 hG
      (rX_bits_x25 _ v25
        (by rw [get?_afterNextPC σ (0x8000832c#64) _ (by decide) (by decide)]; exact hx25))
      (rX_bits_x10 _ v10
        (by rw [get?_afterNextPC σ (0x8000832c#64) _ (by decide) (by decide)]; exact hx10))
      hlo hhiram hhiwin)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008330 — `addi s10,s9,-1` = ITYPE(0xfff,x25,x26,ADDI) : x26 := x25-1 -/
theorem site_80008330_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v25 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx25 : σ.regs.get? Register.x25 = some v25)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008330#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x26 (v25 + sign_extend (m := 64) (0xfff#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008330 hmem
  have hx25₂ : (afterNextPC (afterPrelude σ) (0x80008330#64)).regs.get? Register.x25 = some v25 := by
    rw [get?_afterNextPC σ (0x80008330#64) _ (by decide) (by decide)]; exact hx25
  exact stepObs_alu σ i u (0x80008330#64) vminstret (0xfffc8d13#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x19#5, regidx.Regidx 0x1a#5, iop.ADDI))
    Register.x26 (v25 + sign_extend (m := 64) (0xfff#12)) (0x13#8) (0x8d#8) (0xfc#8) (0xff#8)
    hG hpc hminstret w_fffc8d13_sn nr_fffc8d13_sn
    (Vsa.Sim.DecodeTable.decode_fffc8d13 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_itype_addi_char (0xfff#12) (regidx.Regidx 0x19#5) (regidx.Regidx 0x1a#5) v25
      (afterNextPC (afterPrelude σ) (0x80008330#64))
      (sigma3_alu σ (0x80008330#64) Register.x26 (v25 + sign_extend (m := 64) (0xfff#12)))
      (rX_bits_x25 _ v25 hx25₂) (wX_bits_x26 _ (v25 + sign_extend (m := 64) (0xfff#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008334 — `addiw s7,s7,1` = ADDIW(0x001,x23,x23) : x23 := sext32(x23+1) -/
theorem site_80008334_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v23 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx23 : σ.regs.get? Register.x23 = some v23)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008334#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x23
          (sign_extend (m := 64) (Sail.BitVec.extractLsb (v23 + sign_extend (m := 64) (0x001#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008334 hmem
  have hx23₂ : (afterNextPC (afterPrelude σ) (0x80008334#64)).regs.get? Register.x23 = some v23 := by
    rw [get?_afterNextPC σ (0x80008334#64) _ (by decide) (by decide)]; exact hx23
  exact stepObs_alu σ i u (0x80008334#64) vminstret (0x001b8b9b#32)
    (instruction.ADDIW (0x001#12, regidx.Regidx 0x17#5, regidx.Regidx 0x17#5))
    Register.x23 (sign_extend (m := 64) (Sail.BitVec.extractLsb (v23 + sign_extend (m := 64) (0x001#12)) 31 0))
    (0x9b#8) (0x8b#8) (0x1b#8) (0x00#8)
    hG hpc hminstret w_001b8b9b_sn nr_001b8b9b_sn
    (Vsa.Sim.DecodeTable.decode_001b8b9b (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (execute_addiw_char (0x001#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x17#5) v23
      (afterNextPC (afterPrelude σ) (0x80008334#64))
      (sigma3_alu σ (0x80008334#64) Register.x23
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (v23 + sign_extend (m := 64) (0x001#12)) 31 0)))
      (rX_bits_x23 _ v23 hx23₂)
      (wX_bits_x23 _ (sign_extend (m := 64) (Sail.BitVec.extractLsb (v23 + sign_extend (m := 64) (0x001#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ### 0x80008338 — `beqz s11,0x800082fc` = BTYPE(0x1fc4,x0,x27,BEQ) (grouping-flag test)

For `%lld` the grouping flag `s11 = t1 & 1024 = 0`, so this branch is **always
taken** back to `0x800082fc` (the quotient step), skipping the grouping code.  We
provide the taken arm (`x27 = 0`); the not-taken arm is dead. -/
theorem site_80008338_taken_sn
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v27 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx27 : σ.regs.get? Register.x27 = some v27)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008338#64 : BitVec 64))
    (hv : (v27 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x1fc4#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := svfprintfSlice_at_80008338 hmem
  have hx27₂ : (afterNextPC (afterPrelude σ) (0x80008338#64)).regs.get? Register.x27 = some v27 := by
    rw [get?_afterNextPC σ (0x80008338#64) _ (by decide) (by decide)]; exact hx27
  exact stepObs_branch_taken σ i u (0x80008338#64) vminstret (0x1fc4#13)
    (regidx.Regidx 0x1b#5) (regidx.Regidx 0x00#5) bop.BEQ (0xfc0d82e3#32) (0xe3#8) (0x82#8) (0x0d#8) (0xfc#8)
    hG hpc hminstret w_fc0d82e3_sn nr_fc0d82e3_sn
    (Vsa.Sim.DecodeTable.decode_fc0d82e3 (afterPrelude σ) (misa_pre σ hG) (priv_pre σ hG) (sec_pre σ hG))
    (exec_beq_taken σ (0x80008338#64) (0x1fc4#13) (regidx.Regidx 0x1b#5) (regidx.Regidx 0x00#5) v27 (0#64)
      hG hpc (rX_bits_x27 _ v27 hx27₂) (rX_bits_zero _) (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
