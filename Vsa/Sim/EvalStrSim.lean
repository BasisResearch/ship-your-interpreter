import Vsa.Sim.EvalNullSim
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch03Part22

/-!
# Layer 4 — M4: the `EvalE.str` simulation Triple (`evalStrSim`)

The `EvalE.str` leaf case (`ExprKind` tag `k = 1`, arm PC `0x80003414`). Mirrors
`evalNullSim` (`EvalNullSim.lean`) but with an `ld a1,8(a2)` payload load (the
64-bit `char*` string pointer → `x11`) before the shared `jal <callee>; j` arm
tail — exactly the payload-load shape of `blockC_ee` (`EvalIntSim4.lean`,
`site_80003408_ee`). The arm is three instructions:

    0x80003414: ld a1, 8(a2)     -- load the str payload pointer  (word 0x00863583)
    0x80003418: jal value_str    -- callee fills the sret buffer  (→ 0x8000281c)
    0x8000341c: j   0x800033ec    -- shared PreEpilogue entry

Structure (mirrors `EvalNullSim.lean`):

* **`site_80003414_ee`** — the `ld a1,8(a2)` payload site (identical form to int's
  `site_80003408_ee`, only the PC changes).
* **`site_80003418_ee` / `site_8000341c_ee`** — the `jal value_str` / `j` tail
  sites (mirror `site_8000342c_ee` / `site_80003430_ee`).
* **`exprRepr_str_pay64`** — the `ExprRepr.str` inversion: `read64 (a+8) = p`
  plus `CString m p s` (mirrors `exprRepr_int_pay64`).
* **`value_str_spec_full`** — the strengthened `value_str` spec adding the
  console-output invariance + sret-buffer memory frame `armTail_v` needs (the
  base `str_post` omits both). Re-runs the four `value_str` instructions.
* **`blockC_str`** — the arm `ArmEntryK … 0x80003414 Value_strLoaded (.str s) →
  PreEpilogueV … (.str s)`: runs the `ld` payload site, then `armTail_v` with
  `value_str_spec_full`.
* **`EvalStrEntry` / `evalStrSim`** — the `EvalE.str` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_str (→PreEpilogueV .str s) ≫ blockD_v
  (→EvalExit .str s)`.

## CString survival across the prologue spills (the new difficulty vs null/bool)

`ExprRepr … (.str s)` carries a `CString m p s` fact for the string bytes at the
payload pointer `p`. `blockA_k`'s `hexprSurv` must re-establish `ExprRepr` at the
post-prologue memory `m'` (which agrees with `m0` outside the spill window
`[SL.lo, sp)`). The `read32`/`read64` fields transfer via the `expr_stack_disjoint`
geometry (as for `.int`); the CString bytes `[p, p + s.length]` transfer via
`cstring_agreeP` provided that range is disjoint from `[SL.lo, sp)`. Since the
string pointer `p` is an arbitrary runtime value with no a-priori bound relative
to the stack, `EvalStrEntry` carries a `str_stack_disjoint` field asserting that
disjointness (the string region lives in `.rodata`/heap, disjoint from the live
`eval_expr` stack frame). It is discharged there and threaded into `hexprSurv`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `EX_STR` arm sites (@0x80003414, @0x80003418, @0x8000341c) -/

/-- 0x80003414: `ld a1,8(a2)` → `x11 := payload` (word `0x00863583`, identical
form to int's `site_80003408_ee`; only the PC differs). -/
theorem site_80003414_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003414#64 : BitVec 64))
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
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003414 hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80003414#64)).regs.get? Register.x12 = some vexpr := by
    rw [get?_afterNextPC σ (0x80003414#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80003414#64) vminstret (0x00863583#32)
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
    (exec_ld σ (0x80003414#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x80003414#64) Register.x11
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

/-- 0x80003418: `jal value_str` (word `0xc04ff0ef`, imm `0x1ff404` → `0x8000281c`,
rd=x1=ra). -/
theorem site_80003418_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003418#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff404#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ff404#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003418 hmem
  exact stepObs_jal σ i u (0x80003418#64) vminstret (0xc04ff0ef#32) (0x1ff404#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80003418#64) 4)
    (0xef#8) (0xf0#8) (0x4f#8) (0xc0#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_c04ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x80003418#64) 4)) hi

/-- 0x8000341c: `j 0x800033ec` (word `0xfd1ff06f`, jal x0, imm `0x1fffd0`). -/
theorem site_8000341c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000341c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fffd0#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fffd0#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000341c hmem
  exact stepObs_j σ i u (0x8000341c#64) vminstret (0xfd1ff06f#32) (0x1fffd0#21)
    (0x6f#8) (0xf0#8) (0x1f#8) (0xfd#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fd1ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ## `ExprRepr.str` inversion — the payload the `ld a1,8(a2)` loads -/

/-- An `Expr` node at `a` representing `.str s` pins the kind (`read32 = 1`), the
payload pointer (`read64 (a+8) = p`), and the string bytes (`CString m p s`). The
`EX_STR` arm's `ld a1,8(a2)` loads exactly these 8 payload bytes; `value_str_spec`
then re-reads them into the sret buffer. Mirrors `exprRepr_int_pay64`. -/
theorem exprRepr_str_pay64 {m : Mem} {a : Nat} {s : String}
    (h : ExprRepr m a (.str s)) :
    ∃ p, read32 m a = some 1 ∧ read64 m (a + 8) = some p ∧ CString m p s := by
  cases h with
  | str hk hp hcs => exact ⟨_, hk, hp, hcs⟩

/-- The `EX_STR` kind tag `read32 = some 1`, from `ExprRepr … (.str s)`. -/
theorem exprRepr_str_kind {m : Mem} {a : Nat} {s : String} (h : ExprRepr m a (.str s)) :
    read32 m a = some 1 := by
  cases h with
  | str hk hp hcs => exact hk

/-! ## `value_str_spec_full` — strengthened `value_str` (output + memFrame)

`str_post` (`ValueSpec.lean`) carries `ValueRepr … (.str s)` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the four `value_str` instructions
(`li a5,3; sd a1,8(a0); sw a5,0(a0); ret`), mirroring `value_null_spec_full`'s
output/memFrame threading, and adds those two facts to the post. -/
theorem value_str_spec_full (g : (R : Register) → Option (RegisterType R)) (buf pay r : BitVec 64)
    (s : String) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple
      (fun c => GoodState c.σ ∧ Value_strLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x8000281c#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x11 = some pay ∧
        c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        CString m0 pay.toNat s ∧ StrRegion buf pay s.length ∧
        (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
        c.σ.sailOutput = out0 ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧
        c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        ValueRepr c.σ.mem N φc buf.toNat (.str s) ∧
        c.σ.sailOutput = out0 ∧
        (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hcstr, hreg, hrettgt, hout, hframe⟩ := hpre
  have hpay := str_pay_addr buf hreg.hi
  have htag : (buf + sign_extend (m := 64) (0x000#12)).toNat = buf.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rw [BitVec.add_zero]
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x8000281c: li a5,3 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000281c c.σ c.tick c.steps (0x8000281c#64) vmi hG hpc hmi hloaded rfl htick
  have hmem1eq : σ1.mem = c.σ.mem := by rw [hmem1]
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002820#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000281c#64) 4 = (0x80002820#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x003#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- === 0x80002820: sd a1,8(a0) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002820 σ1 i1 (c.steps + 1) (0x80002820#64) vmi1 buf pay hG1 hpc1 hmi1 ha0_1 ha1_1
      (by rw [hmem1eq]; exact hloaded) rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi1
  have hmem2' : σ2.mem = writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay) := by
    rw [hmem2, mem_afterNextPC, hpay, hmem1eq]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002824#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x80002820#64) 4 = (0x80002824#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_store_other_val hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hloaded2 : Value_strLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_str_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x80002824: sw a5,0(a0) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002824 σ2 i2 (c.steps + 1 + 1) (0x80002824#64) vmi2 buf
      ((0#64) + sign_extend (m := 64) (0x003#12)) hG2 hpc2 hmi2 ha0_2 ha5_2 hloaded2 rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) hi2
  have hmem3' : σ3.mem
      = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
          (swData ((0#64) + sign_extend (m := 64) (0x003#12))) := by
    rw [hmem3, mem_afterNextPC, htag, hmem2']
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002828#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002824#64) 4 = (0x80002828#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_store_other_val hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hloaded3 : Value_strLoaded σ3.mem := by
    rw [hmem3']
    exact loaded_str_writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x003#12)))
      (by have := hreg.code_disjoint; have := hreg.hi; omega)
      (loaded_str_writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)
        (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded)
  -- === 0x80002828: ret ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002828 σ3 i3 (c.steps + 1 + 1 + 1) (0x80002828#64) vmi3 r hG3 hpc3 hmi3 hra_3 hloaded3 rfl
      hrettgt hi3
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  have hmem4eq : σ4.mem = writeMap4 (writeMap8 c.σ.mem (buf.toNat + 8) (sdData_val pay)) buf.toNat
      (swData ((0#64) + sign_extend (m := 64) (0x003#12))) := by rw [hmem4, hmem3']
  have hout4 : σ4.sailOutput = c.σ.sailOutput := by
    rw [hobs4.out, sailOutput_sigmaPost_jump_x0, hobs3.out, sailOutput_sigmaPost_store,
      hobs2.out, sailOutput_sigmaPost_store, hobs1.out, sailOutput_sigmaPost_alu]
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, hG4, obs_jr_pc hobs4,
    obs_jr_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3,
    obs_jr_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3,
    obs_jr_minstret hobs4, hi4, ?_, hout4.trans hout, ?_,
    fun R hR => (frame_jr_v hobs4 R hR).trans
      ((frame_store_v hobs3 R hR).trans ((frame_store_v hobs2 R hR).trans
        ((frame_alu_v hobs1 R hR).trans (hframe R hR))))⟩
  · -- ValueRepr (.str s): tag=3, payload=pay≠0, CString survives
    show ValueRepr σ4.mem N φc buf.toNat (.str s)
    obtain ⟨cs, hcstr0, hlen⟩ := hcstr
    refine ⟨?_, pay.toNat, ?_, hreg.pnz, cs, ?_, hlen⟩
    · show read32 σ4.mem buf.toNat = some 3
      rw [hmem4eq, read32_writeMap4, swData_toNat]; rfl
    · show read64 σ4.mem (buf.toNat + 8) = some pay.toNat
      rw [hmem4eq, read64_writeMap4_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
    · rw [hmem4eq, hmem]
      have hslen : s.length = cs.length := by rw [hlen, String.length_ofList]
      apply cstr_writeMap4_disjoint
      · apply cstr_writeMap8_disjoint _ _ _ _ _ hcstr0
        have := hreg.str_disjoint; rw [← hslen]; omega
      · have := hreg.str_disjoint; rw [← hslen]; omega
  · -- memFrame: outside [buf, buf+24) both writes pass through to `m0 = c.σ.mem`
    intro k hk
    rw [hmem4eq, getElem_writeMap4_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), hmem]

/-! ## `blockC_str` — the `EX_STR` arm (`ld a1,8(a2); jal value_str; j`)

`ArmEntryK … 0x80003414 Value_strLoaded (.str s) → PreEpilogueV … (.str s)`.
Because the arm carries a payload (`x11 := p`), this cannot reuse the payload-free
`armTail_v`; it mirrors int's `blockC_ee` directly, replacing `value_int_spec`
with `value_str_spec_full` and the three arm sites with the `EX_STR` ones. The
string pointer `p` is threaded into `x11`, the sret buffer ends holding
`ValueRepr (.str s)`, and the spills/store/output survive the callee's sret write
(disjoint from `[SL.lo, sp)` and the string bytes). -/
theorem blockC_str
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (s : String)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the sret buffer is disjoint from `value_str`'s code `[0x8000281c,0x8000282c)`
    -- (ArmEntryK carries only the `value_int` code range, so supplied here).
    (hsret_vstr : sret.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ sret.toNat)
    -- `aExpr`'s payload word is outside the stack window (so the pointer read is the
    -- same in `ment` as in `m0`), plus the string payload region geometry
    -- (`StrRegion`'s non-buffer facts): the pointer is nonzero and disjoint from the
    -- sret buffer. Both stated on the ENTRY memory `m0` and transferred to `ment`
    -- via `hmemframe_m0` inside. Threaded from `EvalStrEntry` (the runtime string
    -- lives in rodata/heap, not the sret slot).
    (hexprStk : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat)
    (hstr : ∀ p : Nat, read64 m0 (aExpr.toNat + 8) = some p →
      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat)) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK g N A SL φf φc st (0x80003414#64) Value_strLoaded (.str s)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st (.str s) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hc
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl, _hx11, _hx8, _hx18⟩ := hc
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hpayaddr : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 :=
    expr_pay_addr aExpr hexprHi
  -- payload bytes + pointer from ExprRepr
  obtain ⟨p, hk32, hp64, hpcstr⟩ := exprRepr_str_pay64 hexpr
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hpb0, hpb1, hpb2, hpb3, hpb4, hpb5, hpb6, hpb7, hprec⟩ :=
    read64_bytes ment (aExpr.toNat + 8) p hp64
  -- the loaded payload BitVec value (= the `char*` pointer `p`)
  let payV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  have hpayVnat : payV.toNat = p := by
    show (sign_extend (m := 64)
      ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))).toNat = p
    rw [sext_full, word8_toNat_recon, hprec]
  -- transfer the payload read from `ment` to `m0`: the payload word `[aExpr+8, aExpr+16)`
  -- is outside the spill window `[SL.lo, sp)` (via `hexprStk`), so `ment` and `m0` agree.
  have hp64_m0 : read64 m0 (aExpr.toNat + 8) = some p := by
    rw [← hp64]
    symm
    apply read64_agreeP (P := fun k => ¬ (SL.lo ≤ k ∧ k < sp.toNat))
      (fun k hk => hmemframe_m0 k hk)
    intro k hk; rcases hexprStk with h | h <;> omega
  obtain ⟨hpnz, hpdisj⟩ := hstr p hp64_m0
  have hStrRegion : StrRegion sret payV s.length := by
    refine ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsret_vstr, ?_, ?_⟩
    · rw [hpayVnat]; exact hpnz
    · rw [hpayVnat]; exact hpdisj
  -- ============ 0x80003414: ld a1,8(a2) → x11 := payV ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80003414_ee c.σ c.tick c.steps (0x80003414#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [hpayaddr]; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, htoh]; right; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, hmem]; exact hpb0) (by rw [hpayaddr, hmem]; exact hpb1)
      (by rw [hpayaddr, hmem]; exact hpb2) (by rw [hpayaddr, hmem]; exact hpb3)
      (by rw [hpayaddr, hmem]; exact hpb4) (by rw [hpayaddr, hmem]; exact hpb5)
      (by rw [hpayaddr, hmem]; exact hpb6) (by rw [hpayaddr, hmem]; exact hpb7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003418#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80003414#64) 4 = (0x80003418#64:BitVec 64) from by decide] at this
  have hx11_1 : σ1.regs.get? Register.x11 = some payV :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hviCode1 : Value_strLoaded σ1.mem := by rw [hmem1e]; exact hviCode
  -- ============ 0x80003418: jal value_str → PC := 0x8000281c, x1 := 0x8000341c ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80003418_ee σ1 i1 (c.steps + 1) (0x80003418#64) vmi1 hG1 hpc1 hmi1 (hmem1e ▸ hmem ▸ hcode) rfl
      (by rw [show ((0x80003418#64 : BitVec 64) + sign_extend (m := 64) (0x1ff404#21)) = 0x8000281c#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000281c#64) := by
    have := obs_jal_pc hobs2
    rwa [show ((0x80003418#64 : BitVec 64) + sign_extend (m := 64) (0x1ff404#21)) = 0x8000281c#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink2 : σ2.regs.get? Register.x1 = some (0x8000341c#64) := by
    have := obs_jal_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003418#64 : BitVec 64) 4 = (0x8000341c#64:BitVec 64) from by decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some sret := obs_jal_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hx11_2 : σ2.regs.get? Register.x11 = some payV := obs_jal_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_jal_other hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_jal_minstret hobs2
  have hviCode2 : Value_strLoaded σ2.mem := by rw [hmem2e]; exact hviCode
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_jal, hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  -- ============ jal callee: value_str_spec_full ============
  have hrettgt : (BitVec.update ((0x8000341c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt (0x8000341c#64) (by decide)]; decide
  have hcallpre :
      (GoodState σ2 ∧ Value_strLoaded σ2.mem ∧ σ2.mem = ment ∧
        σ2.regs.get? Register.PC = some (0x8000281c#64 : BitVec 64) ∧
        σ2.regs.get? Register.x10 = some sret ∧ σ2.regs.get? Register.x11 = some payV ∧
        σ2.regs.get? Register.x1 = some (0x8000341c#64) ∧
        (∃ v, σ2.regs.get? Register.minstret = some v) ∧ (⟨σ2, i2, c.steps + 1 + 1⟩ : Config).tick < 2 ∧
        CString ment payV.toNat s ∧ StrRegion sret payV s.length ∧
        (BitVec.update ((0x8000341c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
        σ2.sailOutput = out0 ∧
        (∀ R : Register, NotWrittenV R → σ2.regs.get? R = (fun R => σ2.regs.get? R) R)) := by
    refine ⟨hG2, hviCode2, hmem2e, hpc2, ha0_2, hx11_2, hlink2, ⟨vmi2, hmi2⟩, hi2,
      (by rw [hpayVnat]; exact hpcstr), hStrRegion, hrettgt, hout2, fun R _ => rfl⟩
  obtain ⟨c3, hs3, hG3, hpc3, ha0_3, hlink3, hmi3, htick3, hval3, hout3, hmemframe3, hframe3⟩ :=
    value_str_spec_full (fun R => σ2.regs.get? R) sret payV (0x8000341c#64) s N φc ment out0
      ⟨σ2, i2, c.steps + 1 + 1⟩ hcallpre
  have hpc3' : c3.σ.regs.get? Register.PC = some (0x8000341c#64) := by
    rw [hpc3, show (BitVec.update ((0x8000341c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x8000341c#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hs1_3 : c3.σ.regs.get? Register.x9 = some sret := by
    rw [hframe3 Register.x9 (by decide)]; exact hs1_2
  have hsp_3 : c3.σ.regs.get? Register.x2 = some (sp-1088#64) := by
    rw [hframe3 Register.x2 (by decide)]; exact hsp_2
  have hstep3 : Steps ⟨σ2, i2, c.steps + 1 + 1⟩ c3 := hs3
  -- memory agreement ment ↔ c3.mem outside the sret buffer
  have hAgree : AgreeP (fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24)) ment c3.σ.mem :=
    fun k hk => hmemframe3 k hk
  have hslotRa3 : read64 c3.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotRa
  have hslotS03 : read64 c3.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS0
  have hslotS13 : read64 c3.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS1
  have hslotS23 : read64 c3.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS2
  have hstore3 : StoreRepr c3.σ.mem N A φf φc st.store :=
    hstoreSurv c3.σ.mem (fun k _ hk2 => hmemframe3 k hk2)
  have hcode3 : Eval_exprLoaded c3.σ.mem :=
    loaded_eval_expr_agreeP ment c3.σ.mem
      (fun k hk => hmemframe3 k (by rcases hsretEvalCode with h | h <;> omega)) (hmem ▸ hcode)
  obtain ⟨vmi3, hmi3'⟩ := hmi3
  -- ============ 0x8000341c: j 0x800033ec → PC := 0x800033ec ============
  obtain ⟨c4, i4', hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000341c_ee c3.σ c3.tick c3.steps (0x8000341c#64) vmi3 hG3 hpc3' hmi3' hcode3 rfl
      (by rw [show ((0x8000341c#64 : BitVec 64) + sign_extend (m := 64) (0x1fffd0#21)) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) htick3
  have hstep4 : Step c3 ⟨c4, i4', c3.steps + 1⟩ := by cases c3; exact hs4
  have hmem4e : c4.mem = c3.σ.mem := hmem4
  have hpc4 : c4.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs4
    rwa [show ((0x8000341c#64 : BitVec 64) + sign_extend (m := 64) (0x1fffd0#21)) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_4 : c4.regs.get? Register.x9 = some sret := obs_jr_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_3
  have hsp_4 : c4.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_jr_minstret hobs4
  have hout4 : c4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_jump_x0]; exact hout3
  -- assemble PreEpilogueV at `.str s`
  refine ⟨⟨c4, i4', c3.steps + 1⟩, ?_, c4.mem, hG4, hi4, hpc4, hs1_4, hsp_4, ⟨_, hmi4⟩, hout4, houtStr,
    rfl, hmem4e ▸ hcode3, hmem4e ▸ hval3, hmem4e ▸ hstore3,
    ?_,
    hmem4e ▸ hslotRa3, hmem4e ▸ hslotS03, hmem4e ▸ hslotS13, hmem4e ▸ hslotS23,
    hgx8, hgx9, hgx18, hgx2, ?_,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
  · -- the composed run: step1(ld) ; step2(jal) ; value_str steps ; step4(j)
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
      (hstep3.trans (Steps.single hstep4)))
  · -- the epilogue g-frame: callee-saved (excl x8/x9/x18/x2) preserved across block C
    intro R hR he8 he9 he18 he2
    have hab : AbiPreserved R = true := hR.1
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx11 : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx15 : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx1 : (Register.x1 == R) = false := abi_ne' (by decide)
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11 hnpc' hmii')
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1 hnpc' hmii')
    have f3 : c3.σ.regs.get? R = σ2.regs.get? R := by
      rw [hframe3 R ⟨hx11, hx15, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩]
    have f4 : c4.regs.get? R = c3.σ.regs.get? R :=
      (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f4, f3, f2, f1]
    exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he8 he9 he18 he2
  · -- memFrame: mpre (= c3.mem) vs m0. In sret → left; else compose ment↔m0 and ment↔c3.mem.
    intro a ha _
    rw [hmem4e]
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · exact Or.inr ((hmemframe3 a hsr).symm.trans (hmemframe_m0 a ha))

/-! ## `StrSlotPinned` — the `EX_STR` (tag 1) jump-table slot pin

Slot at `jumpTableBase + 4` holds `bc 94 fe ff` (LE) = offset `0xfffe94bc`, and
`0x80019f58 + (Int32)0xfffe94bc = 0x80003414` (the str arm). Mirrors
`NullSlotPinned`; discharges `KindSlotPinned 1 0x80003414`. -/
def StrSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 4 : Nat)]? = some (0xbc : BitVec 8) ∧
  m[(jumpTableBase + 5 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 6 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 7 : Nat)]? = some (0xff : BitVec 8)

theorem str_slot_kindPinned {m : Mem} (h : StrSlotPinned m) :
    KindSlotPinned 1 (0x80003414#64) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0xbc#8, 0x94#8, 0xfe#8, 0xff#8, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using p0
  · simpa using p1
  · simpa using p2
  · simpa using p3
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide

/-! ## `EvalStrEntry` — the machine precondition for the `EvalE.str` case

Mirrors `EvalNullEntry`, but carries `StrSlotPinned` + `Value_strLoaded` (with the
value_str geometry) in place of the null-specific slot/callee, `ExprRepr … (.str s)`
(kind `read32 = 1`), and — the one field new to `.str` — `str_stack_disjoint` /
`str_sret_disjoint`, placing the runtime string bytes disjoint from the live stack
frame and the sret buffer (they live in rodata/heap). These discharge the
`hexprSurv` CString survival and `blockC_str`'s `hstr`. -/
structure EvalStrEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Vsa.While.Addr) (s : String)
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  a0 : c.σ.regs.get? Register.x10 = some sret
  a1 : c.σ.regs.get? Register.x11 = some aEnv
  a2 : c.σ.regs.get? Register.x12 = some aExpr
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  spReg : c.σ.regs.get? Register.x2 = some sp
  stackOK : StackOK SL sp (1088 + 1088)
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  mem : c.σ.mem = m0
  code : InterpCodeLoaded c.σ.mem
  expr : ExprRepr c.σ.mem aExpr.toNat (.str s)
  store : StoreRepr c.σ.mem N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr c.σ st
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  expr_align : aExpr.toNat % 8 = 0
  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat
  /-- The runtime string bytes `[p, p + s.length]` (at the payload pointer
  `p = read64 m0 (aExpr+8)`) are disjoint from the live stack frame `[SL.lo, sp)` —
  they live in `.rodata`/heap, not the eval_expr stack window. This is what makes
  the `CString m0 p s` survive the prologue spills. -/
  str_stack_disjoint : ∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
    p + s.length < SL.lo ∨ sp.toNat ≤ p
  /-- The string bytes / payload pointer are disjoint from (and nonzero relative to)
  the sret buffer `[sret, sret+24)`. -/
  str_sret_disjoint : ∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
    p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat)
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  /-- sret disjoint from the `value_int` code — the shared `ArmEntryK` field. -/
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  /-- sret disjoint from the `value_str` code `[0x8000281c, 0x8000282c)`. -/
  sret_vstrcode_disjoint : sret.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- `value_str` code `[0x8000281c, 0x8000282c)` disjoint from the stack region —
  keeps `Value_strLoaded` across the prologue spills. -/
  vstrcode_stack_disjoint : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000281c
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  value_str_code : Value_strLoaded c.σ.mem
  str_slot : StrSlotPinned c.σ.mem
  table_stack_disjoint : (0x80019f58 : Nat) + 8 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 4
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)

/-- **The `EvalE.str` simulation goal.** -/
def EvalStrSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (s : String)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a (.str s) st (.str s) →
    Triple
      (EvalStrEntry g N A SL φf φc st d a s sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st (.str s) sp r sret m0)

/-- **The M4 `EvalE.str` gate.** Composes `blockA_k` (prologue + dispatch →
`ArmEntryK` at the str arm), `blockC_str` (arm + `value_str` → epilogue entry),
and `blockD_v` at `.str s` (epilogue → return). -/
theorem evalStrSim : EvalStrSimGoal := by
  intro g N A SL φf φc st d a s sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  -- ExprRepr survival needs the payload pointer `p`; obtain it up front (on m0).
  have hexpr_m0 : ExprRepr m0 aExpr.toNat (.str s) := hc.mem ▸ hc.expr
  obtain ⟨p, hk32, hp64, hpcstr⟩ := exprRepr_str_pay64 hexpr_m0
  -- === block A: prologue + dispatch → ArmEntryK (via blockA_k) ===
  have hkm0 : read32 m0 aExpr.toNat = some 1 := exprRepr_str_kind hexpr_m0
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.str s) 1 (0x80003414#64) Value_strLoaded
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      (str_slot_kindPinned (hc.mem ▸ hc.str_slot)) (hc.mem ▸ hc.value_str_code)
      (fun mem a8 dd hlo hhi hh => by
        have hvs := hc.vstrcode_stack_disjoint
        exact loaded_str_writeMap8 mem a8 dd (by omega) hh)
      (fun m' hag => by
        -- ExprRepr m' aExpr .str s: read32/read64 transfer via expr_stack_disjoint,
        -- and CString via str_stack_disjoint (cstring_agreeP).
        have hstk := hc.expr_stack_disjoint
        have hlo := hc.stackOK.1
        have hstrStk : p + s.length < SL.lo ∨ sp.toNat ≤ p := hc.str_stack_disjoint p (hc.mem.symm ▸ hp64)
        refine ExprRepr.str (p := p) ?_ ?_ ?_
        · -- read32 m' aExpr = read32 m0 aExpr = some 1
          obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m0 aExpr.toNat 1 hkm0
          simp only [read32, readLE, bind, Option.bind]
          rw [← hag aExpr.toNat (by omega), ← hag (aExpr.toNat + 1) (by omega),
              ← hag (aExpr.toNat + 2) (by omega), ← hag (aExpr.toNat + 3) (by omega),
              hb0, hb1, hb2, hb3]
          simp only []; apply congrArg some; omega
        · -- read64 m' (aExpr+8) = read64 m0 (aExpr+8) = some p
          obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
            read64_bytes m0 (aExpr.toNat + 8) p hp64
          simp only [read64, readLE, bind, Option.bind]
          rw [← hag (aExpr.toNat + 8) (by omega), ← hag (aExpr.toNat + 8 + 1) (by omega),
              ← hag (aExpr.toNat + 8 + 2) (by omega), ← hag (aExpr.toNat + 8 + 3) (by omega),
              ← hag (aExpr.toNat + 8 + 4) (by omega), ← hag (aExpr.toNat + 8 + 5) (by omega),
              ← hag (aExpr.toNat + 8 + 6) (by omega), ← hag (aExpr.toNat + 8 + 7) (by omega),
              hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
          simp only []; apply congrArg some; omega
        · -- CString m' p s via cstring_agreeP on the string byte range disjoint from spills
          exact cstring_agreeP (P := fun a => ¬ (SL.lo ≤ a ∧ a < sp.toNat))
            (m := m0) (m' := m') hag
            hpcstr (fun k hk => by rcases hstrStk with h | h <;> omega))
      (by decide)
      (by have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
      hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
      hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
      hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
      hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
      hc.spill_defined⟩, rfl⟩
  -- === block C: arm (ld a1,8(a2); jal value_str; j) → PreEpilogueV .str s ===
  obtain ⟨c2, hs2, mpre, hPre⟩ :=
    blockC_str g N A SL φf φc st s sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0
      hc.sret_vstrcode_disjoint hc.expr_stack_disjoint
      (fun p' hp' => hc.str_sret_disjoint p' (hc.mem.symm ▸ hp'))
      c1 ⟨ment, hArm⟩
  -- === block D: epilogue → EvalExit .str s ===
  obtain ⟨c3, hs3, hExit, _⟩ :=
    blockD_v g N A SL φf φc st (.str s) sp r sret v8 v9 v18 c.σ.sailOutput m0 (fun _ => True)
      c2 ⟨mpre, hPre, trivial⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩

end Vsa.Sim
