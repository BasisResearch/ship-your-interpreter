import Vsa.Sim.EvalIntSim4

/-!
# Layer 4 — M4: the `EvalE.null` simulation Triple (`evalNullSim`)

The second M4 leaf case (after `EvalE.int`). Mirrors `evalIntSim`
(`EvalIntSim4.lean`) but for the `EX_NULL` arm (`ExprKind` tag `k = 3`, arm PC
`0x8000342c`). The arm is only two instructions — `jal value_null` (no payload
load; `null` takes no argument) and `j 0x800033ec` — so its block C is exactly
the shared `armTail_v` (`EvalSimCommon.lean`) instantiated at the `value_null`
callee and produced value `.null`.

Structure:

* **`value_null_spec_full`** — the strengthened `value_null` spec: from the null
  callee precondition it runs to a post carrying (besides `ValueRepr … .null`)
  the console-output and memory-frame facts `armTail_v` needs (the base
  `value_null_spec`'s `null_post` omits them). Re-runs the three `value_null`
  instructions, mirroring `value_int_spec`.
* **`blockC_null`** — the arm `ArmEntryK … 0x8000342c Value_nullLoaded .null →
  PreEpilogueV … .null`, via `armTail_v` with `value_null_spec_full` and the two
  arm sites `site_8000342c_ee` / `site_80003430_ee` (proved here from
  `Eval_exprLoaded`, mirroring the int arm's `jal`/`j` sites).
* **`EvalNullSimGoal`/`evalNullSim`** — the `EvalE.null` Triple, composed
  `blockA_k (→ArmEntryK) ≫ blockC_null (→PreEpilogueV .null) ≫ blockD_v
  (→EvalExit .null)`. Null entry predicate `EvalNullEntry` mirrors `EvalEntry`
  but carries `KindSlotPinned 3 0x8000342c` + `Value_nullLoaded` in place of the
  int-specific slot/callee.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The two `EX_NULL` arm sites (@0x8000342c, @0x80003430)

Mirror the int arm's `site_8000340c_ee` (jal) and `site_80003410_ee` (j), with
the null arm's PCs/words: `jal value_null` (`bc0ff0ef`, imm `0x1ff3c0`, target
`0x800027ec`) and `j 0x800033ec` (`fbdff06f`, imm `0x1fffbc`). -/

/-- 0x8000342c: `jal value_null` (imm 0x1ff3c0 → 0x800027ec, rd=x1=ra). -/
theorem site_8000342c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000342c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ff3c0#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret (0x1ff3c0#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_8000342c hmem
  exact stepObs_jal σ i u (0x8000342c#64) vminstret (0xbc0ff0ef#32) (0x1ff3c0#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000342c#64) 4)
    (0xef#8) (0xf0#8) (0x0f#8) (0xbc#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_bc0ff0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt (0x8000342c#64) 4)) hi

/-- 0x80003430: `j 0x800033ec` (jal x0, imm 0x1fffbc → epilogue). -/
theorem site_80003430_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003430#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fffbc#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fffbc#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_80003430 hmem
  exact stepObs_j σ i u (0x80003430#64) vminstret (0xfbdff06f#32) (0x1fffbc#21)
    (0x6f#8) (0xf0#8) (0xdf#8) (0xfb#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fbdff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ## `value_null_spec_full` — strengthened `value_null` (output + memFrame)

`null_post` (`ValueSpec.lean`) carries `ValueRepr … .null` + the `NotWrittenV`
register frame, but NOT the console-output invariance or the sret-buffer memory
frame that `armTail_v` needs. This re-runs the three `value_null` instructions
(`sw zero,0(a0); sd zero,8(a0); ret`), mirroring `value_int_spec`'s output/memFrame
threading, and adds those two facts to the post. -/
theorem value_null_spec_full (g : (R : Register) → Option (RegisterType R)) (buf r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) :
    Triple
      (fun c => GoodState c.σ ∧ Value_nullLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x800027ec#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        NullRegion buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
        c.σ.sailOutput = out0 ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧
        c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        ValueRepr c.σ.mem N φc buf.toNat .null ∧
        c.σ.sailOutput = out0 ∧
        (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hreg, hrettgt, hout, hframe⟩ := hpre
  have htag := null_tag_addr buf
  have hpay := null_pay_addr buf hreg
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x800027ec: sw zero,0(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800027ec c.σ c.tick c.steps (0x800027ec#64) vmi buf hG hpc hmi ha0 hloaded rfl
      (by rw [htag]; exact hreg.lo) (by rw [htag]; have := hreg.hi; omega)
      (by rw [htag]; have := hreg.win; omega) (by rw [htag]; have := hreg.align; omega) htick
  have hmem1' : σ1.mem = writeMap4 c.σ.mem buf.toNat (swData (0#64)) := by
    rw [hmem1, mem_afterNextPC, htag]
  have hpc1 : σ1.regs.get? Register.PC = some (0x800027f0#64 : BitVec 64) := by
    have := obs_store_pc_val hobs1
    rwa [show BitVec.addInt (0x800027ec#64) 4 = (0x800027f0#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_store_other_val hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_store_other_val hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_store_minstret_val hobs1
  have hloaded1 : Value_nullLoaded σ1.mem := by
    rw [hmem1']
    exact loaded_null_writeMap4 c.σ.mem buf.toNat (swData (0#64))
      (by have := hreg.code_disjoint; have := hreg.hi; omega) hloaded
  -- === 0x800027f0: sd zero,8(a0) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800027f0 σ1 i1 (c.steps + 1) (0x800027f0#64) vmi1 buf hG1 hpc1 hmi1 ha0_1 hloaded1 rfl
      (by rw [hpay]; have := hreg.lo; omega) (by rw [hpay]; have := hreg.hi; omega)
      (by rw [hpay]; have := hreg.win; omega) (by rw [hpay]; have := hreg.align; omega) hi1
  have hmem2' : σ2.mem = writeMap8 (writeMap4 c.σ.mem buf.toNat (swData (0#64))) (buf.toNat + 8) (sdData_val (0#64)) := by
    rw [hmem2, mem_afterNextPC, hpay, hmem1']
  have hpc2 : σ2.regs.get? Register.PC = some (0x800027f4#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x800027f0#64) 4 = (0x800027f4#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hloaded2 : Value_nullLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_null_writeMap8 (writeMap4 c.σ.mem buf.toNat (swData (0#64))) (buf.toNat + 8)
      (sdData_val (0#64)) (by have := hreg.code_disjoint; have := hreg.hi; omega) (hmem1' ▸ hloaded1)
  -- === 0x800027f4: ret ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800027f4 σ2 i2 (c.steps + 1 + 1) (0x800027f4#64) vmi2 r hG2 hpc2 hmi2 hra_2 hloaded2 rfl
      hrettgt hi2
  have hsteps : Steps c ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3))
  have hout3 : σ3.sailOutput = c.σ.sailOutput := by
    rw [hobs3.out, sailOutput_sigmaPost_jump_x0, hobs2.out, sailOutput_sigmaPost_store,
      hobs1.out, sailOutput_sigmaPost_store]
  have hmem3eq : σ3.mem = writeMap8 (writeMap4 c.σ.mem buf.toNat (swData (0#64))) (buf.toNat + 8) (sdData_val (0#64)) := by
    rw [hmem3, hmem2']
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩, hsteps, hG3, obs_jr_pc hobs3,
    obs_jr_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2,
    obs_jr_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2,
    obs_jr_minstret hobs3, hi3, ?_, hout3.trans hout, ?_,
    fun R hR => (frame_jr_v hobs3 R hR).trans
      ((frame_store_v hobs2 R hR).trans ((frame_store_v hobs1 R hR).trans (hframe R hR)))⟩
  · -- ValueRepr .null: read32 buf = 0
    show ValueRepr σ3.mem N φc buf.toNat .null
    show read32 σ3.mem buf.toNat = some 0
    rw [hmem3eq, read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap4, swData_toNat]
    rfl
  · -- memFrame: outside [buf, buf+24) both writeMaps pass through to `m0 = c.σ.mem`
    intro k hk
    rw [hmem3eq, getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap4_disjoint _ _ _ _ (by omega), hmem]

/-! ## `blockC_null` — the `EX_NULL` arm via `armTail_v`

`ArmEntryK … 0x8000342c Value_nullLoaded .null → PreEpilogueV … .null`, closing
the arm through `armTail_v` at the `value_null` callee. No payload load precedes
the tail (null takes no argument), so block C *is* the tail. -/
theorem blockC_null
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the sret buffer is disjoint from `value_null`'s code `[0x800027ec,0x800027f8)`
    -- (ArmEntryK carries only the `value_int` code range, so this is supplied here
    -- and threaded from `EvalNullEntry`).
    (hsret_vnull : sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK g N A SL φf φc st (0x8000342c#64) Value_nullLoaded .null
          sp r sret aExpr v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st .null sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hc
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, ha2, hsp, hra, hmiEx, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl⟩ := hc
  -- region facts for `value_null`'s buffer writes and its `ret`
  have hNullRegion : NullRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsret_vnull⟩
  have hrettgt : (BitVec.update ((0x80003430#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt (0x80003430#64) (by decide)]; decide
  refine armTail_v g N A SL φf φc st .null
    (0x8000342c#64) (0x800027ec#64) (0x80003430#64) (0x1ff3c0#21) (0x1fffbc#21) Value_nullLoaded
    sp r sret v8 v9 v18 out0 m0
    (by apply BitVec.eq_of_toNat_eq; decide)   -- jal target = calleeEntry
    (by apply BitVec.eq_of_toNat_eq; decide)   -- addInt armPC 4 = calleeLink
    (by decide)                                -- calleeLink %4 = 0
    (by rw [show (0x80003430#64 + sign_extend (m := 64) (0x1fffbc#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide)  -- j target %4 = 0
    (by apply BitVec.eq_of_toNat_eq; decide)   -- j target = 0x800033ec
    -- jal site
    (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
      site_8000342c_ee σ i u (0x8000342c#64) vmi hGσ hpcσ hmiσ hcodeσ rfl
        (by rw [show (0x8000342c#64 + sign_extend (m := 64) (0x1ff3c0#21) : BitVec 64) = 0x800027ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hiσ)
    -- j site
    (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
      site_80003430_ee σ i u (0x80003430#64) vmi hGσ hpcσ hmiσ hcodeσ rfl
        (by rw [show (0x80003430#64 + sign_extend (m := 64) (0x1fffbc#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hiσ)
    -- callee behavior (value_null_spec_full)
    (fun gc cc mc hGc hLc hmemc hpcc ha0c hra1c hmic htickc houtc hframec => by
      exact value_null_spec_full gc sret (0x80003430#64) N φc mc out0 cc
        ⟨hGc, hLc, hmemc, hpcc, ha0c, hra1c, hmic, htickc, hNullRegion, hrettgt, houtc, hframec⟩)
    -- the massaged arm-entry precondition
    c ⟨ment, hG, htick, hpc, ha0, hs1, hsp, hmiEx, hout, hmem, hcode, hviCode,
      houtStr, hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
      hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
      hsretStk, hsretEvalCode, hSLloSp,
      hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩

/-! ## `NullSlotPinned` — the `EX_NULL` (tag 3) jump-table slot pin

The slot at `jumpTableBase + 12` holds `d4 94 fe ff` (LE) = offset `0xfffe94d4`,
and `0x80019f58 + (Int32)0xfffe94d4 = 0x8000342c` (the null arm). Mirrors
`IntSlotPinned`; discharges `KindSlotPinned 3 0x8000342c` for the loaded image. -/
def NullSlotPinned (m : Mem) : Prop :=
  m[(jumpTableBase + 12 : Nat)]? = some (0xd4 : BitVec 8) ∧
  m[(jumpTableBase + 13 : Nat)]? = some (0x94 : BitVec 8) ∧
  m[(jumpTableBase + 14 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(jumpTableBase + 15 : Nat)]? = some (0xff : BitVec 8)

theorem null_slot_kindPinned {m : Mem} (h : NullSlotPinned m) :
    KindSlotPinned 3 (0x8000342c#64) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0xd4#8, 0x94#8, 0xfe#8, 0xff#8, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using p0
  · simpa using p1
  · simpa using p2
  · simpa using p3
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide

/-! ## `EvalNullEntry` — the machine precondition for the `EvalE.null` case

Mirrors `EvalEntry` (`InterpEntry.lean`), but carries `NullSlotPinned` +
`Value_nullLoaded` (with the value_null geometry) in place of the int-specific
`int_slot`/`value_int_code`, and `ExprRepr … .null` (`read32 = 3`). -/
structure EvalNullEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Vsa.While.Addr)
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
  expr : ExprRepr c.σ.mem aExpr.toNat .null
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
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  /-- sret disjoint from the `value_int` code — the shared `ArmEntryK` field. For
  the null arm this is unused geometrically but kept so `ArmEntryK` is satisfied. -/
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  /-- sret disjoint from the `value_null` code `[0x800027ec, 0x800027f8)` — the
  null callee's sret-write region (`NullRegion.code_disjoint`). -/
  sret_vnullcode_disjoint : sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- `value_null` code `[0x800027ec, 0x800027f8)` disjoint from the stack region —
  keeps `Value_nullLoaded` across the prologue spills. -/
  vnullcode_stack_disjoint : (0x800027f8 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  value_null_code : Value_nullLoaded c.σ.mem
  null_slot : NullSlotPinned c.σ.mem
  table_stack_disjoint : (0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 12
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)

/-- The `EX_NULL` kind tag `read32 = some 3`, from `ExprRepr … .null`. -/
theorem exprRepr_null_kind {m : Mem} {a : Nat} (h : ExprRepr m a .null) :
    read32 m a = some 3 := by
  cases h with
  | null hk => exact hk

/-- **The `EvalE.null` simulation goal.** -/
def EvalNullSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a .null st .null →
    Triple
      (EvalNullEntry g N A SL φf φc st d a sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st .null sp r sret m0)

/-- **The M4 `EvalE.null` gate.** Composes `blockA_k` (prologue + dispatch →
`ArmEntryK` at the null arm), `blockC_null` (arm + `value_null` → epilogue entry),
and `blockD_v` at `.null` (epilogue → return). -/
theorem evalNullSim : EvalNullSimGoal := by
  intro g N A SL φf φc st d a sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  -- === block A: prologue + dispatch → ArmEntryK (via blockA_k) ===
  have hkm0 : read32 m0 aExpr.toNat = some 3 := hc.mem ▸ exprRepr_null_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st .null 3 (0x8000342c#64) Value_nullLoaded
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      (null_slot_kindPinned (hc.mem ▸ hc.null_slot)) (hc.mem ▸ hc.value_null_code)
      (fun mem a8 dd hlo hhi hh => by
        have hvn := hc.vnullcode_stack_disjoint
        exact loaded_null_writeMap8 mem a8 dd (by omega) hh)
      (fun m' hag => by
        -- ExprRepr m' aExpr .null from read32 m' aExpr = read32 m0 aExpr = some 3
        have hstk := hc.expr_stack_disjoint
        have hlo := hc.stackOK.1
        refine ExprRepr.null ?_
        obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m0 aExpr.toNat 3 hkm0
        simp only [read32, readLE, bind, Option.bind]
        rw [← hag aExpr.toNat (by omega), ← hag (aExpr.toNat + 1) (by omega),
            ← hag (aExpr.toNat + 2) (by omega), ← hag (aExpr.toNat + 3) (by omega),
            hb0, hb1, hb2, hb3]
        simp only []; apply congrArg some; omega)
      (by decide)
      (by have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
      hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
      hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
      hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
      hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
      hc.spill_defined⟩, rfl⟩
  -- === block C: arm (jal value_null; j) → PreEpilogueV .null ===
  obtain ⟨c2, hs2, mpre, hPre⟩ :=
    blockC_null g N A SL φf φc st sp r sret aExpr v8 v9 v18 c.σ.sailOutput m0
      hc.sret_vnullcode_disjoint c1 ⟨ment, hArm⟩
  -- === block D: epilogue → EvalExit .null ===
  obtain ⟨c3, hs3, hExit⟩ :=
    blockD_v g N A SL φf φc st .null sp r sret v8 v9 v18 c.σ.sailOutput m0 c2 ⟨mpre, hPre⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩

end Vsa.Sim
