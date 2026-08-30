import Vsa.Sim.EvalIntSim3
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 gate: blocks C, D, and the `EvalIntSimGoal` assembly

Completes the `EvalE.int` simulation Triple begun in `EvalIntSim2.lean`
(`blockA_ee`) and `EvalIntSim3.lean` (`spill_roundtrip_ee`, `PreEpilogue`):

* **`blockC_ee`** (`ArmEntry → PreEpilogue`): the `EX_INT` arm — `ld a1,8(a2)`
  (payload → `x11`), `jal value_int` (the callee via `value_int_spec`, with the
  callee ghost `fun R => σ2.regs.get? R`), and `j 0x800033ec` to the shared
  epilogue. The sret buffer holds `ValueRepr (.int n)`; the four spill slots,
  `s1`/`sp`, `eval_expr`, the store, and the output all survive the callee.

* **`blockD_ee`** (`PreEpilogue → EvalExit`): the shared epilogue — four `ld`
  restores (via `spill_roundtrip_ee`), `mv a0,s1`, `addi sp,sp,1088`, `ret`.
  Restores `ra`/`s0`/`s1`/`s2`/`sp`, returns `a0 = sret`, `PC → r`.

* **`evalIntSim`** (`EvalIntSimGoal`): `blockA_ee ≫ blockC_ee ≫ blockD_ee`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim


-- payload address no-wrap for `ld a1,8(a2)`
theorem expr_pay_addr (aExpr : BitVec 64) (h : aExpr.toNat + 16 ≤ 0x100000000) :
    (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
  have hsext : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := aExpr.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blockC_ee
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (n : Int)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => ∃ ment, ArmEntry g N A SL φf φc st n sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpre, PreEpilogue g N A SL φf φc st n sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hvicode, hexpr,
    houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl, _hx11, _hx8, _hx18⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hpayaddr : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 :=
    expr_pay_addr aExpr hexprHi
  -- payload bytes + value from ExprRepr
  obtain ⟨p, hp64, hpn⟩ := exprRepr_int_pay64 hexpr
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hpb0, hpb1, hpb2, hpb3, hpb4, hpb5, hpb6, hpb7, hprec⟩ :=
    read64_bytes ment (aExpr.toNat + 8) p hp64
  -- the loaded payload BitVec value
  let payV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  -- ============ 0x80003408: ld a1,8(a2) → x11 := payV ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80003408_ee c.σ c.tick c.steps (0x80003408#64) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [hpayaddr]; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, htoh]; right; omega) (by rw [hpayaddr]; omega)
      (by rw [hpayaddr, hmem]; exact hpb0) (by rw [hpayaddr, hmem]; exact hpb1)
      (by rw [hpayaddr, hmem]; exact hpb2) (by rw [hpayaddr, hmem]; exact hpb3)
      (by rw [hpayaddr, hmem]; exact hpb4) (by rw [hpayaddr, hmem]; exact hpb5)
      (by rw [hpayaddr, hmem]; exact hpb6) (by rw [hpayaddr, hmem]; exact hpb7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000340c#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80003408#64) 4 = (0x8000340c#64:BitVec 64) from by decide] at this
  have hx11_1 : σ1.regs.get? Register.x11 = some payV :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- thread other regs through step 1 for the callee frame reconstruction
  have hvicode1 : Value_intLoaded σ1.mem := by rw [hmem1e]; exact hvicode
  -- ============ 0x8000340c: jal value_int → PC := 0x8000280c, x1 := 0x80003410 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000340c_ee σ1 i1 (c.steps + 1) (0x8000340c#64) vmi1 hG1 hpc1 hmi1 (hmem1e ▸ hcode) rfl
      (by
        rw [show ((0x8000340c#64 : BitVec 64) + sign_extend (m := 64) (0x1ff400#21)) = 0x8000280c#64 from by apply BitVec.eq_of_toNat_eq; decide]
        decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hobs2
    rwa [show ((0x8000340c#64 : BitVec 64) + sign_extend (m := 64) (0x1ff400#21)) = 0x8000280c#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink2 : σ2.regs.get? Register.x1 = some (0x80003410#64) := by
    have := obs_jal_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000340c#64 : BitVec 64) 4 = (0x80003410#64:BitVec 64) from by decide] at this
  have ha0_2 : σ2.regs.get? Register.x10 = some sret := obs_jal_other' hobs2 Register.x10 (by decide) ha0_1
  have hx11_2 : σ2.regs.get? Register.x11 = some payV := obs_jal_other' hobs2 Register.x11 (by decide) hx11_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_jal_other' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_jal_minstret hobs2
  have hvicode2 : Value_intLoaded σ2.mem := by rw [hmem2e]; exact hvicode
  -- output threading through steps 1,2
  have hout2 : σ2.sailOutput = out0 := by
    rw [hobs2.out, sailOutput_sigmaPost_jal, hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  -- ============ jal callee: value_int_spec ============
  have hIntRegion : IntRegion sret :=
    ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hcallpre : int_pre (fun R => σ2.regs.get? R) sret payV (0x80003410#64) ment out0
      ⟨σ2, i2, c.steps + 1 + 1⟩ := by
    refine ⟨hG2, hvicode2, hmem2e, hpc2, ha0_2, hx11_2, hlink2, ⟨vmi2, hmi2⟩, hi2, hIntRegion,
      (by decide), hout2, fun R _ => rfl⟩
  obtain ⟨c3, hs3, hG3, hpc3, ha0_3, hlink3, hmi3, htick3, hval3, hout3, hmemframe3, _hpres3, hframe3⟩ :=
    value_int_spec (fun R => σ2.regs.get? R) sret payV (0x80003410#64) N φc ment out0
      ⟨σ2, i2, c.steps + 1 + 1⟩ hcallpre
  -- payV.toNat = p, so `.int (ofNat payV.toNat).toInt = .int n`
  have hpayVnat : payV.toNat = p := by
    show (sign_extend (m := 64)
      ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))).toNat = p
    rw [sext_full, word8_toNat_recon, hprec]
  have hvalN : ValueRepr c3.σ.mem N φc sret.toNat (.int n) := by
    have : (BitVec.ofNat 64 payV.toNat).toInt = n := by rw [hpayVnat]; exact hpn
    rw [← this]; exact hval3
  -- recover callee-preserved regs: s1(x9), sp(x2) via NotWrittenV frame (= σ2 reads)
  have hs1_3 : c3.σ.regs.get? Register.x9 = some sret := by
    rw [hframe3 Register.x9 (by decide)]; exact hs1_2
  have hsp_3 : c3.σ.regs.get? Register.x2 = some (sp-1088#64) := by
    rw [hframe3 Register.x2 (by decide)]; exact hsp_2
  have hpc3' : c3.σ.regs.get? Register.PC = some (0x80003410#64) := by
    rw [hpc3, show (BitVec.update ((0x80003410#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x80003410#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hstep3 : Steps ⟨σ2, i2, c.steps + 1 + 1⟩ c3 := hs3
  -- memory agreement ment ↔ c3.mem outside the sret buffer (from value_int's memFrame)
  have hAgree : AgreeP (fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24)) ment c3.σ.mem :=
    fun k hk => hmemframe3 k hk
  -- spill slots survive the sret write (each 8-byte slot disjoint from [sret,sret+24))
  have hslotRa3 : read64 c3.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by
      rcases hsretStk with h | h <;> omega)]; exact hslotRa
  have hslotS03 : read64 c3.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by
      rcases hsretStk with h | h <;> omega)]; exact hslotS0
  have hslotS13 : read64 c3.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by
      rcases hsretStk with h | h <;> omega)]; exact hslotS1
  have hslotS23 : read64 c3.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by
      rcases hsretStk with h | h <;> omega)]; exact hslotS2
  -- StoreRepr survives: c3.mem agrees with ment outside window∪sret (⊇ outside sret)
  have hstore3 : StoreRepr c3.σ.mem N A φf φc st.store :=
    hstoreSurv c3.σ.mem (fun k _ hk2 => hmemframe3 k hk2)
  -- Eval_exprLoaded survives (code region disjoint from sret; ment loaded)
  have hcode3 : Eval_exprLoaded c3.σ.mem :=
    loaded_eval_expr_agreeP ment c3.σ.mem
      (fun k hk => hmemframe3 k (by rcases hsretEvalCode with h | h <;> omega)) hcode
  obtain ⟨vmi3, hmi3'⟩ := hmi3
  -- ============ 0x80003410: j 0x800033ec → PC := 0x800033ec ============
  obtain ⟨c4, i4', hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80003410_ee c3.σ c3.tick c3.steps (0x80003410#64) vmi3 hG3 hpc3' hmi3' hcode3 rfl
      (by rw [show ((0x80003410#64 : BitVec 64) + sign_extend (m := 64) (0x1fffdc#21)) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) htick3
  have hstep4 : Step c3 ⟨c4, i4', c3.steps + 1⟩ := by cases c3; exact hs4
  have hmem4e : c4.mem = c3.σ.mem := hmem4
  have hpc4 : c4.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs4
    rwa [show ((0x80003410#64 : BitVec 64) + sign_extend (m := 64) (0x1fffdc#21)) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_4 : c4.regs.get? Register.x9 = some sret := obs_jr_other' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 : c4.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_jr_minstret hobs4
  have hout4 : c4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_jump_x0]; exact hout3
  -- transfer the per-block facts to c4.mem (= c3.mem)
  refine ⟨⟨c4, i4', c3.steps + 1⟩, ?_, c4.mem, hG4, hi4, hpc4, hs1_4, hsp_4, ⟨_, hmi4⟩, hout4, houtStr,
    rfl, hmem4e ▸ hcode3, hmem4e ▸ hvalN, hmem4e ▸ hstore3,
    ?_,  -- the g-frame at the epilogue
    hmem4e ▸ hslotRa3, hmem4e ▸ hslotS03, hmem4e ▸ hslotS13, hmem4e ▸ hslotS23,
    hgx8, hgx9, hgx18, hgx2, ?_,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
  · -- the composed run: step1 ; step2 ; value_int steps ; step4(j)
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
      (hstep3.trans (Steps.single hstep4)))
  · -- the epilogue g-frame: callee-saved (excl x8/x9/x18/x2) preserved across the
    -- whole block C = value_int frame (NotWrittenV) + the j/ld register frames.
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
    -- σ1: ld a1 writes x11
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11 hnpc' hmii')
    -- σ2: jal writes x1
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1 hnpc' hmii')
    -- c3: value_int NotWrittenV frame
    have f3 : c3.σ.regs.get? R = σ2.regs.get? R := by
      rw [hframe3 R ⟨hx11, hx15, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩]
    -- c4: j writes PC
    have f4 : c4.regs.get? R = c3.σ.regs.get? R :=
      (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f4, f3, f2, f1]
    exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he8 he9 he18 he2
  · -- memFrame: mpre (= c3.mem) vs m0. In sret → left; else compose ment↔m0 and
    -- ment↔c3.mem (value_int only wrote the sret buffer).
    intro a ha _
    rw [hmem4e]
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · exact Or.inr ((hmemframe3 a hsr).symm.trans (hmemframe a ha))

/-- The shared EPILOGUE, `.int`-specialized. The seven restore/return instructions
never inspect the sret buffer contents, so this is just the value-agnostic
`blockD_v` (`EvalSimCommon.lean`) at `v := .int n`; its input `PreEpilogue … n`
is definitionally `PreEpilogueV … (.int n)`. The null/bool/str/var leaf cases
reuse `blockD_v` directly at their own produced value. -/
theorem blockD_ee
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (n : Int)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => ∃ mpre, PreEpilogue g N A SL φf φc st n sp r sret v8 v9 v18 out0 m0 mpre c)
      (EvalExit g N A SL φf φc st (.int n) sp r sret m0) := by
  intro c hpre
  obtain ⟨mpre, hPre⟩ := hpre
  obtain ⟨c', hs, hExit, _⟩ :=
    blockD_v g N A SL φf φc st (.int n) sp r sret v8 v9 v18 out0 m0 (fun _ => True)
      c ⟨mpre, hPre, trivial⟩
  exact ⟨c', hs, hExit⟩

/-- **The M4 gate**: the `EvalE.int` simulation Triple. Composes `blockA_ee`
(prologue + dispatch → arm entry), `blockC_ee` (arm + `value_int` call → epilogue
entry), and `blockD_ee` (epilogue → return). -/
theorem evalIntSim : EvalIntSimGoal := by
  intro g N A SL φf φc st d a n sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  -- run block A (out0 := the entry console output; the `sailOutput = out0` premise is `rfl`)
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_ee g N A SL φf φc st d a n sp r sret aEnv aExpr m0 c.σ.sailOutput c ⟨hc, rfl⟩
  -- run block C
  obtain ⟨c2, hs2, mpre, hPre⟩ :=
    blockC_ee g N A SL φf φc st n sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 c1 ⟨ment, hArm⟩
  -- run block D
  obtain ⟨c3, hs3, hExit⟩ :=
    blockD_ee g N A SL φf φc st n sp r sret v8 v9 v18 c.σ.sailOutput m0 c2 ⟨mpre, hPre⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩

end Vsa.Sim

