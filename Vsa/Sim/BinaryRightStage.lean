import Vsa.Sim.BinarySecondData
import Vsa.Sim.BinaryPrefixRun
import Vsa.Sim.BinaryPrefixOwnership
import Vsa.Sim.EvalBinSim
import Vsa.Sim.JalPreCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- The actual total kind word reloaded and respilled between the children. -/
def BinaryPrefix.leftKind (m : Mem) (sp : BitVec 64) : BitVec 64 :=
  bytesVal .lw (EvalChildArm.wordLds8 m (sp.toNat + 120))

/-- The actual total payload word loaded into the right call's saved register. -/
def BinaryPrefix.leftPayload (m : Mem) (sp : BitVec 64) : BitVec 64 :=
  bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 128))

/-- The right call uses its reached register ghost and the left return's maps. -/
structure BinaryRightStaged
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (before after : Config) : Prop where
  frame : ∀ R, AbiPreservedNoise R → before.σ.regs.get? R = gpre R
  window : BinaryPrefix.Window SL (sp - 1088#64)
  call : JalPreCore er after st d env (fun R => after.σ.regs.get? R) N A SL φf φc
    0x80003518#64 0x8000351c#64 0x1ffc4c#21 sp r sret
    ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aEnv aROp v8 v9 v18
    before.σ.sailOutput after.σ.mem
  segment : ∃ br, CountedSelectedFramedSegResult BinaryPrefix.secondSeg
    (BinaryPrefix.secondInput aExpr (sp - 1088#64) aEnv)
    (BinaryPrefix.secondLoads before.σ.mem (sp - 1088#64) br)
    0x800034fc#64 (BinaryPrefix.secondFoot (sp - 1088#64)) BinaryPrefix.secondKeep
    [(12, aROp), (13, BitVec.ofNat 64 (φf env)),
      (16, BinaryPrefix.leftKind before.σ.mem (sp - 1088#64)),
      (10, (sp - 1088#64) + 144#64), (11, aEnv),
      (19, BinaryPrefix.leftPayload before.σ.mem (sp - 1088#64)),
      (2, sp - 1088#64), (8, aExpr), (18, aEnv)] before after

/-- Stage the right operand through the counted reflected prefix. -/
theorem binaryR_midStaged_of_nodeWindow
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config)
    -- SubEvalReturn-supplied register/state facts at cL:
    (hGL : GoodState cL.σ) (htickL : cL.tick < 2)
    (hpcL : cL.σ.regs.get? Register.PC = some (0x800034fc#64))
    (hs1L : cL.σ.regs.get? Register.x9 = some sret)
    (hspL : cL.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hmiL : ∃ w, cL.σ.regs.get? Register.minstret = some w)
    (houtStrL : String.join cL.σ.sailOutput.toList = st'.out)
    (hframeL : ∀ R : Register, AbiPreservedNoise R → cL.σ.regs.get? R = gpre R)
    (hx8L : cL.σ.regs.get? Register.x8 = some aExpr)
    (hx18L : cL.σ.regs.get? Register.x18 = some aEnv)
    (hgx8v : gpre Register.x8 = some aExpr) (hgx18v : gpre Register.x18 = some aEnv)
    (henvValid : EnvValid st' env)
    (henvRead : read64 cL.σ.mem (sp.toNat - 1088) =
      some (BitVec.ofNat 64 (φf1 env)).toNat)
    (henvset : ∃ w19 w20 w21 : BitVec 64,
      gpre Register.x19 = some w19 ∧ gpre Register.x20 = some w20 ∧
        gpre Register.x21 = some w21)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    -- the transported right-operand pointer + node bytes present:
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
    -- StoreRepr / ExprRepr / Value_intLoaded / IntSlotPinned survival at cL.σ.mem:
    (hstoreCL : StoreRepr cL.σ.mem N A φf1 φc1 st'.store)
    (hstoreSurvCL : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        cL.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store)
    (hexprSurvCL : ∀ m : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → cL.σ.mem[k]? = m[k]?) →
      ExprRepr m aROp.toNat er)
    (hviCL : Value_intLoaded cL.σ.mem) (hviSlotCL : IntSlotPinned cL.σ.mem)
    (hnbsCL : NBSPins cL.σ.mem)
    (hslotRaL : read64 cL.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS0L : read64 cL.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS1L : read64 cL.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS2L : read64 cL.σ.mem (sp.toNat - 32) = some v18.toNat)
    -- geometry (BinExtras-shaped):
    (hnode_hi : aExpr.toNat + 32 ≤ 0x100000000)
    (hnode_lo : 0x80000000 ≤ aExpr.toNat)
    (hnode_win : tohostAddr + 16 ≤ aExpr.toNat)
    (hrop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000)
    (hrop_win : tohostAddr + 16 ≤ aROp.toNat)
    (hrop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat)
    (hrop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat)
    (hsp1088 : 1088 ≤ sp.toNat)
    (hsproom : SL.lo + 3264 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi)
    (hsp16 : sp.toNat % 16 = 0) (hsphi : sp.toNat ≤ 0x100000000)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhiRam : SL.hi ≤ 0x100000000)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)
    (htableStk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    -- ITEM ZERO B1: the RIGHT operand's recursion-sound budget at `sp - 1088`,
    -- its `.fn`-bodies bound, and the post-LEFT store-bodies invariant
    -- (threaded; the caller derives them at the arm entry).
    (hstackBudgetR : StackOK SL (sp - 1088#64)
      (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodiesR : Expr.bodiesBound Vsa.While.perCallBudget er = true)
    (hstoreBodiesR : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    -- WAVE 47i: the RIGHT child's entry-ground bundle at `cL.σ.mem`, carried at
    -- the PARENT windows (re-cut to the child windows below via `child_at`).
    (hGroundR_CL : EvalGround cL.σ.mem SL A sp sret aROp.toNat er) :
    LandedN 7 cL (BinaryRightStaged gpre N A SL φf1 φc1 st' d env er
      sp r sret aExpr aEnv aROp v8 v9 v18 cL) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have geometry : BinaryPrefix.Geometry aExpr (sp - 1088#64) :=
    { nodeLo := hnode_lo
      nodeHi := hnode_hi
      nodeHtif := Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide : 8 ≤ 16) _) hnode_win)
      stackLo := by rw [hspsub]; omega
      stackHi := by rw [hspsub]; omega
      stackHtif := by
        rw [hspsub, htoh]
        have bound := hSLwin
        rw [htoh] at bound
        omega
      stackAlign := by rw [hspsub]; omega }
  obtain ⟨br, data⟩ := BinaryPrefix.second_data cL.σ.mem aExpr (sp - 1088#64)
    aEnv aROp geometry hcodeL hnode
  let be := EvalChildArm.wordLds8 cL.σ.mem (sp - 1088#64).toNat
  let bk := EvalChildArm.wordLds8 cL.σ.mem ((sp - 1088#64).toNat + 120)
  let bp := EvalChildArm.wordLds8 cL.σ.mem ((sp - 1088#64).toNat + 128)
  have henv : bytesVal .ld be = BitVec.ofNat 64 (φf1 env) :=
    EvalChildArm.bytesVal_ld_wordLds cL.σ.mem (sp - 1088#64).toNat _
      (by rw [hspsub]; exact henvRead)
  obtain ⟨c7, segment⟩ := BinaryPrefix.second_counted aExpr (sp - 1088#64) aEnv aROp
    (BitVec.ofNat 64 (φf1 env)) (BinaryPrefix.leftKind cL.σ.mem (sp - 1088#64))
    (BinaryPrefix.leftPayload cL.σ.mem (sp - 1088#64)) br be bk bp cL hGL htickL hpcL
    ⟨hx8L, hspL, hx18L, trivial⟩ data.facts data.load.value henv rfl rfl
  obtain ⟨hx12τ7, hx13τ7, hx16τ7, ha0τ7, hx11τ7, hx19τ7, hspτ7, _hx8, _hx18, _⟩ :=
    segment.selected_regs
  have hGτ7 := segment.good
  have hj7 := segment.tick
  have hpcτ7 : c7.σ.regs.get? Register.PC = some 0x80003518#64 := segment.pc
  have hs1τ7 := (segment.reg_frame .x9 (by decide)).trans hs1L
  obtain ⟨vmiτ7, hmiτ7⟩ := segment.minstret
  have houtτ7 := segment.output
  have haddr144' : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  let mcall2 : Mem := writeMap8 cL.σ.mem (sp.toNat - 1088)
    (sdData_val (BinaryPrefix.leftKind cL.σ.mem (sp - 1088#64)))
  have hmemτ7e : c7.σ.mem = mcall2 := by
    rw [segment.mem, BinaryPrefix.second_log]
    change writeMap8 cL.σ.mem (sp - 1088#64).toNat
      (sdData_val (BinaryPrefix.leftKind cL.σ.mem (sp - 1088#64))) = mcall2
    rw [hspsub]
  have hcodeτ7 : Eval_exprLoaded mcall2 :=
    loaded_eval_expr_agreeP cL.σ.mem mcall2
      (fun k hk => (getElem_writeMap8_disjoint cL.σ.mem (sp.toNat-1088) k _
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodeL
  -- agreement `cL.mem ↔ mcall2` outside the stack region `[SL.lo, sp)`.
  have hAgMcall2 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → cL.σ.mem[k]? = mcall2[k]? := by
    intro k hk
    show cL.σ.mem[k]? = (writeMap8 cL.σ.mem (sp.toNat - 1088) _)[k]?
    rw [getElem_writeMap8_disjoint cL.σ.mem (sp.toNat - 1088) k _ (by omega)]
  -- `StoreRepr mcall2` + survival
  have hstore2 : StoreRepr mcall2 N A φf1 φc1 st'.store :=
    hstoreSurvCL mcall2 (fun k hk1 hk2 => hAgMcall2 k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩))
  have hstoreSurv2 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mcall2[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store := by
    intro m' hag
    refine hstoreSurvCL m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hspSLhi⟩
    rw [hAgMcall2 k hk1']; exact hag k hk1 hk2
  have hexprR2 : ExprRepr mcall2 aROp.toNat er := hexprSurvCL mcall2 hAgMcall2
  have hnbs2 : NBSPins mcall2 :=
    hnbsCL.survive_stack hviStk htableStk hAgMcall2
  -- WAVE 47i: the RIGHT child's entry-ground bundle at `mcall2`, child windows —
  -- the carried parent-window ground re-cut by `child_at` (identity projection)
  -- across the single in-stack `sd` write.
  have hGroundR2 : EvalGround mcall2 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aROp.toNat er :=
    hGroundR_CL.child_at (fun _ _ h => h) (fun a ha => (hAgMcall2 a ha).symm)
      (hGroundR_CL.stack_bytes_extend (memExtends_writeMap8 cL.σ.mem
        (sp.toNat - 1088) _))
      htableStk hspSLhi (by rw [hspsub]; omega)
      (by rw [haddr144']; omega) (by rw [haddr144']; omega)
  -- `Value_intLoaded` / `IntSlotPinned` for mcall2
  have hviInt2 : Value_intLoaded mcall2 :=
    loaded_value_int_agreeP cL.σ.mem mcall2
      (fun a ha => hAgMcall2 a (by rcases hviStk with h | h <;> omega)) hviCL
  have hviSlot2 : IntSlotPinned mcall2 :=
    intSlot_writeMap8 cL.σ.mem (sp.toNat - 1088) _
      (by simp only [jumpTableBase]; rcases htableStk with h | h
          · right; omega
          · left; omega) hviSlotCL
  -- the RIGHT frame's four spill slots survive the sp-1088 store (disjoint below)
  have hslotRa2 : read64 mcall2 (sp.toNat - 8) = some r.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 8) (sp.toNat - 1088) _ (by omega)]; exact hslotRaL
  have hslotS02 : read64 mcall2 (sp.toNat - 16) = some v8.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 16) (sp.toNat - 1088) _ (by omega)]; exact hslotS0L
  have hslotS12 : read64 mcall2 (sp.toNat - 24) = some v9.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 24) (sp.toNat - 1088) _ (by omega)]; exact hslotS1L
  have hslotS22 : read64 mcall2 (sp.toNat - 32) = some v18.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 32) (sp.toNat - 1088) _ (by omega)]; exact hslotS2L
  -- the RIGHT ghost `gR7 := c7.σ.regs.get?`: agrees with gpre on AbiPreservedNoise\{x19}
  have hframeτ7_excl : ∀ R : Register, AbiPreservedNoise R → (Register.x19 == R) = false →
      c7.σ.regs.get? R = gpre R := by
    have keep : ∀ R, AbiPreservedNoise R → (Register.x19 == R) = false →
        BinaryPrefix.secondKeep R = true := by
      intro R
      cases R <;> decide
    exact fun R hR h19 => (segment.reg_frame R (keep R hR h19)).trans (hframeL R hR)
  have hgR7_8 : c7.σ.regs.get? Register.x8 = some aExpr :=
    (hframeτ7_excl Register.x8 (by decide) (by decide)).trans hgx8v
  have hgR7_18 : c7.σ.regs.get? Register.x18 = some aEnv :=
    (hframeτ7_excl Register.x18 (by decide) (by decide)).trans hgx18v
  -- ============ land at τ7 (the RIGHT jal PC 0x80003518) as `JalPreBundle er` ============
  obtain ⟨_w19, w20, w21, _hw19, hw20, hw21⟩ := henvset
  refine ⟨7, c7, Nat.le_refl _, segment.steps.toN_of_stepsEq (by exact segment.count), ?_⟩
  refine
    { frame := hframeL
      window :=
        { lo := by rw [hspsub]; omega
          hi := by rw [hspsub]; omega }
      segment := ⟨br, segment⟩
      call := ?_ }
  rw [hmemτ7e]
  exact ⟨henvValid,
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),
      (by apply BitVec.eq_of_toNat_eq; decide),
      (by decide),
      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80003518_ee σ i u (0x80003518#64) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),
      hGτ7, hj7, hpcτ7, ha0τ7, hs1τ7, hx11τ7, hx13τ7, hx12τ7, hspτ7, ⟨vmiτ7, hmiτ7⟩,
      houtτ7, houtStrL, hmemτ7e,
      hGroundR2.valueWordsTotal (by rw [haddr144']; omega) (by rw [haddr144']; omega),
      hcodeτ7, hviInt2, hviSlot2, hnbs2, hGroundR2, hexprR2, hstore2, hstoreSurv2,
      (fun R hR => rfl), ⟨⟨aExpr, hgR7_8⟩, ⟨aEnv, hgR7_18⟩,
        ⟨_, hx19τ7⟩,
        ⟨w20, (hframeτ7_excl Register.x20 (by decide) (by decide)).trans hw20⟩,
        ⟨w21, (hframeτ7_excl Register.x21 (by decide) (by decide)).trans hw21⟩⟩,
      hslotRa2, hslotS02, hslotS12, hslotS22,
      hrop_ram.1, hrop_ram.2, hrop_win, hrop_stk,
      (by rw [haddr144']; omega), (by rw [haddr144']; omega), (by rw [haddr144']; omega),
      (by omega), hspSLhi, hsp16, (by omega), hSLlo, hSLhiRam, hSLwin,
      hcodeStk, hviStk, htableStk, harenaStk, harenaCode,
      hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩



/-- Preserve the legacy node-window premise while using the reflected prefix. -/
theorem binaryR_midStaged
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf1 φc1 : Addr → Nat)
    (st' : Vsa.While.St) (d : Nat) (env : Addr) (er : Expr)
    (sp r sret aExpr aEnv aROp : BitVec 64) (v8 v9 v18 : BitVec 64)
    (cL : Config)
    -- SubEvalReturn-supplied register/state facts at cL:
    (hGL : GoodState cL.σ) (htickL : cL.tick < 2)
    (hpcL : cL.σ.regs.get? Register.PC = some (0x800034fc#64))
    (hs1L : cL.σ.regs.get? Register.x9 = some sret)
    (hspL : cL.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hmiL : ∃ w, cL.σ.regs.get? Register.minstret = some w)
    (houtStrL : String.join cL.σ.sailOutput.toList = st'.out)
    (hframeL : ∀ R : Register, AbiPreservedNoise R → cL.σ.regs.get? R = gpre R)
    (hx8L : cL.σ.regs.get? Register.x8 = some aExpr)
    (hx18L : cL.σ.regs.get? Register.x18 = some aEnv)
    (hgx8v : gpre Register.x8 = some aExpr) (hgx18v : gpre Register.x18 = some aEnv)
    (henvValid : EnvValid st' env)
    (henvRead : read64 cL.σ.mem (sp.toNat - 1088) =
      some (BitVec.ofNat 64 (φf1 env)).toNat)
    (henvset : ∃ w19 w20 w21 : BitVec 64,
      gpre Register.x19 = some w19 ∧ gpre Register.x20 = some w20 ∧
        gpre Register.x21 = some w21)
    (hcodeL : Eval_exprLoaded cL.σ.mem)
    -- the transported right-operand pointer + node bytes present:
    (hnode : read64 cL.σ.mem (aExpr.toNat + 24) = some aROp.toNat)
    -- StoreRepr / ExprRepr / Value_intLoaded / IntSlotPinned survival at cL.σ.mem:
    (hstoreCL : StoreRepr cL.σ.mem N A φf1 φc1 st'.store)
    (hstoreSurvCL : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        cL.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store)
    (hexprSurvCL : ∀ m : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → cL.σ.mem[k]? = m[k]?) →
      ExprRepr m aROp.toNat er)
    (hviCL : Value_intLoaded cL.σ.mem) (hviSlotCL : IntSlotPinned cL.σ.mem)
    (hnbsCL : NBSPins cL.σ.mem)
    (hslotRaL : read64 cL.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS0L : read64 cL.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS1L : read64 cL.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS2L : read64 cL.σ.mem (sp.toNat - 32) = some v18.toNat)
    -- geometry (BinExtras-shaped):
    (hnode_hi : aExpr.toNat + 32 ≤ 0x100000000)
    (hnode_lo : 0x80000000 ≤ aExpr.toNat)
    (hnode_win : tohostAddr + 32 ≤ aExpr.toNat)
    (hrop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000)
    (hrop_win : tohostAddr + 16 ≤ aROp.toNat)
    (hrop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat)
    (hrop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat)
    (hsp1088 : 1088 ≤ sp.toNat)
    (hsproom : SL.lo + 3264 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi)
    (hsp16 : sp.toNat % 16 = 0) (hsphi : sp.toNat ≤ 0x100000000)
    (hSLlo : 0x80000000 ≤ SL.lo) (hSLhiRam : SL.hi ≤ 0x100000000)
    (hSLwin : tohostAddr + 16 ≤ SL.lo)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo)
    (hviStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)
    (htableStk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (harenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)
    -- ITEM ZERO B1: the RIGHT operand's recursion-sound budget at `sp - 1088`,
    -- its `.fn`-bodies bound, and the post-LEFT store-bodies invariant
    -- (threaded; the caller derives them at the arm entry).
    (hstackBudgetR : StackOK SL (sp - 1088#64)
      (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088))
    (hexprBodiesR : Expr.bodiesBound Vsa.While.perCallBudget er = true)
    (hstoreBodiesR : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
    -- WAVE 47i: the RIGHT child's entry-ground bundle at `cL.σ.mem`, carried at
    -- the PARENT windows (re-cut to the child windows below via `child_at`).
    (hGroundR_CL : EvalGround cL.σ.mem SL A sp sret aROp.toNat er) :
    LandedN 7 cL (BinaryRightStaged gpre N A SL φf1 φc1 st' d env er
      sp r sret aExpr aEnv aROp v8 v9 v18 cL) := by
  exact binaryR_midStaged_of_nodeWindow gpre N A SL φf1 φc1 st' d env er sp r sret aExpr aEnv aROp
    v8 v9 v18 cL hGL htickL hpcL hs1L hspL hmiL houtStrL hframeL hx8L hx18L hgx8v hgx18v
    henvValid henvRead henvset hcodeL hnode hstoreCL hstoreSurvCL hexprSurvCL
    hviCL hviSlotCL hnbsCL hslotRaL hslotS0L hslotS1L hslotS2L hnode_hi hnode_lo
    (Nat.le_trans (Nat.add_le_add_left (by decide : 16 ≤ 32) _) hnode_win)
    hrop_ram hrop_win hrop_stk hrop_stkfull hsp1088 hsproom hspSLhi hsp16 hsphi
    hSLlo hSLhiRam hSLwin hcodeStk hviStk htableStk harenaStk harenaCode
    hstackBudgetR hexprBodiesR hstoreBodiesR hGroundR_CL

#print axioms binaryR_midStaged_of_nodeWindow

#print axioms binaryR_midStaged

end Vsa.Sim
