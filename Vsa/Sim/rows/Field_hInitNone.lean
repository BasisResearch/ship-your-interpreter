import Vsa.Sim.rows.ScaffoldRows
import Vsa.Sim.DeriveCase
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.BlockTactics2

/-! Concrete `ExecInit.none` bypass: load the null initializer, preserve the
outer environment in `s3`, and branch to the for-loop head. -/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

#derive_case initNoneBypassSeg chain
  [(0x8000423c#64, 0x00843583#32),
   (0x80004240#64, 0x00050993#32)]
    terminator ⟨0x80004244#64, 0x02058463#32,
      0x63#8, 0x84#8, 0x05#8, 0x02#8,
      .br bop.BEQ true, 11, 0, 0x0028#13, 0#21, 0#12⟩

def initNoneBypassL (aStmt aOuter : BitVec 64) : GRegs :=
  [(8, aStmt), (10, aOuter)]

private theorem initNoneBypass_guard (aStmt aOuter : BitVec 64) :
    guardB bop.BEQ
      (srcVal 11 (runGM
        [mkLine 0x8000423c#64 0x00843583#32, mkLine 0x80004240#64 0x00050993#32]
        (initNoneBypassL aStmt aOuter) [[]]))
      (srcVal 0 (runGM
        [mkLine 0x8000423c#64 0x00843583#32, mkLine 0x80004240#64 0x00050993#32]
        (initNoneBypassL aStmt aOuter) [[]])) = true := by
  simp [initNoneBypassL, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    guardB, bytesVal,
    show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl,
    show (mkLine 0x8000423c#64 0x00843583#32).rd = 11 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).kind = MKind.addi from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).rd = 19 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).rs1 = 10 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).imm = 0 from rfl]
  decide

private theorem read64_zero_lpins (ment : Mem) (a : Nat)
    (hread : read64 ment a = some 0) : LPins8 ment a [] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hbytes⟩ :=
      Vsa.Sim.read64_bytes ment a 0 hread
  have hb0z : b0 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b0.toNat = 0 by omega))
  have hb1z : b1 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b1.toNat = 0 by omega))
  have hb2z : b2 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b2.toNat = 0 by omega))
  have hb3z : b3 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b3.toNat = 0 by omega))
  have hb4z : b4 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b4.toNat = 0 by omega))
  have hb5z : b5 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b5.toNat = 0 by omega))
  have hb6z : b6 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b6.toNat = 0 by omega))
  have hb7z : b7 = 0#8 := BitVec.eq_of_toNat_eq (by simpa using (show b7.toNat = 0 by omega))
  subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6; subst b7
  exact ⟨lpin_of_present hb0, lpin_of_present hb1, lpin_of_present hb2,
    lpin_of_present hb3, lpin_of_present hb4, lpin_of_present hb5,
    lpin_of_present hb6, lpin_of_present hb7⟩

private theorem initNoneBypass_facts
    {ment : Mem} {SL : StackLayout} {A : Arena} {aRet : Nat}
    {aStmt : BitVec 64} {cnd step : Option Expr} {body : Stmt}
    (hast : StmtRegionPins ment SL A aRet aStmt.toNat (.forStmt none cnd step body))
    (hcode : Exec_stmtLoaded ment) (aOuter : BitVec 64)
    (hread : read64 ment (aStmt.toNat + 8) = some 0) :
    ChainFacts ment ment (initNoneBypassL aStmt aOuter) [[]] initNoneBypassSeg := by
    chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
    · obtain ⟨lo, hi, hr⟩ := hast.region
      have hn := hr.nodes.1
      have hlo := hn.lo_le
      have hhi := hn.hi_ge
      have hloRam := hr.lo_ram
      have hhiRam := hr.hi_ram
      have hwin := hr.win
      have hea :
          (eaddrM (mkLine 0x8000423c#64 0x00843583#32)
            (initNoneBypassL aStmt aOuter)).toNat = aStmt.toNat + 8 := by
        unfold eaddrM
        simp only [initNoneBypassL, srcVal, lookupG,
          show (mkLine 0x8000423c#64 0x00843583#32).rs1 = 8 from rfl,
          show (mkLine 0x8000423c#64 0x00843583#32).imm = 0x008#12 from rfl]
        simp only [if_true, Option.getD_some]
        rw [BitVec.toNat_add]
        have himm : (LeanRV64DExecutable.Functions.sign_extend (m := 64)
            (0x008#12)).toNat = 8 := by decide
        rw [himm]
        rw [Nat.mod_eq_of_lt (by omega)]
      unfold MemFacts
      rw [show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl, hea]
      change
        (0x80000000 ≤ aStmt.toNat + 8 ∧ aStmt.toNat + 8 + 8 ≤ 0x100000000 ∧
          (aStmt.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aStmt.toNat + 8)) ∧
        LPins8 ment (aStmt.toNat + 8) []
      refine ⟨⟨by omega, by omega, Or.inr (by omega)⟩, ?_⟩
      exact read64_zero_lpins ment (aStmt.toNat + 8) hread
    · exact initNoneBypass_guard aStmt aOuter

theorem field_hInitNone : ∀ (st : SpecSt) (d : Nat) (env : Addr),
    InitNoneResid st d env := by
  intro st d env cnd step body g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment
  intro cfg hpre
  obtain ⟨liveRA, h⟩ := hpre
  have hread : read64 ment (aStmt.toNat + 8) = some 0 := by
    cases h.stmt with
    | forS _ hinit _ _ _ _ =>
      cases hinit with
      | none hz => exact hz
  let lds : List (List (BitVec 8)) := [[]]
  have hfacts := initNoneBypass_facts h.ground.ast h.code aOuter hread
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ', i', hs, hi', hgood, hmem, hout, hpc, hmi', hregs, hframe⟩ :=
    initNoneBypassSeg_seg cfg.σ cfg.tick cfg.steps 0x8000423c#64 vm
      (initNoneBypassL aStmt aOuter) lds h.good h.pc hmi
      (by exact ⟨h.s0, h.a0, trivial⟩)
      (by show KeysOK [8, 10]; decide)
      (by simpa only [h.mem] using hfacts)
      (by show ChainOK 0x8000423c#64 [8, 10] initNoneBypassSeg; decide) h.tick
  refine ⟨⟨σ', i', cfg.steps + evalBlocksFuel initNoneBypassSeg⟩, hs,
    ⟨⟨φf, φc, liveRA, ⟨PhiExtends.refl _ _, PhiExtends.refl _ _, ?_⟩⟩⟩⟩
  have hmem' : σ'.mem = ment := by
    rw [h.mem] at hmem
    simpa only [initNoneBypassSeg, writeLog, evalBlocks, evalBlock] using hmem
  have hs3' : σ'.regs.get? Register.x19 = some aOuter := by
    simp only [initNoneBypassSeg, initNoneBypassL, lds, evalBlocks, evalBlock,
      runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
      show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl,
      show (mkLine 0x8000423c#64 0x00843583#32).rd = 11 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).rd = 19 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).rs1 = 10 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).imm = 0 from rfl] at hregs
    have hz : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0#12) = 0#64 := by decide
    simp [SegEvalState.init, eraseG, lookupG] at hregs
    simpa only [hz, BitVec.add_zero] using hregs.1
  refine
    { good := hgood
      tick := hi'
      pc := hpc
      s0 := ?_
      s1 := ?_
      s2 := ?_
      s3 := hs3'
      spReg := ?_
      ra := ?_
      mem := rfl
      code := by rw [hmem']; exact h.code
      stmt := by rw [hmem']; exact h.stmt
      outer_addr := h.outer_addr
      store := by rw [hmem']; exact h.store
      env_valid := h.env_valid
      store_survives := by simpa only [hmem'] using h.store_survives
      stack_ram := h.stack_ram
      stack_win := h.stack_win
      code_stack_disjoint := h.code_stack_disjoint
      out := ?_
      saved_ra := by rw [hmem']; exact h.saved_ra
      saved_s0 := by rw [hmem']; exact h.saved_s0
      saved_s1 := by rw [hmem']; exact h.saved_s1
      saved_s2 := by rw [hmem']; exact h.saved_s2
      saved_s3 := by rw [hmem']; exact h.saved_s3
      x20_defined := by
        obtain ⟨v, hv⟩ := h.x20_defined
        exact ⟨v, (hframe Register.x20 (by decide) (by decide)).trans hv⟩
      x21_defined := by
        obtain ⟨v, hv⟩ := h.x21_defined
        exact ⟨v, (hframe Register.x21 (by decide) (by decide)).trans hv⟩
      stack_budget := h.stack_budget
      stmt_bodies := h.stmt_bodies
      store_bodies := h.store_bodies
      ground := by rw [hmem']; exact h.ground
      mem_frame := fun a ha hA => by rw [hmem']; exact h.mem_frame a ha hA
      frame := ?_
      minstret := hmi'
      parentSp := h.parentSp
      ra_align := h.ra_align
      mem_extends := by rw [hmem']; exact h.mem_extends }
  · rw [hframe Register.x8 (by decide) (by decide)]; exact h.s0
  · rw [hframe Register.x9 (by decide) (by decide)]; exact h.s1
  · rw [hframe Register.x18 (by decide) (by decide)]; exact h.s2
  · rw [hframe Register.x2 (by decide) (by decide)]; exact h.spReg
  · rw [hframe Register.x1 (by decide) (by decide)]; exact h.ra
  · change Machine.output σ' = st.out
    change String.join σ'.sailOutput.toList = st.out
    rw [hout]; exact h.out
  · intro R hR
    by_cases hspecial : R = Register.x8 ∨ R = Register.x9 ∨
        R = Register.x18 ∨ R = Register.x19 ∨ R = Register.x2
    · exact Or.inl hspecial
    · right
      have hold : cfg.σ.regs.get? R = g R := by
        rcases h.frame R hR with hclob | hold
        · exact False.elim (hspecial hclob)
        · exact hold
      rw [hframe R (abiNoise_noiseRegs hR)
        (by
          intro n hn
          change n ∈ [11, 19] at hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl
          · have hne : Register.x11 ≠ R := by
              intro heq
              subst R
              exact Bool.noConfusion hR.1
            simpa [gprReg] using hne
          · have hne : Register.x19 ≠ R := by
              intro heq
              exact hspecial (Or.inr (Or.inr (Or.inr (Or.inl heq.symm))))
            simpa [gprReg] using hne)]
      exact hold

end Vsa.Sim.ScaffoldRows

#print axioms Vsa.Sim.ScaffoldRows.field_hInitNone
