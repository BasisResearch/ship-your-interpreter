import Vsa.Sim.WhileCondPrefix

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

private theorem eval_basic_headroom (cnd : Expr) (extra : Nat) :
    1088 + 1088 ≤ cnd.stackNeed + extra + 1088 := by
  have hn := Expr.stackNeed_ge cnd
  simp only [evalFrame] at hn
  omega

/-- Direct statement dispatch and the concrete condition-call prefix. -/
theorem execWhileCondDispatch_closed
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (fun cfg => ∃ (gCond : (R : Register) → Option (RegisterType R))
          (aCond : BitVec 64) (mCond : Mem),
        ExecWhileCondCarrier g N A SL φf φc st d env cnd body
          sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond ∧
        EvalEntry gCond N A SL φf φc st d env cnd
          (sp - 176#64) 0x80004050#64 (sp - 96#64) aInterp aCond mCond cfg) := by
  intro cfg hEntry
  have hGround0 : ExecGround m0 SL A sp aRet aStmt.toNat (.whileStmt cnd body) :=
    hEntry.mem ▸ hEntry.ground
  have hStmt0 : StmtRepr m0 aStmt.toNat (.whileStmt cnd body) :=
    hEntry.mem ▸ hEntry.stmt
  have hkind : read32 m0 aStmt.toNat = some 4 := by
    cases hStmt0 with | whileS hk _ _ _ _ => exact hk
  obtain ⟨cA, hsA, ment, v8, v9, v18, v19, hArm⟩ :=
    execBlockA g N A SL φf φc st d env (.whileStmt cnd body) 4 0x8000403c#64
      sp r aInterp aStmt aEnv aRet m0 cfg.σ.sailOutput
      (by decide) (by decide) hkind hGround0.table.slot4 (by decide)
      ⟨by rcases hGround0.table_stack with h | h <;> omega⟩ cfg ⟨hEntry, rfl⟩
  obtain ⟨hG, htick, hpc, hs0, hs1, hs3, hs2, hsp, hra,
    hmi, hout, houtStr, hmem, hcode, hstore,
    hSavedRa, hSavedS0, hSavedS1, hSavedS2, hSavedS3,
    hG8, hG9, hG18, hG19, hGsp, hFrame, hMemFrame,
    hsp176, hspHi, hspLo, hspWin, hsp8, hraAlign, hMemExt⟩ := hArm
  have hpop : StackBytesPresent ment SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := hGround0.stack_bytes k hlo hhi
    exact hMemExt k b hb
  have hGround := hGround0.transport_offstack hEntry.stackOK.2.1 hpop hMemFrame
  have hStmt := hGround0.stmtRepr_offstack hStmt0 hEntry.stackOK.2.1 hMemFrame
  have hCond : ∃ p, read64 ment (aStmt.toNat + 8) = some p ∧ ExprRepr ment p cnd := by
    cases hStmt with | whileS _ hr he _ _ => exact ⟨_, hr, he⟩
  obtain ⟨p, hread, hrepr⟩ := hCond
  let aCond := BitVec.ofNat 64 p
  have hp : aCond.toNat = p := by
    exact Nat.mod_eq_of_lt (read64_lt_eg4 ment (aStmt.toNat + 8) p hread)
  have hreadB : read64 ment (aStmt.toNat + 8) = some aCond.toNat := hp ▸ hread
  have hreprB : ExprRepr ment aCond.toNat cnd := hp ▸ hrepr
  obtain ⟨cC, hsC, hc⟩ := execWhileCondPrefix_run hGround hcode hreadB
    hG htick hpc hmi hmem ⟨hsp, hs0, hs1, hs2, hs3, True.intro⟩
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hsret : (sp - 96#64).toNat = sp.toNat - 96 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hsub : (sp - 176#64) + 80#64 = sp - 96#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hesp, hsret]
    simp only [BitVec.toNat_ofNat]
    omega
  have hroom := hEntry.stackBudget.1
  have hSLhi := hEntry.stackBudget.2.1
  have hbudget : StackOK SL (sp - 176#64)
      (cnd.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    obtain ⟨hlo, hhi, halign⟩ := hEntry.stackBudget
    simp only [Stmt.stackNeed, execFrame] at hlo
    simp only [StackOK, hesp]
    omega
  have hsretSL : SL.lo ≤ (sp - 96#64).toNat ∧
      (sp - 96#64).toNat + 24 ≤ SL.hi := by rw [hsret]; omega
  have hEvalGround := hGround.whileCond_evalGround hreadB
    (spEval := sp - 176#64) (by rw [hesp]; omega) hsretSL
  obtain ⟨lo, hi, hr⟩ := hEvalGround.ast.region
  have hn := exprIn_node hr.nodes
  obtain ⟨hEvalCode, hViCode, _hTruthy, hIntSlot, hNbs, _hTable⟩ :=
    hGround.eval_call.pins ment (fun _ _ => rfl)
  have hStoreSurv : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store := by
    intro m' hag
    apply hEntry.store_survives m'
    intro k hk
    rw [hEntry.mem]
    exact (hMemFrame k (by
      intro hs
      exact hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hSLhi⟩)).symm.trans (hag k hk)
  have h8 := (hc.frame Register.x8 (by decide)).trans hs0
  have h9 := (hc.frame Register.x9 (by decide)).trans hs1
  have h18 := (hc.frame Register.x18 (by decide)).trans hs2
  have h19 := (hc.frame Register.x19 (by decide)).trans hs3
  have hDefined : (∃ v, cC.σ.regs.get? Register.x20 = some v) ∧
      (∃ v, cC.σ.regs.get? Register.x21 = some v) := by
    obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hEntry.envset_defined
    refine ⟨⟨v20, ?_⟩, ⟨v21, ?_⟩⟩
    · rw [hc.frame Register.x20 (by decide), hFrame Register.x20
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hEntry.frame Register.x20 (by decide)).symm.trans hv20
    · rw [hc.frame Register.x21 (by decide), hFrame Register.x21
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hEntry.frame Register.x21 (by decide)).symm.trans hv21
  refine ⟨cC, hsA.trans hsC, (fun R => cC.σ.regs.get? R), aCond, ment, ?_, ?_⟩
  · refine
      { s0 := h8
        s1 := h9
        s2 := h18
        s3 := h19
        spReg := hc.spReg
        parentSp := hGsp
        code := hcode
        code_stack_disjoint := hEntry.code_stack_disjoint
        stack_ram := hEntry.stack_ram
        stack_win := hEntry.stack_win
        ra_align := hraAlign
        stmt := hStmt
        env_addr := hEntry.envPtr
        store := hstore
        env_valid := hEntry.env_valid
        store_survives := hStoreSurv
        saved_ra := hSavedRa
        saved_s0 := ⟨v8, hSavedS0, hG8⟩
        saved_s1 := ⟨v9, hSavedS1, hG9⟩
        saved_s2 := ⟨v18, hSavedS2, hG18⟩
        saved_s3 := ⟨v19, hSavedS3, hG19⟩
        stack_budget := hEntry.stackBudget
        stmt_bodies := hEntry.stmt_bodies
        store_bodies := hEntry.store_bodies
        envset_defined := hDefined
        ground := hGround
        mem_frame := hMemFrame
        mem_extends := hMemExt
        frame := ?_ }
    intro R hR
    by_cases h8 : R = Register.x8
    · exact Or.inl (Or.inl h8)
    by_cases h9 : R = Register.x9
    · exact Or.inl (Or.inr (Or.inl h9))
    by_cases h18 : R = Register.x18
    · exact Or.inl (Or.inr (Or.inr (Or.inl h18)))
    by_cases h19 : R = Register.x19
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h19))))
    by_cases h2 : R = Register.x2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h2))))
    exact Or.inr ((hc.frame R hR.1).trans (hFrame R hR
      (beq_eq_false_iff_ne.mpr (Ne.symm h8)) (beq_eq_false_iff_ne.mpr (Ne.symm h9))
      (beq_eq_false_iff_ne.mpr (Ne.symm h18)) (beq_eq_false_iff_ne.mpr (Ne.symm h19))
      (beq_eq_false_iff_ne.mpr (Ne.symm h2))))
  · refine
      { good := hc.good
        tick := hc.tick
        pc := hc.pc
        a0 := by simpa only [hsub] using hc.a0
        sret_words := hc.mem ▸ hEvalGround.valueWordsTotal hsretSL.1 hsretSL.2
        a1 := hc.a1
        a2 := hc.a2
        ra := hc.ra
        ra_align := by decide
        spReg := hc.spReg
        stackOK := ?_
        stackBudget := hbudget
        expr_bodies := ?_
        store_bodies := hEntry.store_bodies
        minstret := hc.minstret
        mem := hc.mem
        code := hc.mem ▸ hEvalCode
        expr := hc.mem ▸ hreprB
        store := hc.mem ▸ hstore
        env_valid := hEntry.env_valid
        store_survives := ?_
        out := ?_
        frame := fun _ _ => rfl
        code_stack_disjoint := ?_
        expr_stack_disjoint := ?_
        expr_ram := ?_
        expr_win := ?_
        sret_align := ?_
        sret_ram := ?_
        sret_win := ?_
        sret_vicode_disjoint := ?_
        sret_stack_disjoint := ?_
        sret_evalcode_disjoint := ?_
        vicode_stack_disjoint := ?_
        stack_ram := hEntry.stack_ram
        stack_win := hEntry.stack_win
        value_int_code := hc.mem ▸ hViCode
        int_slot := hc.mem ▸ hIntSlot
        table_stack_disjoint := ?_
        nbs_pins := hc.mem ▸ hNbs
        ground := hc.mem ▸ hEvalGround
        spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩⟩
        envset_defined := ⟨aEnv, hDefined.1.choose, hDefined.2.choose,
          h19, hDefined.1.choose_spec, hDefined.2.choose_spec⟩
        envReg := hEntry.envPtr ▸ hc.a3
        x13_defined := ⟨aEnv, hc.a3⟩ }
    · exact StackOK.mono (eval_basic_headroom cnd _) hbudget
    · have hb := hEntry.stmt_bodies
      simp only [Stmt.bodiesBound, Bool.and_eq_true] at hb
      exact hb.1
    · intro m' hag
      apply hStoreSurv m'
      intro k hk
      exact (hc.mem ▸ hag k hk (by rw [hsret]; intro hs; exact hk ⟨by omega, by omega⟩))
    · change String.join cC.σ.sailOutput.toList = st.out
      rw [hc.out, hout]
      exact hEntry.out
    · rcases hGround.eval_call.code_stack with hd | hd
      · left; rw [hesp]; omega
      · exact Or.inr hd
    · have := hn.lo_le; have := hn.hi_ge
      rcases hr.stack_disjoint with hd | hd <;> simp only [hesp] <;> omega
    · exact ⟨Nat.le_trans hr.lo_ram hn.lo_le,
        Nat.le_trans (Nat.add_le_add_left (by decide : 16 ≤ 40) _)
          (Nat.le_trans hn.hi_ge hr.hi_ram)⟩
    · have := hr.win; have := hn.lo_le; omega
    · rw [hsret]; have := hEntry.stackBudget.2.2; omega
    · exact ⟨Nat.le_trans hEntry.stack_ram.1 hsretSL.1,
        Nat.le_trans hsretSL.2 hEntry.stack_ram.2⟩
    · rw [hsret]; have := hEntry.stack_win; rw [hsret] at hsretSL; omega
    · rcases hGround.eval_call.vi_stack with hd | hd <;> rw [hsret] <;>
        rw [hsret] at hsretSL <;> omega
    · right; rw [hesp, hsret]; omega
    · rcases hGround.eval_call.code_stack with hd | hd <;> rw [hsret] <;>
        rw [hsret] at hsretSL <;> omega
    · rcases hGround.eval_call.vi_stack with hd | hd <;> rw [hesp] <;> omega
    · rcases hGround.eval_call.table_stack with hd | hd <;>
        simp only [jumpTableBase] at hd <;> rw [hesp] <;> omega

#print axioms execWhileCondDispatch_closed

end Vsa.Sim
