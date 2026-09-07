import Vsa.Sim.WhileBodyResume
import Vsa.Sim.ExecRetEpilogue

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- Propagate a returning body's value through the memory-pure parent epilogue.
The return value retains the child's independently selected closure map. -/
theorem execWhileBodyResume_ret
    {g gBody : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φfBody φcBody : Addr → Nat}
    {st stCond stMid : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {rv : Value}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64} {m0 mBody : Mem}
    (hSize : StoreLe st.store stCond.store)
    (_hBody : ExecS stCond d env body stMid (.ret rv))
    (hpf : PhiExtends φf φfBody st.store.frames.size)
    (hpc : PhiExtends φc φcBody st.store.closures.size)
    (h : ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody) :
    Triple
      (ExecExitD gBody N A SL φfBody φcBody stCond.store.frames.size
        stCond.store.closures.size stMid (.ret rv)
        (sp - 176#64) 0x80004088#64 aRet mBody)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        stMid (.ret rv) sp r aRet m0) := by
  intro cfg hChild
  obtain ⟨φf', φc', hpf', hpc', hk⟩ := execWhileBodyExitKit_of_exit h hChild
  obtain ⟨cR, ⟨⟨hgood, hmem, hout, hroutePC, _⟩, hframe, htick, hmi⟩, hrun⟩ :=
    hk.resume
  have hmR : cR.σ.mem = cfg.σ.mem := hmem
  have hpcR : cR.σ.regs.get? Register.PC = some 0x80004150#64 := hroutePC
  have hspR := (hframe Register.x2 (by decide)).trans hk.spReg
  have hroom := h.stack_budget.1
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hgap : SL.lo + 176 ≤ sp.toNat :=
    Nat.le_trans (Nat.add_le_add_left
      (Nat.le_trans (by decide : 176 ≤ 1088) (Nat.le_add_left 1088 _)) SL.lo) hroom
  obtain ⟨v8, hr8, hg8⟩ := hk.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := hk.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := hk.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := hk.saved_s3
  have hpre : ExecRetEpiloguePre (sp - 176#64) r v8 v9 v18 v19 cR := by
    refine ⟨hgood, htick, hpcR, hmi, hspR, ?_, ?_, ?_, ?_, ?_, h.ra_align,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmR]; exact hk.code
    · rw [hspsub]
      exact Nat.le_trans h.stack_ram.1 (Nat.le_sub_of_add_le hgap)
    · rw [hspsub]; have := h.stack_budget.2.1; have := h.stack_ram.2; omega
    · rw [hspsub]; have := h.stack_win; omega
    · rw [hspsub]; have := h.stack_budget.2.2; omega
    · rw [hmR, hspsub, show sp.toNat - 176 + 168 = sp.toNat - 8 by omega]
      exact hk.saved_ra
    · rw [hmR, hspsub, show sp.toNat - 176 + 160 = sp.toNat - 16 by omega]
      exact hr8
    · rw [hmR, hspsub, show sp.toNat - 176 + 152 = sp.toNat - 24 by omega]
      exact hr9
    · rw [hmR, hspsub, show sp.toNat - 176 + 144 = sp.toNat - 32 by omega]
      exact hr18
    · rw [hmR, hspsub, show sp.toNat - 176 + 136 = sp.toNat - 40 by omega]
      exact hr19
  obtain ⟨cD, hp, htail⟩ := execRetEpilogue_run hpre
  have hmD : cD.σ.mem = cfg.σ.mem := hp.mem.trans hmR
  have hf := hpf.trans (PhiExtends.mono hSize.1 hpf')
  have hc := hpc.trans (PhiExtends.mono hSize.2 hpc')
  have hspD : cD.σ.regs.get? Register.x2 = some sp := by
    simpa only [BitVec.sub_add_cancel] using hp.sp
  refine ⟨cD, hrun.steps.trans htail.steps, ?_, ?_, φf', φc', hf, hc, ?_⟩
  · exact
      { good := hp.good
        tick := hp.tick
        pc := by
          simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64
            from by decide, BitVec.add_zero] using hp.pc
        a0 := hp.status
        ra := hp.ra
        spReg := hspD
        minstret := hp.minstret
        store := ⟨φf', φc', hf, hc, by
          rw [hmD]; exact hk.storeSurvives _ (fun _ _ => rfl)⟩
        out := by
          change String.join cD.σ.sailOutput.toList = stMid.out
          rw [hp.output, hout]
          exact hk.out
        retval := by
          intro value hvalue
          obtain ⟨φcv, hcv, hv⟩ := hChild.1.retval value hvalue
          exact ⟨φcv, hpc.trans (PhiExtends.mono hSize.2 hcv), hmD.symm ▸ hv⟩
        frame := by
          intro R hR
          by_cases h2 : R = Register.x2
          · subst R; exact hspD.trans h.parentSp.symm
          by_cases h8 : R = Register.x8
          · subst R; exact hp.s0.trans hg8.symm
          by_cases h9 : R = Register.x9
          · subst R; exact hp.s1.trans hg9.symm
          by_cases h18 : R = Register.x18
          · subst R; exact hp.s2.trans hg18.symm
          by_cases h19 : R = Register.x19
          · subst R; exact hp.s3.trans hg19.symm
          have hkeep : execRetEpilogueKeep R = true := by
            simp [execRetEpilogueKeep, hR.1, h2, h8, h9, h18, h19]
          have hg : gBody R = g R := by
            rcases h.frame R hR with hs | heq
            · rcases hs with hs | hs | hs | hs | hs
              · exact False.elim (h8 hs)
              · exact False.elim (h9 hs)
              · exact False.elim (h18 hs)
              · exact False.elim (h19 hs)
              · exact False.elim (h2 hs)
            · exact heq
          exact (htail.frame.regs.eq R hkeep).trans
            ((hframe R hR.1).trans ((hChild.1.frame R hR).trans hg))
        memFrame := by
          intro a hstk hA
          rw [hmD]
          rcases hChild.1.memFrame a
              (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
          · exact Or.inl hr
          · exact Or.inr (heq.trans (h.mem_frame a hstk hA)) }
  · rw [hmD]
    exact h.mem_extends.trans hChild.2.1
  · rw [hmD]
    exact hk.storeSurvives

#print axioms execWhileBodyResume_ret

end Vsa.Sim
