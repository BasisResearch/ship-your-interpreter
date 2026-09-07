import Vsa.Sim.WhileBodyResume
import Vsa.Sim.WhileNormalExitTail

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)

/-- A breaking body takes the existing normal-exit tail and restores the
parent frame, retaining the body-selected allocation maps and memory. -/
theorem execWhileBodyResume_break
    {g gBody : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φfBody φcBody : Addr → Nat}
    {st stCond stMid : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64} {m0 mBody : Mem}
    (hSize : StoreLe st.store stCond.store)
    (_hBody : ExecS stCond d env body stMid .brk)
    (hpf : PhiExtends φf φfBody st.store.frames.size)
    (hpc : PhiExtends φc φcBody st.store.closures.size)
    (h : ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody) :
    Triple
      (ExecExitD gBody N A SL φfBody φcBody stCond.store.frames.size
        stCond.store.closures.size stMid .brk (sp - 176#64) 0x80004088#64 aRet mBody)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        stMid .normal sp r aRet m0) := by
  have hroom := h.stack_budget.1
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hsp8 : sp.toNat % 8 = 0 := by
    have := h.stack_budget.2.2
    omega
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := sp.isLt
    omega
  have hroom176 : SL.lo + 176 ≤ sp.toNat := by omega
  have hsphi : sp.toNat ≤ 0x100000000 := Nat.le_trans h.stack_budget.2.1 h.stack_ram.2
  have hsplo : 0x80000000 ≤ sp.toNat :=
    Nat.le_trans h.stack_ram.1 (Nat.le_trans (Nat.le_add_right SL.lo _) hroom)
  have hspwin : tohostAddr + 16 + 176 ≤ sp.toNat :=
    Nat.le_trans (Nat.add_le_add_right h.stack_win 176) hroom176
  intro cfg hChild
  obtain ⟨φf', φc', hpf', hpc', hk⟩ := execWhileBodyExitKit_of_exit h hChild
  obtain ⟨cR, ⟨⟨hgood, hmem, hout, hroutePC, _hregs⟩, hframe, htick, hmi⟩, hrun⟩ :=
    hk.resume
  have hmR : cR.σ.mem = cfg.σ.mem := hmem
  have hpre : WhileNormalExitTailPre g N A SL φf φc φf' φc'
      st.store.frames.size st.store.closures.size stMid sp r aRet m0 cR := by
    refine
      { good := hgood
        tick := htick
        pc := hroutePC
        minstret := hmi
        spReg := (hframe Register.x2 (by decide)).trans hk.spReg
        code := by rw [hmR]; exact hk.code
        out := by
          change String.join cR.σ.sailOutput.toList = stMid.out
          rw [hout]
          exact hk.out
        frames := hpf.trans (PhiExtends.mono hSize.1 hpf')
        closures := hpc.trans (PhiExtends.mono hSize.2 hpc')
        storeSurvives := by rw [hmR]; exact hk.storeSurvives
        saved_ra := by rw [hmR]; exact hk.saved_ra
        saved_s0 := by rw [hmR]; exact hk.saved_s0
        saved_s1 := by rw [hmR]; exact hk.saved_s1
        saved_s2 := by rw [hmR]; exact hk.saved_s2
        saved_s3 := by rw [hmR]; exact hk.saved_s3
        parentSp := h.parentSp
        frame := ?_
        memExtends := by rw [hmR]; exact h.mem_extends.trans hChild.2.1
        memFrame := ?_
        spRoom := hsp176
        spHi := hsphi
        spLo := hsplo
        spWin := hspwin
        spAlign := hsp8
        retAlign := h.ra_align }
    · intro R hR he8 he9 he18 he19 he2
      have hg : gBody R = g R := by
        rcases h.frame R hR with hspecial | heq
        · rcases hspecial with rfl | rfl | rfl | rfl | rfl
          · simp at he8
          · simp at he9
          · simp at he18
          · simp at he19
          · simp at he2
        · exact heq
      exact (hframe R hR.1).trans ((hChild.1.frame R hR).trans hg)
    · intro a hstk hA
      rw [hmR]
      rcases hChild.1.memFrame a
          (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
      · exact Or.inl hr
      · exact Or.inr (heq.trans (h.mem_frame a hstk hA))
  obtain ⟨cD, hstepsD, hExit⟩ := execWhileNormalExitTail cR hpre
  exact ⟨cD, hrun.steps.trans hstepsD, hExit⟩

#print axioms execWhileBodyResume_break

end Vsa.Sim
