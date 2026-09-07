import Vsa.Sim.WhileBodyResume
import Vsa.Sim.ReprDelta

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Logic (Triple)
open Vsa.Sim.TermSimAssembly

/-- A continuing body returns to the existing while frame with the selected
allocation maps and the reached source environment. -/
theorem execWhileBodyResume_continue
    {g gBody : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {φf φc φfBody φcBody : Addr → Nat}
    {st stCond stMid stFin : Vsa.While.St} {d : Nat} {env : Addr}
    {cnd : Expr} {body : Stmt} {status finalStatus : Status}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64} {m0 mBody : Mem}
    (hSize : StoreLe st.store stCond.store)
    (hBody : ExecS stCond d env body stMid status)
    (hContinue : status = .normal ∨ status = .cont)
    (hpf : PhiExtends φf φfBody st.store.frames.size)
    (hpc : PhiExtends φc φcBody st.store.closures.size)
    (h : ExecWhileBodyCarrier g N A SL φfBody φcBody stCond d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gBody aBody mBody) :
    Triple
      (ExecExitD gBody N A SL φfBody φcBody stCond.store.frames.size
        stCond.store.closures.size stMid status (sp - 176#64) 0x80004088#64 aRet mBody)
      (ExecWhileStepPostI g N A SL φf φc st stMid stFin d env cnd body
        status finalStatus sp r aInterp aStmt aEnv aRet m0) := by
  intro cfg hChild
  obtain ⟨φf', φc', hpf', hpc', hk⟩ := execWhileBodyExitKit_of_exit h hChild
  have hDelta := ReprDelta.ofExecS h.env_valid hBody hpf' hpc'
  obtain ⟨cfg', ⟨⟨hgood, hmem, hout, hroutePC, hregs⟩, hframe, htick, hmi⟩, hrun⟩ :=
    hk.resume
  have hbs : execWhileBodyResumeSegment status = execWhileLoopRouteSeg := by
    rcases hContinue with rfl | rfl <;> rfl
  have htarget : execWhileBodyResumePC status = 0x80004034#64 := by
    rcases hContinue with rfl | rfl <;> rfl
  rw [hbs] at hmem hregs
  have hm : cfg'.σ.mem = cfg.σ.mem := hmem
  have ha0 : cfg'.σ.regs.get? Register.x10 = some (StatusCode status) :=
    gholds_lookup _ hregs (n := 10) (by rfl)
  have hra : cfg'.σ.regs.get? Register.x1 = some 0x80004088#64 :=
    gholds_lookup _ hregs (n := 1) (by rfl)
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have := h.stack_budget.1
    have := sp.isLt
    omega
  refine ⟨cfg', hrun.steps, Or.inl ⟨hContinue, φf', φc', cfg.σ.mem,
    0x80004088#64, hpf.trans (PhiExtends.mono hSize.1 hDelta.frames),
    hpc.trans (PhiExtends.mono hSize.2 hDelta.closures), ?_⟩⟩
  refine
    { good := hgood
      tick := htick
      pc := htarget ▸ hroutePC
      a0 := ha0
      s0 := (hframe Register.x8 (by decide)).trans hk.s0
      s1 := (hframe Register.x9 (by decide)).trans hk.s1
      s2 := (hframe Register.x18 (by decide)).trans hk.s2
      s3 := (hframe Register.x19 (by decide)).trans hk.s3
      spReg := (hframe Register.x2 (by decide)).trans hk.spReg
      parentSp := h.parentSp
      ra := hra
      mem := hm
      code := hk.code
      code_stack_disjoint := h.code_stack_disjoint
      stack_ram := h.stack_ram
      stack_win := h.stack_win
      ra_align := h.ra_align
      stmt := hk.stmt
      env_addr := ?_
      store := hk.storeSurvives _ (fun _ _ => rfl)
      env_valid := hDelta.envValid
      store_survives := hk.storeSurvives
      out := ?_
      saved_ra := hk.saved_ra
      saved_s0 := hk.saved_s0
      saved_s1 := hk.saved_s1
      saved_s2 := hk.saved_s2
      saved_s3 := hk.saved_s3
      stack_budget := h.stack_budget
      stmt_bodies := h.stmt_bodies
      store_bodies := ?_
      envset_defined := ?_
      ground := hk.ground
      mem_frame := ?_
      mem_extends := h.mem_extends.trans hChild.2.1
      frame := ?_
      minstret := hmi }
  · rw [hpf' env h.env_valid]
    exact h.env_addr
  · change String.join cfg'.σ.sailOutput.toList = stMid.out
    rw [hout]
    exact hk.out
  · apply StoreBodiesBound.afterExecS hBody _ h.store_bodies
    have hb := h.stmt_bodies
    simp only [Stmt.bodiesBound, Bool.and_eq_true] at hb
    exact hb.2
  · obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := h.envset_defined
    exact ⟨⟨v20, (hframe Register.x20 (by decide)).trans
      ((hChild.1.frame Register.x20 (by decide)).trans hv20)⟩,
      ⟨v21, (hframe Register.x21 (by decide)).trans
      ((hChild.1.frame Register.x21 (by decide)).trans hv21)⟩⟩
  · intro a hstk hA
    rcases hChild.1.memFrame a
        (by rw [hspsub]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
    · exact Or.inl hr
    · exact Or.inr (heq.trans (h.mem_frame a hstk hA))
  · intro R hR
    exact (h.frame R hR).imp_right (fun heq =>
      (hframe R hR.1).trans ((hChild.1.frame R hR).trans heq))

#print axioms execWhileBodyResume_continue

end Vsa.Sim
