import Vsa.Sim.rows.ForLoopArms
import Vsa.Sim.rows.SeqForRows
import Vsa.Sim.rows.ExecDispatchRows

/-!
# `Field_hFlBodyClosed` — the three for-loop body residuals, closed

`hFlBodyBreak`, `hFlBodyRet`, and `hFlLoop` compose only parametric pieces:
the loop head as a frame, the condition (through `forCondArm` and
`forTruthy`, or the no-condition bypass), the body call (`forBodyArm`), the
body's exit kit, the status routes, and for the continuing case the step
(`forStepArm`, or the no-step fall-through), the loop-head re-entry, and the
rest-of-loop IH; the reached exit is rebased to the entry maps and memory.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

/-! ## The loop head as a frame -/

/-- The parent frame facts at the loop head. -/
theorem TermSimAssembly.ForLoopReady.frameFacts
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    {liveRA : BitVec 64}
    (h : ForLoopReady g N A SL φf φc st d outer init cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA)) :
    FrameFacts (.forStmt init cnd step body) g N A SL φf φc st d outer
      sp r aInterp aStmt aOuter aRet (fun R => cfg.σ.regs.get? R) ment :=
  { s0 := h.s0, s1 := h.s1, s2 := h.s2, s3 := h.s3, spReg := h.spReg
    parentSp := h.parentSp, code := h.code, code_stack_disjoint := h.code_stack_disjoint
    stack_ram := h.stack_ram, stack_win := h.stack_win, ra_align := h.ra_align
    stmt := h.stmt
    env_addr := by
      rw [h.outer_addr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt aOuter.isLt).symm
    env_valid := h.env_valid, store_survives := h.store_survives
    saved_ra := h.saved_ra, saved_s0 := h.saved_s0, saved_s1 := h.saved_s1
    saved_s2 := h.saved_s2, saved_s3 := h.saved_s3
    stack_budget := h.stack_budget, stmt_bodies := h.stmt_bodies, store_bodies := h.store_bodies
    envset_defined := ⟨h.x20_defined, h.x21_defined⟩, ground := h.ground, frame := h.frame }

/-- The loop head from an arm state at its PC, with its own memory as base. -/
theorem TermSimAssembly.ForLoopReady.of_armState
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {mR : Mem} {cfg : Config}
    {liveRA : BitVec 64}
    (hA : ArmState 0x8000426c#64 (.forStmt init cnd step body) g N A SL φf φc st d outer
      sp r aInterp aStmt aOuter aRet mR mR cfg)
    (hra : cfg.σ.regs.get? Register.x1 = some liveRA)
    (houter : φf outer = aOuter.toNat) :
    ForLoopReady g N A SL φf φc st d outer init cnd step body
      sp r aInterp aStmt aOuter aRet mR mR cfg (liveRA := liveRA) :=
  { good := hA.good, tick := hA.tick, pc := hA.pc, s0 := hA.s0, s1 := hA.s1, s2 := hA.s2
    s3 := hA.s3, spReg := hA.spReg, ra := hra, mem := hA.mem, code := hA.code, stmt := hA.stmt
    outer_addr := houter, store := hA.store, env_valid := hA.env_valid
    store_survives := hA.store_survives, stack_ram := hA.stack_ram, stack_win := hA.stack_win
    code_stack_disjoint := hA.code_stack_disjoint, out := hA.out, saved_ra := hA.saved_ra
    saved_s0 := hA.saved_s0, saved_s1 := hA.saved_s1, saved_s2 := hA.saved_s2
    saved_s3 := hA.saved_s3, x20_defined := hA.envset.1, x21_defined := hA.envset.2
    stack_budget := hA.stack_budget, stmt_bodies := hA.stmt_bodies
    store_bodies := hA.store_bodies, ground := hA.ground
    mem_frame := fun a hstk _ => Or.inr (hA.mem_frame a hstk)
    frame := by
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
      exact Or.inr (hA.frame R hR
        (beq_eq_false_iff_ne.mpr (Ne.symm h8)) (beq_eq_false_iff_ne.mpr (Ne.symm h9))
        (beq_eq_false_iff_ne.mpr (Ne.symm h18)) (beq_eq_false_iff_ne.mpr (Ne.symm h19))
        (beq_eq_false_iff_ne.mpr (Ne.symm h2)))
    minstret := hA.minstret, parentSp := hA.parentSp, ra_align := hA.ra_align
    mem_extends := MemExtends.refl mR }

/-- The ghost frame of a route head, including `s0` through its pinned value. -/
theorem frame_of_routeHead {bs : List BBlock} {endPC : BitVec 64} {L : GRegs}
    {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfgR : Config} {aStmt : BitVec 64}
    (hHead : TruthyCopy.RouteHead bs endPC L lds mR out gC cfgR)
    (hs0 : cfgR.σ.regs.get? Register.x8 = some aStmt) (hgC : gC Register.x8 = some aStmt) :
    ∀ R, AbiPreserved R = true → cfgR.σ.regs.get? R = gC R := by
  intro R hR
  by_cases h8 : R = Register.x8
  · subst h8; exact hs0.trans hgC.symm
  · exact hHead.frame R (by
      unfold TruthyCopy.abiButS0
      rw [hR, beq_eq_false_iff_ne.mpr (Ne.symm h8)]
      rfl)

/-! ## Into the body -/

/-- The arm state at the body call from the loop head: through the condition
child, its copy and truthiness test when there is a condition, or through the
bypass branch when there is none. -/
theorem forBodyArmState_of_ready
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    {liveRA : BitVec 64}
    (hReady : ForLoopReady g N A SL φf φc st d outer init cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA))
    (hCond : ForCondIH st d outer cnd st') :
    ∃ (cfgB : Config) (φf1 φc1 : Addr → Nat) (m1 : Mem),
      Steps cfg cfgB ∧
      PhiExtends φf φf1 st.store.frames.size ∧
      PhiExtends φc φc1 st.store.closures.size ∧
      LoopFrame SL A sp aRet ment m1 ∧
      ArmState 0x800042a8#64 (.forStmt init cnd step body) g N A SL φf1 φc1 st' d outer
        sp r aInterp aStmt aOuter aRet m1 m1 cfgB := by
  cases cnd with
  | none =>
    have hst : st = st' := hCond.symm
    subst hst
    have hnull : read64 ment (aStmt.toNat + 16) = some 0 := by
      cases hReady.stmt with
      | forS _ _ hoc _ _ _ => cases hoc with | none h0 => exact h0
    obtain ⟨cfgR, hsR, hHead⟩ :=
      TruthyCopy.route_of_gholds forNoCondSeg 0x800042a8#64
        (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aOuter) (forRouteLds ment aStmt 16)
        hReady.good hReady.tick hReady.pc hReady.minstret hReady.mem rfl
        ⟨hReady.spReg, hReady.s0, hReady.s1, hReady.s2, hReady.s3, True.intro⟩
        (by change KeysOK [2, 8, 9, 18, 19]; decide) (fun _ _ => rfl)
        (by change ChainOK 0x8000426c#64 [2, 8, 9, 18, 19] forNoCondSeg; decide) rfl
        (by change WrChainAvoids TruthyCopy.abiButS0 forNoCondSeg; decide)
        (forNoCond_facts hReady.ground hReady.code hnull (sp - 176#64) aInterp aOuter)
    exact ⟨cfgR, φf, φc, ment, hsR, PhiExtends.refl _ _, PhiExtends.refl _ _,
      LoopFrame.refl _ _ _ _ _,
      ArmState.of_routeHead hHead rfl rfl rfl rfl rfl rfl hReady.frameFacts hReady.out⟩
  | some c =>
    obtain ⟨v, htruthy, hE, hIH⟩ := hCond
    obtain ⟨cfgC, hsC, gC, aC, mC, hCarrier, hEntry⟩ := forCond_dispatchFromLoopHead hReady
    obtain ⟨cfgX, hsX, hExit⟩ :=
      hIH gC N A SL φf φc (sp - 176#64) forCondArm.retPC (forCondArm.sret (sp - 176#64))
        aInterp aC mC cfgC hEntry
    obtain ⟨φf1, φc1, hpf1, hpc1, hKit, F⟩ :=
      forCondArm.frameFacts_at_exit forCondArm_cert (forCondArm_sem init c step body)
        hCarrier hE cfgX hExit
    obtain ⟨mCopy, cfgCopy, hsCopy, hmCopy, hReadyC⟩ :=
      TruthyCopy.copyReady_of_exitKit forCondArm forCondArm_cert forTruthy forTruthy_cert
        cfgX hCarrier hKit
    obtain ⟨cfgT, hsT, hRet⟩ :=
      TruthyCopy.truthyReturn_of_copyReady forCondArm forTruthy forTruthy_cert N φc1 hReadyC
    rw [htruthy] at hRet
    obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom forCondArm_cert
    have hoff : forCondArm.sretOff = 104 := rfl
    rw [hoff] at hsret
    have hnowrap : (sp - 176#64).toNat + 40 ≤ 0x100000000 := by
      have := hCarrier.stack_ram.2; omega
    have hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
        mCopy[k]? = cfgX.σ.mem[k]? := by
      rw [hmCopy]
      exact TruthyCopy.writeLog_frame forCondArm forTruthy forTruthy_cert cfgX.σ.mem
        (sp - 176#64) aStmt aInterp aRet aOuter hnowrap
    have hcopyExt : MemExtends cfgX.σ.mem mCopy := by
      rw [hmCopy]
      exact TruthyCopy.memExtends forCondArm forTruthy forTruthy_cert cfgX.σ.mem
        (sp - 176#64) aStmt aInterp aRet aOuter
    have hCopyOutside : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mCopy[k]? = cfgX.σ.mem[k]? := by
      intro k hk
      apply hcopyFrame k
      rw [hesp]
      intro hw
      exact hk ⟨by omega, by omega⟩
    have hPop : StackBytesPresent mCopy SL := by
      intro k hklo hkhi
      obtain ⟨b, hb⟩ := hKit.stack_bytes k hklo hkhi
      exact hcopyExt k b hb
    have F' := F.transport hCopyOutside
      (fun k hlo hhi => hcopyFrame k (by rw [hesp]; omega)) hReadyC.code hPop
    obtain ⟨cfgR, hsR, hHead⟩ :=
      TruthyCopy.route_of_truthyReturn forTruthy forTruthyRouteSeg 0x800042a8#64 [] hRet
        (by change ChainOK forTruthy.retPC [10, 2, 1, 8, 9, 18, 19] forTruthyRouteSeg; decide)
        rfl
        (by change WrChainAvoids TruthyCopy.abiButS0 forTruthyRouteSeg; decide)
        (forTruthyRoute_facts mCopy (sp - 176#64) aStmt aInterp aRet aOuter hReadyC.code)
    refine ⟨cfgR, φf1, φc1, mCopy, (((hsC.trans hsX).trans hsCopy).trans hsT).trans hsR,
      hpf1, hpc1, ?_, ArmState.of_routeHead hHead rfl rfl rfl rfl rfl rfl F' hKit.out⟩
    exact (LoopFrame.of_offstack hCarrier.mem_extends hCarrier.mem_frame).trans
      ((LoopFrame.of_evalExit hroom (by rw [hsret]; omega) (by rw [hsret, hesp]; omega)
        hExit).trans (LoopFrame.of_offstack hcopyExt hCopyOutside))

/-- Call the body from its arm state, run its IH, and recover the parent. -/
theorem forBody_run
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf1 φc1 : Addr → Nat}
    {st' st'' : Vsa.While.St} {d : Nat} {outer : Addr} {status : Status}
    {init : Option Stmt} {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m1 : Mem} {cfgB : Config}
    (hA : ArmState 0x800042a8#64 (.forStmt init cnd step body) g N A SL φf1 φc1 st' d outer
      sp r aInterp aStmt aOuter aRet m1 m1 cfgB)
    (hBody : ExecS st' d outer body st'' status)
    (hBodyIH : ExecIH st' d outer body st'' status) :
    ∃ (cfgX : Config) (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64)
      (mC : Mem) (φf2 φc2 : Addr → Nat),
      Steps cfgB cfgX ∧
      forBodyArm.Carrier (.forStmt init cnd step body) body g N A SL φf1 φc1 st' d outer
        sp r aInterp aStmt aOuter aRet m1 gC aC mC ∧
      ExecExitD gC N A SL φf1 φc1 st'.store.frames.size st'.store.closures.size st'' status
        (sp - 176#64) forBodyArm.retPC aRet mC cfgX ∧
      PhiExtends φf1 φf2 st'.store.frames.size ∧
      PhiExtends φc1 φc2 st'.store.closures.size ∧
      forBodyArm.ExitKit (.forStmt init cnd step body) g gC N A SL φf2 φc2 st'' d outer status
        sp r aInterp aStmt aOuter aRet cfgX ∧
      LoopFrame SL A sp aRet m1 cfgX.σ.mem := by
  obtain ⟨cfgC, hsC, gC, aC, mC, hCarrier, hEntry⟩ :=
    forBodyArm.dispatch_of_armState forBodyArm_cert (forBodyArm_sem init cnd step body) hA
  obtain ⟨cfgX, hsX, hExit⟩ :=
    hBodyIH gC N A SL φf1 φc1 (sp - 176#64) forBodyArm.retPC aInterp aC aOuter aRet mC cfgC hEntry
  obtain ⟨φf2, φc2, hpf2, hpc2, K⟩ :=
    forBodyArm.exitKit_of_exit forBodyArm_cert (forBodyArm_sem init cnd step body)
      hCarrier hBody cfgX hExit
  exact ⟨cfgX, gC, aC, mC, φf2, φc2, hsC.trans hsX, hCarrier, hExit, hpf2, hpc2, K,
    (LoopFrame.of_offstack hCarrier.mem_extends hCarrier.mem_frame).trans
      (LoopFrame.of_execExit hCarrier.geom.1 hExit)⟩

/-! ## The break exit -/

/-- The `li a0,0` site of the for arm's break exit. -/
theorem forBreak_liSite : LiZeroSite 0x800042c4#64 :=
  fun σ i u vmi hG hpc hmi hmem hi =>
    site_800042c4_fl σ i u _ vmi hG hpc hmi hmem rfl hi

/-- The `j 0x8000409c` site of the for arm's break exit. -/
theorem forBreak_jSite : JumpSite (BitVec.addInt 0x800042c4#64 4) (0x1ffdd4#21) :=
  fun σ i u vmi hG hpc hmi hmem htgt hi =>
    site_800042c8_fl σ i u _ vmi hG hpc hmi hmem (by decide) htgt hi

/-- Concrete supplier for the breaking-body residual. -/
theorem ScaffoldRows.field_hFlBodyBreak :
    ∀ st st' st'' d env cnd step b hCond hBody,
      Rows.FlBodyBreakResid st st' st'' d env cnd step b hCond hBody := by
  intro st st' st'' d env cnd step b hCond hBody hCondIH hBodyIH
  show ForLoopCtxIH st d env cnd step b st'' .normal
  intro init g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment cfg hPre
  obtain ⟨liveRA, hReady⟩ := hPre
  obtain ⟨cfgB, φf1, φc1, m1, hsB, hpf1, hpc1, hLF1, hA⟩ := forBodyArmState_of_ready hReady hCondIH
  obtain ⟨cfgX, gC, aC, mC, φf2, φc2, hsX, hCarrier, hExit, hpf2, hpc2, K, hLF2⟩ :=
    forBody_run hA hBody hBodyIH
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_ready forBreakSeg 0x800042c4#64 [] K.toRouteReady
      (by change ChainOK forBodyArm.retPC [10, 2, 1, 8, 9, 18, 19] forBreakSeg; decide) rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 forBreakSeg; decide)
      (forBreak_facts cfgX.σ.mem (sp - 176#64) aStmt aInterp aRet aOuter K.ff.code)
  have hPre := normalExitPre_of_routeHead hHead rfl rfl K.ff hpf2 hpc2 K.out
  obtain ⟨cfgE, hsE, hExitD⟩ :=
    normalExitTail 0x800042c4#64 (0x1ffdd4#21) forBreak_liSite forBreak_jSite (by decide) cfgR hPre
  have hsize := forCond_store_mono hCond
  have hExit1 := execExitD_rebaseMaps g N A SL φf φc φf1 φc1 _ _ _ _ st'' .normal sp r aRet
    cfgX.σ.mem cfgE hsize hpf1 hpc1 hExitD
  have hLF : LoopFrame SL A sp aRet m0 cfgX.σ.mem :=
    LoopFrame.trans ⟨hReady.mem_extends, hReady.mem_frame⟩ (hLF1.trans hLF2)
  exact ⟨cfgE, ((hsB.trans hsX).trans hsR).trans hsE,
    Rows.execExitD_rebaseMem g N A SL φf φc _ _ st'' .normal sp r aRet m0 cfgX.σ.mem cfgE
      hLF.1 hLF.2 hExit1⟩

/-- Concrete supplier for the returning-body residual. -/
theorem ScaffoldRows.field_hFlBodyRet :
    ∀ st st' st'' d env cnd step b rv hCond hBody,
      Rows.FlBodyRetResid st st' st'' d env cnd step b rv hCond hBody := by
  intro st st' st'' d env cnd step b rv hCond hBody hCondIH hBodyIH
  show ForLoopCtxIH st d env cnd step b st'' (.ret rv)
  intro init g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment cfg hPre
  obtain ⟨liveRA, hReady⟩ := hPre
  obtain ⟨cfgB, φf1, φc1, m1, hsB, hpf1, hpc1, hLF1, hA⟩ := forBodyArmState_of_ready hReady hCondIH
  obtain ⟨cfgX, gC, aC, mC, φf2, φc2, hsX, hCarrier, hExit, hpf2, hpc2, K, hLF2⟩ :=
    forBody_run hA hBody hBodyIH
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_ready forRetSeg 0x80004150#64 [] K.toRouteReady
      (by change ChainOK forBodyArm.retPC [10, 2, 1, 8, 9, 18, 19] forRetSeg; decide) rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 forRetSeg; decide)
      (forRet_facts cfgX.σ.mem (sp - 176#64) aStmt aInterp aRet aOuter rv K.ff.code)
  obtain ⟨cfgE, hsE, hExitD⟩ := forBodyArm.retExit_of_routeHead hCarrier hExit K hHead rfl rfl
  have hsize := forCond_store_mono hCond
  have hExit1 := execExitD_rebaseMaps g N A SL φf φc φf1 φc1 _ _ _ _ st'' (.ret rv) sp r aRet
    mC cfgE hsize hpf1 hpc1 hExitD
  have hLF : LoopFrame SL A sp aRet m0 mC :=
    LoopFrame.trans ⟨hReady.mem_extends, hReady.mem_frame⟩
      (hLF1.trans (LoopFrame.of_offstack hCarrier.mem_extends hCarrier.mem_frame))
  exact ⟨cfgE, ((hsB.trans hsX).trans hsR).trans hsE,
    Rows.execExitD_rebaseMem g N A SL φf φc _ _ st'' (.ret rv) sp r aRet m0 mC cfgE
      hLF.1 hLF.2 hExit1⟩

/-! ## The continuing iteration -/

/-- Concrete supplier for the continuing-iteration residual. -/
theorem ScaffoldRows.field_hFlLoop :
    ∀ st st' st'' st''' st'''' d env cnd step b status status' hCond hBody hContinue hStep hRest,
      Rows.FlLoopResid st st' st'' st''' st'''' d env cnd step b status status'
        hCond hBody hContinue hStep hRest := by
  intro st st' st'' st''' st'''' d env cnd step b status status' hCond hBody hContinue hStep hRest
    hCondIH hBodyIH hStepIH hRestIH
  show ForLoopCtxIH st d env cnd step b st'''' status'
  intro init g N A SL φf φc sp r aInterp aStmt aOuter aRet m0 ment cfg hPre
  obtain ⟨liveRA, hReady⟩ := hPre
  obtain ⟨cfgB, φf1, φc1, m1, hsB, hpf1, hpc1, hLF1, hA⟩ := forBodyArmState_of_ready hReady hCondIH
  obtain ⟨cfgX, gC, aC, mC, φf2, φc2, hsX, hCarrier, hExit, hpf2, hpc2, K, hLF2⟩ :=
    forBody_run hA hBody hBodyIH
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_ready forContSeg 0x80004264#64 [] K.toRouteReady
      (by change ChainOK forBodyArm.retPC [10, 2, 1, 8, 9, 18, 19] forContSeg; decide) rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 forContSeg; decide)
      (forCont_facts cfgX.σ.mem (sp - 176#64) aStmt aInterp aRet aOuter status hContinue K.ff.code)
  have hA2 : ArmState 0x80004264#64 (.forStmt init cnd step b) g N A SL φf2 φc2 st'' d env
      sp r aInterp aStmt aOuter aRet cfgX.σ.mem cfgX.σ.mem cfgR :=
    ArmState.of_routeHead hHead rfl rfl rfl rfl rfl rfl K.ff K.out
  have henv1 : EnvValid st' env := hReady.env_valid.afterForCond hCond
  have henv2 : EnvValid st'' env := henv1.afterExecS hBody
  have hsize1 := forCond_store_mono hCond
  have hsize2 := execS_store_mono hBody
  have hLF0 : LoopFrame SL A sp aRet m0 cfgX.σ.mem :=
    LoopFrame.trans ⟨hReady.mem_extends, hReady.mem_frame⟩ (hLF1.trans hLF2)
  have houter2 : φf2 env = aOuter.toNat :=
    (hpf2 env henv1).trans ((hpf1 env hReady.env_valid).trans hReady.outer_addr)
  cases step with
  | none =>
    have hst : st'' = st''' := hStepIH.symm
    subst hst
    have hnull : read64 cfgX.σ.mem (aStmt.toNat + 24) = some 0 := by
      cases K.ff.stmt with
      | forS _ _ _ hos _ _ => cases hos with | none h0 => exact h0
    have hL : GHolds cfgR.σ (TruthyCopy.routeL (StatusCode status) (sp - 176#64) forBodyArm.retPC
        aStmt aInterp aRet aOuter) := by
      simp only [TruthyCopy.routeL, GHolds, gprGet]
      exact ⟨gholds_lookup (n := 10) _ hHead.regs (by rfl), gholds_lookup (n := 2) _ hHead.regs (by rfl),
        gholds_lookup (n := 1) _ hHead.regs (by rfl), gholds_lookup (n := 8) _ hHead.regs (by rfl),
        gholds_lookup (n := 9) _ hHead.regs (by rfl), gholds_lookup (n := 18) _ hHead.regs (by rfl),
        gholds_lookup (n := 19) _ hHead.regs (by rfl), True.intro⟩
    obtain ⟨cfgL, hsL, hHeadL⟩ :=
      TruthyCopy.route_of_gholds forNoStepSeg 0x8000426c#64 _ (forRouteLds cfgX.σ.mem aStmt 24)
        hA2.good hA2.tick hA2.pc hA2.minstret hA2.mem hHead.out hL
        (by change KeysOK [10, 2, 1, 8, 9, 18, 19]; decide)
        (frame_of_routeHead hHead hA2.s0 K.ff.s0)
        (by change ChainOK 0x80004264#64 [10, 2, 1, 8, 9, 18, 19] forNoStepSeg; decide) rfl
        (by change WrChainAvoids TruthyCopy.abiButS0 forNoStepSeg; decide)
        (forNoStep_facts K.ff.ground K.ff.code hnull (sp - 176#64) aInterp aOuter _)
    have hA3 : ArmState 0x8000426c#64 (.forStmt init cnd none b) g N A SL φf2 φc2 st'' d env
        sp r aInterp aStmt aOuter aRet cfgX.σ.mem cfgX.σ.mem cfgL :=
      ArmState.of_routeHead hHeadL rfl rfl rfl rfl rfl rfl K.ff K.out
    have hReadyL := ForLoopReady.of_armState hA3 (gholds_lookup (n := 1) _ hHeadL.regs (by rfl)) houter2
    obtain ⟨cfgE, hsE, hExitE⟩ :=
      hRestIH init g N A SL φf2 φc2 sp r aInterp aStmt aOuter aRet cfgX.σ.mem cfgX.σ.mem cfgL
        ⟨_, hReadyL⟩
    have hExit1 := execExitD_rebaseMaps g N A SL φf φc φf2 φc2 _ _ _ _ st'''' status' sp r aRet
      cfgX.σ.mem cfgE (hsize1.trans hsize2)
      (hpf1.trans (PhiExtends.mono hsize1.1 hpf2)) (hpc1.trans (PhiExtends.mono hsize1.2 hpc2))
      hExitE
    exact ⟨cfgE, (((hsB.trans hsX).trans hsR).trans hsL).trans hsE,
      Rows.execExitD_rebaseMem g N A SL φf φc _ _ st'''' status' sp r aRet m0 cfgX.σ.mem cfgE
        hLF0.1 hLF0.2 hExit1⟩
  | some e =>
    obtain ⟨v, hE, hIH⟩ := hStepIH
    obtain ⟨cfgS, hsS, gS, aS, mS, hCarrierS, hEntryS⟩ :=
      forStepArm.dispatch_of_armState forStepArm_cert (forStepArm_sem init cnd e b) hA2
    obtain ⟨cfgY, hsY, hExitY⟩ :=
      hIH gS N A SL φf2 φc2 (sp - 176#64) forStepArm.retPC (forStepArm.sret (sp - 176#64))
        aInterp aS mS cfgS hEntryS
    obtain ⟨φf3, φc3, hpf3, hpc3, KY, FY⟩ :=
      forStepArm.frameFacts_at_exit forStepArm_cert (forStepArm_sem init cnd e b)
        hCarrierS hE cfgY hExitY
    obtain ⟨cfgL, hsL, hHeadL⟩ :=
      TruthyCopy.route_of_ready forStepBackSeg 0x8000426c#64 []
        (forStepArm.routeReady_of_exit forStepArm_cert hCarrierS cfgY hExitY)
        (by change ChainOK forStepArm.retPC [10, 2, 1, 8, 9, 18, 19] forStepBackSeg; decide) rfl
        (by change WrChainAvoids TruthyCopy.abiButS0 forStepBackSeg; decide)
        (forStepBack_facts cfgY.σ.mem _ (sp - 176#64) aStmt aInterp aRet aOuter KY.code)
    have hA3 : ArmState 0x8000426c#64 (.forStmt init cnd (some e) b) g N A SL φf3 φc3 st''' d env
        sp r aInterp aStmt aOuter aRet cfgY.σ.mem cfgY.σ.mem cfgL :=
      ArmState.of_routeHead hHeadL rfl rfl rfl rfl rfl rfl FY KY.out
    have houter3 : φf3 env = aOuter.toNat := (hpf3 env henv2).trans houter2
    have hReadyL := ForLoopReady.of_armState hA3 (gholds_lookup (n := 1) _ hHeadL.regs (by rfl)) houter3
    obtain ⟨cfgE, hsE, hExitE⟩ :=
      hRestIH init g N A SL φf3 φc3 sp r aInterp aStmt aOuter aRet cfgY.σ.mem cfgY.σ.mem cfgL
        ⟨_, hReadyL⟩
    have hsize3 := evalE_store_mono hE
    obtain ⟨h176S, hespS, hsretS, hroomS, hSLhiS, halS⟩ := hCarrierS.geom forStepArm_cert
    have hoffS : forStepArm.sretOff = 16 := rfl
    rw [hoffS] at hsretS
    have hLF3 : LoopFrame SL A sp aRet cfgX.σ.mem cfgY.σ.mem :=
      (LoopFrame.of_offstack hCarrierS.mem_extends hCarrierS.mem_frame).trans
        (LoopFrame.of_evalExit hroomS (by rw [hsretS]; omega) (by rw [hsretS, hespS]; omega) hExitY)
    have hExit1 := execExitD_rebaseMaps g N A SL φf φc φf3 φc3 _ _ _ _ st'''' status' sp r aRet
      cfgY.σ.mem cfgE ((hsize1.trans hsize2).trans hsize3)
      (hpf1.trans (PhiExtends.mono hsize1.1 (hpf2.trans (PhiExtends.mono hsize2.1 hpf3))))
      (hpc1.trans (PhiExtends.mono hsize1.2 (hpc2.trans (PhiExtends.mono hsize2.2 hpc3))))
      hExitE
    exact ⟨cfgE, ((((hsB.trans hsX).trans hsR).trans hsS).trans ((hsY.trans hsL).trans hsE)),
      Rows.execExitD_rebaseMem g N A SL φf φc _ _ st'''' status' sp r aRet m0 cfgY.σ.mem cfgE
        (hLF0.trans hLF3).1 (hLF0.trans hLF3).2 hExit1⟩

#print axioms ScaffoldRows.field_hFlBodyBreak
#print axioms ScaffoldRows.field_hFlBodyRet
#print axioms ScaffoldRows.field_hFlLoop

end Vsa.Sim
