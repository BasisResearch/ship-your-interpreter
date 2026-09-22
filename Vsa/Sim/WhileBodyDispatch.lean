import Vsa.Sim.WhileGeomSuppliers

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

theorem exec_basic_headroom (body : Stmt) (extra : Nat) :
    176 + 1088 ≤ body.stackNeed + extra + 1088 := by
  have hneed := Stmt.stackNeed_ge body
  simp only [execFrame] at hneed
  omega

/-- The body-pointer load is justified by the enclosing AST region. -/
theorem execWhileBodyCall_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {cnd : Expr} {body : Stmt}
    (hground : ExecGround m SL A sp aRet aStmt.toNat (.whileStmt cnd body))
    (hcode : Code.Exec_stmtLoaded m)
    (esp s2 s3 s1 : BitVec 64) :
    ChainFacts m m (stmtWhileBodyL esp aStmt s2 s3 s1)
      (execWhileBodyLds m aStmt) stmtWhileBodySeg := by
  obtain ⟨lo, hi, region⟩ := hground.ast.region
  have hnode := stmtIn_node region.nodes
  have haddr : (aStmt + sign_extend (m := 64) (0x010#12)).toNat =
      aStmt.toNat + 16 := by
    have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
      decide
    rw [hs, BitVec.toNat_add]
    have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [h16, Nat.mod_eq_of_lt]
    have := hnode.hi_ge
    have := region.hi_ram
    omega
  unfold stmtWhileBodySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  change ((0x80000000 ≤ (aStmt + sign_extend (m := 64) (0x010#12)).toNat ∧
    (aStmt + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
    ((aStmt + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) (0x010#12)).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) (0x010#12)).toNat
      (execWhileWordLds m (aStmt.toNat + 16)))
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := region.lo_ram; have := hnode.lo_le; omega
  · have := region.hi_ram; have := hnode.hi_ge; omega
  · right; have := region.win; have := hnode.lo_le; omega
  · simp only [execWhileWordLds, LPins8, List.getD_cons_zero,
      List.getD_cons_succ]
    trivial

/-- Concrete child-call control and ABI, with the same memory and output. -/
structure ExecWhileBodyCallState
    (g : (R : Register) → Option (RegisterType R))
    (esp aInterp aBody aEnv aRet : BitVec 64)
    (m : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80003fe0#64
  ra : cfg.σ.regs.get? Register.x1 = some 0x80004088#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  sp : cfg.σ.regs.get? Register.x2 = some esp
  a0 : cfg.σ.regs.get? Register.x10 = some aInterp
  a1 : cfg.σ.regs.get? Register.x11 = some aBody
  a2 : cfg.σ.regs.get? Register.x12 = some aEnv
  a3 : cfg.σ.regs.get? Register.x13 = some aRet
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R

/-- Execute the body-head marshalling with no assumed instruction facts. -/
theorem execWhileBodyCall_of_stage
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {cnd : Expr} {body : Stmt}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64}
    {m0 mBody : Mem} {cfg : Config}
    (h : ExecWhileBodyHeadStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 aBody mBody cfg) :
    ∃ (aChild : BitVec 64) (cfgChild : Config),
      Vsa.Machine.Steps cfg cfgChild ∧
      read64 mBody (aStmt.toNat + 16) = some aChild.toNat ∧
      StmtRepr mBody aChild.toNat body ∧
      ExecWhileBodyCallState (fun R => cfg.σ.regs.get? R)
        (sp - 176#64) aInterp aChild aEnv aRet mBody cfg.σ.sailOutput cfgChild := by
  obtain ⟨aChild, hread, hchild⟩ := stmtRepr_while_body_bv h.carrier.parent_stmt
  let esp := sp - 176#64
  let lds := execWhileBodyLds mBody aStmt
  let regs := stmtWhileBodyL esp aStmt aRet aEnv aInterp
  have hfacts := execWhileBodyCall_facts h.carrier.ground h.carrier.code
    esp aRet aEnv aInterp
  have hL : GHolds cfg.σ regs := by
    exact ⟨h.carrier.spReg, h.carrier.s0, h.carrier.s2,
      h.carrier.s3, h.carrier.s1, True.intro⟩
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ', i', hs, hi, hgood, hpc, hra, hmi', hregs, hmem, hout, hframe⟩ :=
    execWhileBodyCallBridge cfg.σ cfg.tick cfg.steps vm esp aStmt aRet
      aEnv aInterp mBody lds h.good h.pc hmi h.mem hL
      (h.mem.symm ▸ hfacts) h.tick
      (by
        change KeysOK [10, 12, 13, 11, 2, 8, 18, 19, 9]
        decide)
      (by
        change KeysAvoidRa (evalBlocks stmtWhileBodySeg
          (SegEvalState.init regs lds)).regs
        unfold KeysAvoidRa
        change ∀ n ∈ [10, 12, 13, 11, 2, 8, 18, 19, 9], n ≠ 1
        decide)
      (by simpa +ground only [stmtWhileBodySeg, writeLog, evalBlocks, evalBlock,
        SegEvalState.init, wlogM, List.foldl_nil] using h.carrier.code)
  have hmem' : σ'.mem = mBody := hmem
  have hload := execWhileBodyLds_value mBody aStmt aChild hread
  have hzero : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  change GHolds σ'
    [(10, aInterp + sign_extend (m := 64) (0#12)),
     (12, aEnv + sign_extend (m := 64) (0#12)),
     (13, aRet + sign_extend (m := 64) (0#12)),
     (11, bytesVal MKind.ld ((execWhileBodyLds mBody aStmt).getD 0 [])),
     (2, esp), (8, aStmt), (18, aRet), (19, aEnv), (9, aInterp)] at hregs
  simp only [hzero, BitVec.add_zero, hload] at hregs
  refine ⟨aChild, ⟨σ', i', cfg.steps + evalBlocksFuel stmtWhileBodySeg + 1⟩,
    hs, hread, hchild, ?_⟩
  refine
    { good := hgood
      tick := hi
      pc := hpc
      ra := hra
      minstret := hmi'
      sp := (hframe Register.x2 (by decide)).trans h.carrier.spReg
      a0 := ?_
      a1 := ?_
      a2 := ?_
      a3 := ?_
      mem := hmem'
      out := hout
      frame := hframe }
  · exact gholds_lookup (n := 10) _ hregs (by rfl)
  · exact gholds_lookup (n := 11) _ hregs (by rfl)
  · exact gholds_lookup (n := 12) _ hregs (by rfl)
  · exact gholds_lookup (n := 13) _ hregs (by rfl)

/-- The reached body call supplies the recursive statement entry and retains
the enclosing frame at the same endpoint. -/
theorem execWhileBodyEntry_of_stage
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {cnd : Expr} {body : Stmt}
    {sp r aInterp aStmt aEnv aRet aBody : BitVec 64}
    {m0 mBody : Mem} {cfg : Config}
    (h : ExecWhileBodyHeadStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 aBody mBody cfg) :
    ∃ (aChild : BitVec 64) (cfgChild : Config),
      Vsa.Machine.Steps cfg cfgChild ∧
      ExecWhileBodyCarrier g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0
        (fun R => cfgChild.σ.regs.get? R) aChild mBody ∧
      ExecEntry (fun R => cfgChild.σ.regs.get? R) N A SL φf φc st d env body
        (sp - 176#64) 0x80004088#64 aInterp aChild
        (BitVec.ofNat 64 (φf env)) aRet mBody cfgChild := by
  obtain ⟨aChild, cfgChild, hs, hread, hrepr, hc⟩ := execWhileBodyCall_of_stage h
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have hn : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [hn]
    have := h.carrier.stack_budget.1
    have := sp.isLt
    omega
  have hbudget : StackOK SL (sp - 176#64)
      (body.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    obtain ⟨hlo, hhi, halign⟩ := h.carrier.stack_budget
    simp only [StackOK, hesp]
    simp only [Stmt.stackNeed, execFrame] at hlo
    omega
  have hground : ExecGround mBody SL A (sp - 176#64) aRet aChild.toNat body :=
    h.carrier.ground.child_sameRet
      (fun _ _ hin => stmtIn_while_body hin hread) (by rw [hesp]; omega)
  have h8 := (hc.frame Register.x8 (by decide)).trans h.carrier.s0
  have h9 := (hc.frame Register.x9 (by decide)).trans h.carrier.s1
  have h18 := (hc.frame Register.x18 (by decide)).trans h.carrier.s2
  have h19 := (hc.frame Register.x19 (by decide)).trans h.carrier.s3
  have hdefined : (∃ v, cfgChild.σ.regs.get? Register.x20 = some v) ∧
      (∃ v, cfgChild.σ.regs.get? Register.x21 = some v) := by
    obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := h.carrier.envset_defined
    exact ⟨⟨v20, (hc.frame Register.x20 (by decide)).trans hv20⟩,
      ⟨v21, (hc.frame Register.x21 (by decide)).trans hv21⟩⟩
  refine ⟨aChild, cfgChild, hs, ?_, ?_⟩
  · exact
      { h.carrier with
        s0 := h8
        s1 := h9
        s2 := h18
        s3 := h19
        spReg := hc.sp
        body_stmt := hrepr
        envset_defined := hdefined
        frame := fun R hR => (h.carrier.frame R hR).imp_right
          (fun heq => (hc.frame R hR.1).trans heq) }
  · obtain ⟨lo, hi, region⟩ := hground.ast.region
    have hnode := stmtIn_node region.nodes
    refine
      { good := hc.good
        tick := hc.tick
        pc := hc.pc
        a0 := hc.a0
        a1 := hc.a1
        a2 := h.carrier.env_addr ▸ hc.a2
        envPtr := rfl
        a3 := hc.a3
        ra := hc.ra
        ra_align := by decide
        spReg := hc.sp
        stackOK := ?_
        stackBudget := hbudget
        stmt_bodies := ?_
        store_bodies := h.carrier.store_bodies
        minstret := hc.minstret
        mem := hc.mem
        code := hc.mem ▸ h.carrier.code
        stmt := hc.mem ▸ hrepr
        store := hc.mem ▸ h.carrier.store
        env_valid := h.carrier.env_valid
        store_survives := ?_
        out := ?_
        frame := fun _ _ => rfl
        code_stack_disjoint := ?_
        stack_ram := h.carrier.stack_ram
        stack_win := h.carrier.stack_win
        stmt_stack_disjoint := ?_
        stmt_ram := ?_
        stmt_win := ?_
        spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩, ⟨_, h19⟩⟩
        envset_defined := hdefined
        ground := hc.mem ▸ hground }
    · exact Vsa.Alloc.StackOK.mono (exec_basic_headroom body _) hbudget
    · have hb := h.carrier.stmt_bodies
      simp only [Stmt.bodiesBound, Bool.and_eq_true] at hb
      exact hb.2
    · intro m' hagree
      apply h.carrier.store_survives m'
      simpa only [hc.mem] using hagree
    · change String.join cfgChild.σ.sailOutput.toList = st.out
      rw [hc.out]
      exact h.out
    · rcases h.carrier.code_stack_disjoint with hd | hd
      · left; rw [hesp]; omega
      · exact Or.inr hd
    · have := hnode.lo_le; have := hnode.hi_ge
      have := hbudget.2.1
      rcases region.stack_disjoint with hd | hd
      · left; omega
      · right; omega
    · have := region.lo_ram; have := region.hi_ram
      have := hnode.lo_le; have := hnode.hi_ge
      constructor <;> omega
    · have := region.win; have := hnode.lo_le; omega

#print axioms execWhileBodyCall_facts
#print axioms execWhileBodyCall_of_stage
#print axioms execWhileBodyEntry_of_stage

end Vsa.Sim
