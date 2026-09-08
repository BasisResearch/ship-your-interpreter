import Vsa.Sim.EvalChildArm

/-!
# `EvalChildArmExpr` — the expression-statement instance of `EvalChildArm`

The `expr` arm (`0x80004170`: `ld a2,8(s0); addi a0,sp,16; mv a3,s3; mv a1,s1;
jal eval_expr`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case stmtExprPrefixSeg chain
  [(0x80004170#64, 0x00843603#32),  -- discipline: allow(R10-exec-evalchild-arm) the EvalChildArm instance's own prefix
   (0x80004174#64, 0x01010513#32),
   (0x80004178#64, 0x00098693#32),
   (0x8000417c#64, 0x00048593#32)]

/-- The expression-statement arm. -/
def stmtExprArm : EvalChildArm :=
  { kind := 0
    armPC := 0x80004170#64
    seg := stmtExprPrefixSeg
    jalPC := 0x80004180#64
    jalImm := 0x1fefe4#21
    sretImm := 0x010#12
    childOff := 8 }

theorem stmtExprPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {e : Expr}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.expr e))
    (hcode : Code.Exec_stmtLoaded m) (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (stmtExprArm.lds m aStmt) stmtExprPrefixSeg := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hn := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) (0x008#12)).toNat =
      aStmt.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide
    rw [hs, BitVec.toNat_add]
    have h8 : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [h8, Nat.mod_eq_of_lt]
    have := hn.hi_ge
    have := hr.hi_ram
    omega
  unfold stmtExprPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  change ((0x80000000 ≤ (aStmt + sign_extend (m := 64) (0x008#12)).toNat ∧
    (aStmt + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
    ((aStmt + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) (0x008#12)).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) (0x008#12)).toNat
      (EvalChildArm.wordLds8 m (aStmt.toNat + 8)))
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hn.lo_le; omega
  · have := hr.hi_ram; have := hn.hi_ge; omega
  · right; have := hr.win; have := hn.lo_le; omega
  · simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
    trivial

theorem stmtExprArm_entryCert : stmtExprArm.EntryCert where
  kind_le := by decide
  arm_of_kind := by decide

theorem stmtExprArm_cert : stmtExprArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x80004170#64 [2, 8, 9, 18, 19] stmtExprPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi stmtExprPrefixSeg; decide
  keys_out := by intros; change KeysOK [11, 13, 10, 12, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [11, 13, 10, 12, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  log_nil := by intros; rfl
  a0_out := by intros; rfl
  a1_out := by intros; rfl
  a2_out := by intros; rfl
  a3_out := by intros; rfl
  sp_out := by intros; rfl
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004180_es σ i u _ vmi hG hpc hmi hmem rfl hi

theorem stmtExprArm_sem (e : Expr) : stmtExprArm.Sem (.expr e) e where
  kind_of_repr := fun _ _ h => by cases h with | expr hk _ _ => exact hk
  child_of_repr := fun _ _ h => by cases h with | expr _ hr he => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2 p hp
  need := by simp only [Stmt.stackNeed, execFrame]; omega
  bodies := fun _ h => by simpa only [Stmt.bodiesBound] using h
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode _ =>
    stmtExprPrefix_facts hg hcode esp aInterp aEnv

/-- The parametric dispatch at the expression statement. -/
theorem execStmtExprDispatch_generic
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.expr e) sp r aInterp aStmt aEnv aRet m0)
      (stmtExprArm.DispatchPost (.expr e) e g N A SL φf φc st d env
        sp r aInterp aStmt aEnv aRet m0) :=
  stmtExprArm.dispatch stmtExprArm_cert stmtExprArm_entryCert (stmtExprArm_sem e)
    g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0

#print axioms execStmtExprDispatch_generic

end Vsa.Sim
