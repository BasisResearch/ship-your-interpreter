import Vsa.Sim.EvalChildArm

/-!
# `EvalChildArmRet` — the value-return instance of `EvalChildArm`

The `ret e` arm (`0x80004120`: `ld a2,8(s0); beqz a2 (not taken: the
expression is present); mv a3,s3; mv a1,s1; addi a0,sp,16; jal eval_expr`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case stmtRetPrefixSeg chain
  [(0x80004120#64, 0x00843603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the EvalChildArm instance's own prefix
    terminator ⟨0x80004124#64, 0x1c060663#32, 0x63#8, 0x06#8, 0x06#8, 0x1c#8,
      .br bop.BEQ false, 12, 0, 0x01cc#13, 0#21, 0#12⟩
  ;;
  [(0x80004128#64, 0x00098693#32),
   (0x8000412c#64, 0x00048593#32),
   (0x80004130#64, 0x01010513#32)]

/-- The value-return arm. -/
def stmtRetArm : EvalChildArm :=
  { kind := 6
    armPC := 0x80004120#64
    seg := stmtRetPrefixSeg
    jalPC := 0x80004134#64
    jalImm := 0x1ff030#21
    sretImm := 0x010#12
    childOff := 8 }

theorem stmtRetPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt aChild : BitVec 64} {e : Expr}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ret (some e)))
    (hcode : Code.Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + 8) = some aChild.toNat)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (stmtRetArm.lds m aStmt) stmtRetPrefixSeg := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hn := stmtIn_node hr.nodes
  have hchild := exprIn_node (hr.nodes.2.2 aChild.toNat hread)
  have haddr : (aStmt + sign_extend (m := 64) (0x008#12)).toNat =
      aStmt.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide
    rw [hs, BitVec.toNat_add]
    have h8 : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [h8, Nat.mod_eq_of_lt]
    have := hn.hi_ge
    have := hr.hi_ram
    omega
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 8) aChild hread
  have hnz : (aChild == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h0
    have := hr.lo_ram; have := hchild.lo_le
    rw [h0] at this
    simp at this
    omega
  unfold stmtRetPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change ((0x80000000 ≤ (aStmt + sign_extend (m := 64) (0x008#12)).toNat ∧
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
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 8)) == 0#64) = false
    rw [hload]
    exact hnz

theorem stmtRetArm_entryCert : stmtRetArm.EntryCert where
  kind_le := by decide
  arm_of_kind := by decide

theorem stmtRetArm_cert : stmtRetArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x80004120#64 [2, 8, 9, 18, 19] stmtRetPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi stmtRetPrefixSeg; decide
  keys_out := by intros; change KeysOK [10, 11, 13, 12, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [10, 11, 13, 12, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  log_nil := by intros; rfl
  a0_out := by intros; rfl
  a1_out := by intros; rfl
  a2_out := by intros; rfl
  a3_out := by intros; rfl
  sp_out := by intros; rfl
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004134_es σ i u _ vmi hG hpc hmi hmem rfl hi

theorem stmtRetArm_sem (e : Expr) : stmtRetArm.Sem (.ret (some e)) e where
  kind_of_repr := fun _ _ h => by cases h with | retSome hk _ _ _ => exact hk
  child_of_repr := fun _ _ h => by cases h with | retSome _ hr _ he => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2.2 p hp
  need := by simp only [Stmt.stackNeed, execFrame]; omega
  bodies := fun _ h => by simpa only [Stmt.bodiesBound] using h
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode hread =>
    stmtRetPrefix_facts hg hcode hread esp aInterp aEnv

/-- The parametric dispatch at the value return. -/
theorem execStmtRetDispatch_generic
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.ret (some e)) sp r aInterp aStmt aEnv aRet m0)
      (stmtRetArm.DispatchPost (.ret (some e)) e g N A SL φf φc st d env
        sp r aInterp aStmt aEnv aRet m0) :=
  stmtRetArm.dispatch stmtRetArm_cert stmtRetArm_entryCert (stmtRetArm_sem e)
    g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0

#print axioms execStmtRetDispatch_generic

end Vsa.Sim
