import Vsa.Sim.EvalChildArm
import Vsa.Sim.ExecCondArmSites

/-!
# `EvalChildArmIf` — the if-condition instance of `EvalChildArm`

The `if` arm's condition call (`0x800041e8`: `ld a2,8(s0); mv a3,s3; mv a1,s1;
addi a0,sp,56; jal eval_expr`), for both `ifStmt c t none` and
`ifStmt c t (some e)`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case ifCondPrefixSeg chain
  [(0x800041e8#64, 0x00843603#32),  -- discipline: allow(R10-exec-evalchild-arm) the EvalChildArm instance's own prefix
   (0x800041ec#64, 0x00098693#32),
   (0x800041f0#64, 0x00048593#32),
   (0x800041f4#64, 0x03810513#32)]

/-- The `if` condition arm. -/
def ifCondArm : EvalChildArm :=
  { kind := 3
    armPC := 0x800041e8#64
    seg := ifCondPrefixSeg
    jalPC := 0x800041f8#64
    jalImm := 0x1fef6c#21
    sretImm := 0x038#12
    childOff := 8 }

theorem ifCondPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {c : Expr} {t : Stmt} {oe : Option Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t oe))
    (hcode : Code.Exec_stmtLoaded m) (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (ifCondArm.lds m aStmt) ifCondPrefixSeg := by
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
  unfold ifCondPrefixSeg ChainFacts
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

theorem ifCondArm_entryCert : ifCondArm.EntryCert where
  kind_le := by decide
  arm_of_kind := by decide

theorem ifCondArm_cert : ifCondArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x800041e8#64 [2, 8, 9, 18, 19] ifCondPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi ifCondPrefixSeg; decide
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
    site_800041f8_es σ i u _ vmi hG hpc hmi hmem rfl hi

theorem ifCondArm_sem (c : Expr) (t : Stmt) (oe : Option Stmt) :
    ifCondArm.Sem (.ifStmt c t oe) c where
  kind_of_repr := fun _ _ h => by
    cases h with
    | ifElse hk _ _ _ _ _ _ _ => exact hk
    | ifNoElse hk _ _ _ _ _ => exact hk
  child_of_repr := fun _ _ h => by
    cases h with
    | ifElse _ hr he _ _ _ _ _ => exact ⟨_, hr, he⟩
    | ifNoElse _ hr he _ _ _ => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2.1 p hp
  need := by cases oe <;> simp only [Stmt.stackNeed, execFrame] <;> omega
  bodies := fun _ h => by
    cases oe <;> simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
    · exact h.1
    · exact h.1.1
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode _ =>
    ifCondPrefix_facts hg hcode esp aInterp aEnv

/-- The parametric dispatch at the if condition. -/
theorem execIfCondDispatch_generic
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (oe : Option Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.ifStmt c t oe)
        sp r aInterp aStmt aEnv aRet m0)
      (ifCondArm.DispatchPost (.ifStmt c t oe) c g N A SL φf φc st d env
        sp r aInterp aStmt aEnv aRet m0) :=
  ifCondArm.dispatch ifCondArm_cert ifCondArm_entryCert (ifCondArm_sem c t oe)
    g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0

#print axioms execIfCondDispatch_generic

end Vsa.Sim
