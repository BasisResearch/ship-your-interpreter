import Vsa.Sim.EvalChildArm
import Vsa.Sim.WhileCondPrefix

/-!
# `EvalChildArmWhile` — the while-condition instance of `EvalChildArm`

The descriptor of the `while` arm's condition call (`0x8000403c`: `ld a2,8(s0);
mv a3,s3; addi a0,sp,80; mv a1,s1; jal eval_expr`), its two certificates, and
the confirmation that the parametric dispatch yields exactly the hand-closed
`execWhileCondDispatch_closed` statement.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The `while` condition arm. -/
def whileCondArm : EvalChildArm :=
  { kind := 4
    armPC := 0x8000403c#64
    seg := execWhileCondPrefixSeg
    jalPC := 0x8000404c#64
    jalImm := 0x1ff118#21
    sretImm := 0x050#12
    childOff := 8 }

theorem whileCondArm_entryCert : whileCondArm.EntryCert where
  kind_le := by decide
  arm_of_kind := by decide

theorem whileCondArm_cert : whileCondArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x8000403c#64 [2, 8, 9, 18, 19] execWhileCondPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi execWhileCondPrefixSeg; decide
  keys_out := by intros; change KeysOK [11, 10, 13, 12, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [11, 10, 13, 12, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  log_nil := by intros; rfl
  a0_out := by intros; rfl
  a1_out := by intros; rfl
  a2_out := by intros; rfl
  a3_out := by intros; rfl
  sp_out := by intros; rfl
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_8000404c_es σ i u _ vmi hG hpc hmi hmem rfl hi

theorem whileCondArm_sem (cnd : Expr) (body : Stmt) :
    whileCondArm.Sem (.whileStmt cnd body) cnd where
  kind_of_repr := fun _ _ h => by cases h with | whileS hk _ _ _ _ => exact hk
  child_of_repr := fun _ _ h => by cases h with | whileS _ hr he _ _ => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2.1 p hp
  need := by simp only [Stmt.stackNeed, execFrame]; omega
  bodies := fun _ h => by simp only [Stmt.bodiesBound, Bool.and_eq_true] at h; exact h.1
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode _ =>
    execWhileCondPrefix_facts hg hcode esp aInterp aEnv

/-- The parametric dispatch at the while condition. -/
theorem execWhileCondDispatch_generic
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (whileCondArm.DispatchPost (.whileStmt cnd body) cnd g N A SL φf φc st d env
        sp r aInterp aStmt aEnv aRet m0) :=
  whileCondArm.dispatch whileCondArm_cert whileCondArm_entryCert (whileCondArm_sem cnd body)
    g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0

/-- The generic carrier forgets to the while-specific carrier. -/
theorem EvalChildArm.Carrier.toWhileCond
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {cnd : Expr} {body : Stmt}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (h : whileCondArm.Carrier (.whileStmt cnd body) cnd g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gC aC mC where
  s0 := h.s0
  s1 := h.s1
  s2 := h.s2
  s3 := h.s3
  spReg := h.spReg
  parentSp := h.parentSp
  code := h.code
  code_stack_disjoint := h.code_stack_disjoint
  stack_ram := h.stack_ram
  stack_win := h.stack_win
  ra_align := h.ra_align
  stmt := h.stmt
  env_addr := h.env_addr
  store := h.store
  env_valid := h.env_valid
  store_survives := h.store_survives
  saved_ra := h.saved_ra
  saved_s0 := h.saved_s0
  saved_s1 := h.saved_s1
  saved_s2 := h.saved_s2
  saved_s3 := h.saved_s3
  stack_budget := h.stack_budget
  stmt_bodies := h.stmt_bodies
  store_bodies := h.store_bodies
  envset_defined := h.envset_defined
  ground := h.ground
  mem_frame := h.mem_frame
  mem_extends := h.mem_extends
  frame := h.frame

/-- **Confirmation.**  The hand-closed `execWhileCondDispatch_closed` statement,
re-derived from the parametric layer. -/
theorem execWhileCondDispatch_closed_of_generic
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
  obtain ⟨cfg', hs, gC, aC, mC, hCar, hEntryC⟩ :=
    execWhileCondDispatch_generic g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 cfg hEntry
  have h176 : 176 ≤ sp.toNat := by
    have := hEntry.stackOK.1
    omega
  have hret : whileCondArm.retPC = 0x80004050#64 := by decide
  have hsret : whileCondArm.sret (sp - 176#64) = sp - 96#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [whileCondArm.sret_toNat whileCondArm_cert sp h176, BitVec.toNat_sub]
    have h96 : (96#64 : BitVec 64).toNat = 96 := by decide
    rw [h96]
    have := sp.isLt
    change sp.toNat - 176 + 80 = _
    omega
  rw [hret, hsret] at hEntryC
  exact ⟨cfg', hs, gC, aC, mC, hCar.toWhileCond, hEntryC⟩

#print axioms whileCondArm_cert
#print axioms whileCondArm_sem
#print axioms execWhileCondDispatch_closed_of_generic

end Vsa.Sim
