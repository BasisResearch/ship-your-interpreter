import Vsa.Sim.EvalChildArm
import Vsa.Sim.ExecCondArmSites
import Vsa.Sim.TermSimAssembly

/-!
# `EvalChildArmForCond` — the for-loop condition: the in-frame instance

The for-loop condition call starts at the loop head `0x8000426c`
(`ld a2,16(s0); beqz a2 (not taken: the condition is present); mv a3,s3;
addi a0,sp,104; mv a1,s1; jal eval_expr`), reached in-frame after `env_new`
and the initializer rather than through the prologue.  The descriptor has no
`EntryCert`; `dispatchFromLoopHead` enters `EvalChildArm.dispatch_of_armState`
from the real loop-head state `ForLoopReady`.

The loop-head record carries the parent stack-pointer ghost, the return
alignment, and memory extension, so the conversion needs no extra hypothesis.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

#derive_case forCondPrefixSeg chain
  [(0x8000426c#64, 0x01043603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the EvalChildArm instance's own prefix
    terminator ⟨0x80004270#64, 0x02060c63#32, 0x63#8, 0x0c#8, 0x06#8, 0x02#8,
      .br bop.BEQ false, 12, 0, 0x0038#13, 0#21, 0#12⟩
  ;;
  [(0x80004274#64, 0x00098693#32),
   (0x80004278#64, 0x06810513#32),
   (0x8000427c#64, 0x00048593#32)]

/-- The for-loop condition arm (in-frame). -/
def forCondArm : EvalChildArm :=
  { kind := 5
    armPC := 0x8000426c#64
    seg := forCondPrefixSeg
    jalPC := 0x80004280#64
    jalImm := 0x1feee4#21
    sretImm := 0x068#12
    childOff := 16 }

theorem forCondPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt aChild : BitVec 64} {init : Option Stmt} {c : Expr}
    {step : Option Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.forStmt init (some c) step body))
    (hcode : Code.Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + 16) = some aChild.toNat)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (forCondArm.lds m aStmt) forCondPrefixSeg := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hn := stmtIn_node hr.nodes
  have hchild := exprIn_node (hr.nodes.2.2.1.2 aChild.toNat hread)
  have haddr : (aStmt + sign_extend (m := 64) (0x010#12)).toNat =
      aStmt.toNat + 16 := by
    have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by decide
    rw [hs, BitVec.toNat_add]
    have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [h16, Nat.mod_eq_of_lt]
    have := hn.hi_ge
    have := hr.hi_ram
    omega
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 16) aChild hread
  have hnz : (aChild == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h0
    have := hr.lo_ram; have := hchild.lo_le
    rw [h0] at this
    simp at this
    omega
  unfold forCondPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change ((0x80000000 ≤ (aStmt + sign_extend (m := 64) (0x010#12)).toNat ∧
      (aStmt + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      ((aStmt + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) (0x010#12)).toNat)) ∧
      LPins8 m (aStmt + sign_extend (m := 64) (0x010#12)).toNat
        (EvalChildArm.wordLds8 m (aStmt.toNat + 16)))
    rw [haddr]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · have := hr.lo_ram; have := hn.lo_le; omega
    · have := hr.hi_ram; have := hn.hi_ge; omega
    · right; have := hr.win; have := hn.lo_le; omega
    · simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      trivial
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 16)) == 0#64) = false
    rw [hload]
    exact hnz

theorem forCondArm_cert : forCondArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x8000426c#64 [2, 8, 9, 18, 19] forCondPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi forCondPrefixSeg; decide
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
    site_80004280_es σ i u _ vmi hG hpc hmi hmem rfl hi

theorem forCondArm_sem (init : Option Stmt) (c : Expr) (step : Option Expr) (body : Stmt) :
    forCondArm.Sem (.forStmt init (some c) step body) c where
  kind_of_repr := fun _ _ h => by cases h with | forS hk _ _ _ _ _ => exact hk
  child_of_repr := fun _ _ h => by
    cases h with
    | forS _ _ hoc _ _ _ =>
      cases hoc with | some hr _ he => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2.2.1.2 p hp
  need := by simp only [Stmt.stackNeed, execFrame, Expr.stackNeedOpt]; omega
  bodies := fun _ h => by
    simp only [Stmt.bodiesBound, Expr.bodiesBoundOpt, Bool.and_eq_true] at h
    exact h.1.1.2
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode hread =>
    forCondPrefix_facts hg hcode hread esp aInterp aEnv

/-- The real loop-head state is the arm state of the condition arm, with the
loop-head memory as the frame's own base memory. -/
theorem EvalChildArm.ArmState.ofForLoopReady
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {c : Expr} {step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    {liveRA : BitVec 64}
    (h : ForLoopReady g N A SL φf φc st d outer init (some c) step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA)) :
    forCondArm.ArmState (.forStmt init (some c) step body) g N A SL φf φc st d outer
      sp r aInterp aStmt aOuter aRet ment ment cfg where
  good := h.good
  tick := h.tick
  pc := h.pc
  s0 := h.s0
  s1 := h.s1
  s2 := h.s2
  s3 := h.s3
  spReg := h.spReg
  minstret := h.minstret
  out := h.out
  mem := h.mem
  code := h.code
  store := h.store
  saved_ra := h.saved_ra
  saved_s0 := h.saved_s0
  saved_s1 := h.saved_s1
  saved_s2 := h.saved_s2
  saved_s3 := h.saved_s3
  parentSp := h.parentSp
  frame := by
    intro R hR he8 he9 he18 he19 he2
    rcases h.frame R hR with hspecial | heq
    · rcases hspecial with rfl | rfl | rfl | rfl | rfl
      · simp at he8
      · simp at he9
      · simp at he18
      · simp at he19
      · simp at he2
    · exact heq
  mem_frame := fun _ _ => rfl
  mem_extends := MemExtends.refl ment
  ra_align := h.ra_align
  spSL := h.stack_budget.2.1
  stack_budget := h.stack_budget
  stmt_bodies := h.stmt_bodies
  store_bodies := h.store_bodies
  store_survives := h.store_survives
  env_valid := h.env_valid
  env_addr := by
    rw [h.outer_addr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt aOuter.isLt).symm
  code_stack_disjoint := h.code_stack_disjoint
  stack_ram := h.stack_ram
  stack_win := h.stack_win
  ground := h.ground
  stmt := h.stmt
  envset := ⟨h.x20_defined, h.x21_defined⟩

/-- **The in-frame entry variant.**  From the real loop head, run the
condition prefix and the `jal`; land at the condition's `EvalEntry` with the
parent carrier, relative to the loop-head memory. -/
theorem forCond_dispatchFromLoopHead
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {outer : Addr}
    {init : Option Stmt} {c : Expr} {step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    {liveRA : BitVec 64}
    (h : ForLoopReady g N A SL φf φc st d outer init (some c) step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA)) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      forCondArm.DispatchPost (.forStmt init (some c) step body) c g N A SL φf φc st d outer
        sp r aInterp aStmt aOuter aRet ment cfg' :=
  forCondArm.dispatch_of_armState forCondArm_cert (forCondArm_sem init c step body)
    (EvalChildArm.ArmState.ofForLoopReady h)

#print axioms forCondArm_cert
#print axioms forCondArm_sem
#print axioms forCond_dispatchFromLoopHead

end Vsa.Sim
