import Vsa.Sim.StmtChildArm
import Vsa.Sim.ForLoopSites
import Vsa.Sim.rows.EvalChildArmForCond
import Vsa.Sim.rows.TruthyCopyFor

/-!
# `ForLoopArms` — the for-loop's body call, step arm, and status routes

Instances of the parametric layers for the for-loop tail of `exec_stmt`:

* `forBodyArm` (`StmtChildArm`): `ld a1,32(s0); mv a3,s2; mv a2,s3; mv a0,s1;
  jal exec_stmt` at `0x800042a8`;
* `forStepArm` (`EvalChildArm`, in-frame): `ld a2,24(s0); bnez a2` taken to
  `0x800042dc`, then `mv a3,s3; mv a1,s1; addi a0,sp,16; jal eval_expr`;
* the reflected routes: the no-condition bypass at the loop head, the truthy
  fall-through into the body call, the break exit, the return propagation,
  the continue route to the step arm, the no-step fall-through to the loop
  head, and the step's loop-back jump.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-! ## The body call -/

/-- The named body projection of a for statement's containment witness. -/
theorem StmtIn.forBody {m : Mem} {lo hi a : Nat} {init : Option Stmt} {cnd step : Option Expr}
    {body : Stmt} (h : StmtIn m lo hi a (.forStmt init cnd step body)) :
    ∀ p, read64 m (a + 32) = some p → StmtIn m lo hi p body :=
  h.2.2.2.2  -- discipline: allow(R6-anon-projection-tower) the one named destructurer of StmtIn.forStmt's body clause

#derive_case forBodySeg chain
  [(0x800042a8#64, 0x02043583#32),  -- discipline: allow(R11-exec-stmtchild-arm) the StmtChildArm instance's own prefix
   (0x800042ac#64, 0x00090693#32),
   (0x800042b0#64, 0x00098613#32),
   (0x800042b4#64, 0x00048513#32)]

/-- The for-loop body call. -/
def forBodyArm : StmtChildArm :=
  { armPC := 0x800042a8#64
    seg := forBodySeg
    jalPC := 0x800042b8#64
    jalImm := 0x1ffd28#21
    childOff := 32 }

/-- A node-field load of the enclosing statement is justified by its region. -/
theorem forNode_ld_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {s : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat s) (off : BitVec 12) (n : Nat)
    (hn : n + 8 ≤ 40)
    (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
    (0x80000000 ≤ (aStmt + sign_extend (m := 64) off).toNat ∧
      (aStmt + sign_extend (m := 64) off).toNat + 8 ≤ 0x100000000 ∧
      ((aStmt + sign_extend (m := 64) off).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) off).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) off).toNat
      (EvalChildArm.wordLds8 m (aStmt.toNat + n)) := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hnode := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) off).toNat = aStmt.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hnode.hi_ge; have := hr.hi_ram
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hnode.lo_le; omega
  · have := hr.hi_ram; have := hnode.hi_ge; omega
  · right; have := hr.win; have := hnode.lo_le; omega
  · simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
    trivial

theorem forBody_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {init : Option Stmt} {cnd step : Option Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.forStmt init cnd step body))
    (hcode : Exec_stmtLoaded m) (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (forBodyArm.lds m aStmt) forBodySeg := by
  unfold forBodySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  exact forNode_ld_facts hg 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)

theorem forBodyArm_cert : forBodyArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  child_off := by decide
  chain_ok := by change ChainOK 0x800042a8#64 [2, 8, 9, 18, 19] forBodySeg; decide
  avoid_abi := by change WrChainAvoidAbi forBodySeg; decide
  keys_out := by intros; change KeysOK [10, 12, 13, 11, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [10, 12, 13, 11, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  log_nil := by intros; rfl
  a0_out := by intros; rfl
  a1_out := by intros; rfl
  a2_out := by intros; rfl
  a3_out := by intros; rfl
  sp_out := by intros; rfl
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_800042b8_fl σ i u _ vmi hG hpc hmi hmem rfl hi

theorem forBodyArm_sem (init : Option Stmt) (cnd step : Option Expr) (body : Stmt) :
    forBodyArm.Sem (.forStmt init cnd step body) body where
  child_of_repr := fun _ _ h => by
    cases h with | forS _ _ _ _ hb hrb => exact ⟨_, hb, hrb⟩
  in_proj := fun _ _ _ _ h p hp => h.forBody p hp
  need := by
    simp only [Stmt.stackNeed, execFrame]
    omega
  bodies := fun _ h => by
    simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
    exact h.2
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode _ => forBody_facts hg hcode esp aInterp aEnv

/-! ## The step arm -/

#derive_case forStepPrefixSeg chain
  [(0x80004264#64, 0x01843603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the EvalChildArm instance's own prefix
    terminator ⟨0x80004268#64, 0x06061a63#32, 0x63#8, 0x1a#8, 0x06#8, 0x06#8,
      .br bop.BNE true, 12, 0, 0x0074#13, 0#21, 0#12⟩
  ;;
  [(0x800042dc#64, 0x00098693#32),
   (0x800042e0#64, 0x00048593#32),
   (0x800042e4#64, 0x01010513#32)]

/-- The for-loop step arm (in-frame, after a continuing body). -/
def forStepArm : EvalChildArm :=
  { kind := 5
    armPC := 0x80004264#64
    seg := forStepPrefixSeg
    jalPC := 0x800042e8#64
    jalImm := 0x1fee7c#21
    sretImm := 0x010#12
    childOff := 24 }

theorem forStepPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt aChild : BitVec 64} {init : Option Stmt} {cnd : Option Expr}
    {e : Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.forStmt init cnd (some e) body))
    (hcode : Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + 24) = some aChild.toNat)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (forStepArm.lds m aStmt) forStepPrefixSeg := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hchild := exprIn_node (hr.nodes.2.2.2.1.2 aChild.toNat hread)
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 24) aChild hread
  have hnz : (aChild != 0#64) = true := by
    apply bne_iff_ne.mpr
    intro h0
    have := hr.lo_ram; have := hchild.lo_le
    rw [h0] at this
    simp at this
    omega
  unfold forStepPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact forNode_ld_facts hg 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 24)) != 0#64) = true
    rw [hload]
    exact hnz

theorem forStepArm_cert : forStepArm.Cert where
  arm_align := by decide
  ret_align := by decide
  ret_pc_clean := by decide
  jal_tgt := by decide
  sret_val := by decide
  sret_align := by decide
  sret_room := by decide
  child_off := by decide
  chain_ok := by
    change ChainOK 0x80004264#64 [2, 8, 9, 18, 19] forStepPrefixSeg; decide
  avoid_abi := by change WrChainAvoidAbi forStepPrefixSeg; decide
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
    site_800042e8_fl σ i u _ vmi hG hpc hmi hmem rfl hi

theorem forStepArm_sem (init : Option Stmt) (cnd : Option Expr) (e : Expr) (body : Stmt) :
    forStepArm.Sem (.forStmt init cnd (some e) body) e where
  kind_of_repr := fun _ _ h => by cases h with | forS hk _ _ _ _ _ => exact hk
  child_of_repr := fun _ _ h => by
    cases h with
    | forS _ _ _ hos _ _ =>
      cases hos with | some hr _ he => exact ⟨_, hr, he⟩
  in_proj := fun _ _ _ _ h p hp => h.2.2.2.1.2 p hp
  need := by simp only [Stmt.stackNeed, execFrame, Expr.stackNeedOpt]; omega
  bodies := fun _ h => by
    simp only [Stmt.bodiesBound, Expr.bodiesBoundOpt, Bool.and_eq_true] at h
    exact h.1.2
  facts := fun _ _ _ _ _ _ esp aInterp aEnv _ hg hcode hread =>
    forStepPrefix_facts hg hcode hread esp aInterp aEnv

/-! ## The routes -/

-- No condition: the loop head bypasses the condition call.
#derive_case forNoCondSeg chain
  [(0x8000426c#64, 0x01043603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the no-condition bypass at the loop head
    terminator ⟨0x80004270#64, 0x02060c63#32, 0x63#8, 0x0c#8, 0x06#8, 0x02#8,
      .br bop.BEQ true, 12, 0, 0x0038#13, 0#21, 0#12⟩

/-- The routes' load lists: the one node field they read. -/
def forRouteLds (m : Mem) (aStmt : BitVec 64) (off : Nat) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (aStmt.toNat + off)]

theorem forNoCond_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {init : Option Stmt} {step : Option Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.forStmt init none step body))
    (hcode : Exec_stmtLoaded m)
    (hnull : read64 m (aStmt.toNat + 16) = some 0)
    (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv)
      (forRouteLds m aStmt 16) forNoCondSeg := by
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 16) (0#64) hnull
  unfold forNoCondSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact forNode_ld_facts hg 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 16)) == 0#64) = true
    rw [hload]
    decide

-- Truthy condition: fall through the exit branch into the body call.
#derive_case forTruthyRouteSeg chain
  []
    terminator ⟨0x800042a4#64, 0xde0506e3#32, 0xe3#8, 0x06#8, 0x05#8, 0xde#8,
      .br bop.BEQ false, 10, 0, 0x1dec#13, 0#21, 0#12⟩

theorem forTruthyRoute_facts (m : Mem) (esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL 1#64 esp forTruthy.retPC s0 s1 s2 s3) [] forTruthyRouteSeg := by
  unfold forTruthyRouteSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BEQ (1#64) (0#64) = false
    decide

-- Body returned `brk` (`a0 = 1`): the `bne a0,a5` falls through to the exit.
#derive_case forBreakSeg chain
  [(0x800042bc#64, 0x00100793#32)]
    terminator ⟨0x800042c0#64, 0xf8f51ee3#32, 0xe3#8, 0x1e#8, 0xf5#8, 0xf8#8,
      .br bop.BNE false, 10, 15, 0x1f9c#13, 0#21, 0#12⟩

theorem forBreak_facts (m : Mem) (esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL (StatusCode .brk) esp forBodyArm.retPC s0 s1 s2 s3) []
      forBreakSeg := by
  unfold forBreakSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BNE (StatusCode .brk) (0#64 + sign_extend (m := 64) (0x001#12)) = false
    decide

-- Body returned `ret` (`a0 = 3`): take the status branch, then the ret branch
-- into the status-3 epilogue.
#derive_case forRetSeg chain
  [(0x800042bc#64, 0x00100793#32)]
    terminator ⟨0x800042c0#64, 0xf8f51ee3#32, 0xe3#8, 0x1e#8, 0xf5#8, 0xf8#8,
      .br bop.BNE true, 10, 15, 0x1f9c#13, 0#21, 0#12⟩
  ;;
  [(0x8000425c#64, 0x00300793#32)]
    terminator ⟨0x80004260#64, 0xeef508e3#32, 0xe3#8, 0x08#8, 0xf5#8, 0xee#8,
      .br bop.BEQ true, 10, 15, 0x1ef0#13, 0#21, 0#12⟩

theorem forRet_facts (m : Mem) (esp s0 s1 s2 s3 : BitVec 64) (rv : Value)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL (StatusCode (.ret rv)) esp forBodyArm.retPC s0 s1 s2 s3) []
      forRetSeg := by
  unfold forRetSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BNE (3#64) (0#64 + sign_extend (m := 64) (0x001#12)) = true
    decide
  · change guardB bop.BEQ (3#64) (0#64 + sign_extend (m := 64) (0x003#12)) = true
    decide

-- Body returned `normal`/`cont`: take the status branch, fall through the ret
-- branch to the step arm.
#derive_case forContSeg chain
  [(0x800042bc#64, 0x00100793#32)]
    terminator ⟨0x800042c0#64, 0xf8f51ee3#32, 0xe3#8, 0x1e#8, 0xf5#8, 0xf8#8,
      .br bop.BNE true, 10, 15, 0x1f9c#13, 0#21, 0#12⟩
  ;;
  [(0x8000425c#64, 0x00300793#32)]
    terminator ⟨0x80004260#64, 0xeef508e3#32, 0xe3#8, 0x08#8, 0xf5#8, 0xee#8,
      .br bop.BEQ false, 10, 15, 0x1ef0#13, 0#21, 0#12⟩

theorem forCont_facts (m : Mem) (esp s0 s1 s2 s3 : BitVec 64) (status : Status)
    (hContinue : status = .normal ∨ status = .cont)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL (StatusCode status) esp forBodyArm.retPC s0 s1 s2 s3) []
      forContSeg := by
  unfold forContSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BNE (StatusCode status) (0#64 + sign_extend (m := 64) (0x001#12)) = true
    rcases hContinue with rfl | rfl <;> decide
  · change guardB bop.BEQ (StatusCode status) (0#64 + sign_extend (m := 64) (0x003#12)) = false
    rcases hContinue with rfl | rfl <;> decide

-- No step: the step-pointer test falls through to the loop head.
#derive_case forNoStepSeg chain
  [(0x80004264#64, 0x01843603#32)]  -- discipline: allow(R10-exec-evalchild-arm) the no-step fall-through route at the step head
    terminator ⟨0x80004268#64, 0x06061a63#32, 0x63#8, 0x1a#8, 0x06#8, 0x06#8,
      .br bop.BNE false, 12, 0, 0x0074#13, 0#21, 0#12⟩

theorem forNoStep_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {init : Option Stmt} {cnd : Option Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.forStmt init cnd none body))
    (hcode : Exec_stmtLoaded m)
    (hnull : read64 m (aStmt.toNat + 24) = some 0)
    (esp aInterp aEnv : BitVec 64) (a0 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL a0 esp forBodyArm.retPC aStmt aInterp aRet aEnv)
      (forRouteLds m aStmt 24) forNoStepSeg := by
  have hload := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 24) (0#64) hnull
  unfold forNoStepSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact forNode_ld_facts hg 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 24)) != 0#64) = false
    rw [hload]
    decide

-- After the step expression returns: jump back to the loop head.
#derive_case forStepBackSeg chain
  []
    terminator ⟨0x800042ec#64, 0xf81ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xf8#8,
      .j, 0, 0, 0#13, 0x1fff80#21, 0#12⟩

theorem forStepBack_facts (m : Mem) (a0 esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL a0 esp forStepArm.retPC s0 s1 s2 s3) [] forStepBackSeg := by
  unfold forStepBackSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"

#print axioms forBodyArm_cert
#print axioms forBodyArm_sem
#print axioms forStepArm_cert
#print axioms forStepArm_sem
#print axioms forNoCond_facts
#print axioms forRet_facts
#print axioms forCont_facts
#print axioms forNoStep_facts
#print axioms forStepBack_facts

end Vsa.Sim
