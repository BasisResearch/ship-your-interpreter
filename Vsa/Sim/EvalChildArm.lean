import Vsa.Sim.ExecBrkCont
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EvalRecCommon
import Vsa.Sim.ExecNormalExitTail

/-!
# `EvalChildArm` — the parametric `exec_stmt` arm → `eval_expr` child dispatch

Every `exec_stmt` arm that evaluates ONE child expression (`expr`, `ret e`,
`varDecl x e`, `if`, `while`) reaches `jal eval_expr` through the same machine
shape: the shared prologue and jump-table dispatch (`execBlockA`), a reflected
straight-line prefix that loads the child pointer and marshals the four ABI
arguments (`a0 := esp + sret`, `a1 := interp`, `a2 := child`, `a3 := env`), and
the `jal`.  The while condition closed this seam with arm-specific files
(`WhileCondPrefix`, `WhileCondDispatchClosed`).  This file states the seam ONCE
over an arm descriptor and two certificates:

* `EvalChildArm` — the descriptor: statement tag, arm PC, the reflected prefix,
  the `jal` PC and immediate, the sub-result-slot immediate, the child field
  offset;
* `EvalChildArm.Cert` — decidable facts about the descriptor (chain
  well-formedness, ABI avoidance, the register fold, end PC, empty write log,
  the `jal` site);
* `EvalChildArm.Sem s e` — how the arm's statement constructor exposes its
  child: tag, child field, hereditary region projection, stack budget, bodies
  bound, and the prefix chain facts.

`EvalChildArm.dispatch` then yields, from `ExecEntry` for `s`, the child's
`EvalEntry` for `e` plus an `EvalChildArm.Carrier` retaining the parent frame
across the recursive call; `EvalChildArm.exitKit_at_exit` recovers the parent
facts at the child's widened exit, and `EvalChildArm.normalExitPre_of_exit`
parks a normal completion at the arm's `li a0,0` for `normalExitTail`.  Instances are one descriptor, one `#derive_case`
prefix, and two certificate records each (`rows/EvalChildArm*.lean`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) every `∃` here is either the fixed StepObs
-- site post shape (`Cert.jal_site`), a saved-register or selected-map witness INSIDE a
-- named-field structure (`Carrier`, `ExitKit`, `CallState`), or the reached-config
-- existential of a run; all are consumed through named fields, never positional chains.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-! ## Statement tags and their arm PCs -/

/-- The `exec_stmt` jump-table target of statement tag `k`. -/
def execArmPC : Nat → BitVec 64
  | 0 => execArmExpr
  | 1 => execArmVarDecl
  | 2 => execArmBlock
  | 3 => execArmIf
  | 4 => execArmWhile
  | 5 => execArmFor
  | 6 => execArmRet
  | 7 => execArmBrk
  | 8 => execArmCont
  | _ => 0#64

/-- The tag-indexed slot pin of the batched table pins. -/
theorem StmtTablePins.slotOf {m : Mem} (h : StmtTablePins m) (k : Nat) (hk : k ≤ 8) :
    StmtSlotPinned k (execArmPC k) m := by
  match k, hk with
  | 0, _ => exact h.slot0
  | 1, _ => exact h.slot1
  | 2, _ => exact h.slot2
  | 3, _ => exact h.slot3
  | 4, _ => exact h.slot4
  | 5, _ => exact h.slot5
  | 6, _ => exact h.slot6
  | 7, _ => exact h.slot7
  | 8, _ => exact h.slot8
  | n + 9, hk => exact absurd hk (by omega)

/-! ## The descriptor -/

/-- An `exec_stmt` arm that evaluates one child expression through
`jal eval_expr` at the lowered frame `esp = sp - 176`. -/
structure EvalChildArm where
  /-- Statement tag (jump-table index). -/
  kind : Nat
  /-- Arm entry PC (the jump-table target); the prefix starts here. -/
  armPC : BitVec 64
  /-- The reflected prefix from `armPC` up to (excluding) the `jal`. -/
  seg : List BBlock
  /-- PC of `jal eval_expr`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21
  /-- `addi a0,sp,<sretImm>`: the sub-result slot offset from `esp`. -/
  sretImm : BitVec 12
  /-- The child pointer field offset inside the statement node. -/
  childOff : Nat

namespace EvalChildArm

/-- The link PC written by the `jal`. -/
def retPC (D : EvalChildArm) : BitVec 64 := BitVec.addInt D.jalPC 4

/-- The sub-result slot offset as a number. -/
def sretOff (D : EvalChildArm) : Nat := D.sretImm.toNat

/-- The sub-result slot address at the lowered stack pointer. -/
def sret (D : EvalChildArm) (esp : BitVec 64) : BitVec 64 :=
  esp + sign_extend (m := 64) D.sretImm

/-- The five pinned registers every prefix reads. -/
def regs (esp aStmt aInterp aRet aEnv : BitVec 64) : GRegs :=
  [(2, esp), (8, aStmt), (9, aInterp), (18, aRet), (19, aEnv)]

/-- One total 64-bit machine read, as the eight positional bytes the reflected
evaluator consumes. -/
def wordLds8 (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0,
   (m[a + 3]?).getD 0, (m[a + 4]?).getD 0, (m[a + 5]?).getD 0,
   (m[a + 6]?).getD 0, (m[a + 7]?).getD 0]

/-- The one total load every prefix makes: the child pointer. -/
def lds (D : EvalChildArm) (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [wordLds8 m (aStmt.toNat + D.childOff)]

/-- The reflected outcome of the prefix. -/
def out (D : EvalChildArm) (esp aStmt aInterp aRet aEnv : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks D.seg (SegEvalState.init (regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt))

/-! ## The decidable certificate -/

/-- Facts about the descriptor alone.  Every field of an instance closes by
`decide`, `rfl`, or the generated `jal` site lemma. -/
structure Cert (D : EvalChildArm) : Prop where
  arm_align : D.armPC.toNat % 4 = 0
  ret_align : D.retPC.toNat % 4 = 0
  ret_pc_clean : BitVec.update (D.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = D.retPC
  jal_tgt : D.jalPC + sign_extend (m := 64) D.jalImm = BitVec.ofNat 64 evalExprEntry
  sret_val : (sign_extend (m := 64) D.sretImm : BitVec 64).toNat = D.sretOff
  sret_align : D.sretOff % 8 = 0
  sret_room : D.sretOff + 24 ≤ 136
  child_off : D.childOff + 8 ≤ 40
  chain_ok : ChainOK D.armPC [2, 8, 9, 18, 19] D.seg
  avoid_abi : WrChainAvoidAbi D.seg
  keys_out : ∀ esp aStmt aInterp aRet aEnv m,
    KeysOK (keysG (D.out esp aStmt aInterp aRet aEnv m).regs)
  ra_out : ∀ esp aStmt aInterp aRet aEnv m,
    KeysAvoidRa (D.out esp aStmt aInterp aRet aEnv m).regs
  end_pc : ∀ esp aStmt aInterp aRet aEnv m,
    evalBlocksPC D.armPC
      (SegEvalState.init (regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt)) D.seg = D.jalPC
  log_nil : ∀ esp aStmt aInterp aRet aEnv m, (D.out esp aStmt aInterp aRet aEnv m).log = []
  a0_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 10 (D.out esp aStmt aInterp aRet aEnv m).regs = some (D.sret esp)
  a1_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 11 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (aInterp + sign_extend (m := 64) (0#12))
  a2_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 12 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (bytesVal MKind.ld (wordLds8 m (aStmt.toNat + D.childOff)))
  a3_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 13 (D.out esp aStmt aInterp aRet aEnv m).regs =
      some (aEnv + sign_extend (m := 64) (0#12))
  sp_out : ∀ esp aStmt aInterp aRet aEnv m,
    lookupG 2 (D.out esp aStmt aInterp aRet aEnv m).regs = some esp
  jal_site : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some D.jalPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ D.jalPC vmi D.jalImm Register.x1
        (BitVec.addInt D.jalPC 4))

/-- The two facts only the prologue-and-dispatch entry needs: the arm is the
jump-table target of its tag.  An in-frame entry (the for-loop head) has none. -/
structure EntryCert (D : EvalChildArm) : Prop where
  kind_le : D.kind ≤ 8
  arm_of_kind : execArmPC D.kind = D.armPC

/-! ## The semantic certificate -/

/-- How the arm's statement constructor exposes its child expression. -/
structure Sem (D : EvalChildArm) (s : Stmt) (e : Expr) : Prop where
  kind_of_repr : ∀ (m : Mem) (a : Nat), StmtRepr m a s → read32 m a = some D.kind
  child_of_repr : ∀ (m : Mem) (a : Nat), StmtRepr m a s →
    ∃ p, read64 m (a + D.childOff) = some p ∧ ExprRepr m p e
  in_proj : ∀ (m : Mem) (lo hi a : Nat), StmtIn m lo hi a s →
    ∀ p, read64 m (a + D.childOff) = some p → ExprIn m lo hi p e
  need : e.stackNeed + execFrame ≤ s.stackNeed
  bodies : ∀ P, Stmt.bodiesBound P s = true → Expr.bodiesBound P e = true
  facts : ∀ (m : Mem) (SL : StackLayout) (A : Arena)
    (sp aRet aStmt esp aInterp aEnv aChild : BitVec 64),
    ExecGround m SL A sp aRet aStmt.toNat s → Exec_stmtLoaded m →
    read64 m (aStmt.toNat + D.childOff) = some aChild.toNat →
    ChainFacts m m (regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt) D.seg

/-! ## Geometry of the sub-result slot -/

theorem esp_toNat (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    (sp - 176#64).toNat = sp.toNat - 176 := by
  rw [BitVec.toNat_sub]
  have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
  rw [h176]
  have := sp.isLt
  omega

theorem sret_toNat (D : EvalChildArm) (C : D.Cert) (sp : BitVec 64)
    (hsp : 176 ≤ sp.toNat) :
    (D.sret (sp - 176#64)).toNat = sp.toNat - 176 + D.sretOff := by
  unfold sret
  rw [BitVec.toNat_add, C.sret_val, esp_toNat sp hsp]
  have := sp.isLt
  have := C.sret_room
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The reflected `ld` value -/

/-- The reflected eight-byte load of a represented pointer is that pointer. -/
theorem bytesVal_ld_wordLds (m : Mem) (a : Nat) (v : BitVec 64)
    (hread : read64 m a = some v.toNat) :
    bytesVal MKind.ld (wordLds8 m a) = v := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
    read64_bytes m a v.toNat hread
  simp only [wordLds8, bytesVal, List.getD_cons_zero,
    List.getD_cons_succ, hb0, hb1, hb2, hb3, hb4, hb5,
    hb6, hb7, Option.getD_some]
  rw [sext_full]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon]
  exact hrec

/-! ## The prefix run -/

/-- Exact state after the prefix and its `jal`. -/
structure CallState (D : EvalChildArm)
    (g : (R : Register) → Option (RegisterType R))
    (esp aInterp aChild aEnv : BitVec 64) (m : Mem) (out : Array String)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  ra : cfg.σ.regs.get? Register.x1 = some D.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  spReg : cfg.σ.regs.get? Register.x2 = some esp
  a0 : cfg.σ.regs.get? Register.x10 = some (D.sret esp)
  a1 : cfg.σ.regs.get? Register.x11 = some aInterp
  a2 : cfg.σ.regs.get? Register.x12 = some aChild
  a3 : cfg.σ.regs.get? Register.x13 = some aEnv
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R

/-- Run the reflected prefix and the `jal` from the arm entry. -/
theorem prefix_run (D : EvalChildArm) (C : D.Cert)
    {m : Mem} {aStmt aInterp aEnv aRet aChild esp : BitVec 64} {cfg : Config}
    (hfacts : ChainFacts m m (regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt) D.seg)
    (hcode : Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + D.childOff) = some aChild.toNat)
    (hgood : GoodState cfg.σ) (htick : cfg.tick < 2)
    (hpc : cfg.σ.regs.get? Register.PC = some D.armPC)
    (hmi : ∃ w, cfg.σ.regs.get? Register.minstret = some w)
    (hmem : cfg.σ.mem = m)
    (hregs : GHolds cfg.σ (regs esp aStmt aInterp aRet aEnv)) :
    ∃ cfg', Steps cfg cfg' ∧
      D.CallState (fun R => cfg.σ.regs.get? R) esp aInterp aChild aEnv m
        cfg.σ.sailOutput cfg' := by
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨σ', i', hs, hi, hG, hPC, hRA, hMI, hRegs, hMem, hOut, hFrame⟩ :=
    bridgeOfSegOut D.seg (regs esp aStmt aInterp aRet aEnv) (D.lds m aStmt)
      cfg.σ cfg.tick cfg.steps D.armPC (BitVec.ofNat 64 evalExprEntry) D.retPC vm m
      hgood hpc hvm hmem hregs (by change KeysOK [2, 8, 9, 18, 19]; decide)
      (hmem.symm ▸ hfacts) htick C.chain_ok C.avoid_abi
      (C.keys_out _ _ _ _ _ _) (C.ra_out _ _ _ _ _ _)
      (by
        intro σ i u hG hi hpc hmi hm _
        obtain ⟨vm, hvm⟩ := hmi
        rw [C.end_pc] at hpc
        have hc : Exec_stmtLoaded σ.mem := by
          rw [hm]
          have hl := C.log_nil esp aStmt aInterp aRet aEnv m
          unfold out at hl
          rw [hl]
          exact hcode
        obtain ⟨σ2, i2, hs2, hi2, hG2, hm2, ho2⟩ := C.jal_site σ i u vm hG hpc hvm hc hi
        exact jalStepO_of_obs hs2 hi2 hG2 hm2 ho2 C.jal_tgt)
  have hload := bytesVal_ld_wordLds m (aStmt.toNat + D.childOff) aChild hread
  have hzero : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have hRegs' : GHolds σ' (D.out esp aStmt aInterp aRet aEnv m).regs := hRegs
  refine ⟨⟨σ', i', cfg.steps + evalBlocksFuel D.seg + 1⟩, hs, ?_⟩
  refine
    { good := hG
      tick := hi
      pc := hPC
      ra := hRA
      minstret := hMI
      spReg := gholds_lookup _ hRegs' (C.sp_out _ _ _ _ _ _)
      a0 := gholds_lookup _ hRegs' (C.a0_out _ _ _ _ _ _)
      a1 := ?_
      a2 := ?_
      a3 := ?_
      mem := ?_
      out := hOut
      frame := hFrame }
  · have h := gholds_lookup _ hRegs' (C.a1_out esp aStmt aInterp aRet aEnv m)
    rw [hzero, BitVec.add_zero] at h
    exact h
  · have h := gholds_lookup _ hRegs' (C.a2_out esp aStmt aInterp aRet aEnv m)
    rw [hload] at h
    exact h
  · have h := gholds_lookup _ hRegs' (C.a3_out esp aStmt aInterp aRet aEnv m)
    rw [hzero, BitVec.add_zero] at h
    exact h
  · rw [hMem]
    have hl := C.log_nil esp aStmt aInterp aRet aEnv m
    unfold out at hl
    rw [hl]
    rfl

/-! ## The carrier -/

/-- Static identity of the parent `exec_stmt` frame carried across the child
`eval_expr` call.  `EvalEntry`/`EvalExitD` abstract over the caller; this
record retains the enclosing frame, its AST, and its memory geometry. -/
structure Carrier (D : EvalChildArm) (s : Stmt) (e : Expr)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gC : (R : Register) → Option (RegisterType R))
    (aC : BitVec 64) (mC : Mem) : Prop where
  s0 : gC Register.x8 = some aStmt
  s1 : gC Register.x9 = some aInterp
  s2 : gC Register.x18 = some aRet
  s3 : gC Register.x19 = some aEnv
  spReg : gC Register.x2 = some (sp - 176#64)
  parentSp : g Register.x2 = some sp
  code : Exec_stmtLoaded mC
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ra_align : r.toNat % 4 = 0
  stmt : StmtRepr mC aStmt.toNat s
  child_read : read64 mC (aStmt.toNat + D.childOff) = some aC.toNat
  child_expr : ExprRepr mC aC.toNat e
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  store : StoreRepr mC N A φf φc st.store
  env_valid : EnvValid st env
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mC[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  saved_ra : read64 mC (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 mC (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 mC (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 mC (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 mC (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  stack_budget : StackOK SL sp
    (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget s = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  envset_defined : (∃ v, gC Register.x20 = some v) ∧ (∃ v, gC Register.x21 = some v)
  ground : ExecGround mC SL A sp aRet aStmt.toNat s
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mC[a]? = m0[a]?
  mem_extends : MemExtends m0 mC
  frame : ∀ R : Register, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ gC R = g R

/-- The child entry reached by the arm, with the parent carrier. -/
def DispatchPost (D : EvalChildArm) (s : Stmt) (e : Expr)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (cfg : Config) : Prop :=
  ∃ (gC : (R : Register) → Option (RegisterType R)) (aC : BitVec 64) (mC : Mem),
    D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC ∧
    EvalEntry gC N A SL φf φc st d env e (sp - 176#64) D.retPC (D.sret (sp - 176#64))
      aInterp aC mC cfg

/-! ## Child ground -/

/-- The expression ground bundle of a child expression.  Its AST witness is a
projection of the enclosing statement region; static eval geometry comes from
`EvalCallSupport`. -/
theorem _root_.Vsa.Sim.ExecGround.child_evalGround {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet spEval sret aStmt aChild : BitVec 64} {s : Stmt} {e : Expr}
    (h : ExecGround m SL A sp aRet aStmt.toNat s)
    (hproj : ∀ lo hi, StmtIn m lo hi aStmt.toNat s → ExprIn m lo hi aChild.toNat e)
    (hspEval : spEval.toNat ≤ sp.toNat)
    (hsret : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) :
    EvalGround m SL A spEval sret aChild.toNat e := by
  obtain ⟨_hcode, _hvint, _htruthy, _hint, _hnbs, htable⟩ :=
    h.eval_call.pins m (fun _ _ => rfl)
  refine
    { eval_call := h.eval_call.transport (fun _ _ => rfl)
      table := htable
      stack_bytes := h.stack_bytes
      ast := ?_
      arena_stack := ?_
      arena_code := h.eval_call.arena_code
      arena_vi := by
        rcases h.eval_call.arena_vi with hd | hd
        · exact Or.inl hd
        · exact Or.inr (by omega)
      sret_inSL := hsret
      sret_table_disjoint := ?_ }
  · obtain ⟨lo, hi, hr⟩ := h.ast.region
    refine ⟨lo, hi, ?_⟩
    exact
      { nodes := hproj lo hi hr.nodes
        lo_ram := hr.lo_ram
        hi_ram := hr.hi_ram
        win := hr.win
        stack_disjoint := hr.stack_disjoint
        sret_disjoint := by
          rcases hr.stack_disjoint with hd | hd <;> omega
        arena_disjoint := hr.arena_disjoint }
  · rcases h.arena_stack with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by omega)
  · rcases h.eval_call.table_stack with ht | ht
    · right
      simp only [jumpTableBase] at ht ⊢
      omega
    · left
      simp only [jumpTableBase] at ht ⊢
      omega

private theorem eval_child_headroom (e : Expr) (extra : Nat) :
    1088 + 1088 ≤ e.stackNeed + extra + 1088 := by
  have hn := Expr.stackNeed_ge e
  simp only [evalFrame] at hn
  omega

/-! ## The arm state -/

end EvalChildArm

/-- The machine state at an in-frame arm PC with the entry facts a child call
needs.  `EvalChildArm.armState_of_entry` reaches it through the prologue and
the jump table; the for-loop head and the post-body routes reach it in-frame. -/
structure ArmState (armPC : BitVec 64) (s : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 ment : Mem) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some armPC
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aEnv
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  out : OutRepr cfg.σ st
  mem : cfg.σ.mem = ment
  code : Exec_stmtLoaded ment
  store : StoreRepr ment N A φf φc st.store
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 ment (sp.toNat - 16) = some v.toNat ∧ g Register.x8 = some v
  saved_s1 : ∃ v, read64 ment (sp.toNat - 24) = some v.toNat ∧ g Register.x9 = some v
  saved_s2 : ∃ v, read64 ment (sp.toNat - 32) = some v.toNat ∧ g Register.x18 = some v
  saved_s3 : ∃ v, read64 ment (sp.toNat - 40) = some v.toNat ∧ g Register.x19 = some v
  parentSp : g Register.x2 = some sp
  frame : ∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → cfg.σ.regs.get? R = g R
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?
  mem_extends : MemExtends m0 ment
  ra_align : r.toNat % 4 = 0
  spSL : sp.toNat ≤ SL.hi
  stack_budget : StackOK SL sp
    (s.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget s = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  env_valid : EnvValid st env
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  ground : ExecGround ment SL A sp aRet aStmt.toNat s
  stmt : StmtRepr ment aStmt.toNat s
  envset : (∃ v, cfg.σ.regs.get? Register.x20 = some v) ∧
    (∃ v, cfg.σ.regs.get? Register.x21 = some v)

namespace EvalChildArm

/-- The arm state of a descriptor: the in-frame state at its arm PC. -/
abbrev ArmState (D : EvalChildArm) (s : Stmt)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 ment : Mem) (cfg : Config) : Prop :=
  Vsa.Sim.ArmState D.armPC s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 ment cfg

/-- **The parametric child call from the arm state.**  Run the arm prefix and
the `jal`; land at the child's `EvalEntry` with the parent carrier. -/
theorem dispatch_of_armState (D : EvalChildArm) (C : D.Cert) {s : Stmt} {e : Expr}
    (S : D.Sem s e)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 ment : Mem} {cfg : Config}
    (hA : D.ArmState s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 ment cfg) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      D.DispatchPost s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 cfg' := by
  have hsp176 : 176 ≤ sp.toNat := by
    have hneed := Stmt.stackNeed_ge s
    simp only [execFrame] at hneed
    have := hA.stack_budget.1
    omega
  obtain ⟨p, hread, hrepr⟩ := S.child_of_repr _ _ hA.stmt
  let aChild := BitVec.ofNat 64 p
  have hp : aChild.toNat = p := by
    exact Nat.mod_eq_of_lt (read64_lt_eg4 ment (aStmt.toNat + D.childOff) p hread)
  have hreadB : read64 ment (aStmt.toNat + D.childOff) = some aChild.toNat := hp ▸ hread
  have hreprB : ExprRepr ment aChild.toNat e := hp ▸ hrepr
  have hfacts := S.facts ment SL A sp aRet aStmt (sp - 176#64) aInterp aEnv aChild
    hA.ground hA.code hreadB
  obtain ⟨cC, hsC, hc⟩ := D.prefix_run C hfacts hA.code hreadB hA.good hA.tick hA.pc
    hA.minstret hA.mem ⟨hA.spReg, hA.s0, hA.s1, hA.s2, hA.s3, True.intro⟩
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := esp_toNat sp hsp176
  have hsret : (D.sret (sp - 176#64)).toNat = sp.toNat - 176 + D.sretOff :=
    D.sret_toNat C sp hsp176
  have hroom := hA.stack_budget.1
  have hSLhi := hA.spSL
  have hsretRoom := C.sret_room
  have hsretAl := C.sret_align
  have hneed := S.need
  have hsNeed := Stmt.stackNeed_ge s
  simp only [execFrame] at hneed hsNeed
  have hbudget : StackOK SL (sp - 176#64)
      (e.stackNeed + (maxCallDepth - d) * perCallBudget + 1088) := by
    obtain ⟨hlo, hhi, halign⟩ := hA.stack_budget
    simp only [StackOK, hesp]
    omega
  have hsretSL : SL.lo ≤ (D.sret (sp - 176#64)).toNat ∧
      (D.sret (sp - 176#64)).toNat + 24 ≤ SL.hi := by rw [hsret]; omega
  have hEvalGround := hA.ground.child_evalGround
    (fun lo hi hin => S.in_proj ment lo hi aStmt.toNat hin _ hreadB)
    (spEval := sp - 176#64) (by rw [hesp]; omega) hsretSL
  obtain ⟨lo, hi, hr⟩ := hEvalGround.ast.region
  have hn := exprIn_node hr.nodes
  obtain ⟨hEvalCode, hViCode, _hTruthy, hIntSlot, hNbs, _hTable⟩ :=
    hA.ground.eval_call.pins ment (fun _ _ => rfl)
  have h8 := (hc.frame Register.x8 (by decide)).trans hA.s0
  have h9 := (hc.frame Register.x9 (by decide)).trans hA.s1
  have h18 := (hc.frame Register.x18 (by decide)).trans hA.s2
  have h19 := (hc.frame Register.x19 (by decide)).trans hA.s3
  have hDefined : (∃ v, cC.σ.regs.get? Register.x20 = some v) ∧
      (∃ v, cC.σ.regs.get? Register.x21 = some v) := by
    obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hA.envset
    exact ⟨⟨v20, (hc.frame Register.x20 (by decide)).trans hv20⟩,
      ⟨v21, (hc.frame Register.x21 (by decide)).trans hv21⟩⟩
  refine ⟨cC, hsC, (fun R => cC.σ.regs.get? R), aChild, ment, ?_, ?_⟩
  · refine
      { s0 := h8
        s1 := h9
        s2 := h18
        s3 := h19
        spReg := hc.spReg
        parentSp := hA.parentSp
        code := hA.code
        code_stack_disjoint := hA.code_stack_disjoint
        stack_ram := hA.stack_ram
        stack_win := hA.stack_win
        ra_align := hA.ra_align
        stmt := hA.stmt
        child_read := hreadB
        child_expr := hreprB
        env_addr := hA.env_addr
        store := hA.store
        env_valid := hA.env_valid
        store_survives := hA.store_survives
        saved_ra := hA.saved_ra
        saved_s0 := hA.saved_s0
        saved_s1 := hA.saved_s1
        saved_s2 := hA.saved_s2
        saved_s3 := hA.saved_s3
        stack_budget := hA.stack_budget
        stmt_bodies := hA.stmt_bodies
        store_bodies := hA.store_bodies
        envset_defined := hDefined
        ground := hA.ground
        mem_frame := hA.mem_frame
        mem_extends := hA.mem_extends
        frame := ?_ }
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
    exact Or.inr ((hc.frame R hR.1).trans (hA.frame R hR
      (beq_eq_false_iff_ne.mpr (Ne.symm h8)) (beq_eq_false_iff_ne.mpr (Ne.symm h9))
      (beq_eq_false_iff_ne.mpr (Ne.symm h18)) (beq_eq_false_iff_ne.mpr (Ne.symm h19))
      (beq_eq_false_iff_ne.mpr (Ne.symm h2))))
  · refine
      { good := hc.good
        tick := hc.tick
        pc := hc.pc
        a0 := hc.a0
        sret_words := hc.mem ▸ hEvalGround.valueWordsTotal hsretSL.1 hsretSL.2
        a1 := hc.a1
        a2 := hc.a2
        ra := hc.ra
        ra_align := C.ret_align
        spReg := hc.spReg
        stackOK := ?_
        stackBudget := hbudget
        expr_bodies := ?_
        store_bodies := hA.store_bodies
        minstret := hc.minstret
        mem := hc.mem
        code := hc.mem ▸ hEvalCode
        expr := hc.mem ▸ hreprB
        store := hc.mem ▸ hA.store
        env_valid := hA.env_valid
        store_survives := ?_
        out := ?_
        frame := fun _ _ => rfl
        code_stack_disjoint := ?_
        expr_stack_disjoint := ?_
        expr_ram := ?_
        expr_win := ?_
        sret_align := ?_
        sret_ram := ?_
        sret_win := ?_
        sret_vicode_disjoint := ?_
        sret_stack_disjoint := ?_
        sret_evalcode_disjoint := ?_
        vicode_stack_disjoint := ?_
        stack_ram := hA.stack_ram
        stack_win := hA.stack_win
        value_int_code := hc.mem ▸ hViCode
        int_slot := hc.mem ▸ hIntSlot
        table_stack_disjoint := ?_
        nbs_pins := hc.mem ▸ hNbs
        ground := hc.mem ▸ hEvalGround
        spill_defined := ⟨⟨_, h8⟩, ⟨_, h9⟩, ⟨_, h18⟩⟩
        envset_defined := ⟨aEnv, hDefined.1.choose, hDefined.2.choose,
          h19, hDefined.1.choose_spec, hDefined.2.choose_spec⟩
        envReg := hA.env_addr ▸ hc.a3
        x13_defined := ⟨aEnv, hc.a3⟩ }
    · exact StackOK.mono (eval_child_headroom e _) hbudget
    · exact S.bodies _ hA.stmt_bodies
    · intro m' hag
      apply hA.store_survives m'
      intro k hk
      exact (hc.mem ▸ hag k hk (by rw [hsret]; intro hs; exact hk ⟨by omega, by omega⟩))
    · change String.join cC.σ.sailOutput.toList = st.out
      rw [hc.out]
      exact hA.out
    · rcases hA.ground.eval_call.code_stack with hd | hd
      · left; rw [hesp]; omega
      · exact Or.inr hd
    · have := hn.lo_le; have := hn.hi_ge
      rcases hr.stack_disjoint with hd | hd <;> simp only [hesp] <;> omega
    · exact ⟨Nat.le_trans hr.lo_ram hn.lo_le,
        Nat.le_trans (Nat.add_le_add_left (by decide : 16 ≤ 40) _)
          (Nat.le_trans hn.hi_ge hr.hi_ram)⟩
    · have := hr.win; have := hn.lo_le; omega
    · rw [hsret]; have := hA.stack_budget.2.2; omega
    · exact ⟨Nat.le_trans hA.stack_ram.1 hsretSL.1,
        Nat.le_trans hsretSL.2 hA.stack_ram.2⟩
    · rw [hsret]; have := hA.stack_win; rw [hsret] at hsretSL; omega
    · rcases hA.ground.eval_call.vi_stack with hd | hd <;> rw [hsret] <;>
        rw [hsret] at hsretSL <;> omega
    · right; rw [hesp, hsret]; omega
    · rcases hA.ground.eval_call.code_stack with hd | hd <;> rw [hsret] <;>
        rw [hsret] at hsretSL <;> omega
    · rcases hA.ground.eval_call.vi_stack with hd | hd <;> rw [hesp] <;> omega
    · rcases hA.ground.eval_call.table_stack with hd | hd <;>
        simp only [jumpTableBase] at hd <;> rw [hesp] <;> omega

/-- The prologue and the jump-table dispatch reach the arm state of any
tag: the arm is the jump-table target of the statement's tag, and the tag is
read from the statement representation.  Every arm entered through the
prologue (an expression child, a helper call, a null bridge) starts here. -/
theorem _root_.Vsa.Sim.armState_of_entry_kind (kind : Nat) (armPC : BitVec 64)
    (hkle : kind ≤ 8) (harm : execArmPC kind = armPC) (halign : armPC.toNat % 4 = 0)
    {s : Stmt}
    (hkind : ∀ (m : Mem) (a : Nat), StmtRepr m a s → read32 m a = some kind)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {cfg : Config}
    (hEntry : ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 cfg) :
    ∃ (cfg' : Config) (ment : Mem), Steps cfg cfg' ∧
      Vsa.Sim.ArmState armPC s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 ment cfg' := by
  have hGround0 : ExecGround m0 SL A sp aRet aStmt.toNat s :=
    hEntry.mem ▸ hEntry.ground
  have hStmt0 : StmtRepr m0 aStmt.toNat s := hEntry.mem ▸ hEntry.stmt
  have hkind : read32 m0 aStmt.toNat = some kind := hkind _ _ hStmt0
  have hslot : StmtSlotPinned kind armPC m0 :=
    harm ▸ hGround0.table.slotOf kind hkle
  obtain ⟨cA, hsA, ment, v8, v9, v18, v19, hArm⟩ :=
    execBlockA g N A SL φf φc st d env s kind armPC
      sp r aInterp aStmt aEnv aRet m0 cfg.σ.sailOutput
      hkle (by omega) hkind hslot halign
      ⟨by rcases hGround0.table_stack with h | h <;> omega⟩ cfg ⟨hEntry, rfl⟩
  obtain ⟨hG, htick, hpc, hs0, hs1, hs3, hs2, hsp, hra,
    hmi, hout, houtStr, hmem, hcode, hstore,
    hSavedRa, hSavedS0, hSavedS1, hSavedS2, hSavedS3,
    hG8, hG9, hG18, hG19, hGsp, hFrame, hMemFrame,
    hsp176, hspHi, hspLo, hspWin, hsp8, hraAlign, hMemExt⟩ := hArm
  have hpop : StackBytesPresent ment SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := hGround0.stack_bytes k hlo hhi
    exact hMemExt k b hb
  have hGround := hGround0.transport_offstack hEntry.stackOK.2.1 hpop hMemFrame
  have hStmt := hGround0.stmtRepr_offstack hStmt0 hEntry.stackOK.2.1 hMemFrame
  have hSLhi := hEntry.stackBudget.2.1
  have hStoreSurv : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
      StoreRepr m' N A φf φc st.store := by
    intro m' hag
    apply hEntry.store_survives m'
    intro k hk
    rw [hEntry.mem]
    exact (hMemFrame k (by
      intro hs
      exact hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hSLhi⟩)).symm.trans (hag k hk)
  have hDefined : (∃ v, cA.σ.regs.get? Register.x20 = some v) ∧
      (∃ v, cA.σ.regs.get? Register.x21 = some v) := by
    obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hEntry.envset_defined
    refine ⟨⟨v20, ?_⟩, ⟨v21, ?_⟩⟩
    · rw [hFrame Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hEntry.frame Register.x20 (by decide)).symm.trans hv20
    · rw [hFrame Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hEntry.frame Register.x21 (by decide)).symm.trans hv21
  refine ⟨cA, ment, hsA, ?_⟩
  exact
    { good := hG
      tick := htick
      pc := hpc
      s0 := hs0
      s1 := hs1
      s2 := hs2
      s3 := hs3
      spReg := hsp
      minstret := hmi
      out := by
        change String.join cA.σ.sailOutput.toList = st.out
        rw [hout]
        exact hEntry.out
      mem := hmem
      code := hcode
      store := hstore
      saved_ra := hSavedRa
      saved_s0 := ⟨v8, hSavedS0, hG8⟩
      saved_s1 := ⟨v9, hSavedS1, hG9⟩
      saved_s2 := ⟨v18, hSavedS2, hG18⟩
      saved_s3 := ⟨v19, hSavedS3, hG19⟩
      parentSp := hGsp
      frame := hFrame
      mem_frame := hMemFrame
      mem_extends := hMemExt
      ra_align := hraAlign
      spSL := hSLhi
      stack_budget := hEntry.stackBudget
      stmt_bodies := hEntry.stmt_bodies
      store_bodies := hEntry.store_bodies
      store_survives := hStoreSurv
      env_valid := hEntry.env_valid
      env_addr := hEntry.envPtr
      code_stack_disjoint := hEntry.code_stack_disjoint
      stack_ram := hEntry.stack_ram
      stack_win := hEntry.stack_win
      ground := hGround
      stmt := hStmt
      envset := hDefined }

/-- The prologue and the jump-table dispatch reach the arm state. -/
theorem armState_of_entry (D : EvalChildArm) (C : D.Cert) (E : D.EntryCert)
    {s : Stmt} {e : Expr} (S : D.Sem s e)
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem} {cfg : Config}
    (hEntry : ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 cfg) :
    ∃ (cfg' : Config) (ment : Mem), Steps cfg cfg' ∧
      D.ArmState s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 ment cfg' :=
  armState_of_entry_kind D.kind D.armPC E.kind_le E.arm_of_kind C.arm_align
    S.kind_of_repr hEntry

/-! ## The dispatch -/

/-- **The parametric arm dispatch.**  From the statement entry, run the
prologue, the jump-table dispatch, the arm prefix, and the `jal`; land at the
child's `EvalEntry` with the parent carrier. -/
theorem dispatch (D : EvalChildArm) (C : D.Cert) (E : D.EntryCert) {s : Stmt} {e : Expr}
    (S : D.Sem s e)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0)
      (D.DispatchPost s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0) := by
  intro cfg hEntry
  obtain ⟨cA, ment, hsA, hA⟩ := D.armState_of_entry C E S hEntry
  obtain ⟨cC, hsC, hPost⟩ := D.dispatch_of_armState C S hA
  exact ⟨cC, hsA.trans hsC, hPost⟩

#print axioms EvalChildArm.dispatch

/-! ## The child exit -/

/-- Parent facts recovered at the child's widened exit.  This is the only seam
that opens `EvalExitD`; the arm-specific resume rows consume this package. -/
structure ExitKit (D : EvalChildArm) (s : Stmt)
    (gC : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : SpecSt) (v : Value)
    (sp aStmt aRet : BitVec 64) (mC : Mem) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some D.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  ground : ExecGround cfg.σ.mem SL A sp aRet aStmt.toNat s
  parent_stmt : StmtRepr cfg.σ.mem aStmt.toNat s
  code : Exec_stmtLoaded cfg.σ.mem
  header : TruthyHeaderRepr cfg.σ.mem (D.sret (sp - 176#64)).toNat v
  stack_bytes : ∀ k, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, cfg.σ.mem[k]? = some b
  frame : ∀ R, AbiPreservedNoise R → cfg.σ.regs.get? R = gC R
  out : OutRepr cfg.σ st'

/-- Geometry of the child call shared by every exit consumer. -/
theorem Carrier.geom {D : EvalChildArm} (C : D.Cert) {s : Stmt} {e : Expr}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d : Nat} {env : Addr}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (h : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    176 ≤ sp.toNat ∧ (sp - 176#64).toNat = sp.toNat - 176 ∧
    (D.sret (sp - 176#64)).toNat = sp.toNat - 176 + D.sretOff ∧
    SL.lo + 176 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 := by
  have hneed := Stmt.stackNeed_ge s
  simp only [execFrame] at hneed
  obtain ⟨hlo, hhi, hal⟩ := h.stack_budget
  have h176 : 176 ≤ sp.toNat := by omega
  exact ⟨h176, esp_toNat sp h176, D.sret_toNat C sp h176, by omega, hhi, hal⟩

/-- Recover the parent ground, AST, code, and truthiness header from the
widened child exit. -/
theorem exitKit_at_exit (D : EvalChildArm) (C : D.Cert) {s : Stmt} {e : Expr}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (cfg : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfg) :
    ∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      (∀ m' : Mem,
        (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf' φc' st'.store) ∧
      D.ExitKit s gC N A SL φf' φc' st' v sp aStmt aRet mC cfg := by
  rcases hExitD with ⟨hExit, hExt, _hWords, φf', φc', hpf, hpc, hStoreSurv⟩
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, _hal⟩ := hCarrier.geom C
  have hsretRoom := C.sret_room
  have hPop : ∀ k, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, cfg.σ.mem[k]? = some b := by
    intro k hklo hkhi
    obtain ⟨b, hb⟩ := hCarrier.ground.stack_bytes k hklo hkhi
    exact hExt k b hb
  have hSretGeom : SL.lo ≤ (D.sret (sp - 176#64)).toNat ∧
      (D.sret (sp - 176#64)).toNat + 24 ≤ sp.toNat := by rw [hsret]; omega
  have hFrameOuter : ∀ a : Nat,
      ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      ((D.sret (sp - 176#64)).toNat ≤ a ∧ a < (D.sret (sp - 176#64)).toNat + 24) ∨
        cfg.σ.mem[a]? = mC[a]? := by
    intro a hstk harena
    apply hExit.memFrame a
    · intro hc
      apply hstk
      exact ⟨hc.1, Nat.lt_of_lt_of_le hc.2 (by rw [hesp]; omega)⟩
    · exact harena
  have hGround : ExecGround cfg.σ.mem SL A sp aRet aStmt.toNat s :=
    hCarrier.ground.transport_evalExit hSLhi hSretGeom hPop hFrameOuter
  have hParent : StmtRepr cfg.σ.mem aStmt.toNat s :=
    hCarrier.ground.stmtRepr_evalExit hCarrier.stmt hSLhi hSretGeom hFrameOuter
  have hCode : Exec_stmtLoaded cfg.σ.mem := by
    apply loaded_exec_stmt_agree mC cfg.σ.mem _ hCarrier.code
    intro k hklo hkhi
    have hstk : ¬ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat) := by
      intro hc
      rcases hCarrier.code_stack_disjoint with hd | hd <;> omega
    have harena : ¬ (A.lo ≤ k ∧ k < A.hi) := by
      intro hc
      rcases hCarrier.ground.arena_code with hd | hd <;> omega
    rcases hExit.memFrame k hstk harena with hs | heq
    · exfalso
      rw [hsret] at hs
      rcases hCarrier.code_stack_disjoint with hd | hd <;> omega
    · exact heq
  obtain ⟨_φcv, _hφcv, hValue⟩ := hExit.result
  exact ⟨φf', φc', hpf, hpc, hStoreSurv,
    { good := hExit.good
      tick := hExit.tick
      pc := by rw [← C.ret_pc_clean]; exact hExit.pc
      minstret := hExit.minstret
      ground := hGround
      parent_stmt := hParent
      code := hCode
      header := truthyHeaderRepr_of_valueRepr hValue
      stack_bytes := hPop
      frame := hExit.frame
      out := hExit.out }⟩

/-- A normal completion that runs straight from the child's return into the
arm's `li a0,0` (the `expr` shape) is already at the parametric tail head. -/
theorem normalExitPre_of_exit (D : EvalChildArm) (C : D.Cert) {s : Stmt} {e : Expr}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet : BitVec 64} {m0 : Mem}
    {gC : (R : Register) → Option (RegisterType R)} {aC : BitVec 64} {mC : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (cfg : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfg) :
    ∃ (φf' φc' : Addr → Nat),
      NormalExitTailPre D.retPC g N A SL φf φc φf' φc'
        st.store.frames.size st.store.closures.size st' sp r aRet m0 cfg := by
  obtain ⟨φf', φc', hpf, hpc, hStoreSurv, hKit⟩ := D.exitKit_at_exit C hCarrier cfg hExitD
  rcases hExitD with ⟨hExit, hExt, _hWords, _⟩
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom C
  have hsretRoom := C.sret_room
  have hSaved : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) cfg.σ.mem mC := by
    intro k hk
    rcases hExit.memFrame k
        (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq
  have hSavedRead (off : Nat) (hlo : 8 ≤ off) (hhi : off ≤ 40) :
      read64 cfg.σ.mem (sp.toNat - off) = read64 mC (sp.toNat - off) :=
    read64_agreeP hSaved (fun k hk => ⟨by omega, by omega⟩)
  refine ⟨φf', φc', ?_⟩
  refine
    { good := hKit.good
      tick := hKit.tick
      pc := hKit.pc
      minstret := hKit.minstret
      spReg := (hExit.frame Register.x2 (by decide)).trans hCarrier.spReg
      code := hKit.code
      out := hKit.out
      frames := hpf
      closures := hpc
      storeSurvives := hStoreSurv
      saved_ra := (hSavedRead 8 (by omega) (by omega)).trans hCarrier.saved_ra
      saved_s0 := ?_
      saved_s1 := ?_
      saved_s2 := ?_
      saved_s3 := ?_
      parentSp := hCarrier.parentSp
      frame := ?_
      memExtends := hCarrier.mem_extends.trans hExt
      memFrame := ?_
      spRoom := h176
      spHi := Nat.le_trans hSLhi hCarrier.stack_ram.2
      spLo := Nat.le_trans hCarrier.stack_ram.1 (by omega)
      spWin := by have := hCarrier.stack_win; omega
      spAlign := by omega
      retAlign := hCarrier.ra_align }
  · obtain ⟨v8, hs8, hg8⟩ := hCarrier.saved_s0
    exact ⟨v8, (hSavedRead 16 (by omega) (by omega)).trans hs8, hg8⟩
  · obtain ⟨v9, hs9, hg9⟩ := hCarrier.saved_s1
    exact ⟨v9, (hSavedRead 24 (by omega) (by omega)).trans hs9, hg9⟩
  · obtain ⟨v18, hs18, hg18⟩ := hCarrier.saved_s2
    exact ⟨v18, (hSavedRead 32 (by omega) (by omega)).trans hs18, hg18⟩
  · obtain ⟨v19, hs19, hg19⟩ := hCarrier.saved_s3
    exact ⟨v19, (hSavedRead 40 (by omega) (by omega)).trans hs19, hg19⟩
  · intro R hR he8 he9 he18 he19 he2
    have hg : gC R = g R := by
      rcases hCarrier.frame R hR with hspecial | heq
      · rcases hspecial with rfl | rfl | rfl | rfl | rfl
        · simp at he8
        · simp at he9
        · simp at he18
        · simp at he19
        · simp at he2
      · exact heq
    exact (hExit.frame R hR).trans hg
  · intro k hstk hA
    apply Or.inr
    rcases hExit.memFrame k
        (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
    · exfalso
      rw [hsret] at hr
      exact hstk ⟨by omega, by omega⟩
    · exact heq.trans (hCarrier.mem_frame k hstk)

#print axioms EvalChildArm.exitKit_at_exit
#print axioms EvalChildArm.normalExitPre_of_exit

end EvalChildArm

end Vsa.Sim
