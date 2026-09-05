import Vsa.Sim.ExecWhileIndexed
import Vsa.Sim.SegEffect
import Vsa.Sim.rows.ArmDispatchInstancesExec
import Vsa.Sim.rows.ExecWhileRouteRows

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

local notation "SpecSt" => Vsa.While.St

/-- Registers not explicitly owned by the live while frame. -/
def ExecWhileFrameKeep (R : Register) : Prop :=
  AbiPreservedNoise R ∧ (Register.x8 == R) = false ∧
  (Register.x9 == R) = false ∧ (Register.x18 == R) = false ∧
  (Register.x19 == R) = false ∧ (Register.x2 == R) = false

/-- Convert the consumer's propositional exclusions once at the seam. -/
theorem ExecWhileFrameKeep.of_ne (R : Register) (hR : AbiPreservedNoise R)
    (h8 : R ≠ Register.x8) (h9 : R ≠ Register.x9)
    (h18 : R ≠ Register.x18) (h19 : R ≠ Register.x19)
    (h2 : R ≠ Register.x2) : ExecWhileFrameKeep R := by
  exact ⟨hR,
    beq_eq_false_iff_ne.mpr (Ne.symm h8),
    beq_eq_false_iff_ne.mpr (Ne.symm h9),
    beq_eq_false_iff_ne.mpr (Ne.symm h18),
    beq_eq_false_iff_ne.mpr (Ne.symm h19),
    beq_eq_false_iff_ne.mpr (Ne.symm h2)⟩

/-- Opaque result of decoded dispatch plus the while-condition arm prefix.
Only the facts needed to reconstruct the enclosing frame survive this cut. -/
structure ExecWhileCondArmStage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cfg : Config) : Prop where
  arm : ∃ (v8 v9 v18 v19 : BitVec 64),
    ExecArmEntryK g N A SL φf φc st (0x8000403c#64)
      sp r aInterp aStmt aEnv aRet v8 v9 v18 v19 cfg.σ.sailOutput m0 ment cfg
  ready : LandedN 4 cfg (ExecWhileCondJalReady gpre N A SL φf φc
    cnd st d env sp aInterp aStmt aEnv aRet aCond ment)
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      ¬ (aInterp.toNat ≤ k ∧ k < aInterp.toNat + 24) →
      ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  outer_frame : ∀ R : Register, AbiPreservedNoise R →
    cfg.σ.regs.get? R = gpre R

/-- First opaque stage: decoded statement dispatch followed by the exact
four-instruction condition-call prefix. -/
theorem execWhileCondArmStage_of_resid
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hR : ∀ cfg : Config,
      ExecArmDispatchResid 4 (0x8000403c#64) (.whileStmt cnd body)
        cnd 8 16 st d env cfg) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (fun cfg => ∃ (gpre : (R : Register) → Option (RegisterType R))
          (aCond : BitVec 64) (ment : Mem),
        ExecWhileCondArmStage g N A SL φf φc st d env cnd body
          sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cfg) := by
  intro cfg hEntry
  have hDisp := stmtWhileCondArmDispatch_of_resid cnd body st d env cfg (hR cfg)
  obtain ⟨cA, hsA, hMid⟩ :=
    hDisp g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 hEntry cfg rfl
  obtain ⟨gpre, aCond, v8, v9, v18, v19, ment, hArm, hpay, hExpr,
    hstmtAl, hstmtLo, hstmtHi, hstmtWin, hEvalCode, hViCode, hViSlot,
    hNbs, hEvalGround, hWords, henvPtr, hStoreSurv,
    hcondAl, hcondLo, hcondHi, hcondWin, hcondStk, hsproom, hsp16,
    hSLlo, hSLhi, hSLwin, hjspHi, hcodeStkJ, htableStkJ1,
    htableStkJ2, harenaStkJ, harenaCode, hgpre, hg8, hg18, hg19,
    hg20, hg21, hcondBudget, hcondBodies, hstoreBodies⟩ := hMid
  have hReady := blockB_stmtWhileCond_stagePre g gpre N A SL φf φc
    st d env cnd sp r aInterp aStmt aEnv aRet aCond v8 v9 v18 v19
    cA.σ.sailOutput m0 ment cA hEntry.env_valid
    ⟨hArm, hpay, hExpr, hstmtAl, hstmtLo, hstmtHi, hstmtWin,
      hEvalCode, hViCode, hViSlot, hNbs, hEvalGround, hWords, henvPtr,
      hStoreSurv, hcondAl, hcondLo, hcondHi, hcondWin, hcondStk,
      hsproom, hsp16, hSLlo, hSLhi, hSLwin, hjspHi, hcodeStkJ,
      htableStkJ1, htableStkJ2, harenaStkJ, harenaCode, hgpre,
      hg8, hg18, hg19, hg20, hg21, hcondBudget, hcondBodies,
      hstoreBodies⟩
  exact ⟨cA, hsA, gpre, aCond, ment,
    { arm := ⟨v8, v9, v18, v19, hArm⟩
      ready := hReady
      store_survives := hStoreSurv
      outer_frame := hgpre }⟩

#print axioms execWhileCondArmStage_of_resid

/-- Memory and representation facts transported through the prologue writes. -/
structure ExecWhileCondMemKit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (ment : Mem) : Prop where
  code : Vsa.Sim.Code.Exec_stmtLoaded ment
  stmt : StmtRepr ment aStmt.toNat (.whileStmt cnd body)
  store : StoreRepr ment N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  ground : ExecGround ment SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  mem_frame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ment[a]? = m0[a]?

/-- Saved enclosing-frame words and their original register meanings. -/
structure ExecWhileCondSpillKit
    (g : (R : Register) → Option (RegisterType R))
    (sp r : BitVec 64) (ment : Mem) : Prop where
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : ∃ v, read64 ment (sp.toNat - 16) = some v.toNat ∧
    g Register.x8 = some v
  saved_s1 : ∃ v, read64 ment (sp.toNat - 24) = some v.toNat ∧
    g Register.x9 = some v
  saved_s2 : ∃ v, read64 ment (sp.toNat - 32) = some v.toNat ∧
    g Register.x18 = some v
  saved_s3 : ∃ v, read64 ment (sp.toNat - 40) = some v.toNat ∧
    g Register.x19 = some v
/-- Exact ghost-frame relation at the condition jal seam. -/
structure ExecWhileCondFrameKit
    (g gpre : (R : Register) → Option (RegisterType R))
    (aStmt aEnv aRet : BitVec 64) : Prop where
  gpre_s0 : gpre Register.x8 = some aStmt
  gpre_s2 : gpre Register.x18 = some aRet
  gpre_s3 : gpre Register.x19 = some aEnv
  frame : ∀ R : Register, AbiPreservedNoise R →
    R ≠ Register.x8 → R ≠ Register.x9 → R ≠ Register.x18 →
    R ≠ Register.x19 → R ≠ Register.x2 → gpre R = g R

/-- The small outer kit has one field per consumer group. -/
structure ExecWhileCondTransportKit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (ment : Mem) : Prop where
  mem : ExecWhileCondMemKit g N A SL φf φc st d env cnd body
    sp r aInterp aStmt aEnv aRet m0 ment
  spills : ExecWhileCondSpillKit g sp r ment
  frame : ExecWhileCondFrameKit g gpre aStmt aEnv aRet

/-- Transport the memory and syntax representations. -/
theorem execWhileCondMemKit_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cfg0 cA : Config)
    (hEntry : ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0 cfg0)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    ExecWhileCondMemKit g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 ment := by
  obtain ⟨v8, v9, v18, v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, _hs0, _hs1, _hs3, _hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, hcode, hstore,
    hsavedRa, hsavedS0, hsavedS1, hsavedS2, hsavedS3,
    hv8, hv9, hv18, hv19, _hgsp, hArmFrame, hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, hMemExt⟩ := hArm
  have hGround0 : ExecGround m0 SL A sp aRet aStmt.toNat
      (.whileStmt cnd body) := by
    rw [← hEntry.mem]
    exact hEntry.ground
  have hStmt0 : StmtRepr m0 aStmt.toNat (.whileStmt cnd body) := by
    rw [← hEntry.mem]
    exact hEntry.stmt
  have hPop : ∀ k : Nat, SL.lo ≤ k → k < SL.hi →
      ∃ b : BitVec 8, ment[k]? = some b := by
    intro k hklo hkhi
    obtain ⟨b, hb⟩ := hGround0.stack_bytes k hklo hkhi
    exact hMemExt k b hb
  have hGroundMent : ExecGround ment SL A sp aRet aStmt.toNat
      (.whileStmt cnd body) :=
    hGround0.transport_offstack hEntry.stackOK.2.1 hPop hMemFrame
  have hStmtMent : StmtRepr ment aStmt.toNat (.whileStmt cnd body) :=
    hGround0.stmtRepr_offstack hStmt0 hEntry.stackOK.2.1 hMemFrame
  refine
    { code := hcode
      stmt := hStmtMent
      store := hstore
      store_survives := by
        intro m' hag
        exact hStage.store_survives m' (fun k hk _ => hag k hk)
      ground := hGroundMent
      mem_frame := hMemFrame }

#print axioms execWhileCondMemKit_of_stage

/-- Project the five saved words without forcing representation transport. -/
theorem execWhileCondSpillKit_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    ExecWhileCondSpillKit g sp r ment := by
  obtain ⟨v8, v9, v18, v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, _hs0, _hs1, _hs3, _hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, _hcode, _hstore,
    hsavedRa, hsavedS0, hsavedS1, hsavedS2, hsavedS3,
    hv8, hv9, hv18, hv19, _hgsp, _hArmFrame, _hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, _hMemExt⟩ := hArm
  exact
    { saved_ra := hsavedRa
      saved_s0 := ⟨v8, hsavedS0, hv8⟩
      saved_s1 := ⟨v9, hsavedS1, hv9⟩
      saved_s2 := ⟨v18, hsavedS2, hv18⟩
      saved_s3 := ⟨v19, hsavedS3, hv19⟩ }

#print axioms execWhileCondSpillKit_of_stage

/-- The exact s0 pin in the pre-jal ghost frame. -/
theorem execWhileCondFrameS0_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    gpre Register.x8 = some aStmt := by
  obtain ⟨_v8, _v9, _v18, _v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, hs0, _hs1, _hs3, _hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, _hcode, _hstore,
    _hsavedRa, _hsavedS0, _hsavedS1, _hsavedS2, _hsavedS3,
    _hv8, _hv9, _hv18, _hv19, _hgsp, _hArmFrame, _hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, _hMemExt⟩ := hArm
  exact (hStage.outer_frame Register.x8 (by decide)).symm.trans hs0

#print axioms execWhileCondFrameS0_of_stage

/-- The exact s2 pin in the pre-jal ghost frame. -/
theorem execWhileCondFrameS2_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    gpre Register.x18 = some aRet := by
  obtain ⟨_v8, _v9, _v18, _v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, _hs0, _hs1, _hs3, hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, _hcode, _hstore,
    _hsavedRa, _hsavedS0, _hsavedS1, _hsavedS2, _hsavedS3,
    _hv8, _hv9, _hv18, _hv19, _hgsp, _hArmFrame, _hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, _hMemExt⟩ := hArm
  exact (hStage.outer_frame Register.x18 (by decide)).symm.trans hs2

#print axioms execWhileCondFrameS2_of_stage

/-- The exact s3 pin in the pre-jal ghost frame. -/
theorem execWhileCondFrameS3_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    gpre Register.x19 = some aEnv := by
  obtain ⟨_v8, _v9, _v18, _v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, _hs0, _hs1, hs3, _hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, _hcode, _hstore,
    _hsavedRa, _hsavedS0, _hsavedS1, _hsavedS2, _hsavedS3,
    _hv8, _hv9, _hv18, _hv19, _hgsp, _hArmFrame, _hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, _hMemExt⟩ := hArm
  exact (hStage.outer_frame Register.x19 (by decide)).symm.trans hs3

#print axioms execWhileCondFrameS3_of_stage

/-- Every other ABI-preserved register agrees with the outer entry ghost. -/
theorem execWhileCondOuterStable_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    EffectStable ExecWhileFrameKeep (fun R => cA.σ.regs.get? R) gpre := by
  refine ⟨fun R hR => ?_⟩
  exact hStage.outer_frame R hR.1

#print axioms execWhileCondOuterStable_of_stage

/-- The arm-entry frame agrees with the outer entry on the same keep set. -/
theorem execWhileCondArmStable_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    EffectStable ExecWhileFrameKeep (fun R => cA.σ.regs.get? R) g := by
  obtain ⟨_v8, _v9, _v18, _v19, hArm⟩ := hStage.arm
  obtain ⟨_hG, _htick, _hpc, _hs0, _hs1, _hs3, _hs2, _hsp, _hra,
    _hmi, _hout, _houtStr, _hmem, _hcode, _hstore,
    _hsavedRa, _hsavedS0, _hsavedS1, _hsavedS2, _hsavedS3,
    _hv8, _hv9, _hv18, _hv19, _hgsp, hArmFrame, _hMemFrame,
    _hsp176, _hsphi, _hsplo, _hspwin, _hsp8, _hraAl, _hMemExt⟩ := hArm
  refine ⟨fun R hR => ?_⟩
  exact hArmFrame R hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1
    hR.2.2.2.2.1 hR.2.2.2.2.2

#print axioms execWhileCondArmStable_of_stage

/-- Every other ABI-preserved register agrees with the outer entry ghost. -/
theorem execWhileCondFrameOther_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    ∀ R : Register, AbiPreservedNoise R →
      R ≠ Register.x8 → R ≠ Register.x9 → R ≠ Register.x18 →
      R ≠ Register.x19 → R ≠ Register.x2 → gpre R = g R := by
  intro R hR h8 h9 h18 h19 h2
  have hOuter := execWhileCondOuterStable_of_stage g N A SL φf φc st d env
    cnd body sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
  have hArm := execWhileCondArmStable_of_stage g N A SL φf φc st d env
    cnd body sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
  exact (hOuter.symm.trans hArm).eq R
    (ExecWhileFrameKeep.of_ne R hR h8 h9 h18 h19 h2)

#print axioms execWhileCondFrameOther_of_stage

/-- Assemble the four opaque frame fields. -/
theorem execWhileCondFrameKit_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cA : Config)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    ExecWhileCondFrameKit g gpre aStmt aEnv aRet := by
  exact
    { gpre_s0 := execWhileCondFrameS0_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
      gpre_s2 := execWhileCondFrameS2_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
      gpre_s3 := execWhileCondFrameS3_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
      frame := execWhileCondFrameOther_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage }

#print axioms execWhileCondFrameKit_of_stage

/-- Assemble the three already-opaque transport groups. -/
theorem execWhileCondTransportKit_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cfg0 cA : Config)
    (hEntry : ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0 cfg0)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA) :
    ExecWhileCondTransportKit g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre ment := by
  exact
    { mem := execWhileCondMemKit_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cfg0 cA hEntry hStage
      spills := execWhileCondSpillKit_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage
      frame := execWhileCondFrameKit_of_stage g N A SL φf φc st d env cnd body
        sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA hStage }

#print axioms execWhileCondTransportKit_of_stage

/-- Third opaque stage: combine a transported static kit with the exact
post-jal register frame. -/
theorem execWhileCondCarrier_of_kit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cfg0 cC : Config)
    (hEntry : ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0 cfg0)
    (hKit : ExecWhileCondTransportKit g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre ment)
    (hFrame : ExecEvalJalFrame gpre aInterp ((sp - 176#64) + 1088#64) cC) :
    ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 (fun R => cC.σ.regs.get? R) aCond ment := by
  refine
    { s0 := hFrame.s0.trans hKit.frame.gpre_s0
      s1 := hFrame.s1
      s2 := hFrame.s2.trans hKit.frame.gpre_s2
      s3 := hFrame.s3.trans hKit.frame.gpre_s3
      spReg := by
        simpa only [BitVec.add_sub_cancel] using hFrame.spReg
      code := hKit.mem.code
      code_stack_disjoint := hEntry.code_stack_disjoint
      stack_ram := hEntry.stack_ram
      stack_win := hEntry.stack_win
      ra_align := hEntry.ra_align
      stmt := hKit.mem.stmt
      env_addr := hEntry.envPtr
      store := hKit.mem.store
      env_valid := hEntry.env_valid
      store_survives := hKit.mem.store_survives
      saved_ra := hKit.spills.saved_ra
      saved_s0 := hKit.spills.saved_s0
      saved_s1 := hKit.spills.saved_s1
      saved_s2 := hKit.spills.saved_s2
      saved_s3 := hKit.spills.saved_s3
      stack_budget := hEntry.stackBudget
      stmt_bodies := hEntry.stmt_bodies
      store_bodies := hEntry.store_bodies
      envset_defined := by
        obtain ⟨⟨v20, hv20⟩, ⟨v21, hv21⟩⟩ := hEntry.envset_defined
        refine ⟨⟨v20, ?_⟩, ⟨v21, ?_⟩⟩
        · rw [hFrame.frame Register.x20 (by decide),
            hKit.frame.frame Register.x20 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)]
          exact (hEntry.frame Register.x20 (by decide)).symm.trans hv20
        · rw [hFrame.frame Register.x21 (by decide),
            hKit.frame.frame Register.x21 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)]
          exact (hEntry.frame Register.x21 (by decide)).symm.trans hv21
      ground := hKit.mem.ground
      mem_frame := hKit.mem.mem_frame
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
        · exact Or.inr ((hFrame.frame R hR).trans
            (hKit.frame.frame R hR h8 h9 h18 h19 h2)) }

#print axioms execWhileCondCarrier_of_kit

/-- Opaque composer retained for clients that still own the arm stage. -/
theorem execWhileCondCarrier_of_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (gpre : (R : Register) → Option (RegisterType R))
    (aCond : BitVec 64) (ment : Mem) (cfg0 cA cC : Config)
    (hEntry : ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
      sp r aInterp aStmt aEnv aRet m0 cfg0)
    (hStage : ExecWhileCondArmStage g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cA)
    (hChild : EvalEntry (fun R => cC.σ.regs.get? R) N A SL φf φc
        st d env cnd (sp - 176#64) (0x80004050#64)
        ((sp - 176#64) + sign_extend (m := 64) (0x050#12))
        aInterp aCond ment cC ∧
      ExecEvalJalFrame gpre aInterp ((sp - 176#64) + 1088#64) cC) :
    ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 (fun R => cC.σ.regs.get? R) aCond ment := by
  have hKit := execWhileCondTransportKit_of_stage g N A SL φf φc st d env
    cnd body sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cfg0 cA
    hEntry hStage
  exact execWhileCondCarrier_of_kit g N A SL φf φc st d env cnd body
    sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cfg0 cC
    hEntry hKit hChild.2

#print axioms execWhileCondCarrier_of_stage

/-- The decoded statement dispatch and exact while-arm prefix supply the
indexed condition call.  This final stage only composes the two opaque
suppliers above. -/
theorem execWhileCondDispatch_of_armResid
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hR : ∀ cfg : Config,
      ExecArmDispatchResid 4 (0x8000403c#64) (.whileStmt cnd body)
        cnd 8 16 st d env cfg) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.whileStmt cnd body)
        sp r aInterp aStmt aEnv aRet m0)
      (fun cfg => ∃ (gCond : (R : Register) → Option (RegisterType R))
          (aCond : BitVec 64) (mCond : Mem),
        ExecWhileCondCarrier g N A SL φf φc st d env cnd body
          sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond ∧
        EvalEntry gCond N A SL φf φc st d env cnd
          (sp - 176#64) (0x80004050#64) (sp - 96#64)
          aInterp aCond mCond cfg) := by
  intro cfg hEntry
  obtain ⟨cA, hsA, gpre, aCond, ment, hStage⟩ :=
    execWhileCondArmStage_of_resid g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 hR cfg hEntry
  obtain ⟨nJ, cJ, _hnJ, hsJ, hJ⟩ := hStage.ready
  obtain ⟨nC, cC, _hnC, hsC, hChild⟩ := hJ.child
  have hsub :
      (sp - 176#64) + sign_extend (m := 64) (0x050#12) = sp - 96#64 := by
    apply BitVec.eq_of_toNat_eq
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    have h96 : (96#64 : BitVec 64).toNat = 96 := by decide
    have h80 : (sign_extend (m := 64) (0x050#12) : BitVec 64).toNat = 80 := by decide
    have hroom := hEntry.stackOK.1
    have hlt := sp.isLt
    have hespN : (sp - 176#64).toNat = sp.toNat - 176 := by
      rw [BitVec.toNat_sub, h176]
      omega
    have hsp96N : (sp - 96#64).toNat = sp.toNat - 96 := by
      rw [BitVec.toNat_sub, h96]
      omega
    rw [BitVec.toNat_add, hespN, h80, hsp96N]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hEval := hChild.1
  rw [hsub] at hEval
  have hCarrier := execWhileCondCarrier_of_stage g N A SL φf φc st d env
    cnd body sp r aInterp aStmt aEnv aRet m0 gpre aCond ment cfg cA cC
    hEntry hStage hChild
  exact ⟨cC, hsA.trans (hsJ.toSteps.trans hsC.toSteps),
    (fun R => cC.σ.regs.get? R), aCond, ment, hCarrier, hEval⟩

#print axioms execWhileCondDispatch_of_armResid

/-! ## Condition return to recursive body entry -/

/-- The represented body pointer and child representation carried by a
represented `while` node. -/
theorem stmtRepr_while_body {m : Mem} {a : Nat} {cnd : Expr} {body : Stmt}
    (h : StmtRepr m a (.whileStmt cnd body)) :
    ∃ aBody : Nat,
      read64 m (a + 16) = some aBody ∧ StmtRepr m aBody body := by
  cases h with
  | whileS _ _ _ hBody hBodyRepr =>
      exact ⟨_, hBody, hBodyRepr⟩

/-- Bit-vector form of `stmtRepr_while_body`, matching the recursive-call ABI. -/
theorem stmtRepr_while_body_bv {m : Mem} {a : Nat}
    {cnd : Expr} {body : Stmt}
    (h : StmtRepr m a (.whileStmt cnd body)) :
    ∃ aBody : BitVec 64,
      read64 m (a + 16) = some aBody.toNat ∧
      StmtRepr m aBody.toNat body := by
  obtain ⟨p, hp, hBody⟩ := stmtRepr_while_body h
  have hpLt : p < 2 ^ 64 := read64_lt_eg4 m (a + 16) p hp
  let aBody : BitVec 64 := BitVec.ofNat 64 p
  have haBody : aBody.toNat = p := by
    simp only [aBody, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpLt]
  exact ⟨aBody, by simpa only [haBody] using hp,
    by simpa only [haBody] using hBody⟩

/-- Hereditary AST containment projects from a `while` node to its body. -/
theorem stmtIn_while_body {m : Mem} {lo hi a aBody : Nat}
    {cnd : Expr} {body : Stmt}
    (h : StmtIn m lo hi a (.whileStmt cnd body))
    (hBody : read64 m (a + 16) = some aBody) :
    StmtIn m lo hi aBody body :=
  h.2.2 aBody hBody

/-- Semantic and static facts recovered at the condition-IH return.  This is
the only seam that opens `EvalExitD`; the finite copy/truthiness rows consume
this compact package. -/
structure ExecWhileCondExitKit
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (v : Value) (cnd : Expr) (body : Stmt)
    (sp aStmt aRet : BitVec 64) (mCond : Mem)
    (aBody : BitVec 64) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004050#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  ground : ExecGround cfg.σ.mem SL A sp aRet aStmt.toNat (.whileStmt cnd body)
  parent_stmt : StmtRepr cfg.σ.mem aStmt.toNat (.whileStmt cnd body)
  body_read : read64 cfg.σ.mem (aStmt.toNat + 16) = some aBody.toNat
  body_stmt : StmtRepr cfg.σ.mem aBody.toNat body
  code : Vsa.Sim.Code.Exec_stmtLoaded cfg.σ.mem
  header : TruthyHeaderRepr cfg.σ.mem ((sp - 176#64).toNat + 80) v
  stack_bytes : ∀ k, SL.lo ≤ k → k < SL.hi →
    ∃ b : BitVec 8, cfg.σ.mem[k]? = some b
  frame : ∀ R, AbiPreservedNoise R → cfg.σ.regs.get? R = gCond R
  out : OutRepr cfg.σ st

/-- Recover the parent AST, body child, static code, and truthiness header from
the widened condition exit. -/
theorem execWhileCondExitKit_of_exit
    (g : (R : Register) → Option (RegisterType R))
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stCond : SpecSt) (d : Nat) (env : Addr)
    (cnd : Expr) (body : Stmt) (v : Value)
    (sp r aInterp aStmt aEnv aRet aCond : BitVec 64)
    (m0 mCond : Mem)
    (hCarrier : ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond) :
    Triple
      (EvalExitD gCond N A SL φf φc st.store.frames.size
        st.store.closures.size stCond v (sp - 176#64)
        0x80004050#64 (sp - 96#64) mCond)
      (fun cfg => ∃ (φfBody φcBody : Addr → Nat) (aBody : BitVec 64),
        PhiExtends φf φfBody st.store.frames.size ∧
        PhiExtends φc φcBody st.store.closures.size ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
          StoreRepr m' N A φfBody φcBody stCond.store) ∧
        ExecWhileCondExitKit gCond N A SL φfBody φcBody stCond v cnd body
          sp aStmt aRet mCond aBody cfg) := by
  intro cfg hExitD
  rcases hExitD with ⟨hExit, hExt, _hWords, φfBody, φcBody,
    hφfBody, hφcBody, hStoreSurv⟩
  have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
  have h96 : (96#64 : BitVec 64).toNat = 96 := by decide
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub, h176]
    have := hCarrier.stack_budget.1
    omega
  have hsret : (sp - 96#64).toNat = sp.toNat - 96 := by
    rw [BitVec.toNat_sub, h96]
    have := hCarrier.stack_budget.1
    omega
  have hsretSrc : (sp - 96#64).toNat = (sp - 176#64).toNat + 80 := by
    rw [hesp, hsret]
    have := hCarrier.stack_budget.1
    omega
  have hPop : ∀ k, SL.lo ≤ k → k < SL.hi →
      ∃ b : BitVec 8, cfg.σ.mem[k]? = some b := by
    intro k hklo hkhi
    obtain ⟨b, hb⟩ := hCarrier.ground.stack_bytes k hklo hkhi
    exact hExt k b hb
  have hSretGeom : SL.lo ≤ (sp - 96#64).toNat ∧
      (sp - 96#64).toNat + 24 ≤ sp.toNat := by
    rw [hsret]
    have := hCarrier.stack_budget.1
    omega
  have hFrameOuter : ∀ a : Nat,
      ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      ((sp - 96#64).toNat ≤ a ∧ a < (sp - 96#64).toNat + 24) ∨
        cfg.σ.mem[a]? = mCond[a]? := by
    intro a hstk harena
    apply hExit.memFrame a
    · intro hc
      apply hstk
      exact ⟨hc.1, Nat.lt_of_lt_of_le hc.2 (by rw [hesp]; omega)⟩
    · exact harena
  have hGround : ExecGround cfg.σ.mem SL A sp aRet aStmt.toNat
      (.whileStmt cnd body) :=
    hCarrier.ground.transport_evalExit hCarrier.stack_budget.2.1
      hSretGeom hPop hFrameOuter
  have hParent : StmtRepr cfg.σ.mem aStmt.toNat
      (.whileStmt cnd body) :=
    hCarrier.ground.stmtRepr_evalExit hCarrier.stmt
      hCarrier.stack_budget.2.1 hSretGeom hFrameOuter
  obtain ⟨aBody, hBodyRead, hBodyStmt⟩ := stmtRepr_while_body_bv hParent
  have hCode : Vsa.Sim.Code.Exec_stmtLoaded cfg.σ.mem := by
    apply loaded_exec_stmt_agree mCond cfg.σ.mem _ hCarrier.code
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
  obtain ⟨φcv, _hφcv, hValue⟩ := hExit.result
  have hHeader : TruthyHeaderRepr cfg.σ.mem
      ((sp - 176#64).toNat + 80) v := by
    rw [← hsretSrc]
    exact truthyHeaderRepr_of_valueRepr hValue
  exact ⟨cfg, Vsa.Machine.Steps.refl cfg, φfBody, φcBody, aBody,
    hφfBody, hφcBody, hStoreSurv,
    { ground := hGround
      good := hExit.good
      tick := hExit.tick
      pc := by simpa using hExit.pc
      minstret := hExit.minstret
      parent_stmt := hParent
      body_read := hBodyRead
      body_stmt := hBodyStmt
      code := hCode
      header := hHeader
      stack_bytes := hPop
      frame := hExit.frame
      out := hExit.out }⟩

#print axioms execWhileCondExitKit_of_exit

/-- Exact machine state at the truthy body head.  The carrier is already
rebased to the condition's extended store maps; the remaining finite prefix
only loads the child pointer and marshals the four ABI arguments. -/
structure ExecWhileBodyHeadStage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (aBody : BitVec 64) (mBody : Mem) (cfg : Config) : Prop where
  carrier : ExecWhileBodyCarrier g N A SL φf φc st d env cnd body
    sp r aInterp aStmt aEnv aRet m0 (fun R => cfg.σ.regs.get? R) aBody mBody
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004074#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mBody
  out : OutRepr cfg.σ st

/-- The faithful body-pointer load data computes the represented child
address, not the total-read default zero. -/
theorem execWhileBodyLds_value
    (m : Mem) (aStmt aBody : BitVec 64)
    (hread : read64 m (aStmt.toNat + 16) = some aBody.toNat) :
    bytesVal MKind.ld
      ((execWhileBodyLds m aStmt).getD 0 []) = aBody := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
    read64_bytes m (aStmt.toNat + 16) aBody.toNat hread
  simp only [execWhileBodyLds, execWhileWordLds, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil, bytesVal, hb0, hb1, hb2, hb3,
    hb4, hb5, hb6, hb7, Option.getD_some]
  rw [sext_full]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon]
  exact hrec

#print axioms execWhileBodyLds_value

/-- The one lowered-frame geometry calculation used by the copy and body-call
segments.  In particular, the copy's largest read remains below the original
stack pointer, so its address arithmetic cannot wrap. -/
theorem execWhile_lowered_copy_geom {SL : StackLayout} {sp : BitVec 64}
    {headroom : Nat} (hroom : 176 ≤ headroom)
    (hstack : StackOK SL sp headroom) :
    SL.lo ≤ (sp - 176#64).toNat ∧
    (sp - 176#64).toNat + 104 ≤ SL.hi ∧
    (sp - 176#64).toNat % 16 = 0 := by
  obtain ⟨hlo, hhi, halign⟩ := hstack
  have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
  have hsp : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub, h176]
    have := sp.isLt
    omega
  rw [hsp]
  omega

/-- Control result of the finite condition-copy and truthiness route. -/
structure ExecWhileTruthyBodyHead
    (gCond : (R : Register) → Option (RegisterType R))
    (mHead : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004074#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mHead
  out : cfg.σ.sailOutput = out
  frame : ∀ R, Vsa.Alloc.AbiPreserved R = true →
    cfg.σ.regs.get? R = gCond R

/-- The condition-copy destination is disjoint from the static evaluator
support because it lies wholly inside the lowered stack frame. -/
theorem execWhileCondCopy_evalCall_agree
    {m mCopy : Mem} {SL : StackLayout} {A : Arena} {sp esp : BitVec 64}
    (hSupport : EvalCallSupport m SL A sp)
    (hlo : SL.lo ≤ esp.toNat) (hhi : esp.toNat + 40 ≤ SL.hi)
    (hframe : ∀ k, ¬ (esp.toNat + 16 ≤ k ∧ k < esp.toNat + 40) →
      mCopy[k]? = m[k]?) :
    ∀ k, EvalCallFootprint k → mCopy[k]? = m[k]? := by
  intro k hk
  apply hframe k
  intro hdst
  rcases hk with hcode | hvi | htable
  · rcases hSupport.code_stack with hd | hd <;> omega
  · rcases hSupport.vi_stack with hd | hd <;> omega
  · rcases hSupport.table_stack with hd | hd <;> omega

private theorem abiPreservedNoise_of_abi {R : Register}
    (hR : AbiPreserved R = true) : AbiPreservedNoise R := by
  cases R <;> simp [AbiPreserved, AbiPreservedNoise] at hR ⊢

/-- Exact parked state after the copy and its `jal value_truthy`. -/
structure ExecWhileCondCopyReady
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (esp aStmt aInterp aRet aEnv : BitVec 64)
    (mCopy : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x8000282c#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mCopy
  out : cfg.σ.sailOutput = out
  code : Vsa.Sim.Code.Exec_stmtLoaded mCopy
  truthy_loaded : Vsa.Sim.Code.Value_truthyLoaded mCopy
  header : TruthyHeaderRepr mCopy
    (esp + sign_extend (m := 64) (0x010#12)).toNat v
  region : TruthyRegion (esp + sign_extend (m := 64) (0x010#12))
  a0 : cfg.σ.regs.get? Register.x10 =
    some (esp + sign_extend (m := 64) (0x010#12))
  ra : cfg.σ.regs.get? Register.x1 = some 0x80004070#64
  sp : cfg.σ.regs.get? Register.x2 = some esp
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aEnv
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gCond R

/-- Execute the 24-byte condition-result copy and stop at the exact helper
entry.  Only `TruthyHeaderRepr` crosses the copy. -/
theorem execWhileCondCopyReady_of_exitKit
    (g : (R : Register) → Option (RegisterType R))
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfBody φcBody : Addr → Nat)
    (st stCond : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (v : Value) (sp r aInterp aStmt aEnv aRet aCond : BitVec 64)
    (m0 mCond : Mem) (aBody : BitVec 64) (cfg : Config)
    (hCarrier : ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond)
    (hKit : ExecWhileCondExitKit gCond N A SL φfBody φcBody stCond v cnd body
      sp aStmt aRet mCond aBody cfg) :
    ∃ (mCopy : Mem) (cfgCopy : Config),
      Vsa.Machine.Steps cfg cfgCopy ∧
      ExecWhileCondCopyReady gCond N φcBody v (sp - 176#64) aStmt
        aInterp aRet aEnv mCopy cfg.σ.sailOutput cfgCopy := by
  let esp : BitVec 64 := sp - 176#64
  let lds := execWhileCondCopyLds cfg.σ.mem esp
  let copyOut := evalBlocks execWhileCondCopySeg
    (SegEvalState.init (execWhileCondCopyL esp aStmt aInterp aRet aEnv) lds)
  let mCopy : Mem := writeLog cfg.σ.mem copyOut.log
  have hroom : 176 ≤
      (Stmt.whileStmt cnd body).stackNeed +
        (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088 := by
    have hneed := Stmt.stackNeed_ge (.whileStmt cnd body)
    simp only [Vsa.While.execFrame] at hneed
    omega
  have hgeom := execWhile_lowered_copy_geom hroom hCarrier.stack_budget
  obtain ⟨hespLo, hespHi, hespAlign⟩ := hgeom
  change SL.lo ≤ esp.toNat at hespLo
  change esp.toNat + 104 ≤ SL.hi at hespHi
  change esp.toNat % 16 = 0 at hespAlign
  obtain ⟨hstackLo, hstackHi⟩ := hCarrier.stack_ram
  have hespNat : esp.toNat = sp.toNat - 176 := by
    simp only [esp, BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]
    have hspLo := hCarrier.stack_budget.1
    omega
  have hsp176 : 176 ≤ sp.toNat := by
    have hspLo := hCarrier.stack_budget.1
    omega
  have hnowrap : esp.toNat + 104 ≤ 0x100000000 :=
    Nat.le_trans hespHi hstackHi
  have hcopyFrame : ∀ k,
      ¬ (esp.toNat + 16 ≤ k ∧ k < esp.toNat + 40) →
      mCopy[k]? = cfg.σ.mem[k]? := by
    intro k hk
    exact execWhileCondCopy_writeLog_frame cfg.σ.mem esp aStmt aInterp
      aRet aEnv hnowrap k hk
  have hcodeCopy : Vsa.Sim.Code.Exec_stmtLoaded mCopy := by
    apply loaded_exec_stmt_agree cfg.σ.mem mCopy _ hKit.code
    intro k hklo hkhi
    exact hcopyFrame k (by
      intro hd
      rcases hd with ⟨hdlo, hdhi⟩
      rcases hCarrier.code_stack_disjoint with hs | hs <;> omega)
  have hEvalAgree : ∀ k, EvalCallFootprint k →
      mCopy[k]? = cfg.σ.mem[k]? :=
    execWhileCondCopy_evalCall_agree hKit.ground.eval_call hespLo
      (by omega) hcopyFrame
  obtain ⟨_interp, _vint, htruthyLoaded, _intSlot, _nbs, _kind⟩ :=
    hKit.ground.eval_call.pins mCopy hEvalAgree
  have hHeaderCopy : TruthyHeaderRepr mCopy (esp.toNat + 16) v :=
    execWhileCondCopy_truthyHeader cfg.σ.mem esp aStmt aInterp aRet aEnv
      v hnowrap hKit.header
  have hL : GHolds cfg.σ (execWhileCondCopyL esp aStmt aInterp aRet aEnv) := by
    simp only [execWhileCondCopyL, GHolds, gprGet]
    exact ⟨(hKit.frame Register.x2 (by decide)).trans hCarrier.spReg,
      (hKit.frame Register.x8 (by decide)).trans hCarrier.s0,
      (hKit.frame Register.x9 (by decide)).trans hCarrier.s1,
      (hKit.frame Register.x18 (by decide)).trans hCarrier.s2,
      (hKit.frame Register.x19 (by decide)).trans hCarrier.s3,
      True.intro⟩
  have hfacts : ChainFacts cfg.σ.mem cfg.σ.mem
      (execWhileCondCopyL esp aStmt aInterp aRet aEnv) lds
      execWhileCondCopySeg :=
    execWhileCondCopy_facts_of_stack cfg.σ.mem SL esp aStmt aInterp aRet
      aEnv hKit.code hespLo hespHi ⟨hstackLo, hstackHi⟩
      hCarrier.stack_win hespAlign
  obtain ⟨vm, hmi⟩ := hKit.minstret
  obtain ⟨σCopy, iCopy, hsCopy, hiCopy, hgoodCopy, hpcCopy, hraCopy,
      hmiCopy, hregsCopy, hmemCopy, houtCopy, hframeCopy⟩ :=
    execWhileCondCopyCallBridge cfg.σ cfg.tick cfg.steps vm esp aStmt
      aInterp aRet aEnv cfg.σ.mem lds hKit.good hKit.pc hmi rfl hL hfacts
      hKit.tick
      (by
        change KeysOK (keysG copyOut.regs)
        have hk : keysG copyOut.regs =
            [10, 15, 14, 13, 2, 8, 9, 18, 19] := by rfl
        rw [hk]
        decide)
      (by
        change KeysAvoidRa copyOut.regs
        have hk : keysG copyOut.regs =
            [10, 15, 14, 13, 2, 8, 9, 18, 19] := by rfl
        unfold KeysAvoidRa
        rw [hk]
        decide)
      hcodeCopy
  let cfgCopy : Config :=
    ⟨σCopy, iCopy, cfg.steps + evalBlocksFuel execWhileCondCopySeg + 1⟩
  have hmemCopy' : σCopy.mem = mCopy := by
    simpa only [mCopy, copyOut, lds] using hmemCopy
  have hbufNat :
      (esp + sign_extend (m := 64) (0x010#12)).toNat = esp.toNat + 16 := by
    have hsext : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hsext, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbufRegion : TruthyRegion
      (esp + sign_extend (m := 64) (0x010#12)) := by
    refine
      { align := ?_
        lo := ?_
        hi := ?_
        win := ?_ }
    · rw [hbufNat]
      omega
    · rw [hbufNat]
      omega
    · rw [hbufNat]
      omega
    · rw [hbufNat]
      have hwin := hCarrier.stack_win
      omega
  have hx2Copy : σCopy.regs.get? Register.x2 = some esp :=
    (hframeCopy Register.x2 (by decide)).trans
      ((hKit.frame Register.x2 (by decide)).trans hCarrier.spReg)
  have hx8Copy : σCopy.regs.get? Register.x8 = some aStmt :=
    (hframeCopy Register.x8 (by decide)).trans
      ((hKit.frame Register.x8 (by decide)).trans hCarrier.s0)
  have hx9Copy : σCopy.regs.get? Register.x9 = some aInterp :=
    (hframeCopy Register.x9 (by decide)).trans
      ((hKit.frame Register.x9 (by decide)).trans hCarrier.s1)
  have hx18Copy : σCopy.regs.get? Register.x18 = some aRet :=
    (hframeCopy Register.x18 (by decide)).trans
      ((hKit.frame Register.x18 (by decide)).trans hCarrier.s2)
  have hx19Copy : σCopy.regs.get? Register.x19 = some aEnv :=
    (hframeCopy Register.x19 (by decide)).trans
      ((hKit.frame Register.x19 (by decide)).trans hCarrier.s3)
  have hx10Copy : σCopy.regs.get? Register.x10 =
      some (esp + sign_extend (m := 64) (0x010#12)) := by
    simpa only [gprGet] using
      (gholds_lookup (n := 10) _ hregsCopy (by rfl))
  refine ⟨mCopy, cfgCopy, hsCopy, ?_⟩
  refine
    { good := hgoodCopy
      tick := hiCopy
      pc := hpcCopy
      minstret := hmiCopy
      mem := hmemCopy'
      out := houtCopy
      code := hcodeCopy
      truthy_loaded := htruthyLoaded
      header := ?_
      region := hbufRegion
      a0 := hx10Copy
      ra := hraCopy
      sp := hx2Copy
      s0 := hx8Copy
      s1 := hx9Copy
      s2 := hx18Copy
      s3 := hx19Copy
      frame := ?_ }
  · rw [hbufNat]
    exact hHeaderCopy
  · intro R hR
    exact (hframeCopy R hR).trans
      (hKit.frame R (abiPreservedNoise_of_abi hR))

/-- Run the header-only truthiness helper from its exact parked state. -/
theorem execWhileTruthy_of_copyReady
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (esp aStmt aInterp aRet aEnv : BitVec 64)
    (mCopy : Mem) (out : Array String) (cfgCopy : Config)
    (hReady : ExecWhileCondCopyReady gCond N φc v esp aStmt aInterp
      aRet aEnv mCopy out cfgCopy)
    (htruthy : v.truthy = true) :
    ∃ cfgHead : Config,
      Vsa.Machine.Steps cfgCopy cfgHead ∧
      ExecWhileTruthyBodyHead gCond mCopy out cfgHead := by
  have hPre : ExecWhileTruthyHeaderPre
      (fun R => cfgCopy.σ.regs.get? R) N φc v
      (esp + sign_extend (m := 64) (0x010#12)) esp aStmt aInterp aRet aEnv
      mCopy out cfgCopy := by
    refine ⟨?_, hReady.code, htruthy, hReady.sp, hReady.s0, hReady.s1,
      hReady.s2, hReady.s3⟩
    refine ⟨hReady.good, ?_, hReady.mem, hReady.pc, hReady.a0, hReady.ra,
      hReady.minstret, hReady.tick, hReady.header, hReady.region, ?_,
      hReady.out, ?_⟩
    · exact hReady.mem.symm ▸ hReady.truthy_loaded
    · decide
    · intro R _hR
      rfl
  obtain ⟨cfgHead, hsHead, hroute, hframeHead, htickHead, hmiHead⟩ :=
    execWhileTruthyHeaderToBodyHead_framed
      (fun R => cfgCopy.σ.regs.get? R) N φc v
      (esp + sign_extend (m := 64) (0x010#12)) esp aStmt aInterp aRet aEnv
      mCopy out cfgCopy hPre
  rcases hroute with ⟨hgoodHead, hmemHead, houtHead, hpcHead, _hregsHead⟩
  have hmemHead' : cfgHead.σ.mem = mCopy := by
    simpa only [execWhileTruthyBranch_writeLog_eq] using hmemHead
  refine ⟨cfgHead, hsHead, ?_⟩
  exact
    { good := hgoodHead
      tick := htickHead
      pc := hpcHead
      minstret := hmiHead
      mem := hmemHead'
      out := houtHead
      frame := fun R hR => (hframeHead R hR).trans (hReady.frame R hR) }

/-- Execute the condition copy and truthiness helper, stopping at the exact
body-head PC. -/
theorem execWhileCondCopyTruthy_of_exitKit
    (g : (R : Register) → Option (RegisterType R))
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfBody φcBody : Addr → Nat)
    (st stCond : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (body : Stmt)
    (v : Value) (sp r aInterp aStmt aEnv aRet aCond : BitVec 64)
    (m0 mCond : Mem) (aBody : BitVec 64) (cfg : Config)
    (hCarrier : ExecWhileCondCarrier g N A SL φf φc st d env cnd body
      sp r aInterp aStmt aEnv aRet m0 gCond aCond mCond)
    (hKit : ExecWhileCondExitKit gCond N A SL φfBody φcBody stCond v cnd body
      sp aStmt aRet mCond aBody cfg)
    (htruthy : v.truthy = true) :
    ∃ (mCopy : Mem) (cfgHead : Config),
      Vsa.Machine.Steps cfg cfgHead ∧
      ExecWhileTruthyBodyHead gCond mCopy cfg.σ.sailOutput cfgHead := by
  obtain ⟨mCopy, cfgCopy, hsCopy, hReady⟩ :=
    execWhileCondCopyReady_of_exitKit g gCond N A SL φf φc φfBody φcBody
      st stCond d env cnd body v sp r aInterp aStmt aEnv aRet aCond m0
      mCond aBody cfg hCarrier hKit
  obtain ⟨cfgHead, hsHead, hHead⟩ :=
    execWhileTruthy_of_copyReady gCond N φcBody v (sp - 176#64) aStmt
      aInterp aRet aEnv mCopy cfg.σ.sailOutput cfgCopy hReady htruthy
  exact ⟨mCopy, cfgHead, hsCopy.trans hsHead, hHead⟩


end Vsa.Sim
