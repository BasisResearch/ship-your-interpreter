import Vsa.Sim.rows.ScaffoldRows
import Vsa.Sim.rows.StmtForInitArmStagePre
import Vsa.Sim.rows.StmtForLoopSegPreB
import Vsa.Sim.ExecBlock
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.BlockTactics2

/-!
# Concrete `ExecInit.some` prefix

The initializer prefix loads the present statement pointer and enters the
`exec_stmt` child through the reflected `0x80004248..0x80004254` call span.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

/-! The present-initializer discriminator.  Its fallthrough is the already
reflected `stmtForInitBodySeg` at `0x80004248`. -/
#derive_case initSomeDispatchSeg chain
  [(0x8000423c#64, 0x00843583#32),
   (0x80004240#64, 0x00050993#32)]
    terminator ⟨0x80004244#64, 0x02058463#32,
      0x63#8, 0x84#8, 0x05#8, 0x02#8,
      .br bop.BEQ false, 11, 0, 0x0028#13, 0#21, 0#12⟩

def initSomeDispatchL (aStmt aOuter : BitVec 64) : GRegs :=
  [(8, aStmt), (10, aOuter)]

/-- Selected bytes and semantic child attached to the present-initializer load. -/
structure InitSomeDispatchWitness
    (ment : Mem) (aStmt aOuter : BitVec 64) (s : Stmt) : Type where
  p : BitVec 64
  bs : List (BitVec 8)
  nonzero : p ≠ 0
  value : bytesVal .ld bs = p
  init_ptr : read64 ment (aStmt.toNat + 8) = some p.toNat
  child : StmtRepr ment p.toNat s
  facts : ChainFacts ment ment (initSomeDispatchL aStmt aOuter) [bs]
    initSomeDispatchSeg

/-- A saved machine word paired with its entry-register value. -/
def SavedRegWord (ment : Mem) (addr : Nat) (regValue : Option (BitVec 64)) : Prop :=
  ∃ v : BitVec 64, read64 ment addr = some v.toNat ∧ regValue = some v

/-- A register has a selected value in this machine state. -/
def RegDefined (cfg : Config) (R : Register) : Prop :=
  ∃ v, cfg.σ.regs.get? R = some v

private theorem initSomeDispatch_guard
    (aStmt aOuter p : BitVec 64) (bs : List (BitVec 8))
    (hp : bytesVal .ld bs = p) (hne : p ≠ 0) :
    guardB bop.BEQ
      (srcVal 11 (runGM
        [mkLine 0x8000423c#64 0x00843583#32, mkLine 0x80004240#64 0x00050993#32]
        (initSomeDispatchL aStmt aOuter) [bs]))
      (srcVal 0 (runGM
        [mkLine 0x8000423c#64 0x00843583#32, mkLine 0x80004240#64 0x00050993#32]
        (initSomeDispatchL aStmt aOuter) [bs])) = false := by
  have hne' : ¬ p = 0#64 := hne
  simp [initSomeDispatchL, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    guardB,
    show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl,
    show (mkLine 0x8000423c#64 0x00843583#32).rd = 11 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).kind = MKind.addi from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).rd = 19 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).rs1 = 10 from rfl,
    show (mkLine 0x80004240#64 0x00050993#32).imm = 0 from rfl,
    hp, hne']

/-- The typed ready state supplies the exact bytes and non-null guard needed
by the reflected present-initializer discriminator. -/
theorem initSomeDispatch_facts
    {ment : Mem} {SL : StackLayout} {A : Arena} {aRet : Nat}
    {aStmt aOuter : BitVec 64} {s : Stmt} {cnd step : Option Expr} {body : Stmt}
    (hast : StmtRegionPins ment SL A aRet aStmt.toNat
      (.forStmt (some s) cnd step body))
    (hcode : Exec_stmtLoaded ment)
    (hstmt : StmtRepr ment aStmt.toNat (.forStmt (some s) cnd step body)) :
    Nonempty (InitSomeDispatchWitness ment aStmt aOuter s) := by
  cases hstmt with
  | forS _ hinit _ _ _ _ =>
    cases hinit with
    | @some _ q _ hread hpne hs =>
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
        hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hbytes⟩ :=
          Vsa.Sim.read64_bytes ment (aStmt.toNat + 8) _ hread
      let p : BitVec 64 := BitVec.ofNat 64 q
      let bs : List (BitVec 8) := [b0, b1, b2, b3, b4, b5, b6, b7]
      have hpNat : p.toNat = q := by
        simp only [p, BitVec.toNat_ofNat]
        have hpRam : q < 2 ^ 64 := by
          have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt
          have h3 := b3.isLt; have h4 := b4.isLt; have h5 := b5.isLt
          have h6 := b6.isLt; have h7 := b7.isLt
          omega
        omega
      refine ⟨⟨p, bs, ?_, ?_, ?_, hpNat.symm ▸ hs, ?_⟩⟩
      · intro hz
        apply hpne
        have hzNat := congrArg BitVec.toNat hz
        rw [hpNat] at hzNat
        simpa using hzNat
      · apply BitVec.eq_of_toNat_eq
        rw [hpNat]
        show (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) :
            BitVec (8 * 8))).toNat = q
        rw [sext_full, word8_toNat_recon, hbytes]
      · simpa only [hpNat] using hread
      · chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
        · obtain ⟨lo, hi, hr⟩ := hast.region
          have hn := hr.nodes.1
          have hlo := hn.lo_le
          have hhi := hn.hi_ge
          have hloRam := hr.lo_ram
          have hhiRam := hr.hi_ram
          have hwin := hr.win
          have hea :
              (eaddrM (mkLine 0x8000423c#64 0x00843583#32)
                (initSomeDispatchL aStmt aOuter)).toNat = aStmt.toNat + 8 := by
            unfold eaddrM
            simp only [initSomeDispatchL, srcVal, lookupG,
              show (mkLine 0x8000423c#64 0x00843583#32).rs1 = 8 from rfl,
              show (mkLine 0x8000423c#64 0x00843583#32).imm = 0x008#12 from rfl,
              if_true, Option.getD_some]
            rw [BitVec.toNat_add]
            have himm : (sign_extend (m := 64) (0x008#12)).toNat = 8 := by decide
            rw [himm, Nat.mod_eq_of_lt (by omega)]
          unfold MemFacts
          rw [show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl, hea]
          change
            (0x80000000 ≤ aStmt.toNat + 8 ∧ aStmt.toNat + 8 + 8 ≤ 0x100000000 ∧
              (aStmt.toNat + 8 + 8 ≤ tohostAddr ∨
                tohostAddr + 8 ≤ aStmt.toNat + 8)) ∧
            LPins8 ment (aStmt.toNat + 8) bs
          refine ⟨⟨by omega, by omega, Or.inr (by omega)⟩, ?_⟩
          exact ⟨lpin_of_present hb0, lpin_of_present hb1,
            lpin_of_present hb2, lpin_of_present hb3,
            lpin_of_present hb4, lpin_of_present hb5,
            lpin_of_present hb6, lpin_of_present hb7⟩
        · apply initSomeDispatch_guard aStmt aOuter p bs
          · apply BitVec.eq_of_toNat_eq
            rw [hpNat]
            show (sign_extend (m := 64)
              ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) :
                BitVec (8 * 8))).toNat = q
            rw [sext_full, word8_toNat_recon, hbytes]
          · intro hz
            apply hpne
            have hzNat := congrArg BitVec.toNat hz
            rw [hpNat] at hzNat
            simpa using hzNat

/-- Ready-state specialization of `initSomeDispatch_facts`. -/
theorem initSomeDispatch_facts_of_ready
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : SpecSt} {d outer : Nat} {s : Stmt} {cnd step : Option Expr} {body : Stmt}
    {sp r aInterp aStmt aOuter aRet : BitVec 64} {m0 ment : Mem}
    {cfg : Config} {liveRA : BitVec 64}
    (h : ExecInitReady g N A SL φf φc st d outer (some s) cnd step body
      sp r aInterp aStmt aOuter aRet m0 ment cfg (liveRA := liveRA)) :
    Nonempty (InitSomeDispatchWitness ment aStmt aOuter s) :=
  initSomeDispatch_facts h.ground.ast h.code h.stmt

/-- State at the first initializer-argument setup instruction. -/
structure InitSomeStage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr) (s : Stmt)
    (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) (liveRA p : BitVec 64) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (0x80004248#64)
  s0 : cfg.σ.regs.get? Register.x8 = some aStmt
  s1 : cfg.σ.regs.get? Register.x9 = some aInterp
  s2 : cfg.σ.regs.get? Register.x18 = some aRet
  s3 : cfg.σ.regs.get? Register.x19 = some aOuter
  a0 : cfg.σ.regs.get? Register.x10 = some aOuter
  a1 : cfg.σ.regs.get? Register.x11 = some p
  spReg : cfg.σ.regs.get? Register.x2 = some (sp - 176#64)
  ra : cfg.σ.regs.get? Register.x1 = some liveRA
  mem : cfg.σ.mem = ment
  code : Exec_stmtLoaded ment
  stmt : StmtRepr ment aStmt.toNat (.forStmt (some s) cnd step body)
  child : StmtRepr ment p.toNat s
  init_ptr : read64 ment (aStmt.toNat + 8) = some p.toNat
  outer_addr : φf outer = aOuter.toNat
  store : StoreRepr ment N A φf φc st.store
  env_valid : EnvValid st outer
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  code_stack_disjoint : sp.toNat ≤ execStmtEntry ∨ execStmtEnd ≤ SL.lo
  out : OutRepr cfg.σ st
  saved_ra : read64 ment (sp.toNat - 8) = some r.toNat
  saved_s0 : SavedRegWord ment (sp.toNat - 16) (g Register.x8)
  saved_s1 : SavedRegWord ment (sp.toNat - 24) (g Register.x9)
  saved_s2 : SavedRegWord ment (sp.toNat - 32) (g Register.x18)
  saved_s3 : SavedRegWord ment (sp.toNat - 40) (g Register.x19)
  x20_defined : RegDefined cfg Register.x20
  x21_defined : RegDefined cfg Register.x21
  stack_budget : StackOK SL sp
    ((Stmt.forStmt (some s) cnd step body).stackNeed +
      (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  stmt_bodies : Stmt.bodiesBound Vsa.While.perCallBudget
    (.forStmt (some s) cnd step body) = true
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  ground : ExecGround ment SL A sp aRet aStmt.toNat (.forStmt (some s) cnd step body)
  mem_frame : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
    ¬ (A.lo ≤ a ∧ a < A.hi) →
    (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ ment[a]? = m0[a]?
  frame : ∀ R, AbiPreservedNoise R →
    (R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
      R = Register.x19 ∨ R = Register.x2) ∨ cfg.σ.regs.get? R = g R
  minstret : ∃ v, cfg.σ.regs.get? Register.minstret = some v

/-- Execute the present-initializer discriminator to its fallthrough. -/
theorem initSome_to_stage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr) (s : Stmt)
    (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem) :
    Triple
      (fun cfg => ∃ liveRA, ExecInitReady g N A SL φf φc st d outer
        (some s) cnd step body sp r aInterp aStmt aOuter aRet m0 ment cfg
          (liveRA := liveRA))
      (fun cfg => ∃ liveRA p, InitSomeStage g N A SL φf φc st d outer s cnd step body
        sp r aInterp aStmt aOuter aRet m0 ment cfg liveRA p) := by
  intro cfg hpre
  obtain ⟨liveRA, h⟩ := hpre
  obtain ⟨w⟩ := initSomeDispatch_facts_of_ready h
  rcases w with ⟨p, bs, hpne, hp, hinitPtr, hchild, hfacts⟩
  obtain ⟨σ', i', hs, hi', hgood, hmem, hout, hpc, hmi', hregs, hframe⟩ :=
    initSomeDispatchSeg_seg cfg.σ cfg.tick cfg.steps 0x8000423c#64
      (Classical.choose h.minstret) (initSomeDispatchL aStmt aOuter) [bs]
      h.good h.pc (Classical.choose_spec h.minstret)
      ⟨h.s0, h.a0, trivial⟩ (by show KeysOK [8, 10]; decide)
      (by simpa only [h.mem] using hfacts)
      (by show ChainOK 0x8000423c#64 [8, 10] initSomeDispatchSeg; decide) h.tick
  let cfg' : Config := ⟨σ', i', cfg.steps + evalBlocksFuel initSomeDispatchSeg⟩
  have hmem' : σ'.mem = ment := by
    rw [h.mem] at hmem
    simpa only [initSomeDispatchSeg, writeLog, evalBlocks, evalBlock] using hmem
  have hs3' : σ'.regs.get? Register.x19 = some aOuter := by
    simp only [initSomeDispatchSeg, initSomeDispatchL, evalBlocks, evalBlock,
      runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
      show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl,
      show (mkLine 0x8000423c#64 0x00843583#32).rd = 11 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).rd = 19 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).rs1 = 10 from rfl,
      show (mkLine 0x80004240#64 0x00050993#32).imm = 0 from rfl] at hregs
    simpa [SegEvalState.init, eraseG, lookupG,
      show sign_extend (m := 64) (0#12) = 0#64 by decide] using hregs.1
  have ha1' : σ'.regs.get? Register.x11 = some p := by
    simp only [initSomeDispatchSeg, initSomeDispatchL, evalBlocks, evalBlock,
      runGM, stepGM, wvalM, srcVal, lookupG, eraseG] at hregs
    simpa [SegEvalState.init, eraseG, lookupG, hp,
      show (mkLine 0x8000423c#64 0x00843583#32).kind = MKind.ld from rfl,
      show (mkLine 0x8000423c#64 0x00843583#32).rd = 11 from rfl] using hregs.2.1
  refine ⟨cfg', hs, liveRA, p, ?_⟩
  refine ⟨hgood, hi', hpc, ?_, ?_, ?_, hs3', ?_, ha1', ?_, ?_, hmem',
    ?_, ?_, ?_, hinitPtr, h.outer_addr, ?_, h.env_valid, h.store_survives,
    h.stack_ram, h.stack_win, h.code_stack_disjoint, ?_, h.saved_ra,
    h.saved_s0, h.saved_s1, h.saved_s2, h.saved_s3, ?_, ?_, h.stack_budget,
    h.stmt_bodies, h.store_bodies, h.ground, h.mem_frame, ?_, hmi'⟩
  · exact (hframe Register.x8 (by decide) (by decide)).trans h.s0
  · exact (hframe Register.x9 (by decide) (by decide)).trans h.s1
  · exact (hframe Register.x18 (by decide) (by decide)).trans h.s2
  · exact (hframe Register.x10 (by decide) (by decide)).trans h.a0
  · exact (hframe Register.x2 (by decide) (by decide)).trans h.spReg
  · exact (hframe Register.x1 (by decide) (by decide)).trans h.ra
  · exact h.code
  · exact h.stmt
  · exact hchild
  · exact h.store
  · change Machine.output σ' = st.out
    change String.join σ'.sailOutput.toList = st.out
    rw [hout]
    exact h.out
  · obtain ⟨v, hv⟩ := h.x20_defined
    exact ⟨v, (hframe Register.x20 (by decide) (by decide)).trans hv⟩
  · obtain ⟨v, hv⟩ := h.x21_defined
    exact ⟨v, (hframe Register.x21 (by decide) (by decide)).trans hv⟩
  · intro R hR
    by_cases hs : R = Register.x8 ∨ R = Register.x9 ∨ R = Register.x18 ∨
        R = Register.x19 ∨ R = Register.x2
    · exact Or.inl hs
    · right
      rcases h.frame R hR with hsp | hold
      · exact False.elim (hs hsp)
      · rw [hframe R (abiNoise_noiseRegs hR) (by
          intro n hn
          change n ∈ [11, 19] at hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl
          · simpa [gprReg] using (show Register.x11 ≠ R by
              intro heq; subst R; exact Bool.noConfusion hR.1)
          · simpa [gprReg] using (show Register.x19 ≠ R by
              intro heq; exact hs (Or.inr (Or.inr (Or.inr (Or.inl heq.symm))))))]
        exact hold

/-- Selected landing of the reflected initializer setup and `jal exec_stmt`.
The originating stage is retained for the later child-entry marshaller. -/
structure InitSomeBodyLanding
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr) (s : Stmt)
    (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) : Type where
  origin : Config
  liveRA : BitVec 64
  p : BitVec 64
  stage : InitSomeStage g N A SL φf φc st d outer s cnd step body
    sp r aInterp aStmt aOuter aRet m0 ment origin liveRA p
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some (0x80003fe0#64)
  ra : cfg.σ.regs.get? Register.x1 = some (0x80004258#64)
  minstret : RegDefined cfg Register.minstret
  regs : GHolds cfg.σ
    (evalBlocks stmtForInitBodySeg
      (SegEvalState.init
        (stmtForInitBodyL (sp - 176#64) aOuter aRet aInterp p) [])).regs
  mem : cfg.σ.mem = ment
  out : OutRepr cfg.σ st
  frame : ∀ R, AbiPreserved R = true →
    cfg.σ.regs.get? R = origin.σ.regs.get? R

/-- Proposition wrapper selecting a concrete initializer-body landing. -/
def InitSomeBodyPost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr) (s : Stmt)
    (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem)
    (cfg : Config) : Prop :=
  Nonempty (InitSomeBodyLanding g N A SL φf φc st d outer s cnd step body
    sp r aInterp aStmt aOuter aRet m0 ment cfg)

/-- Reflected `0x80004248..0x80004250` setup plus the certified
`jal exec_stmt @ 0x80004254`. -/
theorem initSome_stage_to_bodyPost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (outer : Addr) (s : Stmt)
    (cnd step : Option Expr) (body : Stmt)
    (sp r aInterp aStmt aOuter aRet : BitVec 64) (m0 ment : Mem) :
    Triple
      (fun cfg => ∃ liveRA p, InitSomeStage g N A SL φf φc st d outer s cnd step body
        sp r aInterp aStmt aOuter aRet m0 ment cfg liveRA p)
      (InitSomeBodyPost g N A SL φf φc st d outer s cnd step body
        sp r aInterp aStmt aOuter aRet m0 ment) := by
  intro cfg hpre
  obtain ⟨liveRA, p, h⟩ := hpre
  let L := stmtForInitBodyL (sp - 176#64) aOuter aRet aInterp p
  have hfacts : ChainFacts ment ment L [] stmtForInitBodySeg := by
    chain_facts h.code with "Vsa.Sim.Code.exec_stmt_at_"
  obtain ⟨vmi, hmi⟩ := h.minstret
  obtain ⟨σ2, i2, hs, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hout2,
      hframe2⟩ :=
    bridgeOfSegOut stmtForInitBodySeg L [] cfg.σ cfg.tick cfg.steps
      0x80004248#64 0x80003fe0#64 0x80004258#64 vmi ment
      h.good h.pc hmi h.mem
      (by exact ⟨h.spReg, h.a0, h.s2, h.s1, h.a1, trivial⟩)
      (by change KeysOK [2, 10, 18, 9, 11]; decide)
      (by rw [h.mem]; simpa only [L] using hfacts) h.tick
      (by change ChainOK 0x80004248#64 [2, 10, 18, 9, 11] stmtForInitBodySeg
          decide)
      (by show WrChainAvoidAbi stmtForInitBodySeg; decide)
      (by
        change KeysOK [10, 13, 12, 2, 18, 9, 11]
        decide)
      (by
        change KeysAvoidRa (evalBlocks stmtForInitBodySeg
          (SegEvalState.init L [])).regs
        unfold KeysAvoidRa
        change ∀ n ∈ [10, 13, 12, 2, 18, 9, 11], n ≠ 1
        decide)
      (by
        intro σ' i' u' hG' hi' hpc' hmi' hmem' hregs'
        obtain ⟨vm', hmi'v⟩ := hmi'
        have hpc'' : σ'.regs.get? Register.PC = some (0x80004254#64) := by
          simpa only [stmtForInitBodySeg, L, evalBlocksPC, evalBlocks,
            evalBlock, SegEvalState.init, runGM, stepGM] using hpc'
        have hcode' : Exec_stmtLoaded σ'.mem := by
          rw [hmem']
          simpa only [stmtForInitBodySeg, writeLog, evalBlocks, evalBlock] using h.code
        obtain ⟨hb0, hb1, hb2, hb3⟩ := exec_stmt_at_80004254 hcode'
        obtain ⟨σj, ij, hstepj, hij, hGj, hmemj, hobsj⟩ :=
          stepObs_jal σ' i' u' (0x80004254#64) vm' (0xd8dff0ef#32) (0x1ffd8c#21)
            (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80004254#64) 4)
            (0xef#8) (0xf0#8) (0xdf#8) (0xd8#8)
            hG' hpc'' hmi'v hb0 hb1 hb2 hb3
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (Vsa.Sim.DecodeTable.decode_d8dff0ef (afterPrelude σ')
              (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.misa)
              (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.cur_privilege)
              (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.mseccfg))
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (wX_bits_x1 _ (BitVec.addInt (0x80004254#64) 4)) hi'
        have hlink : BitVec.addInt (0x80004254#64) 4 = (0x80004258#64) := by
          apply BitVec.eq_of_toNat_eq
          decide
        rw [hlink] at hobsj
        exact jalStepO_of_obs hstepj hij hGj hmemj hobsj
          (by apply BitVec.eq_of_toNat_eq; decide))
  let cfg2 : Config := ⟨σ2, i2, cfg.steps + evalBlocksFuel stmtForInitBodySeg + 1⟩
  refine ⟨cfg2, hs, ⟨⟨cfg, liveRA, p, h, hG2, hi2, hpc2, hra2, hmi2, hregs2, ?_, ?_,
    hframe2⟩⟩⟩
  · simpa only [stmtForInitBodySeg, writeLog, evalBlocks, evalBlock] using hmem2
  · change String.join σ2.sailOutput.toList = st.out
    rw [hout2]
    exact h.out

#print axioms initSomeDispatch_facts
#print axioms initSome_to_stage
#print axioms initSome_stage_to_bodyPost

end Vsa.Sim.ScaffoldRows
