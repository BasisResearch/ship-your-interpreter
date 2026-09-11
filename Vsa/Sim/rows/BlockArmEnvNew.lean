import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.HelperCallSites
import Vsa.Sim.SeqSuffixGroundBlock
import Vsa.Sim.ExecNormalExitTail
import Vsa.Sim.rows.ExecDispatchRows

/-!
# `BlockArmEnvNew` — the block arm on the layer

`{ ss }` (`0x8000418c`: `mv a0,s3; jal env_new`, return `0x80004194`:
`lw a5,16(s0); mv s3,a0; li a6,0; blez a5`) allocates the block scope and
lands in the indexed sequence entry `ExecSeqEntryI .blockBody` at the loop
head `0x800041a4` (nonempty) or, through `li a0,0; j 0x8000409c`, at the
shared epilogue entry (empty).  `blockArm_run` closes `BlockIndexedGeom.hArm`
from the `env_new` contract and retains the parent frame as
`Rows.BlockArmFrame`; `blockEpilogue_run` closes `hEpi` from that frame and the
sequence exit `ExecSeqExitI .blockBody` (whose block window
`ExecSeqStackFrame .blockBody` keeps `[esp+136, SL.hi)` outside the retslot
and the arena) through the shared epilogue `epilogueTail`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

#derive_case blockEnvNewSeg chain
  [(0x8000418c#64, 0x00098513#32)]  -- discipline: allow(R12-helper-call-arm) the HelperCall instance's own prefix

/-- The scope allocation of the block arm. -/
def blockEnvNewCall : HelperCall :=
  { headPC := 0x8000418c#64
    seg := blockEnvNewSeg
    jalPC := 0x80004190#64
    jalImm := 0x1fe86c#21
    entry := 0x800029fc#64 }

theorem blockEnvNewCall_cert : blockEnvNewCall.Cert where
  ret_align := by decide
  ret_clean := by decide
  jal_tgt := by decide
  avoid_abi := by change WrChainAvoidAbi blockEnvNewSeg; decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004190_hc σ i u _ vmi hG hpc hmi hmem rfl hi

theorem blockEnvNew_facts (m : Mem) (esp aStmt aInterp aRet aEnv : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv) [] blockEnvNewSeg := by
  unfold blockEnvNewSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"

/-! ## The continuation after `env_new`: count read, scope set, loop head -/

-- Nonempty block: `blez a5` falls through to the loop head.
#derive_case blockLoopHeadSeg chain
  [(0x80004194#64, 0x01042783#32),
   (0x80004198#64, 0x00050993#32),
   (0x8000419c#64, 0x00000813#32)]
    terminator ⟨0x800041a0#64, 0xeef058e3#32, 0xe3#8, 0x58#8, 0xf0#8, 0xee#8,
      .br bop.BGE false, 0, 15, 0x1ef0#13, 0#21, 0#12⟩

-- Empty block: `blez a5` is taken into `li a0,0; j 0x8000409c`.
#derive_case blockEmptySeg chain
  [(0x80004194#64, 0x01042783#32),
   (0x80004198#64, 0x00050993#32),
   (0x8000419c#64, 0x00000813#32)]
    terminator ⟨0x800041a0#64, 0xeef058e3#32, 0xe3#8, 0x58#8, 0xf0#8, 0xee#8,
      .br bop.BGE true, 0, 15, 0x1ef0#13, 0#21, 0#12⟩
  ;;
  [(0x80004090#64, 0x00000513#32)]
    terminator ⟨0x80004094#64, 0x0080006f#32, 0x6f#8, 0x00#8, 0x80#8, 0x00#8,
      .j, 0, 0, 0#13, 0x000008#21, 0#12⟩

/-- The one load of the continuation: the statement count. -/
def blockLds (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [wordLds4 m (aStmt.toNat + 16)]

/-- The registers the continuation keeps: the ABI set without `s3`. -/
def keepS3 (R : Register) : Bool := AbiPreserved R && !(Register.x19 == R)

theorem keepS3_noise : ∀ rr ∈ noiseRegs, keepS3 rr = false := by decide

theorem keepS3_abi : ∀ R, keepS3 R = true → AbiPreserved R = true :=
  fun R h => ((Bool.and_eq_true _ _).mp h).1

theorem blockLoopHead_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64} {ss : List Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.block ss))
    (hcode : Exec_stmtLoaded m)
    (hcount : read32 m (aStmt.toNat + 16) = some ss.length)
    (hlt : ss.length < 2 ^ 31) (hne : 0 < ss.length)
    (a0 esp ra s1 s2 s3 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL a0 esp ra aStmt s1 s2 s3) (blockLds m aStmt)
      blockLoopHeadSeg := by
  have hval := bytesVal_lw_wordLds4 m (aStmt.toNat + 16) ss.length hlt hcount
  unfold blockLoopHeadSeg blockLds ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact hg.node_lw_facts (0x010#12) 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change guardB bop.BGE (0#64) (bytesVal MKind.lw (wordLds4 m (aStmt.toNat + 16))) = false
    rw [hval]
    exact blez_guard_pos _ hne (by omega)

theorem blockEmpty_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.block []))
    (hcode : Exec_stmtLoaded m)
    (hcount : read32 m (aStmt.toNat + 16) = some 0)
    (a0 esp ra s1 s2 s3 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL a0 esp ra aStmt s1 s2 s3) (blockLds m aStmt)
      blockEmptySeg := by
  have hval := bytesVal_lw_wordLds4 m (aStmt.toNat + 16) 0 (by decide) hcount
  unfold blockEmptySeg blockLds ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · exact hg.node_lw_facts (0x010#12) 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  · change guardB bop.BGE (0#64) (bytesVal MKind.lw (wordLds4 m (aStmt.toNat + 16))) = true
    rw [hval]
    exact blez_guard_zero

/-! ## The arm -/

/-- The block continuation retains its complete suffix and caller frame. -/
structure BlockArmResumePost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC resultF : Addr → Nat)
    (st : Vsa.While.St) (d env : Nat) (ss : List Stmt)
    (sp r aStmt aRet : BitVec 64) (base : Nat) (m0 mReturn : Mem)
    (arm after : Config) : Prop where
  entry : ExecSeqEntryI .blockBody after.σ.regs.get? N A SL resultF phiC
    ⟨(st.store.allocFrame (some env)).1, st.out⟩ d st.store.frames.size ss
    (sp - 176#64) aRet after.σ.mem after
  parent : Rows.BlockArmFrame g after.σ.regs.get? A SL phiF phiC resultF phiC st
    (st.store.allocFrame (some env)).1 sp r aRet m0 after.σ.mem
  memory : after.σ.mem = mReturn
  kept : ∀ R, keepS3 R = true → after.σ.regs.get? R = arm.σ.regs.get? R
  ground : ExecGround after.σ.mem SL A sp aRet aStmt.toNat (.block ss)
  baseRead : read64 after.σ.mem (aStmt.toNat + 8) = some base
  countRead : read32 after.σ.mem (aStmt.toNat + 16) = some ss.length
  suffix : SeqSuffixGround after.σ.mem SL A (sp - 176#64) aRet d base ss

/-- Reuse the existing block routes after an actual env_new return. -/
theorem blockArm_resume
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' : Addr → Nat}
    {st : Vsa.While.St} {d : Nat} {env : Addr} {ss : List Stmt}
    {sp r aInterp aStmt aEnv aRet p : BitVec 64} {m0 ment : Mem} {cA cR : Config}
    (hA : ArmState execArmBlock (.block ss) g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 ment cA)
    (hRet : blockEnvNewCall.Return cA.σ.regs.get? p (sp - 176#64) aStmt aInterp aRet aEnv
      ment cR.σ.mem
      (fun k => (A.lo ≤ k ∧ k < A.hi) ∨ (SL.lo ≤ k ∧ k < (sp - 176#64).toNat))
      cA.σ.sailOutput cR)
    (hFresh : EnvNewFresh N A SL φf φc st env p φf' cR.σ.mem) :
    ∃ cfgR base, Steps cR cfgR ∧
      BlockArmResumePost g N A SL φf φc φf' st d env ss sp r aStmt aRet base m0 cR.σ.mem cA cfgR := by
  have F := hA.frameFacts
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hsext : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have hAlloc : st.store.allocFrame (some env) =
      ((st.store.allocFrame (some env)).1, st.store.frames.size) := rfl
  -- the memory after the callee
  have hframeP : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cR.σ.mem[a]? = ment[a]? := by
    intro a hstk hA'
    right
    exact hRet.mem_frame a (fun h => h.elim hA' (fun hs => hstk ⟨hs.1, by rw [hesp] at hs; omega⟩))
  have hpop : StackBytesPresent cR.σ.mem SL := by
    intro k hlo hhi
    obtain ⟨b, hb⟩ := hA.ground.stack_bytes k hlo hhi
    exact hRet.mem_extends k b hb
  have hcode : Exec_stmtLoaded cR.σ.mem := by
    have hcs := hA.code_stack_disjoint
    have hac := hA.ground.arena_code
    simp only [execStmtEntry, execStmtEnd] at hcs hac
    apply loaded_exec_stmt_agreeP ment cR.σ.mem _ hA.code
    intro a ha
    rcases hframeP a (by intro hs; rcases hcs with hd | hd <;> omega)
        (by intro hA'; rcases hac with hd | hd <;> omega) with hr | heq
    · exfalso
      have hret := hA.ground.aret.inSL
      have hwin := hA.stack_win
      rw [tohostAddr_val] at hwin
      omega
    · exact heq.symm
  have hstmtR : StmtRepr cR.σ.mem aStmt.toNat (.block ss) :=
    hA.ground.stmtRepr_execExit hA.stmt hSLhi hframeP
  have hgroundR : ExecGround cR.σ.mem SL A sp aRet aStmt.toNat (.block ss) :=
    hA.ground.transport_execExit hSLhi hpop hframeP
  obtain ⟨base, hbase, hcount, hlt, hsuffix, _⟩ :=
    ExecGround.blockSuffix hgroundR hstmtR hA.stack_budget hA.stmt_bodies
  have hpNat : (BitVec.ofNat 64 (φf' st.store.frames.size)) = p := by
    rw [hFresh.addr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.isLt]
  have hretPC : blockEnvNewCall.retPC = 0x80004194#64 := by decide
  have hbaseLt : base < 2 ^ 64 := read64_lt_eg4 cR.σ.mem (aStmt.toNat + 8) base hbase
  have hbaseBV : (BitVec.ofNat 64 base).toNat = base := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbaseLt]
  -- the parent's saved registers survive `env_new`
  have hagS : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) ment cR.σ.mem := by
    intro k hk
    have hAS := hA.ground.arena_stack
    exact (hRet.mem_frame k (fun h => by
      rcases h with h | h
      · omega
      · rw [hesp] at h; omega)).symm
  have hrdS : ∀ off, 8 ≤ off → off ≤ 40 →
      read64 cR.σ.mem (sp.toNat - off) = read64 ment (sp.toNat - off) :=
    fun off h1 h2 => (read64_agreeP hagS (fun k hk => ⟨by omega, by omega⟩)).symm
  have hRetExt : MemExtends ment cR.σ.mem := hRet.mem_extends
  have mkFrame : ∀ cfgR : Config, cfgR.σ.mem = cR.σ.mem →
      (∀ R, keepS3 R = true → cfgR.σ.regs.get? R = cA.σ.regs.get? R) →
      cfgR.σ.regs.get? Register.x2 = some (sp - 176#64) →
      Rows.BlockArmFrame g (fun R => cfgR.σ.regs.get? R) A SL φf φc φf' φc st
        (st.store.allocFrame (some env)).1 sp r aRet m0 cfgR.σ.mem := by
    intro cfgR hmR hkeep h2
    have hsz := allocFrame_size st.store (some env)
    exact
      { frames := hFresh.map_extends
        closures := PhiExtends.refl _ _
        frames_le := by rw [hsz.1]; exact Nat.le_succ _
        closures_le := by rw [hsz.2]; exact Nat.le_refl _
        code := by rw [hmR]; exact hcode
        saved_ra := by rw [hmR, hrdS 8 (by omega) (by omega)]; exact hA.saved_ra
        saved_s0 := by rw [hmR, hrdS 16 (by omega) (by omega)]; exact hA.saved_s0
        saved_s1 := by rw [hmR, hrdS 24 (by omega) (by omega)]; exact hA.saved_s1
        saved_s2 := by rw [hmR, hrdS 32 (by omega) (by omega)]; exact hA.saved_s2
        saved_s3 := by rw [hmR, hrdS 40 (by omega) (by omega)]; exact hA.saved_s3
        parentSp := hA.parentSp
        seqSp := h2
        seqFrame := fun R hR he8 he9 he18 he19 he2 =>
          (hkeep R (by simp [keepS3, hR.1, he19])).trans
            (hA.frame R hR he8 he9 he18 he19 he2)
        memExtends := by rw [hmR]; exact hA.mem_extends.trans hRetExt
        memFrame := fun a hs hA' => by
          rw [hmR]
          exact (hframeP a hs hA').imp_right (fun h => h.trans (hA.mem_frame a hs))
        spRoom := h176
        spHi := by have := hA.stack_ram.2; omega
        spLo := by have := hA.stack_ram.1; omega
        spWin := by have := hA.stack_win; omega
        spAlign := by omega
        retAlign := hA.ra_align
        stackLo := hSLlo
        stackHi := hSLhi
        stackWin := hA.stack_win
        arenaStack := hA.ground.arena_stack
        arenaCode := hA.ground.arena_code
        retAbove := by
          have h1 := hA.ground.aret.scribble_disjoint
          have h2 := hA.ground.aret.inSL
          omega }
  cases ss with
  | nil =>
    -- the empty block: through `li a0,0; j` to the shared epilogue entry
    obtain ⟨cfgR, hsRoute, hHead⟩ := routeK_of_ready keepS3 keepS3_noise keepS3_abi
      blockEmptySeg 0x8000409c#64 (blockLds cR.σ.mem aStmt) hRet.ready
      (by change ChainOK blockEnvNewCall.retPC [10, 2, 1, 8, 9, 18, 19] blockEmptySeg; decide)
      rfl
      (by change WrChainAvoids keepS3 blockEmptySeg; decide)
      (blockEmpty_facts hgroundR hcode (by simpa using hcount) _ _ _ _ _ _)
    have hmR : cfgR.σ.mem = cR.σ.mem := by rw [hHead.mem]; rfl
    have h2 : cfgR.σ.regs.get? Register.x2 = some (sp - 176#64) := by
      simpa only [gprGet] using gholds_lookup (n := 2) _ hHead.regs rfl
    refine ⟨cfgR, base, hsRoute,
      { entry := ?_, parent := mkFrame cfgR hmR hHead.frame h2
        memory := hmR, kept := hHead.frame
        ground := by rw [hmR]; exact hgroundR
        baseRead := by rw [hmR]; exact hbase
        countRead := by rw [hmR]; exact hcount
        suffix := by rw [hmR]; exact hsuffix }⟩
    exact
      { good := hHead.good
        tick := hHead.tick
        pc := hHead.pc
        store := by rw [hmR]; exact hFresh.store
        store_survives := by rw [hmR]; exact hFresh.survives
        out := by
          change String.join cfgR.σ.sailOutput.toList = st.out
          rw [hHead.out]; exact hA.out
        mem := rfl
        ready := fun h => absurd rfl h
        empty_status := fun _ => by
          have h10 : lookupG 10 (evalBlocks blockEmptySeg (SegEvalState.init
              (TruthyCopy.routeL p (sp - 176#64) blockEnvNewCall.retPC aStmt aInterp aRet aEnv)
              (blockLds cR.σ.mem aStmt))).regs = some (0#64 + sign_extend (m := 64) (0#12)) := rfl
          have := gholds_lookup _ hHead.regs h10
          simpa only [gprGet, hsext, BitVec.add_zero] using this
        frame := fun _ _ => rfl
        minstret := hHead.minstret }
  | cons s rest =>
    -- the nonempty block: the loop head
    have hne : 0 < (s :: rest).length := by simp
    obtain ⟨cfgR, hsRoute, hHead⟩ := routeK_of_ready keepS3 keepS3_noise keepS3_abi
      blockLoopHeadSeg 0x800041a4#64 (blockLds cR.σ.mem aStmt) hRet.ready
      (by change ChainOK blockEnvNewCall.retPC [10, 2, 1, 8, 9, 18, 19] blockLoopHeadSeg; decide)
      rfl
      (by change WrChainAvoids keepS3 blockLoopHeadSeg; decide)
      (blockLoopHead_facts hgroundR hcode hcount hlt hne _ _ _ _ _ _)
    have hmR : cfgR.σ.mem = cR.σ.mem := by rw [hHead.mem]; rfl
    -- the reflected registers at the loop head
    have h8 : cfgR.σ.regs.get? Register.x8 = some aStmt := by
      simpa only [gprGet] using gholds_lookup (n := 8) _ hHead.regs rfl
    have h9 : cfgR.σ.regs.get? Register.x9 = some aInterp := by
      simpa only [gprGet] using gholds_lookup (n := 9) _ hHead.regs rfl
    have h18 : cfgR.σ.regs.get? Register.x18 = some aRet := by
      simpa only [gprGet] using gholds_lookup (n := 18) _ hHead.regs rfl
    have h2 : cfgR.σ.regs.get? Register.x2 = some (sp - 176#64) := by
      simpa only [gprGet] using gholds_lookup (n := 2) _ hHead.regs rfl
    have h16 : cfgR.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 0) := by
      have := gholds_lookup (n := 16) (v := 0#64 + sign_extend (m := 64) (0#12)) _ hHead.regs rfl
      simpa only [gprGet, hsext, BitVec.add_zero] using this
    have h19 : cfgR.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (φf' st.store.frames.size)) := by
      have := gholds_lookup (n := 19) (v := p + sign_extend (m := 64) (0#12)) _ hHead.regs rfl
      rw [hpNat]
      simpa only [gprGet, hsext, BitVec.add_zero] using this
    -- the statement array
    obtain ⟨stmts, count, hbase', hcount', harray⟩ : ∃ stmts count,
        read64 cR.σ.mem (aStmt.toNat + 8) = some stmts ∧
        read32 cR.σ.mem (aStmt.toNat + 16) = some count ∧
        StmtArrayRepr cR.σ.mem stmts count (s :: rest) := by
      cases hstmtR with
      | block _ hb hc ha => exact ⟨_, _, hb, hc, ha⟩
    have hstmts : stmts = base := Option.some.inj (hbase'.symm.trans hbase)
    have hcountEq : count = (s :: rest).length := Option.some.inj (hcount'.symm.trans hcount)
    rw [hstmts, hcountEq] at harray
    obtain ⟨q, hq, hsg⟩ := hsuffix.head
    have hqLt : q < 2 ^ 64 := read64_lt_eg4 cR.σ.mem base q hq
    have hneed := Stmt.stackNeed_ge s
    simp only [execFrame] at hneed
    refine ⟨cfgR, base, hsRoute,
      { entry := ?_, parent := mkFrame cfgR hmR hHead.frame h2
        memory := hmR, kept := hHead.frame
        ground := by rw [hmR]; exact hgroundR
        baseRead := by rw [hmR]; exact hbase
        countRead := by rw [hmR]; exact hcount
        suffix := by rw [hmR]; exact hsuffix }⟩
    exact
      { good := hHead.good
        tick := hHead.tick
        pc := hHead.pc
        store := by rw [hmR]; exact hFresh.store
        store_survives := by rw [hmR]; exact hFresh.survives
        out := by
          change String.join cfgR.σ.sailOutput.toList = st.out
          rw [hHead.out]; exact hA.out
        mem := rfl
        ready := fun _ =>
          { env_valid := EnvValid.allocatedFrame (st := st) hAlloc
            code := by rw [hmR]; exact hcode
            cursor := by
              refine ⟨aStmt, BitVec.ofNat 64 base, 0, (s :: rest).length, h8, h16, h19, h18, h2,
                ?_, ?_, by simp, hlt, ?_⟩
              · rw [hmR, hbaseBV]; exact hbase
              · rw [hmR]; exact hcount
              · rw [hmR, hbaseBV, Nat.mul_zero, Nat.add_zero]; exact harray
            head_ground := by
              refine ⟨BitVec.ofNat 64 q, ⟨aStmt, BitVec.ofNat 64 base, 0, h8, h16, ?_, ?_⟩,
                ?_, ⟨aInterp, h9, h19, h18⟩, ?_, ?_, ?_, hsg.bodies,
                fun a cd h => hA.store_bodies a cd h⟩
              · rw [hmR, hbaseBV]; exact hbase
              · rw [hmR, hbaseBV, Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hqLt]
                exact hq
              · rw [hmR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqLt]; exact hsg.stmt
              · rw [hmR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqLt]; exact hsg.ground
              · obtain ⟨hlo, hhi, hal'⟩ := hsg.stackBudget
                refine ⟨?_, hhi, hal'⟩
                rw [← Nat.add_assoc, ← Nat.add_assoc] at hlo
                generalize (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget = k at hlo
                generalize s.stackNeed = n at hlo hneed
                show SL.lo + 1264 ≤ (sp - 176#64).toNat
                omega
              · exact hsg.stackBudget
            store_survives := by rw [hmR]; exact hFresh.survives
            stack_ram := hA.stack_ram
            stack_win := hA.stack_win }
        empty_status := fun h => by cases h
        frame := fun _ _ => rfl
        minstret := hHead.minstret }

/-- The block arm from the statement entry to the indexed sequence entry. -/
theorem blockArm_run (hEN : EnvNewContract)
    {st : Vsa.While.St} {d : Nat} {env : Addr} {ss : List Stmt}
    {store' : Store} {inner : Addr}
    (hAlloc : st.store.allocFrame (some env) = (store', inner))
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.block ss) sp r aInterp aStmt aEnv aRet m0)
      (fun cfg => ∃ (gSeq : (R : Register) → Option (RegisterType R))
          (φf' φc' : Addr → Nat) (mSeq : Mem),
        ExecSeqEntryI .blockBody gSeq N A SL φf' φc'
          ⟨store', st.out⟩ d inner ss (sp - 176#64) aRet mSeq cfg ∧
        Rows.BlockArmFrame g gSeq A SL φf φc φf' φc' st store' sp r aRet m0 mSeq) := by
  intro cfg hEntry
  have hstore' : store' = (st.store.allocFrame (some env)).1 := by
    simpa using (congrArg Prod.fst hAlloc).symm
  have hinner : inner = st.store.frames.size := by
    simpa using (congrArg Prod.snd hAlloc).symm
  subst hstore' hinner
  obtain ⟨cA, ment, hsA, hA⟩ := armState_of_entry_kind 2 execArmBlock (by decide) rfl (by decide)
    (fun _ _ h => by cases h with | block hk _ _ _ => exact hk) hEntry
  have F := hA.frameFacts
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hstack := F.espStack
  have harena := F.espArena
  -- park at `env_new`
  obtain ⟨cP, hsP, hP⟩ := blockEnvNewCall.parked_of_armState blockEnvNewCall_cert hA []
    (by change ChainOK 0x8000418c#64 [2, 8, 9, 18, 19] blockEnvNewSeg; decide) rfl
    (by change KeysOK [10, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [10, 2, 8, 9, 18, 19], n ≠ 1; decide)
    (by show Exec_stmtLoaded (writeLog ment []); exact hA.code)
    (blockEnvNew_facts ment _ _ _ _ _ hA.code)
  have hsext : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have hM : EnvNewMem N A SL φf φc st env (aEnv + sign_extend (m := 64) (0#12)) (sp - 176#64)
      (writeLog ment []) :=
    { text := hA.ground.eval_call.image.text
      store := hA.store
      store_survives := hA.store_survives
      env_valid := hA.env_valid
      env_addr := by rw [hsext, BitVec.add_zero]; exact hA.env_addr
      stack := hstack
      stack_ram := hA.stack_ram
      stack_win := hA.stack_win
      stack_bytes := hA.ground.stack_bytes
      arena_stack := harena }
  obtain ⟨cR, p, φf', hsR, hRet, hFresh⟩ :=
    blockEnvNewCall.envNewReturn_of_parked blockEnvNewCall_cert rfl hEN hP rfl rfl rfl rfl rfl rfl hM
  obtain ⟨cfgR, base, resume, post⟩ := blockArm_resume hA hRet hFresh
  exact ⟨cfgR, hsA.trans (hsP.trans (hsR.trans resume)), cfgR.σ.regs.get?,
    φf', φc, cfgR.σ.mem, post.entry, post.parent⟩

#print axioms blockArm_resume

/-- The epilogue seam of the block: from the indexed sequence exit at the
shared epilogue entry to the widened statement exit, through the retained
parent frame. -/
theorem blockEpilogue_memory
    {g gSeq : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : Vsa.While.St} {store' : Store} {status : Status}
    {sp r aRet : BitVec 64} {m0 mSeq : Mem}
    (hFr : Rows.BlockArmFrame g gSeq A SL φf φc φf' φc' st store' sp r aRet m0 mSeq) :
    ∀ cfg,
      ExecSeqExitI .blockBody gSeq N A SL φf' φc'
        store'.frames.size store'.closures.size st' status (sp - 176#64) aRet mSeq cfg →
      ∃ after, Steps cfg after ∧
      ExecTailResult g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0 cfg.σ.mem after := by
  intro cfg hX
  have h176 := hFr.spRoom
  have hesp : (sp - 176#64).toNat = sp.toNat - 176 := EvalChildArm.esp_toNat sp h176
  obtain ⟨φfS, φcS, hpfS, hpcS, hsurv⟩ := hX.store_survives
  -- the parent's saved registers survive the sequence
  have hwin : ∀ a, sp.toNat - 40 ≤ a → a < sp.toNat → cfg.σ.mem[a]? = mSeq[a]? := by
    intro a hlo hhi
    have hret := hFr.retAbove
    have hSLhi := hFr.stackHi
    have hSLlo := hFr.stackLo
    have hAS := hFr.arenaStack
    apply hX.stack_frame a (by rw [hesp]; omega) (by omega)
    · intro hr; omega
    · intro hA; omega
  have hag : AgreeP (fun a => sp.toNat - 40 ≤ a ∧ a < sp.toNat) mSeq cfg.σ.mem :=
    fun a ha => (hwin a ha.1 ha.2).symm
  have hrd : ∀ off, 8 ≤ off → off ≤ 40 →
      read64 cfg.σ.mem (sp.toNat - off) = read64 mSeq (sp.toNat - off) :=
    fun off h1 h2 => (read64_agreeP hag (fun k hk => ⟨by omega, by omega⟩)).symm
  -- the code survives: it is below the stack and outside the arena
  have hcode : Exec_stmtLoaded cfg.σ.mem := by
    have hac := hFr.arenaCode
    have hsw := hFr.stackWin
    rw [tohostAddr_val] at hsw
    simp only [execStmtEntry, execStmtEnd] at hac
    apply loaded_exec_stmt_agreeP mSeq cfg.σ.mem _ hFr.code
    intro a ha
    exact (hX.mem_frame a (by intro hs; omega)
      (by intro hA; rcases hac with hd | hd <;> omega)).symm
  have hsp : cfg.σ.regs.get? Register.x2 = some (sp - 176#64) :=
    (hX.frame Register.x2 ⟨by decide, trivial⟩).trans hFr.seqSp
  refine epilogueTail_memory (φf' := φfS) (φc' := φcS) cfg ?_
  exact
    { good := hX.good
      tick := hX.tick
      pc := by have h := hX.pc; cases status <;> exact h
      a0 := by have h := hX.status_abi; cases status <;> exact h
      minstret := hX.minstret
      spReg := hsp
      code := hcode
      out := hX.out
      frames := hFr.frames.trans (PhiExtends.mono hFr.frames_le hpfS)
      closures := hFr.closures.trans (PhiExtends.mono hFr.closures_le hpcS)
      storeSurvives := hsurv
      retval := fun v hv => by
        obtain ⟨φc3, hp3, hrepr⟩ := hX.retval v hv
        exact ⟨φc3, PhiExtends.of_common (PhiExtends.mono hFr.closures_le hpcS)
          (PhiExtends.mono hFr.closures_le hp3), hrepr⟩
      saved_ra := by rw [hrd 8 (by omega) (by omega)]; exact hFr.saved_ra
      saved_s0 := by rw [hrd 16 (by omega) (by omega)]; exact hFr.saved_s0
      saved_s1 := by rw [hrd 24 (by omega) (by omega)]; exact hFr.saved_s1
      saved_s2 := by rw [hrd 32 (by omega) (by omega)]; exact hFr.saved_s2
      saved_s3 := by rw [hrd 40 (by omega) (by omega)]; exact hFr.saved_s3
      parentSp := hFr.parentSp
      frame := fun R hR he8 he9 he18 he19 he2 =>
        (hX.frame R ⟨hR, trivial⟩).trans (hFr.seqFrame R hR he8 he9 he18 he19 he2)
      memExtends := hFr.memExtends.trans hX.mem_extends
      memFrame := fun a hstk hA => by
        by_cases hr : aRet.toNat ≤ a ∧ a < aRet.toNat + 24
        · exact Or.inl hr
        · right
          rcases hFr.memFrame a hstk hA with hr' | heq
          · exact absurd hr' hr
          · rw [← heq]
            by_cases hs : SL.lo ≤ a ∧ a < SL.hi
            · have hSLlo := hFr.stackLo
              exact hX.stack_frame a (by rw [hesp]; omega) hs.2 hr hA
            · exact hX.mem_frame a hs hA
      spRoom := hFr.spRoom
      spHi := hFr.spHi
      spLo := hFr.spLo
      spWin := hFr.spWin
      spAlign := hFr.spAlign
      retAlign := hFr.retAlign }

/-- Project the ordinary block exit from the same memory-preserving epilogue. -/
theorem blockEpilogue_run
    {g gSeq : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : Vsa.While.St} {store' : Store} {status : Status}
    {sp r aRet : BitVec 64} {m0 mSeq : Mem}
    (hFr : Rows.BlockArmFrame g gSeq A SL φf φc φf' φc' st store' sp r aRet m0 mSeq) :
    Triple
      (ExecSeqExitI .blockBody gSeq N A SL φf' φc'
        store'.frames.size store'.closures.size st' status (sp - 176#64) aRet mSeq)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' status sp r aRet m0) := by
  intro cfg hX
  obtain ⟨after, steps, result⟩ := blockEpilogue_memory hFr cfg hX
  exact ⟨after, steps, result.exit⟩

#print axioms blockEpilogue_memory

/-- The block residual from the `env_new` contract alone. -/
theorem ScaffoldRows.field_hSBlock (hEN : EnvNewContract) :
    ∀ st st' d env ss status store' inner hSeq,
      Rows.BlockCaseResid st st' d env ss status store' inner hSeq :=
  fun st st' d env ss status store' inner _ hAlloc _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 _ _ =>
    { hArm := blockArm_run hEN hAlloc g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
      hEpi := fun _ _ _ _ hFr => blockEpilogue_run hFr }

#print axioms blockEnvNewCall_cert
#print axioms blockArm_run
#print axioms blockEpilogue_run
#print axioms ScaffoldRows.field_hSBlock

end Vsa.Sim
