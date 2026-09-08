import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.rows.TruthyCopyIf

/-!
# `Field_hSIfBranchClosed` — the two `if` residuals with a taken branch, closed

`hSIfTrue` and `hSIfFalse` compose only parametric pieces: the arm dispatch
(`ifCondArm`), the child's exit kit, the copy and `value_truthy` (`ifTruthy`),
the reflected truthy / falsy-with-`else` routes, and the construction of the
in-frame re-dispatch state `ExecDispatchReady` for the selected branch at the
memory actually reached.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- Every arm PC of the statement jump table is 4-aligned. -/
theorem execArmPC_align (k : Nat) (hk : k ≤ 8) : (execArmPC k).toNat % 4 = 0 := by
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | n + 9, hk => exact absurd hk (by omega)

/-- The register readbacks a branch route must certify. -/
structure IfRouteLookups (bs : List BBlock) (status : BitVec 64) (off : Nat) : Prop where
  s0 : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    lookupG 8 (evalBlocks bs (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off))).regs =
      some (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + off)))
  a4 : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    lookupG 14 (evalBlocks bs (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off))).regs =
      some (0x80019fb8#64)
  a6 : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    lookupG 16 (evalBlocks bs (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off))).regs =
      some (8#64)
  ra : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    lookupG 1 (evalBlocks bs (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off))).regs =
      some ifTruthy.retPC
  log_nil : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    (evalBlocks bs (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off))).log = []
  chain_ok : ChainOK ifTruthy.retPC [10, 2, 1, 8, 9, 18, 19] bs
  end_pc : ∀ (m : Mem) (esp aStmt s1 s2 s3 : BitVec 64),
    evalBlocksPC ifTruthy.retPC (SegEvalState.init
      (TruthyCopy.routeL status esp ifTruthy.retPC aStmt s1 s2 s3) (ifRouteLds m aStmt off)) bs =
      0x80004014#64
  avoid : WrChainAvoids TruthyCopy.abiButS0 bs

/-- The jump-table base materialised by `auipc a4; addi a4` on both if routes. -/
theorem ifRoute_tableBase :
    ((0x80004220#64 : BitVec 64) + sign_extend (m := 64)
        (imm20Of (mkLine 0x80004220#64 0x00016717#32) +++ (0x000#12)))
      + sign_extend (m := 64) (mkLine 0x80004224#64 0xd9870713#32).imm = 0x80019fb8#64 := by
  decide

/-- Reduce a route fold to its register list and read back `a4`. -/
macro "if_route_a4" seg:ident : tactic => `(tactic|
  (intros
   simp only [$seg:ident, TruthyCopy.routeL, ifRouteLds, evalBlocks, evalBlock, runGM, stepGM,
     wvalM, srcVal, lookupG, eraseG, SegEvalState.init, ldsRunM, stepLdsM, List.headD, List.tail,
     show (mkLine 0x8000421c#64 0x00800813#32).kind = MKind.addi from rfl,
     show (mkLine 0x8000421c#64 0x00800813#32).rd = 16 from rfl,
     show (mkLine 0x8000421c#64 0x00800813#32).rs1 = 0 from rfl,
     show (mkLine 0x80004220#64 0x00016717#32).kind = MKind.auipc from rfl,
     show (mkLine 0x80004220#64 0x00016717#32).rd = 14 from rfl,
     show (mkLine 0x80004224#64 0xd9870713#32).kind = MKind.addi from rfl,
     show (mkLine 0x80004224#64 0xd9870713#32).rd = 14 from rfl,
     show (mkLine 0x80004224#64 0xd9870713#32).rs1 = 14 from rfl,
     show (mkLine 0x8000422c#64 0x01043403#32).kind = MKind.ld from rfl,
     show (mkLine 0x8000422c#64 0x01043403#32).rd = 8 from rfl]
   simp only [show (mkLine 0x80004220#64 0x00016717#32).pc = 0x80004220#64 from rfl,
     Nat.reduceEqDiff, ↓reduceIte, lookupG, eraseG]
   exact congrArg some ifRoute_tableBase))

theorem ifTruthySeg_lookups : IfRouteLookups ifTruthySeg (1#64) 16 where
  s0 := by intros; rfl
  a4 := by if_route_a4 ifTruthySeg
  a6 := by intros; rfl
  ra := by intros; rfl
  log_nil := by intros; rfl
  chain_ok := by decide
  end_pc := by intros; rfl
  avoid := by decide

theorem ifFalsyElseSeg_lookups : IfRouteLookups ifFalsyElseSeg (0#64) 24 where
  s0 := by intros; rfl
  a4 := by if_route_a4 ifFalsyElseSeg
  a6 := by intros; rfl
  ra := by intros; rfl
  log_nil := by intros; rfl
  chain_ok := by decide
  end_pc := by intros; rfl
  avoid := by decide

/-- The branch resume shared by both taken-branch cases: from the condition's
widened exit, copy and test the value, run the route selecting the branch
node at `aStmt + off`, and assemble the in-frame re-dispatch state. -/
theorem ifBranch_resume
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {c : Expr} {t : Stmt} {e : Option Stmt}
    {v : Value} {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem}
    (bs : List BBlock) (b : Bool) (off : Nat) (branch : Stmt)
    (L : IfRouteLookups bs (cond b (1#64) (0#64)) off)
    (hb : v.truthy = b)
    (hbranchRepr : ∀ m : Mem, StmtRepr m aStmt.toNat (.ifStmt c t e) →
      ∃ q, read64 m (aStmt.toNat + off) = some q ∧ StmtRepr m q branch)
    (hin : ∀ (m : Mem) (lo hi : Nat), StmtIn m lo hi aStmt.toNat (.ifStmt c t e) →
      ∀ q, read64 m (aStmt.toNat + off) = some q → StmtIn m lo hi q branch)
    (hfacts : ∀ m : Mem, ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t e) →
      Exec_stmtLoaded m → StmtRepr m aStmt.toNat (.ifStmt c t e) →
      ChainFacts m m (TruthyCopy.routeL (cond b (1#64) (0#64)) (sp - 176#64) ifTruthy.retPC
        aStmt aInterp aRet aEnv) (ifRouteLds m aStmt off) bs)
    (hCarrier : ifCondArm.Carrier (.ifStmt c t e) c g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC) :
    Triple
      (EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) ifCondArm.retPC (ifCondArm.sret (sp - 176#64)) mC)
      (fun cfg => ∃ (φf' φc' : Addr → Nat),
        PhiExtends φf φf' st.store.frames.size ∧
        PhiExtends φc φc' st.store.closures.size ∧
        MemExtends m0 cfg.σ.mem ∧
        (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cfg.σ.mem[a]? = m0[a]?) ∧
        Rows.IfBranchReady g N A SL φf' φc' st' branch sp r aInterp aEnv aRet cfg) := by
  intro cfgX hExit
  obtain ⟨φf', φc', hpf, hpc, hSurv, hKit⟩ :=
    ifCondArm.exitKit_at_exit ifCondArm_cert hCarrier cfgX hExit
  obtain ⟨mCopy, cfgCopy, hsCopy, hmCopy, hReady⟩ :=
    TruthyCopy.copyReady_of_exitKit ifCondArm ifCondArm_cert ifTruthy ifTruthy_cert
      cfgX hCarrier hKit
  obtain ⟨cfgT, hsT, hRet⟩ :=
    TruthyCopy.truthyReturn_of_copyReady ifCondArm ifTruthy ifTruthy_cert N φc' hReady
  rw [hb] at hRet
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom ifCondArm_cert
  have hsretRoom := ifCondArm_cert.sret_room
  have hnowrap : (sp - 176#64).toNat + 40 ≤ 0x100000000 := by
    have := hCarrier.stack_ram.2; omega
  have hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfgX.σ.mem[k]? := by
    rw [hmCopy]
    exact TruthyCopy.writeLog_frame ifCondArm ifTruthy ifTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aEnv hnowrap
  have hcopyExt : MemExtends cfgX.σ.mem mCopy := by
    rw [hmCopy]
    exact TruthyCopy.memExtends ifCondArm ifTruthy ifTruthy_cert cfgX.σ.mem
      (sp - 176#64) aStmt aInterp aRet aEnv
  have hCopyOutside : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mCopy[k]? = cfgX.σ.mem[k]? := by
    intro k hk
    apply hcopyFrame k
    rw [hesp]
    intro hw
    exact hk ⟨by omega, by omega⟩
  have hPop : StackBytesPresent mCopy SL := by
    intro k hklo hkhi
    obtain ⟨bb, hbb⟩ := hKit.stack_bytes k hklo hkhi
    exact hcopyExt k bb hbb
  have hGroundCopy : ExecGround mCopy SL A sp aRet aStmt.toNat (.ifStmt c t e) :=
    hKit.ground.transport_offstack hSLhi hPop hCopyOutside
  have hStmtCopy : StmtRepr mCopy aStmt.toNat (.ifStmt c t e) :=
    hKit.ground.stmtRepr_offstack hKit.parent_stmt hSLhi hCopyOutside
  obtain ⟨q, hq, hBranchRepr⟩ := hbranchRepr mCopy hStmtCopy
  let aBranch : BitVec 64 := BitVec.ofNat 64 q
  have hqEq : aBranch.toNat = q :=
    Nat.mod_eq_of_lt (read64_lt_eg4 mCopy (aStmt.toNat + off) q hq)
  have hqB : read64 mCopy (aStmt.toNat + off) = some aBranch.toNat := hqEq ▸ hq
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_truthyReturn ifTruthy bs 0x80004014#64
      (ifRouteLds mCopy aStmt off) hRet L.chain_ok (L.end_pc _ _ _ _ _ _) L.avoid
      (hfacts mCopy hGroundCopy hReady.code hStmtCopy)
  have hmemR : cfgR.σ.mem = mCopy := by
    rw [hHead.mem, L.log_nil]; rfl
  have hRegs := hHead.regs
  have hx8 : cfgR.σ.regs.get? Register.x8 = some aBranch := by
    have h := gholds_lookup _ hRegs (L.s0 mCopy (sp - 176#64) aStmt aInterp aRet aEnv)
    rw [EvalChildArm.bytesVal_ld_wordLds mCopy (aStmt.toNat + off) aBranch hqB] at h
    exact h
  have hx14 : cfgR.σ.regs.get? Register.x14 = some (0x80019fb8#64) :=
    gholds_lookup _ hRegs (L.a4 mCopy (sp - 176#64) aStmt aInterp aRet aEnv)
  have hx16 : cfgR.σ.regs.get? Register.x16 = some (8#64) :=
    gholds_lookup _ hRegs (L.a6 mCopy (sp - 176#64) aStmt aInterp aRet aEnv)
  have hx1 : cfgR.σ.regs.get? Register.x1 = some ifTruthy.retPC :=
    gholds_lookup _ hRegs (L.ra mCopy (sp - 176#64) aStmt aInterp aRet aEnv)
  have hfr (R : Register) (hR : TruthyCopy.abiButS0 R = true) : cfgR.σ.regs.get? R = gC R :=
    hHead.frame R hR
  have hSaved : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mCopy mC := by
    intro k hk
    rw [hcopyFrame k (by rw [hesp]; omega)]
    rcases hExit.1.memFrame k
        (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq
  have hSavedRead (o : Nat) (hlo : 8 ≤ o) (hhi : o ≤ 40) :
      read64 mCopy (sp.toNat - o) = read64 mC (sp.toNat - o) :=
    read64_agreeP hSaved (fun k hk => ⟨by omega, by omega⟩)
  obtain ⟨v8, hs8, hg8⟩ := hCarrier.saved_s0
  obtain ⟨v9, hs9, hg9⟩ := hCarrier.saved_s1
  obtain ⟨v18, hs18, hg18⟩ := hCarrier.saved_s2
  obtain ⟨v19, hs19, hg19⟩ := hCarrier.saved_s3
  obtain ⟨lo, hi, hr⟩ := hGroundCopy.ast.region
  have hnode := stmtIn_node (hin mCopy lo hi hr.nodes q hq)
  have hkle := kindOfStmt_le branch
  refine ⟨cfgR, (hsCopy.trans hsT).trans hsR, φf', φc', hpf, hpc, ?_, ?_,
    aBranch, ifTruthy.retPC, v8, v9, v18, v19, ?_⟩
  · rw [hmemR]
    exact (hCarrier.mem_extends.trans hExit.2.1).trans hcopyExt
  · intro k hstk hA
    apply Or.inr
    rw [hmemR, hCopyOutside k hstk]
    rcases hExit.1.memFrame k
        (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr' | heq
    · exfalso
      rw [hsret] at hr'
      exact hstk ⟨by omega, by omega⟩
    · exact heq.trans (hCarrier.mem_frame k hstk)
  · refine ⟨hHead.good, hHead.tick, hHead.pc, hx8,
      (hfr Register.x9 (by decide)).trans hCarrier.s1,
      (hfr Register.x19 (by decide)).trans hCarrier.s3,
      (hfr Register.x18 (by decide)).trans hCarrier.s2,
      hx14, hx16, (hfr Register.x2 (by decide)).trans hCarrier.spReg, hx1,
      hHead.minstret, rfl, ?_, rfl, ?_, ?_, ?_,
      ⟨execArmPC (kindOfStmt branch), ?_, execArmPC_align _ hkle, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, hg8, hg9, hg18, hg19, hCarrier.parentSp, ?_,
      fun _ _ => rfl, h176, Nat.le_trans hSLhi hCarrier.stack_ram.2,
      Nat.le_trans hCarrier.stack_ram.1 (by omega),
      (by have := hCarrier.stack_win; omega), (by omega), hCarrier.ra_align,
      ?_, ?_, ?_, MemExtends.refl _⟩
    · change String.join cfgR.σ.sailOutput.toList = st'.out
      rw [hHead.out]
      exact hKit.out
    · rw [hmemR]; exact hReady.code
    · rw [hmemR]
      apply hSurv mCopy
      intro k hk
      exact (hCopyOutside k (by
        intro hs
        exact hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hSLhi⟩)).symm
    · rw [hmemR, hqEq]; exact hBranchRepr
    · rw [hmemR]; exact hGroundCopy.table.slotOf _ hkle
    · rcases hGroundCopy.table_stack with ht | ht
      · left; omega
      · right; omega
    · rw [hmemR]; exact (hSavedRead 8 (by omega) (by omega)).trans hCarrier.saved_ra
    · rw [hmemR]; exact (hSavedRead 16 (by omega) (by omega)).trans hs8
    · rw [hmemR]; exact (hSavedRead 24 (by omega) (by omega)).trans hs9
    · rw [hmemR]; exact (hSavedRead 32 (by omega) (by omega)).trans hs18
    · rw [hmemR]; exact (hSavedRead 40 (by omega) (by omega)).trans hs19
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
      have hP : TruthyCopy.abiButS0 R = true := by
        unfold TruthyCopy.abiButS0; rw [hR.1, he8]; rfl
      exact (hfr R hP).trans hg
    · have := hnode.lo_le; have := hnode.hi_ge
      rcases hr.stack_disjoint with hd | hd
      · left; rw [hqEq]; omega
      · right; rw [hqEq]; omega
    · rw [hqEq]
      exact ⟨Nat.le_trans hr.lo_ram hnode.lo_le, by have := hnode.hi_ge; have := hr.hi_ram; omega⟩
    · right; rw [hqEq]; have := hr.win; have := hnode.lo_le; omega

/-- Concrete supplier for the `if`-true residual. -/
theorem ScaffoldRows.field_hSIfTrue :
    ∀ st st' st'' d env c t e v status hC hB,
      Rows.IfTrueCaseResid st st' st'' d env c t e v status hC hB := by
  intro st st' st'' d env c t e v status hC hB hTruthy _ _ _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact
    { dispatch := execIfCondDispatch_generic g N A SL φf φc st d env c t e
        sp r aInterp aStmt aEnv aRet m0
      resume := fun gC aC mC hCarrier =>
        ifBranch_resume ifTruthySeg true 16 t ifTruthySeg_lookups hTruthy
          (fun m h => by
            cases h with
            | ifElse _ _ _ ht hrt _ _ _ => exact ⟨_, ht, hrt⟩
            | ifNoElse _ _ _ ht hrt _ => exact ⟨_, ht, hrt⟩)
          (fun m lo hi h q hq => h.2.2.1 q hq)
          (fun m hg hcode _ => ifTruthy_facts hg hcode (sp - 176#64) aInterp aRet aEnv)
          hCarrier }

/-- Concrete supplier for the `if`-false residual. -/
theorem ScaffoldRows.field_hSIfFalse :
    ∀ st st' st'' d env c t e v status hC hB,
      Rows.IfFalseCaseResid st st' st'' d env c t e v status hC hB := by
  intro st st' st'' d env c t e v status hC hB hFalsy _ _ _
    g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact
    { dispatch := execIfCondDispatch_generic g N A SL φf φc st d env c t (some e)
        sp r aInterp aStmt aEnv aRet m0
      resume := fun gC aC mC hCarrier =>
        ifBranch_resume ifFalsyElseSeg false 24 e ifFalsyElseSeg_lookups hFalsy
          (fun m h => by
            cases h with
            | ifElse _ _ _ _ _ he _ hre => exact ⟨_, he, hre⟩)
          (fun m lo hi (h : StmtIn m lo hi aStmt.toNat (.ifStmt c t (some e))) q hq =>
            (h.2.2.2 : OptStmtIn m lo hi (aStmt.toNat + 24) (some e)).2 q hq)
          (fun m hg hcode hstmt => by
            obtain ⟨q, hq, hne, _⟩ : ∃ q, read64 m (aStmt.toNat + 24) = some q ∧ q ≠ 0 ∧
                StmtRepr m q e := by
              cases hstmt with
              | ifElse _ _ _ _ _ he hne hre => exact ⟨_, he, hne, hre⟩
            have hqEq : (BitVec.ofNat 64 q).toNat = q :=
              Nat.mod_eq_of_lt (read64_lt_eg4 m (aStmt.toNat + 24) q hq)
            exact ifFalsyElse_facts hg hcode (aElse := BitVec.ofNat 64 q)
              (by rw [hqEq]; exact hq)
              (by
                intro h0
                apply hne
                rw [← hqEq, h0]
                rfl)
              (sp - 176#64) aInterp aRet aEnv)
          hCarrier }

#print axioms ScaffoldRows.field_hSIfTrue
#print axioms ScaffoldRows.field_hSIfFalse

end Vsa.Sim
