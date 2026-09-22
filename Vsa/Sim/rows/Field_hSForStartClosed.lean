import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.HelperCallSites
import Vsa.Sim.rows.ExecDispatchRows

/-!
# `Field_hSForStartClosed` — the for-statement start on the layer

`for (init; cnd; step) b` (`0x80004234`: `mv a0,s3; jal env_new`, return
`0x8000423c`) allocates the loop scope and lands in `ExecInitReady`, the
boundary the typed initializer and loop motives consume.  The prologue to the
arm state, the `HelperCall` instance parked at `env_new`, and the `env_new`
adapter are generic; the `env_new` contract is the one named premise.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

#derive_case forEnvNewSeg chain
  [(0x80004234#64, 0x00098513#32)]  -- discipline: allow(R12-helper-call-arm) the HelperCall instance's own prefix

/-- The scope allocation of the for arm. -/
def forEnvNewCall : HelperCall :=
  { headPC := 0x80004234#64
    seg := forEnvNewSeg
    jalPC := 0x80004238#64
    jalImm := 0x1fe7c4#21
    entry := 0x800029fc#64 }

theorem forEnvNewCall_cert : forEnvNewCall.Cert where
  ret_align := by decide
  ret_clean := by decide
  jal_tgt := by decide
  avoid_abi := by change WrChainAvoidAbi forEnvNewSeg; decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004238_hc σ i u _ vmi hG hpc hmi hmem rfl hi

theorem forEnvNew_facts (m : Mem) (esp aStmt aInterp aRet aEnv : BitVec 64)
    (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (EvalChildArm.regs esp aStmt aInterp aRet aEnv) [] forEnvNewSeg := by
  unfold forEnvNewSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"

/-- The for arm from the statement entry to the initializer boundary. -/
theorem forStart_run (hEN : EnvNewContract)
    {st : Vsa.While.St} {d : Nat} {env : Addr}
    {init : Option Stmt} {cnd step : Option Expr} {b : Stmt}
    {store' : Store} {outer : Addr}
    (hAlloc : st.store.allocFrame (some env) = (store', outer)) :
    Rows.ForStartPrefixResid st st d env init cnd step b store' outer := by
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 cfg hEntry
  have hstore' : store' = (st.store.allocFrame (some env)).1 := by
    simpa using (congrArg Prod.fst hAlloc).symm
  have houter : outer = st.store.frames.size := by
    simpa [Vsa.While.Store.allocFrame] using (congrArg Prod.snd hAlloc).symm
  subst hstore' houter
  obtain ⟨cA, ment, hsA, hA⟩ := armState_of_entry_kind 5 execArmFor (by decide) rfl (by decide)
    (fun _ _ h => by cases h with | forS hk _ _ _ _ _ => exact hk) hEntry
  have F := hA.frameFacts
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hstack := F.espStack
  have harena := F.espArena
  -- park at `env_new`
  obtain ⟨cP, hsP, hP⟩ := forEnvNewCall.parked_of_armState forEnvNewCall_cert hA []
    (by change ChainOK 0x80004234#64 [2, 8, 9, 18, 19] forEnvNewSeg; decide) rfl
    (by change KeysOK [10, 2, 8, 9, 18, 19]; decide)
    (by change ∀ n ∈ [10, 2, 8, 9, 18, 19], n ≠ 1; decide)
    (by show Exec_stmtLoaded (writeLog ment []); exact hA.code)
    (forEnvNew_facts ment _ _ _ _ _ hA.code)
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
    forEnvNewCall.envNewReturn_of_parked forEnvNewCall_cert rfl hEN hP rfl rfl rfl rfl rfl rfl hM
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
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) ment cR.σ.mem := by
    intro k hk
    exact (hRet.mem_frame k (fun h => h.elim
      (fun hA' => by rcases hA.ground.arena_stack with hd | hd <;> omega)
      (fun hs => by rw [hesp] at hs; omega))).symm
  obtain ⟨v8, hr8, hg8⟩ := hA.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := hA.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := hA.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := hA.saved_s3
  obtain ⟨hra, hs0, hs1, hs2, hs3⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag hA.saved_ra hr8 hr9 hr18 hr19
  have hpNat : (BitVec.ofNat 64 (φf' st.store.frames.size)) = p := by
    rw [hFresh.addr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.isLt]
  have hretPC : forEnvNewCall.retPC = 0x8000423c#64 := by decide
  refine ⟨cR, hsA.trans (hsP.trans hsR), φf', φc, cR.σ.mem, forEnvNewCall.retPC,
    hFresh.map_extends, PhiExtends.refl φc _, ?_⟩
  exact
    { good := hRet.ready.good
      tick := hRet.ready.tick
      pc := by rw [hRet.ready.pc, hretPC]
      s0 := hRet.ready.s0
      s1 := hRet.ready.s1
      s2 := hRet.ready.s2
      a0 := by rw [hpNat]; exact hRet.ready.a0
      spReg := hRet.ready.sp
      ra := hRet.ready.ra
      mem := rfl
      code := hcode
      stmt := hA.ground.stmtRepr_execExit hA.stmt hSLhi hframeP
      outer_addr := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        rw [hFresh.addr]; exact p.isLt
      store := hFresh.store
      env_valid := EnvValid.allocatedFrame (st := st) hAlloc
      store_survives := hFresh.survives
      stack_ram := hA.stack_ram
      stack_win := hA.stack_win
      code_stack_disjoint := hA.code_stack_disjoint
      out := by
        change String.join cR.σ.sailOutput.toList = st.out
        rw [hRet.ready.out]
        exact hA.out
      saved_ra := hra
      saved_s0 := ⟨v8, hs0, hg8⟩
      saved_s1 := ⟨v9, hs1, hg9⟩
      saved_s2 := ⟨v18, hs2, hg18⟩
      saved_s3 := ⟨v19, hs3, hg19⟩
      x20_defined := by
        obtain ⟨v, hv⟩ := hA.envset.1
        exact ⟨v, (hRet.ready.frame Register.x20 (by decide)).trans hv⟩
      x21_defined := by
        obtain ⟨v, hv⟩ := hA.envset.2
        exact ⟨v, (hRet.ready.frame Register.x21 (by decide)).trans hv⟩
      stack_budget := hA.stack_budget
      stmt_bodies := hA.stmt_bodies
      store_bodies := fun a cd h => hA.store_bodies a cd h
      ground := hA.ground.transport_execExit hSLhi hpop hframeP
      mem_frame := by
        intro a hstk hA'
        rcases hframeP a hstk hA' with hr | heq
        · exact Or.inl hr
        · exact Or.inr (heq.trans (hA.mem_frame a hstk))
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
        right
        exact (hRet.ready.frame R hR.1).trans (hA.frame R hR
          (beq_eq_false_iff_ne.mpr (Ne.symm h8)) (beq_eq_false_iff_ne.mpr (Ne.symm h9))
          (beq_eq_false_iff_ne.mpr (Ne.symm h18)) (beq_eq_false_iff_ne.mpr (Ne.symm h19))
          (beq_eq_false_iff_ne.mpr (Ne.symm h2)))
      minstret := hRet.ready.minstret
      parentSp := hA.parentSp
      ra_align := hA.ra_align
      mem_extends := hA.mem_extends.trans hRet.mem_extends }

/-- Supplier for the for-start residual, from the `env_new` contract. -/
theorem ScaffoldRows.field_hSForStart (hEN : EnvNewContract) :
    ∀ st st' st'' d env init cnd step b status store' outer hInit hFor,
      Rows.ForStartCaseResid st st' st'' d env init cnd step b status store' outer hInit hFor :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAlloc _ _ =>
    forStart_run hEN hAlloc

#print axioms forEnvNewCall_cert
#print axioms forStart_run
#print axioms ScaffoldRows.field_hSForStart

end Vsa.Sim
