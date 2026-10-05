import Vsa.Sim.SegEffect
import Vsa.Sim.RunT

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps RunT)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def pcsB (b : BBlock) : List (BitVec 64) :=
  b.body.map (·.pc) ++ (match b.term with
    | none => []
    | some t => [t.pc])

def pcsC : List BBlock → List (BitVec 64)
  | [] => []
  | b :: bs => pcsB b ++ pcsC bs

theorem pcsC_cons (b : BBlock) (bs : List BBlock) : pcsC (b :: bs) = pcsB b ++ pcsC bs := rfl

theorem block_mem_runT (is : List MInstr) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (lds : List (List (BitVec 8)))
      (mc m : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m →
    (∀ j, j < tohostAddr → m[j]? = mc[j]?) →
    GHolds σ L →
    KeysOK (keysG L) →
    (∀ n ∈ dom, n ∈ keysG L) →
    ProgFactsM mc m L lds is →
    BlockOKM pc0 dom is →
    i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      RunT ⟨σ, i, u⟩ (is.map (·.pc)) ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog m (wlogM is L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCM pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM is L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction is with
  | nil =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem _ hL _ _ _ _ hi
    exact ⟨σ, i, RunT.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons a r ih =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hfacts hwf hi
    subst hmem
    obtain ⟨⟨hb0, hb1, hb2, hb3⟩, hdec, hextra, hfr⟩ : BytePinsM mc a ∧ DecodeFactM a ∧
        MemFacts σ.mem L (lds.headD []) a ∧
        ProgFactsM mc (stepMemM σ.mem a L) (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) r :=
      hfacts
    obtain ⟨⟨hpcn, hwn, hrvcn, hlo, hhi, halign, hkok⟩, hwfr⟩ :
        InstrOKM pc0 dom a ∧ BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r := hwf
    obtain rfl : pc0 = a.pc := (BitVec.eq_of_toNat_eq hpcn).symm
    have hhi' : a.pc.toNat + 4 ≤ tohostAddr := hhi
    have F : Fetched σ a.pc (astOfM a) :=
      Fetched.of_bytes hG hpc ((hlow _ (by omega)).trans hb0) ((hlow _ (by omega)).trans hb1)
        ((hlow _ (by omega)).trans hb2) ((hlow _ (by omega)).trans hb3) hlo hhi halign
        (BitVec.eq_of_toNat_eq hrvcn) (BitVec.eq_of_toNat_eq hwn)
        (hdec _ (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
          (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
          (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    have hG0 : GoodState (afterNextPC (afterPrelude σ) a.pc) :=
      (hG.insert_nonpinned (r := Register.minstret_increment) (by decide) _).insert_nonpinned
        (r := Register.nextPC) (by decide) _
    have hsteps : ∀ {σ1 σf : MState} {i1 i' : Nat}, Step ⟨σ, i, u⟩ ⟨σ1, i1, u + 1⟩ →
        RunT ⟨σ1, i1, u + 1⟩ (r.map (·.pc)) ⟨σf, i', u + 1 + r.length⟩ →
        RunT ⟨σ, i, u⟩ ((a :: r).map (·.pc)) ⟨σf, i', u + (a :: r).length⟩ := fun h1 h2 => by
      have e : u + 1 + r.length = u + (a :: r).length := by simp only [List.length_cons]; omega
      exact e ▸ RunT.step h1 hpc h2
    cases hk : isStoreM a.kind
    · -- register kinds: one commit, one register write
      obtain ⟨hrd, hexec⟩ := exec_reg_kind σ a L (lds.headD []) dom hG hpc hL hdom hk hkok hextra
      obtain ⟨hnpc, hinc, hms, hhart, hnp⟩ := gpr_rd_ok a.rd (by omega) hrd.1
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ := stepObs_retire (u := u)
        (try_step_retire F hexec
          ⟨by reg_reads [hhart, hG.hart_state], by reg_reads [hnpc], by reg_reads [hinc],
           by reg_reads [hms, hmi]⟩)
        hG ((hG0.insert_nonpinned hnp _).retirePost _ _) hi
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      rw [stepMemM_reg hk, stepGM_reg hk] at hfr
      rw [domStepM_reg hk] at hwfr
      obtain ⟨σf, i', hs, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt a.pc 4) vm1 ((a.rd, wvalM a L (lds.headD [])) :: eraseG a.rd L)
          _ mc σ.mem (a.rd :: dom)
          hG1 (obs_alu_pc hobs1) hmi1 hmem1 hlow
          ⟨obs_gpr_rd a.rd hrd.1 hrd.2 _ hobs1, gholds_eraseG hobs1 hrd.1 hrd.2 L hkeys hL⟩
          (keysOK_cons_erase hrd.1 hrd.2 L hkeys) (dom_cons_erase hdom) hfr hwfr hi1
      refine ⟨σf, i', hsteps hs1 hs, hi', hGf, ?_, houtf.trans hobs1.2, hpcf, hmif, ?_, ?_⟩
      · rw [wlogM_reg hk, stepGM_reg hk]; exact hmemf
      · simp only [runGM, stepGM_reg hk]; exact hGHf
      · intro R hn hrds
        rw [wrRegsM_reg hk] at hrds
        exact (hframef R hn fun n hn' => hrds n (List.mem_cons_of_mem _ hn')).trans
          (frame_step_alu hobs1 R hn (hrds _ List.mem_cons_self))
    · -- store kinds: one commit, one write-log entry
      obtain ⟨hexec, hlow1⟩ := exec_store_kind σ a L (lds.headD []) dom hG hL hdom hk hkok hextra
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ := stepObs_retire (u := u)
        (try_step_retire F hexec
          ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hmi]⟩)
        hG ((GoodState.of_regs_eq (σ := afterNextPC (afterPrelude σ) a.pc)
          (σ' := sigma3_store σ a.pc (applyW σ.mem (wentryM a L))) rfl hG0).retirePost _ _) hi
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      rw [stepMemM_store hk, stepGM_store hk] at hfr
      rw [domStepM_store hk] at hwfr
      obtain ⟨σf, i', hs, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt a.pc 4) vm1 L _ mc (applyW σ.mem (wentryM a L)) dom
          hG1 (obs_store_pc hobs1) hmi1 hmem1 (fun j hj => (hlow1 j hj).trans (hlow j hj))
          (gholds_store hobs1 L hkeys hL) hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', hsteps hs1 hs, hi', hGf, ?_, houtf.trans hobs1.2, hpcf, hmif, ?_, ?_⟩
      · rw [wlogM_store hk]; rw [stepLdsM_store hk] at hmemf; exact hmemf
      · simp only [runGM, stepGM_store hk]; exact hGHf
      · intro R hn hrds
        rw [wrRegsM_store hk] at hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)


theorem bblock_run_btT (b : BBlock) (σ : MState) (i u : Nat) (pc0 vm : BitVec 64)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (mc m : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m)
    (hlow : ∀ j, j < tohostAddr → m[j]? = mc[j]?)
    (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
    (hdom : ∀ n ∈ dom, n ∈ keysG L)
    (hfacts : BBlockFacts mc m L lds b)
    (hwf : BBlockOK pc0 dom b)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      RunT ⟨σ, i, u⟩ (pcsB b) ⟨σ', i', u + blenB b⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog m (wlogM b.body L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCB pc0 b L lds) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM b.body L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM b.body, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  obtain ⟨body, term⟩ := b
  obtain ⟨hbf, htp, htfo⟩ := hfacts
  obtain ⟨hbo, hto⟩ := hwf
  obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
    block_mem_runT body σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hbf hbo hi
  cases term with
  | none =>
    exact ⟨σ1, i1, by simpa [pcsB, blenB] using hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩
  | some t =>
    obtain ⟨hpceq, hwft⟩ :=
      (hto : t.pc.toNat = (endPCM pc0 body).toNat ∧ TermWF (domRunM body dom) t)
    have hpct : t.pc = endPCM pc0 body := BitVec.eq_of_toNat_eq hpceq
    obtain ⟨htb, htd⟩ := (htp : BytePinsT mc t ∧ DecodeFactT t)
    obtain ⟨vm1, hmi1'⟩ := hmi1
    have hlow1 : ∀ j, j < tohostAddr → σ1.mem[j]? = mc[j]? := by
      intro j hj
      rw [hmem1]
      exact (writeLog_wlog_low_bt mc body m L lds hbf j hj).trans (hlow j hj)
    have hhit : t.pc.toNat + 4 ≤ tohostAddr := hwft.2.2.2.1
    have hb0 : σ1.mem[t.pc.toNat]? = some t.b0 := (hlow1 _ (by omega)).trans htb.1
    have hb1 : σ1.mem[t.pc.toNat + 1]? = some t.b1 := (hlow1 _ (by omega)).trans htb.2.1
    have hb2 : σ1.mem[t.pc.toNat + 2]? = some t.b2 := (hlow1 _ (by omega)).trans htb.2.2.1
    have hb3 : σ1.mem[t.pc.toNat + 3]? = some t.b3 := (hlow1 _ (by omega)).trans htb.2.2.2
    have hkeys1 : KeysOK (keysG (runGM body L lds)) :=
      keysOK_runGM_bt body pc0 dom L lds hbo hkeys
    have hdom1 : ∀ n ∈ domRunM body dom, n ∈ keysG (runGM body L lds) :=
      domRun_keys_bt body L lds dom hdom
    have hpc1' : σ1.regs.get? Register.PC = some t.pc := by rw [hpct]; exact hpc1
    obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hout2, hpc2, hmi2, hGH2, hframe2⟩ :=
      term_step_bt t σ1 i1 (u + body.length) vm1 (runGM body L lds) (domRunM body dom)
        hG1 hpc1' hmi1' hGH1 hkeys1 hdom1 hb0 hb1 hb2 hb3 htd hwft htfo hi1
    refine ⟨σ2, i2, ?_, hi2, hG2, hmem2.trans hmem1, hout2.trans hout1, hpc2, hmi2, hGH2, ?_⟩
    · have h := hsteps1.trans (RunT.single hstep2 hpc1')
      have e : u + body.length + 1 = u + (body.length + 1) := by omega
      rw [e] at h
      exact h
    · intro R hn hw
      exact (hframe2 R hn).trans (hframe1 R hn hw)


theorem bblocks_run_btT (bs : List BBlock) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (lds : List (List (BitVec 8))) (mc m : Std.ExtHashMap Nat (BitVec 8))
      (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m →
    (∀ j, j < tohostAddr → m[j]? = mc[j]?) →
    GHolds σ L → KeysOK (keysG L) → (∀ n ∈ dom, n ∈ keysG L) →
    ChainFacts mc m L lds bs → ChainOK pc0 dom bs → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      RunT ⟨σ, i, u⟩ (pcsC bs) ⟨σ', i', u + chainLen bs⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = memChain bs m L lds ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (chainEndPC pc0 L lds bs) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runChain bs L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction bs with
  | nil =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem _ hL _ _ _ _ hi
    exact ⟨σ, i, RunT.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons b bs ih =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hfacts hwf hi
    have hfacts' : BBlockFacts mc m L lds b ∧
        ChainFacts mc (writeLog m (wlogM b.body L lds)) (runGM b.body L lds)
          (ldsRunM b.body lds) bs := hfacts
    obtain ⟨hbf, hcf⟩ := hfacts'
    have hwf' : BBlockOK pc0 dom b ∧ TermChainO b.term bs ∧
        ChainOK (nextPC0 pc0 b) (domRunM b.body dom) bs := hwf
    obtain ⟨hbo, htc, hco⟩ := hwf'
    obtain ⟨σ1, i1, hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1, hframe1⟩ :=
      bblock_run_btT b σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hbf hbo hi
    cases bs with
    | nil =>
      exact ⟨σ1, i1, by simpa [pcsC, chainLen] using hsteps1, hi1, hG1, hmem1, hout1, hpc1, hmi1, hGH1,
        fun R hn hw =>
          hframe1 R hn (fun n h => hw n (List.mem_append_left [] h))⟩
    | cons b2 rest =>
      obtain ⟨vm1, hmi1'⟩ := hmi1
      have hpc1' : σ1.regs.get? Register.PC = some (nextPC0 pc0 b) := by
        rw [endPCB_eq_nextPC0_bt b pc0 L lds (htc : TermNotJrO b.term)] at hpc1
        exact hpc1
      have hlow1 : ∀ j, j < tohostAddr → (writeLog m (wlogM b.body L lds))[j]? = mc[j]? :=
        fun j hj => (writeLog_wlog_low_bt mc b.body m L lds hbf.1 j hj).trans (hlow j hj)
      have hkeys1 : KeysOK (keysG (runGM b.body L lds)) :=
        keysOK_runGM_bt b.body pc0 dom L lds hbo.1 hkeys
      have hdom1 : ∀ n ∈ domRunM b.body dom, n ∈ keysG (runGM b.body L lds) :=
        domRun_keys_bt b.body L lds dom hdom
      obtain ⟨σf, i', hstepsf, hif, hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + blenB b) (nextPC0 pc0 b) vm1 (runGM b.body L lds)
          (ldsRunM b.body lds) mc (writeLog m (wlogM b.body L lds)) (domRunM b.body dom)
          hG1 hpc1' hmi1' hmem1 hlow1 hGH1 hkeys1 hdom1 hcf hco hi1
      refine ⟨σf, i', ?_, hif, hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have h := hsteps1.trans hstepsf
        rw [← pcsC_cons] at h
        have e : u + blenB b + chainLen (b2 :: rest)
            = u + (blenB b + chainLen (b2 :: rest)) := by omega
        rw [e] at h
        exact h
      · intro R hn hw
        exact (hframef R hn (fun n h => hw n (List.mem_append_right _ h))).trans
          (hframe1 R hn (fun n h => hw n (List.mem_append_left _ h)))


theorem segEval_selected_framedT
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 vm : BitVec 64) (foot : Nat → Prop) (keep : Register → Bool)
    (selected : GRegs) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some pc0)
    (hmi : c.σ.regs.get? Register.minstret = some vm)
    (hL : GHolds c.σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs) (hi : c.tick < 2)
    (hfoot : ∀ k, ¬ foot k → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)[k]?)
    (hnoise : ∀ rr ∈ noiseRegs, keep rr = false)
    (havoid : WrChainAvoids keep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init L lds)).regs selected) :
    ∃ c', SelectedFramedSegResult bs L lds pc0 foot keep selected c c' ∧ RunT c (pcsC bs) c' := by
  obtain ⟨sigma', i', hrun, hi', hG', hmem', hout', hpc', hmi', hregs', hframe'⟩ :=
    bblocks_run_btT bs c.σ c.tick c.steps pc0 vm L lds c.σ.mem c.σ.mem (keysG L)
      hG hpc hmi rfl (fun _ _ => rfl) hL hkeys (fun _ h => h) hfacts hwf hi
  let c' : Config := ⟨sigma', i', c.steps + chainLen bs⟩
  refine ⟨c', ?_, hrun⟩
  refine
    { steps := hrun.steps
      good := hG'
      tick := hi'
      mem := by rw [writeLog_evalBlocks_init]; exact hmem'
      outside := ?_
      output := hout'
      pc := hpc'
      minstret := hmi'
      selected_regs := by
        refine gholds_selected hproj ?_
        rw [evalBlocks_regs]; exact hregs'
      reg_frame := ?_ }
  · intro k hk
    have hm : sigma'.mem = writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log := by
      rw [writeLog_evalBlocks_init]; exact hmem'
    exact (hfoot k hk).trans (congrArg (fun m : Vsa.MemRepr.Mem => m[k]?) hm).symm
  · intro R hR
    exact frame_of_wrChain_avoids (P := keep) hnoise havoid hframe' R hR

end Vsa.Sim
