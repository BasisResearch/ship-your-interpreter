import VsaIris.Vsa.SymRun
import VsaIris.Vsa.SegRun
import Vsa.Sim.SnprintfSitesRet5

/-!
# Indirect calls in symbolic runs

`TKind` has no linking `jalr` (an indirect call). VSA proves one by a step
observation (`stepObs_jalr`: one `Step` whose post-state reads like
`sigmaPost_jalr`). `SymObs.lean` does this for `sltu`/`sltiu`; this file does
it for the indirect call:

* `NStep` / `swp_nstep`: one observed step that writes one GPR and moves the
  PC anywhere (`SymObs.swp_alu` is the `i + 4` case);
* `JalrObs` / `nstep_of_jalrObs`: a linking indirect call through a register
  holding the target (`_svfprintf_r`'s call of the locale's `mbtowc` hook).

A site then only supplies its observation (a generated one-liner over VSA's
`stepObs_*`), not a copy of the framing argument.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config MState)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem noise_ne_htif : ∀ r ∈ noiseRegs, (r == Register.htif_payload_writes) = false := by
  decide

theorem addInt_four (i : Nat) : BitVec.addInt (BitVec.ofNat 64 i) 4 = BitVec.ofNat 64 (i + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.addInt, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (BitVec.ofInt 64 4).toNat = 4 from rfl]
  omega

section Alu

variable {live : Nat → Prop}

theorem pc_of_vsaOk {c : Config} (hok : VsaOk live c) {i : Nat}
    (hpc : vsaReg c VsaIris.PC = BitVec.ofNat 64 i) :
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
  obtain ⟨w, hw⟩ := hok.good.PC
  have h : pcVal c.σ = BitVec.ofNat 64 i := hpc
  unfold pcVal at h
  rw [hw] at h ⊢
  exact congrArg some h

/-- One observational step at `i` that writes the GPR `rd := val` and moves
the PC to `npc` (`AluStep` with any successor PC: `npc = i + 4` for an ALU
instruction, the target for an indirect call). -/
def NStep (live : Nat → Prop) (i : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (rd : Nat) (val npc : BitVec 64) : Prop :=
  ∀ c : Config, VsaOk live c → vsaReg c VsaIris.PC = BitVec.ofNat 64 i →
    (∀ q ∈ RR, vsaReg c q.1 = q.2.2) → (∀ q ∈ MR, (vsaModel live).mem c q.1 = q.2.2) →
    ∃ c' : Config, Vsa.Machine.Step c c' ∧ VsaOk live c' ∧
      vsaReg c' VsaIris.PC = npc ∧ vsaReg c' rd = val ∧
      (∀ k, k ≠ VsaIris.PC → k ≠ rd → vsaReg c' k = vsaReg c k) ∧
      (∀ a, (vsaModel live).mem c' a = (vsaModel live).mem c a) ∧
      (vsaModel live).out c' = (vsaModel live).out c

/-- **An `NStep` as a one-step `RunFact`.** -/
theorem runFact_of_nstep {i : Nat}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {rd : Nat} {old val npc : BitVec 64} (h : NStep live i RR MR rd val npc) :
    RunFact (vsaModel live) 0 RR MR
      [(VsaIris.PC, BitVec.ofNat 64 i, npc), (rd, old, val)] [] := by
  intro c hok hfoot
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hpc : vsaReg c VsaIris.PC = BitVec.ofNat 64 i := hRW _ List.mem_cons_self
  obtain ⟨c', hstep, hok', hpc', hrd', hframe, hmem, hout⟩ := h c hok hpc hRR hMR
  refine ⟨c', ReachesN.succ (M := vsaModel live) (vsaStep_of_step hstep)
    (ReachesN.zero (M := vsaModel live) c'), hok', ⟨?_, ?_, ?_, ?_⟩, hout⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpc'
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hrd'
      · cases hq
  · intro k hk
    exact hframe k (fun e => hk _ List.mem_cons_self e.symm)
      (fun e => hk _ (.tail _ List.mem_cons_self) e.symm)
  · intro q hq; cases hq
  · intro a _; exact hmem a

variable {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **One observational step** as one `SWP` step: `rd` takes the value and
the run continues at `npc`. -/
theorem swp_nstep {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (rd : Nat) (val npc : BitVec 64) (hexec : NStep live i RR MR rd val npc)
    (hMR : ∀ p ∈ MR, (p.1, p.2.2) ∈ text)
    (hRR : ∀ p ∈ RR, p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2.2)
    (hPC : VsaIris.PC ∈ rs) (hrd : rd ∈ rs) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q npc (upd R rd val) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_nstep (old := rv rd) hexec) (fun p hp => ?_) (fun p hp => .inl (hMR p hp)) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hRR p hp
    exact .inr ⟨h1, by rw [hm.regs _ h1 h2, h3]⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hrd, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = rd
      · subst hr1
        rw [upd_same]
        exact h1 (r, rv r, val) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

/-- The step frame of a linking `jalr` (the twin of `StepFrameOut.of_jal`). -/
theorem stepFrameOut_of_jalr {σ σ' : MState} {pc vm tgt : BitVec 64}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd link)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := hobs.out
  frame := by
    intro R hR
    have h := all_notin (S := rd :: noiseRegs)
      (List.all_eq_true.mpr (fun r hr => by simpa using hR r hr))
    have hrd : (rd == R) = false := h _ (List.mem_cons_self ..)
    have hms : (Register.minstret == R) = false := h _ (by simp [noiseRegs])
    have hpc : (Register.PC == R) = false := h _ (by simp [noiseRegs])
    have hnp : (Register.nextPC == R) = false := h _ (by simp [noiseRegs])
    have hmi' : (Register.minstret_increment == R) = false := h _ (by simp [noiseRegs])
    have hmc : (Register.mcycle == R) = false := h _ (by simp [noiseRegs])
    have hmt : (Register.mtime == R) = false := h _ (by simp [noiseRegs])
    have hmip : (Register.mip == R) = false := h _ (by simp [noiseRegs])
    exact (hobs.1 R hmc hmt hmip).trans
      (get?_sigmaPost_jalr σ pc vm tgt rd link R hms hpc hrd hnp hmi')

/-- A step observation of a linking indirect call at `i` through the GPR `rs`
holding `tgt`: `ra := i + 4`, `PC := tgt`. -/
def JalrObs (i : Nat) (code : List (BitVec 8)) (rs : Nat) (tgt : BitVec 64) : Prop :=
  ∀ (σ : MState) (ti u : Nat) (vm : BitVec 64), GoodState σ →
    σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
    σ.regs.get? Register.minstret = some vm → gprGet σ rs = some tgt →
    (∀ p ∈ codeFoot i code, σ.mem[p.1]? = some p.2.2) → ti < 2 →
    ∃ (σ' : MState) (i' : Nat), Vsa.Machine.Step ⟨σ, ti, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧
      GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jalr σ (BitVec.ofNat 64 i) vm tgt Register.x1
        (BitVec.addInt (BitVec.ofNat 64 i) 4))

/-- **A linking indirect call is an `NStep`** writing `ra` and jumping to `tgt`. -/
theorem nstep_of_jalrObs {i : Nat} {code : List (BitVec 8)} {rs : Nat} {tgt : BitVec 64}
    (hlive : ∀ p ∈ codeFoot i code, live p.1) (hobs : JalrObs i code rs tgt)
    (hrs1 : 1 ≤ rs) (hrs31 : rs ≤ 31) :
    NStep live i [(rs, DFrac.own 1, tgt)] (codeFoot i code) 1 (BitVec.ofNat 64 (i + 4)) tgt := by
  intro c hok hpc hRRv hMR
  have hread := code_present hok _ hMR hlive
  obtain ⟨vm, hvm⟩ := hok.good.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs'⟩ :=
    hobs c.σ c.tick c.steps vm hok.good (pc_of_vsaOk hok hpc) hvm
      (gprGet_eq_of_vsaReg hok hrs1 hrs31 (hRRv _ List.mem_cons_self)) hread hok.tick
  have hframe := stepFrameOut_of_jalr hobs'
  have hnoise : ∀ n, n < 32 → 1 ≤ n → ∀ R ∈ noiseRegs, (R == gprReg n) = false := by decide
  have hgprFrame : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 1 → gprGet σ' n = gprGet c.σ n := by
    intro n h1 h31 hn
    refine gprGet_of_frame (wrs := [1]) n h1 h31 (hnoise n (by omega) h1)
      (fun mm hmm => ?_) (fun R hR hw => hframe.frame R fun rr hrr => ?_)
    · rcases List.mem_cons.mp hmm with rfl | hmm
      · exact gprReg_beq_false 1 (by omega) n (by omega) (by omega) h1 (fun e => hn e.symm)
      · cases hmm
    · rcases List.mem_cons.mp hrr with rfl | hrr
      · exact hw 1 List.mem_cons_self
      · exact hR rr hrr
  have hra : gprGet σ' 1 = some (BitVec.ofNat 64 (i + 4)) := by
    have := obs_jalr_rd hobs' (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [addInt_four] at this
    exact this
  refine ⟨⟨σ', i', c.steps + 1⟩, hstep, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, ?_, fun a => ?_, ?_⟩
  · show (gprGet σ' n).isSome = true
    by_cases hn : n = 1
    · subst hn; rw [hra]; rfl
    · rw [hgprFrame n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome
    rw [hmem']; exact hok.live a ha
  · rw [hframe.frame Register.htif_payload_writes (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · exact noise_ne_htif r hr)]
    exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal
    rw [obs_jalr_pc hobs']
    rfl
  · change vsaReg ⟨σ', i', c.steps + 1⟩ 1 = _
    rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
    change (gprGet σ' 1).getD 0 = _
    rw [hra]; rfl
  · intro k hkpc hk1
    change vsaReg ⟨σ', i', c.steps + 1⟩ k = vsaReg c k
    rw [vsaReg_gpr hkpc, vsaReg_gpr (c := c) hkpc]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · rw [hgprFrame k hr.1 hr.2 hk1]
    · rw [gprGet_none (by unfold VsaIris.PC at hkpc; omega),
        gprGet_none (by unfold VsaIris.PC at hkpc; omega)]
  · change (σ'.mem[a]?).getD 0 = ((c.σ.mem)[a]?).getD 0
    rw [hmem']
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output
    rw [hframe.out]

end Alu

end VsaIris.Sym
