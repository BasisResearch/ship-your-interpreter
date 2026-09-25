import VsaIris.Vsa.SymObs
import Vsa.Sim.SnprintfSitesRet5

/-!
# Indirect calls in symbolic runs (lane N1)

`jalr ra, imm(rs1)` (a call through a function pointer: `__sflush_r` calls
`fp->_write`) is outside the reflected block model (`TKind` has `jr` only).
VSA proves it by observation: `stepObs_jalr` gives ONE step to
`(rs1 + imm) & ~1` that writes the link into `ra` and leaves memory and every
other register alone.

* `JalrStep`: such a step at every well-formed state parked at `i` whose
  source registers and code bytes hold;
* `jalrStep_of_obs`: the observation (generated per site) as a `JalrStep`;
* `swp_jalr`: a `JalrStep` as one step of a symbolic run (`swp_jal`'s twin
  with a register target).
-/

namespace VsaIris.Sym

open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim VsaIris.Inst VsaIris.MallocFast

/-- One indirect call at `i`: the PC becomes `tgt`, `ra` the link, nothing
else changes. -/
def JalrStep (live : Nat → Prop) (i : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (tgt link : BitVec 64) : Prop :=
  ∀ c : Config, VsaOk live c → vsaReg c VsaIris.PC = BitVec.ofNat 64 i →
    (∀ q ∈ RR, vsaReg c q.1 = q.2.2) → (∀ q ∈ MR, (vsaModel live).mem c q.1 = q.2.2) →
    ∃ c' : Config, Vsa.Machine.Step c c' ∧ VsaOk live c' ∧
      vsaReg c' VsaIris.PC = tgt ∧ vsaReg c' 1 = link ∧
      (∀ k, k ≠ VsaIris.PC → k ≠ 1 → vsaReg c' k = vsaReg c k) ∧
      (∀ a, (vsaModel live).mem c' a = (vsaModel live).mem c a) ∧
      (vsaModel live).out c' = (vsaModel live).out c

/-- **An observed `jalr` as a `JalrStep`.** `hsite` is the observation at
every well-formed state parked at `i` whose source registers `RR` (GPRs) and
code bytes `MR` hold (the generated per-site proof). -/
theorem jalrStep_of_obs {live : Nat → Prop} {i : Nat} {RR : List (Nat × DFrac × BitVec 64)}
    {MR : List (Nat × DFrac × BitVec 8)} {tgt link : BitVec 64}
    (hRRk : ∀ q ∈ RR, 1 ≤ q.1 ∧ q.1 ≤ 31)
    (hlive : ∀ p ∈ MR, live p.1)
    (hsite : ∀ c : Config, GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
      (∀ q ∈ RR, gprGet c.σ q.1 = some q.2.2) → (∀ q ∈ MR, c.σ.mem[q.1]? = some q.2.2) →
      ∃ (σ' : MState) (i' : Nat) (vm : BitVec 64),
        Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jalr c.σ (BitVec.ofNat 64 i) vm tgt Register.x1 link)) :
    JalrStep live i RR MR tgt link := by
  intro c hok hpc hRR hMR
  have hpcσ : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
    obtain ⟨w, hw⟩ := hok.good.PC
    have h : pcVal c.σ = BitVec.ofNat 64 i := hpc
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have hRRσ : ∀ q ∈ RR, gprGet c.σ q.1 = some q.2.2 := fun q hq =>
    gprGet_eq_of_vsaReg hok (hRRk q hq).1 (hRRk q hq).2 (hRR q hq)
  obtain ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩ :=
    hsite c hok.good hok.tick hpcσ hRRσ (code_present hok MR hMR hlive)
  have hother : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ ([1] : List Nat), (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    rw [hobs.1 R (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact post_jalr_other _ _ _ _ _ _ R (hn _ (by decide)) (hn _ (by decide))
      (hw 1 (by simp)) (hn _ (by decide)) (hn _ (by decide))
  have hgpr : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 1 → gprGet σ' n = gprGet c.σ n := fun n h1 h31 hne =>
    gprGet_of_frame n h1 h31 (gpr_avoids_noiseO n (by omega) h1)
      (fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm
        exact gprReg_beq_false 1 (by omega) n (by omega) (by omega) h1 (Ne.symm hne))
      hother
  have hrdg : gprGet σ' 1 = some link :=
    obs_jalr_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨σ', i', c.steps + 1⟩, hs, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, fun k hk1 hk2 => ?_, fun a => ?_, ?_⟩
  · by_cases hn : n = 1
    · subst hn; rw [hrdg]; rfl
    · rw [hgpr n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome; rw [hmem]; exact hok.live a ha
  · rw [hother _ (by decide) (fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact gpr_htif _ (by omega) (by omega))]
    exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal; rw [obs_jalr_pc hobs]; rfl
  · change vsaReg _ 1 = link
    rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
    change (gprGet σ' 1).getD 0 = link
    rw [hrdg]; rfl
  · change vsaReg _ k = vsaReg c k
    rw [vsaReg_gpr hk1, vsaReg_gpr (c := c) hk1]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · change (gprGet σ' k).getD 0 = _
      rw [hgpr k hr.1 hr.2 hk2]
    · change (gprGet σ' k).getD 0 = _
      rw [gprGet_none (by unfold VsaIris.PC at hk1; omega),
        gprGet_none (by unfold VsaIris.PC at hk1; omega)]
  · change (σ'.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0
    rw [hmem]
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output; rw [hobs.2]

/-- **An indirect call as a one-step `RunFact`.** -/
theorem runFact_of_jalrStep {live : Nat → Prop} {i : Nat}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {tgt link old : BitVec 64} (h : JalrStep live i RR MR tgt link) :
    RunFact (vsaModel live) 0 RR MR
      [(VsaIris.PC, BitVec.ofNat 64 i, tgt), (1, old, link)] [] := by
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

section SWP

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **An indirect call in a symbolic run**: `ra` takes the link, the run
continues at the target. -/
theorem swp_jalr {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Vsa.MemRepr.Mem}
    (i : Nat) (code : List (BitVec 8)) (ks : List Nat) (tgt : BitVec 64)
    (hstep : JalrStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i code) tgt
      (BitVec.ofNat 64 (i + 4)))
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text)
    (hPC : VsaIris.PC ∈ rs) (hra : 1 ∈ rs)
    (hks : ∀ k ∈ ks, k ∈ rs ∧ k ≠ VsaIris.PC) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q tgt (upd R 1 (BitVec.ofNat 64 (i + 4))) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_jalrStep (old := rv 1) hstep) (fun p hp => ?_) (fun p hp => .inl (hcode p hp)) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact .inr ⟨(hks k hk).1, hm.regs _ (hks k hk).1 (hks k hk).2⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hra, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = 1
      · subst hr1
        rw [upd_same]
        exact h1 (1, rv 1, BitVec.ofNat 64 (i + 4)) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end SWP

end VsaIris.Sym
