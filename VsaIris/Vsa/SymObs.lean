import VsaIris.Vsa.SegRun
import VsaIris.Vsa.SymRun
import Vsa.Sim.Muldi3Spec
import VsaIris.Vsa.Console

/-!
# Observed ALU steps in symbolic runs

The reflected block model (`MKind`, `Vsa/Sim/BlockMem.lean`) has no `sltu`
or `sltiu`, so `snez`/`seqz` have no reflected segment. VSA proves such an
instruction by observation: `stepObs_alu` gives ONE step that advances the PC
by four, writes ONE GPR and leaves memory and every other register alone
(`ReadsLikePost σ' (sigmaPost_alu …)`).

* `aluStep_of_obs`: such an observation, stated at every well-formed state
  whose source registers and code bytes hold, is H3's `Inst.AluStep` for any
  destination register (H3's `snezAluStep` and H5's `aluA0_runFact` are the
  `a0` instances written by hand).
* `swp_alu`: an `AluStep` as one step of a symbolic run (`SWP`), the
  `swp_jal` of an ALU instruction outside the block model.

The step-table generators (`scripts/gen_interp_steps.py`) emit, per `sltu`/
`sltiu` instruction, the observation (`stepObs_alu` + the decode table + the
`execute_*_char` lemma) and an `itO_<pc>` step lemma over these two.
-/

namespace VsaIris.Sym

open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim VsaIris.Inst VsaIris.MallocFast

theorem gpr_avoids_noiseO : ∀ n, n < 32 → 1 ≤ n → ∀ rr ∈ noiseRegs, (rr == gprReg n) = false := by
  decide

theorem gpr_htif : ∀ n, n < 32 → 1 ≤ n → (gprReg n == Register.htif_payload_writes) = false := by
  decide

theorem gpr_avoids_noiseO' : ∀ n, n < 32 → 1 ≤ n → ∀ rr ∈ noiseRegs, (gprReg n == rr) = false := by
  decide

/-- The destination of an observed ALU step, as a `gprGet` read (cased on the
index: `RegisterType (gprReg rd)` is `BitVec 64` only per index). -/
theorem gprGet_obs_rd {σ' σ : MState} {pc vm : BitVec 64} {v : BitVec 64} :
    ∀ rd, 1 ≤ rd → rd ≤ 31 →
      ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg rd) (gprRT rd v)) → gprGet σ' rd = some v
  | 1, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 2, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 3, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 4, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 5, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 6, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 7, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 8, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 9, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 10, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 11, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 12, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 13, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 14, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 15, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 16, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 17, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 18, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 19, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 20, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 21, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 22, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 23, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 24, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 25, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 26, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 27, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 28, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 29, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 30, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 31, _, _, h => obs_alu_rd h (by decide) (by decide) (by decide) (by decide) (by decide)
  | 0, h, _, _ => absurd h (by decide)
  | _ + 32, _, h, _ => absurd h (by omega)

/-- **An observed ALU step writing GPR `rd`, as an `AluStep`.** `hsite` is the
observation at every well-formed state parked at `i` whose source registers
`RR` (GPRs) and read bytes `MR` hold (the generated per-instruction proof). -/
theorem aluStep_of_obs {live : Nat → Prop} {i : Nat} {RR : List (Nat × DFrac × BitVec 64)}
    {MR : List (Nat × DFrac × BitVec 8)} {rd : Nat} {val : BitVec 64}
    (hrd1 : 1 ≤ rd) (hrd31 : rd ≤ 31) (hRRk : ∀ q ∈ RR, 1 ≤ q.1 ∧ q.1 ≤ 31)
    (hlive : ∀ p ∈ MR, live p.1)
    (hsite : ∀ c : Config, GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
      (∀ q ∈ RR, gprGet c.σ q.1 = some q.2.2) → (∀ q ∈ MR, c.σ.mem[q.1]? = some q.2.2) →
      ∃ (σ' : MState) (i' : Nat) (vm : BitVec 64),
        Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_alu c.σ (BitVec.ofNat 64 i) vm (gprReg rd) (gprRT rd val))) :
    AluStep live i RR MR rd val := by
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
  have hrdn : ∀ rr ∈ noiseRegs, (gprReg rd == rr) = false :=
    gpr_avoids_noiseO' rd (by omega) hrd1
  have hother : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ ([rd] : List Nat), (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    rw [hobs.1 R (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact get?_sigmaPost_alu _ _ _ _ _ R (hn _ (by decide)) (hn _ (by decide))
      (hw rd (by simp)) (hn _ (by decide)) (hn _ (by decide))
  have hgpr : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ rd → gprGet σ' n = gprGet c.σ n := fun n h1 h31 hne =>
    gprGet_of_frame n h1 h31 (gpr_avoids_noiseO n (by omega) h1)
      (fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm
        exact gprReg_beq_false m (by omega) n (by omega) hrd1 h1 (Ne.symm hne))
      hother
  have hrdg : gprGet σ' rd = some val := gprGet_obs_rd rd hrd1 hrd31 hobs
  refine ⟨⟨σ', i', c.steps + 1⟩, hs, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, fun k hk1 hk2 => ?_, fun a => ?_, ?_⟩
  · by_cases hn : n = rd
    · subst hn; rw [hrdg]; rfl
    · rw [hgpr n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome; rw [hmem]; exact hok.live a ha
  · rw [hother _ (by decide) (fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact gpr_htif _ (by omega) (by omega))]
    exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal; rw [obs_alu_pc hobs, VsaIris.Inst.addInt_ofNat_four]; rfl
  · change vsaReg _ rd = val
    rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
    change (gprGet σ' rd).getD 0 = val
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

/-- **An observed ALU step in a symbolic run** (`swp_jal`'s twin): the
destination `rd` takes `val`, the PC advances by four. `ks` are the source
registers the observation reads, off the symbolic register file `R`. -/
theorem swp_alu {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Vsa.MemRepr.Mem}
    (i : Nat) (code : List (BitVec 8)) (rd : Nat) (ks : List Nat) (val : BitVec 64)
    (hstep : AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i code) rd val)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text)
    (hPC : VsaIris.PC ∈ rs) (hrd : rd ∈ rs) (hrdPC : rd ≠ VsaIris.PC)
    (hks : ∀ k ∈ ks, k ∈ rs ∧ k ≠ VsaIris.PC) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q (BitVec.ofNat 64 (i + 4)) (upd R rd val) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_aluStep (old := rv rd) hstep) ?_ (fun p hp => .inl (hcode p hp)) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact .inr ⟨(hks k hk).1, hm.regs k (hks k hk).1 (hks k hk).2⟩
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

end VsaIris.Sym
