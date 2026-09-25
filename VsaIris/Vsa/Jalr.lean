import VsaIris.Vsa.SymRun
import Vsa.Sim.SnprintfSitesRet5

/-!
# Linking `jalr` (lane N3)

newlib calls through function pointers: `exit`'s `jalr a5` (the stdio exit
handler), `_fwalk_sglue`'s `jalr s5` (`_fclose_r`), `_fclose_r`'s `jalr a5`
(the `FILE`'s close callback), `__sfvwrite_r`'s write callback, and
`_vfprintf_r`'s `jalr s0` (the locale's `mbtowc`). The reflected block model
has only `jalr x0` (`TKind.jr`), so a linking `jalr ra,0(rs1)` is one observed
step (M3's `stepObs_jalr`):

* `JalrExec`: the Iris exec fact, `JalExec` with the target read from `rs1`;
* `jalrStep_of_obs`: VSA's `JalStep` (the bridge record `jalExec_of_site`
  consumes) from a `jalr` observation, once;
* `jalrExec_of_site`: `jalExec_of_site` with the target read from `rs1`;
* `swp_jalr`: the step of a symbolic run (`SWP`).

The per-site facts `jalrx_<pc>` are generated with the step tables.
-/

namespace VsaIris.Inst

open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim

/-- The exec fact for `jalr ra, 0(rs1)` at `i`: from any well-formed state
parked at `i` whose `rs1` holds an aligned `t`, one step to `t` with the
link `i + 4` in `ra`, nothing else changed, nothing printed. -/
def JalrExec (M : MachineModel) (i : Nat) (code : List (BitVec 8)) (rs1 : Nat) : Prop :=
  ∀ v t σ, M.ok σ → t.toNat % 4 = 0 →
    FootHolds (M := M) σ [(rs1, DFrac.own 1, t)] (codeFoot i code)
      [(VsaIris.PC, BitVec.ofNat 64 i, t), (VsaIris.ra, v, BitVec.ofNat 64 (i + 4))] [] →
    ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧
      LocalStep (M := M) σ σ'
        [(VsaIris.PC, BitVec.ofNat 64 i, t), (VsaIris.ra, v, BitVec.ofNat 64 (i + 4))] [] ∧
      M.out σ' = M.out σ

/-- **`JalStep` from a linking `jalr` observation** (the mirror of
`jalStep_of_obs`). -/
theorem jalrStep_of_obs {σp σ2 : MState} {ip up i2 : Nat} {pc vm tgt link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2 (sigmaPost_jalr σp pc vm tgt Register.x1 link)) :
    JalStep tgt link σp ip up := by
  refine ⟨σ2, i2, hstep, hi2, hG2, hmem, obs_jalr_pc hobs,
    obs_jalr_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_jalr_minstret hobs, ?_, ?_⟩
  · intro n hn1 hn31 hne w hw
    match n, hn1, hn31, hne, hw with
    | 0, h, _, _, _ => exact absurd h (by omega)
    | 1, _, _, hne, _ => exact absurd rfl hne
    | 2, _, _, _, hw => exact obs_jalr_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 3, _, _, _, hw => exact obs_jalr_other hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 4, _, _, _, hw => exact obs_jalr_other hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 5, _, _, _, hw => exact obs_jalr_other hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 6, _, _, _, hw => exact obs_jalr_other hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 7, _, _, _, hw => exact obs_jalr_other hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 8, _, _, _, hw => exact obs_jalr_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 9, _, _, _, hw => exact obs_jalr_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 10, _, _, _, hw => exact obs_jalr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 11, _, _, _, hw => exact obs_jalr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 12, _, _, _, hw => exact obs_jalr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 13, _, _, _, hw => exact obs_jalr_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 14, _, _, _, hw => exact obs_jalr_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 15, _, _, _, hw => exact obs_jalr_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 16, _, _, _, hw => exact obs_jalr_other hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 17, _, _, _, hw => exact obs_jalr_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 18, _, _, _, hw => exact obs_jalr_other hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 19, _, _, _, hw => exact obs_jalr_other hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 20, _, _, _, hw => exact obs_jalr_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 21, _, _, _, hw => exact obs_jalr_other hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 22, _, _, _, hw => exact obs_jalr_other hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 23, _, _, _, hw => exact obs_jalr_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 24, _, _, _, hw => exact obs_jalr_other hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 25, _, _, _, hw => exact obs_jalr_other hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 26, _, _, _, hw => exact obs_jalr_other hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 27, _, _, _, hw => exact obs_jalr_other hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 28, _, _, _, hw => exact obs_jalr_other hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 29, _, _, _, hw => exact obs_jalr_other hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 30, _, _, _, hw => exact obs_jalr_other hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 31, _, _, _, hw => exact obs_jalr_other hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | k+32, _, h, _, _ => exact absurd h (by omega)
  · intro R hR
    exact (hobs.1 R (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide))).trans
      (get?_sigmaPost_jalr σp pc vm tgt Register.x1 link R
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)))

/-- The console frame of a linking `jalr` step, from its observation. -/
theorem stepConFrame_of_jalrObs {σp σ2 : MState} {ip up i2 : Nat} {pc vm tgt link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩)
    (hobs : ReadsLikePost σ2 (sigmaPost_jalr σp pc vm tgt Register.x1 link)) :
    StepConFrame σp ip up :=
  stepConFrame_of_obs hstep hobs rfl
    (get?_sigmaPost_jalr σp pc vm tgt Register.x1 link _ (by decide) (by decide) (by decide)
      (by decide) (by decide))

/-- **A linking `jalr` site as an Iris exec fact** (`jalExec_of_site` with the
target read from `rs1`). -/
theorem jalrExec_of_site (live : Nat → Prop) (i : Nat) (code : List (BitVec 8)) (rs1 : Nat)
    (h1 : 1 ≤ rs1) (h31 : rs1 ≤ 31)
    (hlive : ∀ p ∈ codeFoot i code, live p.1)
    (hsite : ∀ (c : Config) (t : BitVec 64), GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
      (∀ p ∈ codeFoot i code, c.σ.mem[p.1]? = some p.2.2) →
      gprGet c.σ rs1 = some t → t.toNat % 4 = 0 →
      JalStep t (BitVec.ofNat 64 (i + 4)) c.σ c.tick c.steps ∧
        StepConFrame c.σ c.tick c.steps) :
    JalrExec (vsaModel live) i code rs1 := by
  intro v t c hok ht hfoot
  have hok : VsaOk live c := hok
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hpc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = _ at h
    obtain ⟨w, hw⟩ := hok.good.PC
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have hrs : gprGet c.σ rs1 = some t :=
    gprGet_eq_of_vsaReg hok h1 h31 (hRR _ List.mem_cons_self)
  obtain ⟨⟨σ2, i2, hs, hi2, hG2, hmem, hpc2, hra2, _, hnonra, _⟩, hcon⟩ :=
    hsite c t hok.good hok.tick hpc (code_present hok _ hMR hlive) hrs ht
  obtain ⟨hout2, hpw2⟩ := hcon _ hs
  have hra2' : gprGet σ2 1 = some (BitVec.ofNat 64 (i + 4)) := hra2
  have hframe : ∀ n, n ≠ 1 → gprGet σ2 n = gprGet c.σ n := by
    intro n hn
    by_cases hr : 1 ≤ n ∧ n ≤ 31
    · have hs := hok.gpr n hr.1 hr.2
      cases hg : gprGet c.σ n with
      | none => rw [hg] at hs; cases hs
      | some w => exact hnonra n hr.1 hr.2 hn w hg
    · rw [gprGet_none (by omega), gprGet_none (by omega)]
  refine ⟨⟨σ2, i2, c.steps + 1⟩, vsaStep_of_step hs, ⟨hG2, hi2, fun n h1 h31 => ?_, ?_,
    hpw2.trans hok.htifIdle⟩, ?_,
    show Vsa.Machine.output σ2 = Vsa.Machine.output c.σ by unfold Vsa.Machine.output; rw [hout2]⟩
  · by_cases hn : n = 1
    · subst hn; rw [hra2']; rfl
    · rw [hframe n hn]; exact hok.gpr n h1 h31
  · intro a ha
    change (σ2.mem[a]?).isSome
    rw [hmem]; exact hok.live a ha
  · constructor
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · change pcVal σ2 = t
        unfold pcVal; rw [hpc2]; rfl
      · change vsaReg _ 1 = _
        rw [vsaReg_gpr (by decide)]
        simp only [hra2']
        rfl
    · intro k hk
      have hk1 : VsaIris.PC ≠ k := hk _ List.mem_cons_self
      have hk2 : (1 : Nat) ≠ k := hk _ (.tail _ List.mem_cons_self)
      change vsaReg _ k = vsaReg c k
      rw [vsaReg_gpr (Ne.symm hk1), vsaReg_gpr (c := c) (Ne.symm hk1), hframe k (Ne.symm hk2)]
    · intro p hp; cases hp
    · intro k _
      change (σ2.mem[k]?).getD 0 = (c.σ.mem[k]?).getD 0
      rw [hmem]

end VsaIris.Inst

namespace VsaIris.Sym

open Iris Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

section SWP

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **One linking `jalr`** (an indirect call): `ra` takes the return address
and the run continues at the aligned target in `rs1`. -/
theorem swp_jalr {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (code : List (BitVec 8)) (rs1 : Nat)
    (hexec : JalrExec (vsaModel live) i code rs1)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text)
    (hPC : VsaIris.PC ∈ rs) (hra : VsaIris.ra ∈ rs) (hrs1 : rs1 ∈ rs) (hne : rs1 ≠ VsaIris.PC)
    (hpc : pc = BitVec.ofNat 64 i) (hal : (R rs1).toNat % 4 = 0)
    (hk : SWP live text rs S Q (R rs1) (upd R VsaIris.ra (BitVec.ofNat 64 (i + 4))) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (RR := [(rs1, DFrac.own 1, R rs1)])
    (MW := [])
    (RW := [(VsaIris.PC, BitVec.ofNat 64 i, R rs1),
      (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4))])
    (fun σ hok hf => by
      obtain ⟨σ', hs, hok', hloc⟩ := hexec (rv VsaIris.ra) (R rs1) σ hok hal hf
      exact ⟨σ', .succ hs (.zero _), hok', hloc⟩)
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact .inr ⟨hrs1, hm.regs rs1 hrs1 hne⟩)
    (fun p hp => .inl (hcode p hp)) ?_ (fun p hp => by cases hp) ?_⟩⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hra, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne' => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = VsaIris.ra
      · subst hr1
        rw [upd_same]
        exact h1 (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4)) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne')
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne' e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end SWP

end VsaIris.Sym
