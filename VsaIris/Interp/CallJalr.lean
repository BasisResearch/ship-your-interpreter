import VsaIris.Interp.CallRegs
import VsaIris.CallAbort
import Vsa.Sim.EvalCallNative3

/-!
# An indirect call (`jalr ra, 0(rs)`) (lane E4)

The call arm dispatches a native through its function pointer:
`0x800039f4 jalr a6` (`interp.c:174`, `callee.as.native.fn(in, argc, args,
line)`), with `a6` the value's third word, `N.addr f` for `.native f`.

* `JalrExec M i code rs tgt`: the exec fact of a linking `jalr` at `i` whose
  source register `rs` holds the target `tgt` — `JalExec` with `rs` as a read
  footprint entry (the shape of `RetExec`, which reads `ra`).
* `wp_jalrW`, `wp_callRW`, `wp_callAbortR`: the `jal` rules of `Call.lean` /
  `CallAbort.lean` for it, for either WP.
* `jalrExec_of_site` (VSA instance): a `jalr` site's per-state fact (`JalStep`
  and its console frame, from a state whose `rs` holds `tgt`) is the Iris
  `JalrExec`; `jalrx_800039f4` is the native dispatch's, over VSA's hand site
  `site_800039f4_nw` (`EvalCallNative3.lean`).
* `ms_callHelperR`, `ms_callAbortR`: the call from a symbolic run's state
  (`ms`), `a6` read from the run's register file (the `jalr` twins of
  `ms_callHelper`).
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section Generic

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- The exec fact for `jalr ra, 0(rs)` at `i`, `rs` holding `tgt`. -/
def JalrExec (M : MachineModel) (i : Nat) (code : List (BitVec 8)) (rs : Nat) (tgt : BitVec 64) :
    Prop :=
  ∀ v σ, M.ok σ → FootHolds (M := M) σ [(rs, DFrac.own 1, tgt)] (codeFoot i code)
      [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] →
    ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧
      LocalStep (M := M) σ σ' [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] ∧
      M.out σ' = M.out σ

/-- **JALR** to a call target, for either WP. -/
theorem wp_jalrW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {rs : Nat} {tgt v : BitVec 64} (hexec : JalrExec M i code rs tgt) :
    instrAt (GF := GF) i code ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ rs ↦ᵣ tgt ∗
      (PC ↦ᵣ tgt -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ rs ↦ᵣ tgt -∗ Wp.lat (Wp.W Φ)) ⊢ Wp.W Φ := by
  iintro ⟨#Hi, Hpc, Hra, Hrs, Hk⟩
  iapply Wp.local_stepL [(rs, DFrac.own 1, tgt)] (codeFoot i code)
    [(PC, BitVec.ofNat 64 i, tgt), (ra, v, BitVec.ofNat 64 (i + 4))] [] (fun σ hok h => hexec v σ hok h)
  unfold footPre footPost
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hpc Hra Hrs
  iintro ⟨⟨Hrs, -⟩, -, ⟨Hpc, Hra, -⟩, -⟩
  iapply Hk $$ Hpc Hra Hrs

/-- **Indirect call** into a function meeting `fnSpecAbort`, for either WP;
the source register is handed back into the precondition. -/
theorem wp_callAbortR (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {rs : Nat} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    {A X : IProp GF} (hexec : JalrExec M i code rs entry) :
    instrAt (GF := GF) i code ∗ fnSpecAbort Wp entry P Q A ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗
      ra ↦ᵣ v ∗ rs ↦ᵣ entry ∗ X ∗ (rs ↦ᵣ entry -∗ X -∗ P (BitVec.ofNat 64 (i + 4))) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold fnSpecAbort
  iintro ⟨#Hi, #Hspec, Hpc, Hra, Hrs, HX, HP, Hk⟩
  iapply wp_jalrW Wp hexec
  iframe Hi Hpc Hra Hrs
  iintro Hpc Hra Hrs
  iapply Wp.lat_intro
  ihave HP := HP $$ Hrs HX
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

/-- **Indirect call** into a function meeting `fnSpecW`, for either WP. -/
theorem wp_callRW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {rs : Nat} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    {X : IProp GF} (hexec : JalrExec M i code rs entry) :
    instrAt (GF := GF) i code ∗ fnSpecW Wp entry P Q ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗
      ra ↦ᵣ v ∗ rs ↦ᵣ entry ∗ X ∗ (rs ↦ᵣ entry -∗ X -∗ P (BitVec.ofNat 64 (i + 4))) ∗
      (PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold fnSpecW
  iintro ⟨#Hi, #Hspec, Hpc, Hra, Hrs, HX, HP, Hk⟩
  iapply wp_jalrW Wp hexec
  iframe Hi Hpc Hra Hrs
  iintro Hpc Hra Hrs
  iapply Wp.lat_intro
  ihave HP := HP $$ Hrs HX
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP Hk

end Generic

end VsaIris

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config Step MState)
open Vsa.Sim

/-- **A `jalr ra, 0(rs)` site as an Iris exec fact** (the twin of
`jalExec_of_site`): VSA's per-state fact, from any good state parked at `i`
whose `rs` holds `tgt`, with the site's bytes present. -/
theorem jalrExec_of_site (live : Nat → Prop) (i : Nat) (code : List (BitVec 8)) (rs : Nat)
    (tgt : BitVec 64) (hrs1 : 1 ≤ rs) (hrs31 : rs ≤ 31)
    (hlive : ∀ p ∈ codeFoot i code, live p.1)
    (hsite : ∀ c : Config, GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) → gprGet c.σ rs = some tgt →
      (∀ p ∈ codeFoot i code, c.σ.mem[p.1]? = some p.2.2) →
      JalStep tgt (BitVec.ofNat 64 (i + 4)) c.σ c.tick c.steps ∧
        StepConFrame c.σ c.tick c.steps) :
    JalrExec (vsaModel live) i code rs tgt := by
  intro v c hok hfoot
  have hok : VsaOk live c := hok
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hpc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = _ at h
    obtain ⟨w, hw⟩ := hok.good.PC
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have hrs : gprGet c.σ rs = some tgt :=
    gprGet_eq_of_vsaReg hok hrs1 hrs31 (hRR _ List.mem_cons_self)
  obtain ⟨⟨σ2, i2, hs, hi2, hG2, hmem, hpc2, hra2, _, hnonra, _⟩, hcon⟩ :=
    hsite c hok.good hok.tick hpc hrs (code_present hok _ hMR hlive)
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
    hpw2.trans hok.htifIdle⟩, ?_, show Vsa.Machine.output σ2 = Vsa.Machine.output c.σ by unfold Vsa.Machine.output; rw [hout2]⟩
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
      · change pcVal σ2 = tgt
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

/-- A linking `jalr`'s observation as VSA's `JalStep` (the twin of
`jalStep_of_obs`). -/
theorem jalrStep_of_obs {σp σ2 : MState} {ip up i2 : Nat} {pc vm tgt link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2 (sigmaPost_jalr σp pc vm tgt Register.x1 link)) :
    JalStep tgt link σp ip up := by
  have hother : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ ([1] : List Nat), (gprReg m == R) = false) → σ2.regs.get? R = σp.regs.get? R := by
    intro R hn hw
    rw [hobs.1 R (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact get?_sigmaPost_jalr _ _ _ _ _ _ R (hn _ (by decide)) (hn _ (by decide))
      (hw 1 (by simp)) (hn _ (by decide)) (hn _ (by decide))
  refine ⟨σ2, i2, hstep, hi2, hG2, hmem, obs_jalr_pc hobs,
    obs_jalr_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_jalr_minstret hobs, ?_, ?_⟩
  · intro n hn1 hn31 hne w hw
    rw [← hw]
    exact gprGet_of_frame n hn1 hn31 (VsaIris.Sym.gpr_avoids_noiseO n (by omega) hn1)
      (fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm
        exact gprReg_beq_false 1 (by omega) n (by omega) (by omega) hn1 (Ne.symm hne))
      hother
  · intro R hR
    exact (hobs.1 R (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide))).trans
      (get?_sigmaPost_jalr σp pc vm tgt Register.x1 link R
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)))

end VsaIris.Inst

namespace VsaIris.Sym

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim VsaIris.Inst

/-- **The native dispatch `jalr a6` (`0x800039f4`)** as an Iris exec fact,
for every 4-aligned target (a native's entry). -/
theorem jalrx_800039f4 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800039f4 [0xe7#8, 0x00#8, 0x08#8, 0x00#8], live p.1)
    (tgt : BitVec 64) (hal : tgt.toNat % 4 = 0) :
    JalrExec (vsaModel live) 0x800039f4 [0xe7#8, 0x00#8, 0x08#8, 0x00#8] 16 tgt := by
  refine jalrExec_of_site live _ _ 16 tgt (by decide) (by decide) hlive fun c hG hi hpc hrs hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800039f4, .discard, 0xe7#8) (by simp [codeFoot])
  have hb1 := hb (0x800039f5, .discard, 0x00#8) (by simp [codeFoot])
  have hb2 := hb (0x800039f6, .discard, 0x08#8) (by simp [codeFoot])
  have hb3 := hb (0x800039f7, .discard, 0x00#8) (by simp [codeFoot])
  have htgt : BitVec.update (tgt + sign_extend (m := 64) (0x000#12)) 0 0#1 = tgt :=
    jalr_native_target tgt hal
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jalr c.σ c.tick c.steps (0x800039f4#64) vm tgt (0x000800e7#32) (0x000#12)
      (regidx.Regidx 0x10#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800039f4#64) 4)
      (0xe7#8) (0x00#8) (0x08#8) (0x00#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000800e7 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (rX_bits_x16 _ tgt
        (by rw [get?_afterNextPC c.σ (0x800039f4#64) _ (by decide) (by decide)]; exact hrs))
      (by rw [htgt]; exact hal)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800039f4#64) 4)) hi
  rw [htgt] at hobs
  have h := jalrStep_of_obs hs hi' hG' hmem hobs
  refine ⟨?_, stepConFrame_of_obs hs hobs ?_ ?_⟩
  · rwa [show BitVec.addInt (0x800039f4#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800039f4 + 4) from by
      apply BitVec.eq_of_toNat_eq; decide] at h
  · rfl
  · exact get?_sigmaPost_jalr c.σ _ _ _ Register.x1 _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide)

end VsaIris.Sym

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The body's registers but `a6`. -/
abbrev fRegsNo16 : List Nat :=
  [2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

/-- `a6` out of the register file. -/
theorem regFile_a6 (R : Nat → BitVec 64) :
    regFile (GF := GF) R ⊣⊢ iprop((16 : Nat) ↦ᵣ R 16 ∗ sepL fRegsNo16 (fun x => x ↦ᵣ R x)) := by
  refine (regFile_cut (L := [16]) (K := fRegsNo16) (by decide) R).trans ?_
  simp only [sepL_cons, sepL_nil]
  exact sep_congr sep_emp .rfl

variable {live : Nat → Prop}

/-- **An indirect helper call from a run** (`jalr a6` at `i`, `a6 = entry`),
for either WP: the `jalr` twin of `ms_callHelper`. -/
theorem ms_callHelperR (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalrExec (vsaModel live) i code 16 entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (h16 : R 16 = entry) :
    ⌜pins R⌝ ∗ helperSpec (vsaModel live) Wp entry clob pins Pre Post ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ Pre ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗ Post R' -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  subst h16
  unfold ms helperSpec
  iintro ⟨%hpins, Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HPre, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %R
  ihave ⟨H16, HK⟩ := (regFile_a6 R).1 $$ Hregs
  iapply wp_callRW Wp hexec (X := iprop(sepL fRegsNo16 (fun x => x ↦ᵣ R x) ∗ Pre))
  iframe Hi Hspec Hpc Hra H16
  isplitl [HK HPre]
  · iframe HK HPre
  isplitl []
  · iintro H16 ⟨HK, HPre⟩
    ihave Hregs := (regFile_a6 R).2 $$ [H16 HK]
    · iframe H16 HK
    iframe Hregs HPre Hcode
    ipureintro; exact ⟨hal, hpins⟩
  iintro Hpc Hra Hpost
  icases Hpost with ⟨%R', Hregs, %hkeep, HPost⟩
  iapply Hk $$ %R' %hkeep HPost
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

/-- **An indirect call from a run into a function that returns or aborts**
(`jalr a6` at `i`, `a6 = entry`; `fnSpecAbort` over the run's registers, the
shape of `nativeAssertSpec`), for either WP. `Pre` is the rest of the
precondition; the return hands back some register file with `Post`, the
abort `A`. -/
theorem ms_callAbortR (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalrExec (vsaModel live) i code 16 entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {P Q : BitVec 64 → IProp GF} {A Pre : IProp GF} {Post : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (h16 : R 16 = entry)
    (hP : iprop(regFile R ∗ codeRes ∗ Pre) ⊢ P (BitVec.ofNat 64 (i + 4)))
    (hQ : Q (BitVec.ofNat 64 (i + 4)) ⊢ ∃ R' : Nat → BitVec 64, regFile R' ∗ Post R') :
    fnSpecAbort Wp entry P Q A ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ Pre ∗
      ((∀ R' : Nat → BitVec 64, Post R' -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ) ∧
       (A -∗ ownSet S (fun a => a ↦ₘ imgM Mt a) -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  subst h16
  unfold ms
  iintro ⟨#Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HPre, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave ⟨H16, HK⟩ := (regFile_a6 R).1 $$ Hregs
  iapply wp_callAbortR Wp hexec (X := iprop(sepL fRegsNo16 (fun x => x ↦ᵣ R x) ∗ Pre))
  iframe Hi Hspec Hpc Hra H16
  isplitl [HK HPre]
  · iframe HK HPre
  isplitl []
  · iintro H16 ⟨HK, HPre⟩
    ihave Hregs := (regFile_a6 R).2 $$ [H16 HK]
    · iframe H16 HK
    iapply hP
    iframe Hregs HPre Hcode
  isplit
  · iintro Hpc Hra HQ
    ihave ⟨%R', Hregs, HPost⟩ := hQ $$ HQ
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %R' HPost
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro HA
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA HS

end

end VsaIris.Interp
