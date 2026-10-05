import Vsa.CT.SailLift
import Vsa.Compiler.LibT

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step Steps StepsN Halted Halts RunT pcOfC output)

noncomputable def libTr (t : Nat) (x y r : BitVec 64) : List (BitVec 64) :=
  if h : r.toNat % 4 = 0 then
    if t = mulPC then Classical.choose (sim_mulT x y r h)
    else if h2 : t = divPC ∧ y.toInt ≠ 0 then Classical.choose (sim_divT x y r h2.2 h)
    else if h3 : t = modPC ∧ y.toInt ≠ 0 then Classical.choose (sim_modT x y r h3.2 h)
    else []
  else []

theorem libTr_ok : LibOK libTr := by
  intro t x y r res A c hres hral hc hpc hr hx hy h12 h13 hlib
  unfold libRes at hres
  unfold libTr
  rw [dif_pos hral]
  split at hres
  · rename_i hm
    cases hres
    rw [if_pos hm]
    exact Classical.choose_spec (sim_mulT x y r hral) hc (by rw [hpc, hm]; rfl) hr hx hy h12 h13 hlib
  · rename_i hm
    rw [if_neg hm]
    split at hres
    · rename_i hd
      cases hres
      rw [dif_pos hd]
      exact Classical.choose_spec (sim_divT x y r hd.2 hral) hc (by rw [hpc, hd.1]; rfl) hr hx hy h12 h13 hlib
    · rename_i hd
      rw [dif_neg hd]
      split at hres
      · rename_i hmo
        cases hres
        rw [dif_pos hmo]
        exact Classical.choose_spec (sim_modT x y r hmo.2 hral) hc (by rw [hpc, hmo.1]; rfl) hr hx hy h12 h13
          hlib
      · cases hres

structure Boot (p : Program) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80004800#64
  pw : c.σ.regs.get? Register.htif_payload_writes = some 0#4
  out : output c.σ = ""
  code : ∀ k, k < (compileBytes p).length → c.σ.mem[0x80004800 + k]? = (compileBytes p)[k]?
  lib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
    Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
    Code.__moddi3Loaded c.σ.mem

theorem Boot.corr {p : Program} {c : Config} (h : Boot p c) : Corr c (A0 c.σ.mem c.σ.sailOutput) :=
  ⟨h.good, h.tick, by rw [h.pc]; rfl, trivial, (fun _ h => by cases h), rfl, rfl, h.pw⟩

theorem Boot.libs {p : Program} {c : Config} (h : Boot p c) : LibLoaded (A0 c.σ.mem c.σ.sailOutput).mem :=
  let ⟨h1, h2, h3, h4, h5⟩ := h.lib; ⟨h1, h2, h3, h4, h5⟩

theorem Boot.run {p : Program} {c : Config} (hb : Boot p c) (hfit : Fits (compile p)) {τ : List Obs}
    {o : String}
    (h : ∀ (m : Mem) (os : Array String), String.join os.toList = "" →
      ∃ B, StarT (compile p) τ (A0 m os) B ∧ astep (compile p) B = some (.halt 0) ∧
        String.join B.out.toList = o) :
    ∃ c' σf, RunT c (sailTr libTr τ) c' ∧ Halted c' 0 σf ∧ output σf = o := by
  obtain ⟨B, r, hh, hBo⟩ := h c.σ.mem c.σ.sailOutput hb.out
  obtain ⟨c', σf, hr, hH, ho⟩ := halts_of_abstractT libTr_ok hfit hb.corr (codeAt_of_bytes hb.code)
    hb.libs r hh
  exact ⟨c', σf, hr, hH, ho.trans hBo⟩

theorem ct_machine {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hct : ctSeq sec body = true) (hnat : ∀ p ∈ ins1, isNat p.1 = false) (hlow : LowIns sec ins1 ins2)
    (hsup1 : Supported (prog sec ins1 body)) (hsup2 : Supported (prog sec ins2 body))
    (hfit1 : 0x80004800 + 4 * (compile (prog sec ins1 body)).length ≤ 0x8001ad00)
    (hfit2 : 0x80004800 + 4 * (compile (prog sec ins2 body)).length ≤ 0x8001ad00)
    {c1 c2 : Config} (hb1 : Boot (prog sec ins1 body) c1) (hb2 : Boot (prog sec ins2 body) c2)
    {o1 : String} (hh1 : Halts c1 o1 0) :
    ∃ o2 ℓ1 ℓ2, BigStepL (prog sec ins1 body) o1 ℓ1 ∧ BigStepL (prog sec ins2 body) o2 ℓ2 ∧
      Halts c2 o2 0 ∧ skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ T : List (BitVec 64),
        (∃ c' σf, RunT c1 T c' ∧ Halted c' 0 σf ∧ output σf = o1) ∧
        (∃ c' σf, RunT c2 T c' ∧ Halted c' 0 σf ∧ output σf = o2)) := by
  have cc1 := compile_correct _ hsup1 hfit1 c1 hb1.good hb1.tick hb1.pc hb1.pw hb1.out hb1.code hb1.lib
  have cc2 := compile_correct _ hsup2 hfit2 c2 hb2.good hb2.tick hb2.pc hb2.pw hb2.out hb2.code hb2.lib
  obtain ⟨ℓ1, h1⟩ := (bigStep_iff_L _ _).mp ((cc1.1 o1).mpr hh1)
  obtain ⟨o2, ℓ2, h2, hsk, hk⟩ := am_ct hct hnat hlow hsup1 hsup2 hfit1 hfit2 h1
  have hh2 : Halts c2 o2 0 := (cc2.1 o2).mp ((bigStep_iff_L _ _).mpr ⟨ℓ2, h2⟩)
  refine ⟨o2, ℓ1, ℓ2, h1, h2, hh2, hsk, fun ho => ?_⟩
  obtain ⟨heq, τ, hτ⟩ := hk ho
  exact ⟨heq, sailTr libTr τ, hb1.run hfit1 fun m os h => (hτ m os h).1,
    hb2.run hfit2 fun m os h => (hτ m os h).2⟩

theorem ct_machine_pub {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hct : ctSeqPub sec body = true) (hnat : ∀ p ∈ ins1, isNat p.1 = false) (hlow : LowIns sec ins1 ins2)
    (hsup1 : Supported (prog sec ins1 body)) (hsup2 : Supported (prog sec ins2 body))
    (hfit1 : 0x80004800 + 4 * (compile (prog sec ins1 body)).length ≤ 0x8001ad00)
    (hfit2 : 0x80004800 + 4 * (compile (prog sec ins2 body)).length ≤ 0x8001ad00)
    {c1 c2 : Config} (hb1 : Boot (prog sec ins1 body) c1) (hb2 : Boot (prog sec ins2 body) c2)
    {o1 : String} (hh1 : Halts c1 o1 0) :
    Halts c2 o1 0 ∧ ∃ T : List (BitVec 64),
      (∃ c' σf, RunT c1 T c' ∧ Halted c' 0 σf ∧ output σf = o1) ∧
      (∃ c' σf, RunT c2 T c' ∧ Halted c' 0 σf ∧ output σf = o1) := by
  have cc1 := compile_correct _ hsup1 hfit1 c1 hb1.good hb1.tick hb1.pc hb1.pw hb1.out hb1.code hb1.lib
  have cc2 := compile_correct _ hsup2 hfit2 c2 hb2.good hb2.tick hb2.pc hb2.pw hb2.out hb2.code hb2.lib
  obtain ⟨ℓ, h1⟩ := (bigStep_iff_L _ _).mp ((cc1.1 o1).mpr hh1)
  obtain ⟨o2, h2, rfl⟩ := ct_sound_pub hct hnat hlow h1
  have hh2 : Halts c2 o2 0 := (cc2.1 o2).mp ((bigStep_iff_L _ _).mpr ⟨ℓ, h2⟩)
  obtain ⟨τ, hτ⟩ := am_ct_core hlow hsup1 hsup2 hfit1 hfit2 h1 h2
  exact ⟨hh2, sailTr libTr τ, hb1.run hfit1 fun m os h => (hτ m os h).1,
    hb2.run hfit2 fun m os h => (hτ m os h).2⟩

end Vsa.Compiler
