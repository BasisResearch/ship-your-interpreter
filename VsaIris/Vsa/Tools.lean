import VsaIris.Vsa.Instance
import VsaIris.DlHeap
import Vsa.Sim.BridgeSeg

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config Step MState)
open Vsa.Sim

section Tools

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem sepL_perm {α} {l₁ l₂ : List α} (Φ : α → IProp GF) (h : l₁.Perm l₂) :
    sepL l₁ Φ ⊣⊢ sepL l₂ Φ := by
  induction h with
  | nil => exact .rfl
  | cons x _ ih => simp only [sepL_cons]; exact sep_congr_right ih
  | swap x y l =>
    simp only [sepL_cons]
    exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans sep_assoc)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem blockOwn_range (p n : Nat) :
    blockOwn (GF := GF) p n ⊢ sepL (List.range' p n) byteAny := by
  unfold blockOwn ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  have hperm : l.Perm (List.range' p n) := by
    refine (List.perm_ext_iff_of_nodup hnd (List.nodup_range' _ (by omega))).mpr fun a => ?_
    rw [hmem a, List.mem_range']
    unfold InExt
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a - p, by simp at h2; omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; simp; omega
  iapply (sepL_perm byteAny hperm).1 $$ Hl

theorem sepL_byteAny_exists : ∀ l : List Nat,
    sepL (GF := GF) l byteAny ⊢
      ∃ W : List (Nat × BitVec 8), ⌜W.map Prod.fst = l⌝ ∗ sepL W (fun q => q.1 ↦ₘ q.2)
  | [] => by
    iintro _
    iexists []
    isplitr
    · ipureintro; rfl
    simp only [sepL_nil]; iempintro
  | a :: l => by
    rw [sepL_cons]
    iintro ⟨⟨%b, Ha⟩, Hl⟩
    ihave ⟨%W, %hW, HW⟩ := sepL_byteAny_exists l $$ Hl
    iexists (a, b) :: W
    rw [sepL_cons]
    iframe Ha HW
    ipureintro
    simp [hW]

theorem sepL_to_ownSet (l : List Nat) (hnd : l.Nodup) (Φ : Nat → IProp GF) :
    sepL l Φ ⊢ ownSet (fun a => a ∈ l) Φ := by
  unfold ownSet
  iintro H
  iexists l
  iframe H
  ipureintro
  exact ⟨hnd, fun _ => Iff.rfl⟩

theorem ownSet_to_sepL (l : List Nat) (hnd : l.Nodup) (Φ : Nat → IProp GF) :
    ownSet (fun a => a ∈ l) Φ ⊢ sepL l Φ := by
  unfold ownSet
  iintro ⟨%l', %⟨hnd', hmem⟩, H⟩
  iapply (sepL_perm Φ ((List.perm_ext_iff_of_nodup hnd' hnd).mpr hmem)).1 $$ H

theorem code_present {live : Nat → Prop} {c : Config} (hok : VsaOk live c)
    (MR : List (Nat × DFrac × BitVec 8)) (hmr : ∀ p ∈ MR, (vsaModel live).mem c p.1 = p.2.2)
    (hlive : ∀ p ∈ MR, live p.1) : ∀ p ∈ MR, c.σ.mem[p.1]? = some p.2.2 := by
  intro p hp
  have hv := hmr p hp
  have hs := hok.live _ (hlive p hp)
  change (c.σ.mem[p.1]?).getD 0 = p.2.2 at hv
  cases hg : c.σ.mem[p.1]? with
  | none => rw [hg] at hs; cases hs
  | some b => rw [hg] at hv; exact congrArg some hv

def StepConFrame (σp : MState) (ip up : Nat) : Prop :=
  ∀ c' : Config, Step ⟨σp, ip, up⟩ c' → c'.σ.sailOutput = σp.sailOutput ∧
    c'.σ.regs.get? Register.htif_payload_writes = σp.regs.get? Register.htif_payload_writes

theorem stepConFrame_of_obs {σp σ2 spost : MState} {ip up i2 : Nat}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hobs : ReadsLikePost σ2 spost)
    (hout : spost.sailOutput = σp.sailOutput)
    (hpw : spost.regs.get? Register.htif_payload_writes =
      σp.regs.get? Register.htif_payload_writes) :
    StepConFrame σp ip up := by
  intro c' hs
  cases hstep.deterministic hs
  exact ⟨hobs.out.trans hout, (hobs.1 _ (by decide) (by decide) (by decide)).trans hpw⟩

theorem stepConFrame_of_jalObs {σp σ2 : MState} {ip up i2 : Nat}
    {jalPC vm : BitVec 64} {imm : BitVec 21} {link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩)
    (hobs : ReadsLikePost σ2 (sigmaPost_jal σp jalPC vm imm Register.x1 link)) :
    StepConFrame σp ip up :=
  stepConFrame_of_obs hstep hobs rfl
    (get?_sigmaPost_jal σp jalPC vm imm Register.x1 link _ (by decide) (by decide) (by decide)
      (by decide) (by decide))

theorem jalExec_of_site (live : Nat → Prop) (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64)
    (hlive : ∀ p ∈ codeFoot i code, live p.1)
    (hsite : ∀ c : Config, GoodState c.σ → c.tick < 2 →
      c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) →
      (∀ p ∈ codeFoot i code, c.σ.mem[p.1]? = some p.2.2) →
      JalStep tgt (BitVec.ofNat 64 (i + 4)) c.σ c.tick c.steps ∧
        StepConFrame c.σ c.tick c.steps) :
    JalExec (vsaModel live) i code tgt := by
  intro v c hok hfoot
  have hok : VsaOk live c := hok
  obtain ⟨_, hMR, hRW, _⟩ := hfoot
  have hpc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 i) := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = _ at h
    obtain ⟨w, hw⟩ := hok.good.PC
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  obtain ⟨⟨σ2, i2, hs, hi2, hG2, hmem, hpc2, hra2, _, hnonra, _⟩, hcon⟩ :=
    hsite c hok.good hok.tick hpc (code_present hok _ hMR hlive)
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

end Tools

end VsaIris.Inst
