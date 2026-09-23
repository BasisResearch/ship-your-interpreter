import VsaIris.Vsa.Instance
import VsaIris.DlHeap
import Vsa.Sim.BridgeSeg

/-!
# Tools for function proofs over `vsaModel`

Generic pieces a function proof needs besides `wp_seg` and `wp_call`:

* `instrAt_append`: the persistent code of a function splits into the code
  of its segments and call sites;
* `sepL_perm`, `blockOwn_range`: an allocator block (`ownSet`) as a list of
  owned bytes, so a segment can write it;
* `code_present`: owned code bytes inside `live` are present, which is what
  VSA's fetch facts (`BytePins`, `Code.*Loaded`) require;
* `jalExec_of_site`: a `jal` site's VSA fact (`JalStep`, produced by
  `jalStep_of_obs` from the generated site lemma) as the Iris `JalExec`.
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config Step MState)
open Vsa.Sim

section Tools

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem codeFoot_append (i : Nat) (c₁ c₂ : List (BitVec 8)) :
    codeFoot i (c₁ ++ c₂) = codeFoot i c₁ ++ codeFoot (i + c₁.length) c₂ := by
  unfold codeFoot
  rw [List.zipIdx_append, List.map_append, List.zipIdx_eq_map_add (l := c₂), List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [Nat.add_assoc]

theorem sepL_append' {α} (l₁ l₂ : List α) (Φ : α → IProp GF) :
    sepL (l₁ ++ l₂) Φ ⊣⊢ sepL l₁ Φ ∗ sepL l₂ Φ := sepL_append l₁ l₂ Φ

/-- A function's code splits into consecutive slices. -/
theorem instrAt_append (i : Nat) (c₁ c₂ : List (BitVec 8)) :
    instrAt (GF := GF) i (c₁ ++ c₂) ⊣⊢ instrAt i c₁ ∗ instrAt (i + c₁.length) c₂ := by
  rw [instrAt_eq, instrAt_eq, instrAt_eq, codeFoot_append]
  exact sepL_append _ _ _

theorem sepL_perm {α} {l₁ l₂ : List α} (Φ : α → IProp GF) (h : l₁.Perm l₂) :
    sepL l₁ Φ ⊣⊢ sepL l₂ Φ := by
  induction h with
  | nil => exact .rfl
  | cons x _ ih => simp only [sepL_cons]; exact sep_congr_right ih
  | swap x y l =>
    simp only [sepL_cons]
    exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans sep_assoc)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An allocator block is its bytes, each at some value. -/
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

/-- Bytes owned at some value are bytes owned at known values. -/
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

/-- Forget the values of owned bytes. -/
theorem sepL_forget (W : List (Nat × BitVec 8)) (f : Nat → BitVec 8) :
    sepL (GF := GF) W (fun q => q.1 ↦ₘ f q.1) ⊢ sepL (W.map Prod.fst) byteAny := by
  rw [sepL_map]
  apply sepL_mono
  intro q
  iintro H
  iexists f q.1
  iexact H

/-- Forget the values of owned bytes listed as read footprint entries. -/
theorem sepL_map_forget (W : List (Nat × BitVec 8)) (f : Nat → BitVec 8) :
    sepL (GF := GF) (W.map fun q => (q.1, DFrac.own 1, f q.1)) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ⊢
      sepL (W.map Prod.fst) byteAny := by
  rw [sepL_map, sepL_map]
  apply sepL_mono
  intro q
  iintro H
  iexists f q.1
  iexact H

/-- Forget the values of a read footprint listed by address. -/
theorem sepL_map_forget' (l : List Nat) (f : Nat → BitVec 8) :
    sepL (GF := GF) (l.map fun a => (a, DFrac.own 1, f a)) (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ⊢
      sepL l byteAny := by
  rw [sepL_map]
  apply sepL_mono
  intro a
  iintro H
  iexists f a
  iexact H

/-- A duplicate-free list of owned bytes is an owned byte set. -/
theorem sepL_to_ownSet (l : List Nat) (hnd : l.Nodup) (Φ : Nat → IProp GF) :
    sepL l Φ ⊢ ownSet (fun a => a ∈ l) Φ := by
  unfold ownSet
  iintro H
  iexists l
  iframe H
  ipureintro
  exact ⟨hnd, fun _ => Iff.rfl⟩

/-- An owned byte set with the members of a duplicate-free list is that
list of owned bytes. -/
theorem ownSet_to_sepL (l : List Nat) (hnd : l.Nodup) (Φ : Nat → IProp GF) :
    ownSet (fun a => a ∈ l) Φ ⊢ sepL l Φ := by
  unfold ownSet
  iintro ⟨%l', %⟨hnd', hmem⟩, H⟩
  iapply (sepL_perm Φ ((List.perm_ext_iff_of_nodup hnd' hnd).mpr hmem)).1 $$ H

/-- Two lists of exclusively owned bytes have disjoint addresses. -/
theorem sepL_disjoint (W₁ W₂ : List (Nat × BitVec 8)) (f g : Nat × BitVec 8 → BitVec 8) :
    sepL (GF := GF) W₁ (fun q => q.1 ↦ₘ f q) ∗ sepL W₂ (fun q => q.1 ↦ₘ g q) ⊢
      sepL W₁ (fun q => q.1 ↦ₘ f q) ∗ sepL W₂ (fun q => q.1 ↦ₘ g q) ∗
        ⌜∀ q₁ ∈ W₁, ∀ q₂ ∈ W₂, q₁.1 ≠ q₂.1⌝ := by
  induction W₁ with
  | nil =>
    iintro ⟨H1, H2⟩
    iframe H1 H2
    ipureintro; intro _ h; cases h
  | cons x xs ih =>
    rw [sepL_cons]
    iintro ⟨⟨Hx, Hxs⟩, H2⟩
    ihave ⟨Hxs, H2, %hxs⟩ := ih $$ [Hxs H2]
    · iframe Hxs H2
    have hone : ∀ l : List (Nat × BitVec 8),
        (x.1 ↦ₘ f x) ∗ sepL l (fun q => q.1 ↦ₘ g q) ⊢@{IProp GF}
          (x.1 ↦ₘ f x) ∗ sepL l (fun q => q.1 ↦ₘ g q) ∗ ⌜∀ q ∈ l, x.1 ≠ q.1⌝ := by
      intro l
      induction l with
      | nil => iintro ⟨Hx, H⟩; iframe Hx H; ipureintro; intro _ h; cases h
      | cons y ys ihy =>
        rw [sepL_cons]
        iintro ⟨Hx, Hy, Hys⟩
        ihave %hy := mem_ne x.1 y.1 _ (f x) (g y) $$ Hx Hy
        ihave ⟨Hx, Hys, %hys⟩ := ihy $$ [Hx Hys]
        · iframe Hx Hys
        iframe Hx Hy Hys
        ipureintro
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hy
        · exact hys q hq
    ihave ⟨Hx, H2, %hx⟩ := hone W₂ $$ [Hx H2]
    · iframe Hx H2
    iframe Hx Hxs H2
    ipureintro
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hx
    · exact hxs q hq

theorem codeFoot_bounds {i : Nat} {code : List (BitVec 8)} {p : Nat × DFrac × BitVec 8}
    (h : p ∈ codeFoot i code) : i ≤ p.1 ∧ p.1 < i + code.length := by
  unfold codeFoot at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  have := List.snd_lt_of_mem_zipIdx hq
  simp at this ⊢
  omega

/-- Owned code bytes that `live` keeps present are present with their
values. -/
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

/-- The console frame of a step (INTERP_DESIGN.md §2 F2): whatever `Step`
the machine takes from `σp`, it prints nothing and leaves the HTIF mailbox
counter alone. `Step` is deterministic, so this is a fact about THE step. -/
def StepConFrame (σp : MState) (ip up : Nat) : Prop :=
  ∀ c' : Config, Step ⟨σp, ip, up⟩ c' → c'.σ.sailOutput = σp.sailOutput ∧
    c'.σ.regs.get? Register.htif_payload_writes = σp.regs.get? Register.htif_payload_writes

/-- The console frame from a step observation (`StepObs`'s `ReadsLikePost`):
the observed post-state's output and mailbox counter are the pre-state's. -/
theorem stepConFrame_of_obs {σp σ2 spost : MState} {ip up i2 : Nat}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hobs : ReadsLikePost σ2 spost)
    (hout : spost.sailOutput = σp.sailOutput)
    (hpw : spost.regs.get? Register.htif_payload_writes =
      σp.regs.get? Register.htif_payload_writes) :
    StepConFrame σp ip up := by
  intro c' hs
  cases hstep.deterministic hs
  exact ⟨hobs.out.trans hout, (hobs.1 _ (by decide) (by decide) (by decide)).trans hpw⟩

/-- The console frame of a `jal ra` step, from its observation. -/
theorem stepConFrame_of_jalObs {σp σ2 : MState} {ip up i2 : Nat}
    {jalPC vm : BitVec 64} {imm : BitVec 21} {link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩)
    (hobs : ReadsLikePost σ2 (sigmaPost_jal σp jalPC vm imm Register.x1 link)) :
    StepConFrame σp ip up :=
  stepConFrame_of_obs hstep hobs rfl
    (get?_sigmaPost_jal σp jalPC vm imm Register.x1 link _ (by decide) (by decide) (by decide)
      (by decide) (by decide))

/-- **A `jal` site as an Iris exec fact.** VSA's per-site fact (`JalStep`:
one step to the callee with the link in `ra`, every other GPR and all of
memory unchanged) plus its console frame (`StepConFrame`, from the same
observation), from any good state parked at `i` with the site's bytes
present, is the `JalExec` that `wp_jal`/`wp_call` consume. -/
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
