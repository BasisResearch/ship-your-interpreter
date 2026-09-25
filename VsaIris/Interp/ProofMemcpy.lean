import VsaIris.Vsa.MemcpyLoops
import VsaIris.Vsa.StrlenOwned
import VsaIris.Interp.SpecStringify
import VsaIris.Interp.HelperRun

/-!
# `memcpy` in the Iris logic

newlib's `memcpy` (`0x80006bc8`, `memcpyPC`) is ONE bounded local run
(`Memcpy.memcpyLocalRun`, over the step table `MemcpySteps.lean`), so each
spec is one `wp_localRunW` application (`memcpy_wp`), for either WP.

* `memcpy_spec_env`: the read-only source of `memcpySpec` sits in the run's
  read-only text (`srcText`).
* `memcpy_spec_owned`: the owned source of `memcpySpecOwned` is promoted
  from the read-only text to the owned set (`LocalRun.promote`) and handed
  back unchanged.

Both specs require `htifLo + 16 ≤ dst.toNat`: VSA's store facts (`MemFacts`
`.sd`/`.sb`) hold only above the HTIF words.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Newlib VsaIris.MallocFast VsaIris.Sym VsaIris.Memcpy


/-! ## Code and registers -/

/-- `memcpy`'s code is the image's. -/
theorem memcpyCode_text : TextAt memcpyBase memcpyCode := by decide +kernel

theorem memcpy_live {live : Nat → Prop} (hcl : CodeLive live) : ∀ p ∈ mText, live p.1 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hcl _ (memcpyCode_text q hq).1

/-- The registers at the entry: the arguments, `ra`, and the caller-saved
registers at their values `f`. -/
def entryRV (r dst src : BitVec 64) (n : Nat) (f : Nat → BitVec 64) : Nat → BitVec 64 := fun k =>
  if k = VsaIris.PC then memcpyPC
  else if k = 1 then r
  else if k = 10 then dst
  else if k = 11 then src
  else if k = 12 then BitVec.ofNat 64 n
  else f k

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem entryRV_sepL (r dst src : BitVec 64) (n : Nat) (f : Nat → BitVec 64) :
    sepL (GF := GF) Memcpy.mRegs (fun k => k ↦ᵣ entryRV r dst src n f k) =
      iprop(VsaIris.PC ↦ᵣ memcpyPC ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ dst ∗ (11 : Nat) ↦ᵣ src ∗
        (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗ (13 : Nat) ↦ᵣ f 13 ∗ (14 : Nat) ↦ᵣ f 14 ∗
        (15 : Nat) ↦ᵣ f 15 ∗ (16 : Nat) ↦ᵣ f 16 ∗ (17 : Nat) ↦ᵣ f 17 ∗ (5 : Nat) ↦ᵣ f 5 ∗
        (6 : Nat) ↦ᵣ f 6 ∗ (28 : Nat) ↦ᵣ f 28 ∗ (29 : Nat) ↦ᵣ f 29 ∗ (30 : Nat) ↦ᵣ f 30 ∗
        (31 : Nat) ↦ᵣ f 31 ∗ emp) :=
  rfl

/-- The registers at the return: the PC, `ra`, `a0`, and the rest clobbered
(with `t2`, which the run does not touch). -/
theorem post_regs (rv : Nat → BitVec 64) (v7 : BitVec 64) :
    sepL (GF := GF) Memcpy.mRegs (fun k => k ↦ᵣ rv k) ∗ (7 : Nat) ↦ᵣ v7 ⊢
      VsaIris.PC ↦ᵣ rv VsaIris.PC ∗ (1 : Nat) ↦ᵣ rv 1 ∗ (10 : Nat) ↦ᵣ rv 10 ∗
        clobbered retClob := by
  simp only [Memcpy.mRegs, sepL_cons, sepL_nil]
  iintro ⟨⟨Hpc, H1, H10, H11, H12, H13, H14, H15, H16, H17, H5, H6, H28, H29, H30, H31, -⟩, H7⟩
  iframe Hpc H1 H10
  iapply clobbered_of_fn retClob (fun k => if k = 7 then v7 else rv k)
  simp only [retClob, argClob, sepL_cons, sepL_nil, Nat.reduceEqDiff, ite_true, ite_false]
  iframe H11 H12 H5 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31

variable {live : Nat → Prop}

/-- **`memcpy` at the Iris level**, for either WP, from any bounded local run
of it over the owned registers `mRegs`: the continuation receives the PC and
`ra` at the return address, `a0 = dst`, the caller-saved registers clobbered,
and the owned bytes at values satisfying the run's end condition. -/
theorem memcpy_wp (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {text : List (Nat × BitVec 8)} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {r dst src : BitVec 64} {n : Nat}
    (f : Nat → BitVec 64) (mv : Nat → BitVec 8) (N : Nat)
    (hrun : LocalRun (vsaModel live) [] text Memcpy.mRegs S Q N (entryRV r dst src n f) mv)
    (hQ : ∀ rv mv, Q rv mv → rv VsaIris.PC = r ∧ rv 1 = r ∧ rv 10 = dst) :
    roOwn [] text ∗ VsaIris.PC ↦ᵣ memcpyPC ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ dst ∗
      (11 : Nat) ↦ᵣ src ∗ (12 : Nat) ↦ᵣ BitVec.ofNat 64 n ∗ sepL argClob (fun k => k ↦ᵣ f k) ∗
      ownSet S (fun a => a ↦ₘ mv a) ∗
      (∀ mv', ⌜∃ rv', Q rv' mv'⌝ -∗ VsaIris.PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ dst -∗
        clobbered retClob -∗ ownSet S (fun a => a ↦ₘ mv' a) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  simp only [argClob, sepL_cons, sepL_nil]
  iintro ⟨#Hro, Hpc, H1, H10, H11, H12, ⟨H5, H6, H7, H13, H14, H15, H16, H17, H28, H29, H30, H31, -⟩,
    HS, Hk⟩
  iapply wp_localRunW Wp N (entryRV r dst src n f) mv hrun
  isplitl []
  · iexact Hro
  isplitl [Hpc H1 H10 H11 H12 H5 H6 H13 H14 H15 H16 H17 H28 H29 H30 H31]
  · rw [entryRV_sepL]
    iframe Hpc H1 H10 H11 H12 H5 H6 H13 H14 H15 H16 H17 H28 H29 H30 H31
  isplitl [HS]
  · iexact HS
  unfold runKontW
  iintro %rv' %mv' %hq Hregs HS'
  obtain ⟨e1, e2, e3⟩ := hQ rv' mv' hq
  ihave ⟨Hpc, H1, H10, Hcl⟩ := post_regs rv' (f 7) $$ [Hregs H7]
  · iframe Hregs H7
  ihave Hpc := Strlen.reg_cast e1 $$ Hpc
  ihave H1 := Strlen.reg_cast e2 $$ H1
  ihave H10 := Strlen.reg_cast e3 $$ H10
  iapply Hk $$ %mv' %⟨rv', hq⟩ Hpc H1 H10 Hcl HS'

/-- The read-only source as the run's text. -/
theorem roImg_srcText (X n : Nat) (img : Nat → BitVec 8) :
    roImg (GF := GF) (InExt (X, n)) img ⊢ sepL (srcText X n img) (fun p => p.1 ↦ₘ□ p.2) := by
  have h : ∀ l : List (Nat × BitVec 8), (∀ p ∈ l, InExt (X, n) p.1 ∧ p.2 = img p.1) →
      roImg (GF := GF) (InExt (X, n)) img ⊢ sepL l (fun p => p.1 ↦ₘ□ p.2) := by
    intro l
    induction l with
    | nil => intro _; iintro _; simp only [sepL_nil]; iempintro
    | cons q l ih =>
      intro hl
      simp only [sepL_cons]
      iintro #H
      isplitl
      · obtain ⟨hs, he⟩ := hl q List.mem_cons_self
        unfold roImg
        rw [he]
        iapply H $$ %q.1 %hs
      · iapply ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) $$ H
  refine h _ fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := mem_srcText hp
  exact ⟨⟨h1, h2⟩, h3⟩

theorem srcText_iff (X n : Nat) (img : Nat → BitVec 8) (a : Nat) :
    InExt (X, n) a ↔ ∃ p ∈ srcText X n img, p.1 = a := by
  constructor
  · intro h
    refine ⟨(a, img a), List.mem_map.mpr ⟨a - X, List.mem_range.mpr (by unfold InExt at h; simp at h; omega), ?_⟩, rfl⟩
    unfold InExt at h
    simp only [Prod.mk.injEq]; constructor <;> congr 1 <;> simp at h <;> omega
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, _⟩ := mem_srcText hp
    exact ⟨h1, h2⟩

/-- The run's geometry from the specs' pure precondition. -/
theorem geo_of_pre {dst src r : BitVec 64} {n : Nat} (hal : r.toNat % 4 = 0)
    (hwd : RamWin dst.toNat n) (hhd : htifLo + 16 ≤ dst.toNat) (hws : RamWin src.toNat n) :
    Geo dst src r n where
  dlo := hwd.lo
  dhi := hwd.hi
  dhtif := hhd
  slo := hws.lo
  shi := hws.hi
  shtif := hws.htif
  ral := hal

/-- The final destination bytes are the source's. -/
theorem dst_img {dst r : BitVec 64} {n X : Nat} {img : Nat → BitVec 8} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (hq : mQ dst r n X img rv mv) :
    ∀ a, InExt (dst.toNat, n) a → mv a = img (a - dst.toNat + X) := by
  intro a ha
  unfold InExt at ha
  simp only at ha
  have := hq.2.2.2 (a - dst.toNat) (by omega)
  rw [show dst.toNat + (a - dst.toNat) = a by omega] at this
  rw [this]; congr 1; omega

end Iris

section Proofs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem blockOwn_fn (p n : Nat) :
    blockOwn (GF := GF) p n ⊢ ∃ f : Nat → BitVec 8, ownSet (InExt (p, n)) (fun a => a ↦ₘ f a) :=
  ownSet_fn _

/-- **`memcpy` from read-only bytes**, for every code-live `live` and every
`MachWP`. -/
theorem memcpy_spec_env (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) : binImg (GF := GF) ⊢ memcpySpec Wp := by
  have hlive := memcpy_live hcl
  iintro #Himg
  ihave #Hcode := instrAt_of_binImg memcpyCode_text $$ Himg
  unfold memcpySpec
  imodintro
  iintro %dst %src %n %img
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hpre, H10, H11, H12, Hcl, Hdst, #Hsrc⟩ Hk
  obtain ⟨hal, hwd, hhd, hws⟩ := hpre
  have Gm := geo_of_pre hal hwd hhd hws
  ihave ⟨%f, Hcl⟩ := clobbered_fn argClob (by decide) $$ Hcl
  ihave ⟨%fd, Hdst⟩ := blockOwn_fn _ _ $$ Hdst
  ihave ⟨%Mt, HS, -⟩ := ownSet_trackedAt _ fd $$ Hdst
  obtain ⟨N, hrun⟩ := memcpyLocalRun (img := img) hlive Gm (entryRV r dst src n f) Mt rfl rfl rfl
    rfl rfl
  ihave #Htext := roImg_srcText src.toNat n img $$ Hsrc
  unfold VsaIris.ra
  iapply memcpy_wp Wp f (imgM Mt) N hrun (fun rv mv h => ⟨h.1, h.2.1, h.2.2.1⟩)
  isplitl []
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    iapply (sepL_append _ _ _).2
    isplitl []
    · rw [← Strlen.instrAt_text]
      iexact Hcode
    · iexact Htext
  iframe Hpc Hra H10 H11 H12 Hcl HS
  iintro %mv' %⟨rv', hq⟩ Hpc Hra H10 Hcl HS'
  iapply Hk $$ Hpc Hra
  isplitl [H10]
  · iexact H10
  isplitl [Hcl]
  · iexact Hcl
  iapply ownSet_congr (fun a ha => by rw [dst_img hq a ha]) $$ HS'

/-- **`memcpy` from an owned source**, handed back unchanged, for every
code-live `live` and every `MachWP`. -/
theorem memcpy_spec_owned (live : Nat → Prop) (hcl : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) :
    binImg (GF := GF) ⊢ memcpySpecOwned (vsaModel live) Wp := by
  have hlive := memcpy_live hcl
  iintro #Himg
  ihave #Hcode := instrAt_of_binImg memcpyCode_text $$ Himg
  unfold memcpySpecOwned
  imodintro
  iintro %dst %src %n %img
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hpre, H10, H11, H12, Hcl, Hdst, Hsrc, -⟩ Hk
  obtain ⟨hal, hwd, hhd, hws⟩ := hpre
  have Gm := geo_of_pre hal hwd hhd hws
  ihave ⟨%f, Hcl⟩ := clobbered_fn argClob (by decide) $$ Hcl
  ihave ⟨%fd, Hdst⟩ := blockOwn_fn _ _ $$ Hdst
  ihave %hd := ownSet_disj _ _ fd img $$ [Hdst Hsrc]
  · iframe Hdst Hsrc
  ihave HU := ownSet_glue _ _ fd img hd $$ [Hdst Hsrc]
  · iframe Hdst Hsrc
  ihave ⟨%Mt, HU, %hMt⟩ := ownSet_trackedAt _ _ $$ HU
  have hd' : ∀ p ∈ srcText src.toNat n img, ¬ InExt (dst.toNat, n) p.1 := fun p hp h =>
    hd _ h ((srcText_iff src.toNat n img p.1).2 ⟨p, hp, rfl⟩)
  have hsrcv : ∀ p ∈ srcText src.toNat n img, imgM Mt p.1 = p.2 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_srcText hp
    rw [hMt _ (.inr ⟨h1, h2⟩), glue, ite_eq_right_of_eq_false _ _ (eq_false (hd' p hp)), h3]
  obtain ⟨N, hrun⟩ := memcpyLocalRun (img := img) hlive Gm (entryRV r dst src n f) Mt rfl rfl rfl
    rfl rfl
  have hrun' := LocalRun.promote hd' N _ _ hrun hsrcv
  ihave HU := ownSet_iff _ (fun a => or_congr_right (srcText_iff src.toNat n img a)) $$ HU
  unfold VsaIris.ra
  iapply memcpy_wp Wp f (imgM Mt) N hrun' (fun rv mv h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩)
  isplitl []
  · unfold roOwn
    simp only [sepL_nil]
    isplitr
    · iempintro
    rw [← Strlen.instrAt_text]
    iexact Hcode
  iframe Hpc Hra H10 H11 H12 Hcl HU
  iintro %mv' %⟨rv', hq, hsrc'⟩ Hpc Hra H10 Hcl HS'
  ihave HS' := ownSet_iff _ (fun a => or_congr_right (srcText_iff src.toNat n img a).symm) $$ HS'
  ihave ⟨HD, HX⟩ := ownSet_unglue _ _ _ hd $$ HS'
  iapply Hk $$ Hpc Hra
  isplitl [H10]
  · iexact H10
  isplitl [Hcl]
  · iexact Hcl
  isplitl [HD]
  · iapply ownSet_congr (fun a ha => by rw [dst_img hq a ha]) $$ HD
  · iapply ownSet_congr (fun a ha => by
      obtain ⟨p, hp, rfl⟩ := (srcText_iff src.toNat n img a).1 ha
      rw [hsrc' p hp, (mem_srcText hp).2.2]) $$ HX

end Proofs

#print axioms memcpy_spec_env
#print axioms memcpy_spec_owned

end VsaIris.Interp
