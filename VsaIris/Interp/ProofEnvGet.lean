import VsaIris.Interp.EnvScan
import VsaIris.Interp.EnvGetHit

/-!
# `env_get`, proved (INTERP_DESIGN.md §9 H1)

`envGet_spec : textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ envGetSpec Wp N`,
for every `MachWP`.

`env_get` is the scan code (`EnvScan.lean`) at `getSite` — its spans are
`EnvGetSpans.lean` — with the hit arm `get_hit` (copy `vals[i]` out, return 1,
`EnvGetHit.lean`). The machine's answer is `Store.get?`'s: the chain's path
keeps the lookup (`ChainFrom.look`), a frame's scan finds the first binding
named `x` (`look_hit`), and the root misses (`look_root`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- `env_get`'s address of the scan code. -/
def getSite (live : Nat → Prop) (hl : ∀ p ∈ envText, live p.1) : ScanSite live where
  entry := 0x80002c10#64
  head := 0x80002c40#64
  scan := 0x80002c60#64
  jal := 0x80002c68
  jcode := [0xef#8, 0x40#8, 0x80#8, 0x23#8]
  hit := 0x80002c70#64
  tail := 0x80002cc4#64
  epi := 0x80002ca0#64
  jexec := jalx_80002c68 live fun p hp => hl _ (env_code_80002c68 p hp)
  jtext := env_code_80002c68
  jal4 := by decide
  nameR := 19
  cntR := 18
  cntOK := by decide
  nameIs := rfl
  cntIs := rfl
  sEntry := get_entry hl
  sHead := get_head hl
  sLoad := get_load hl
  sCmp := get_cmp hl
  sParent := get_parent hl
  sEpi := get_epi hl

section Main

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- **`env_get`** (`env.c:43`), for every `MachWP`. -/
theorem envGet_spec (Wp : MachWP (GF := GF) (vsaModel live)) (hl : ∀ p ∈ envText, live p.1)
    (N : NativeAddrs) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ envGetSpec Wp N := by
  iintro ⟨#Ht, #Hgp, #Hcmp⟩
  unfold envGetSpec
  imodintro
  iintro %st %B %fa %x %e %pn %out %s %saved %hsv
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hr, hsp, hslot⟩, Ha0, Ha1, Ha2, Hsp, Hcl, Hsv, Hstk, #Hfa, #Hx, Hout, Hst, -, -⟩ Hk
  ihave ⟨Hst, %⟨-, hfalt, hinv⟩⟩ := storeRepr_frameInfo N $$ [Hst Hfa]
  · iframe Hst Hfa
  have hs64 : 64 ≤ s.toNat := by have := hsp.lo; unfold htifLo envGetNeed at this; omega
  have hget : ∀ a, ChainFrom st x fa a → st.get? fa x = look st a x := fun a h =>
    (get?_eq_look hinv.parents hfalt x).trans (h.look hinv.parents)
  unfold slot24
  ihave ⟨%fo, Hout⟩ := blockOwn_img _ _ $$ Hout
  ihave ⟨⟨Hout, Hstk⟩, %hdo⟩ := keep_pure (ownSet_off _ _ fo) $$ [Hout Hstk]
  · iframe Hout; unfold stackScratch blockOwn; iexact Hstk
  have hsep : out.toNat + 24 ≤ s.toNat - 64 ∨ s.toNat ≤ out.toNat := by
    have := interval_apart (a := out.toNat) (n := 24) (b := s.toNat - envGetNeed)
      (m := envGetNeed) (by omega) (by unfold envGetNeed; omega) fun c h1 h2 => by
        have := hdo c
        unfold InExt at this; omega
    unfold envGetNeed at this; omega
  unfold envGetPC
  iapply scan_entry Wp (getSite live hl) N (fo := fo) hsv hr hsp hslot
  rw [show (getSite live hl).entry = 0x80002c10#64 from rfl]
  iframe Ht Hgp Hcmp Hpc Hra Ha0 Ha1 Ha2 Hsp Hcl Hsv Hfa Hx Hout Hst
  isplitl [Hstk]
  · unfold stackScratch blockOwn; iexact Hstk
  isplit
  · -- the chain missed: return 0, `out` untouched
    unfold scanMissK
    iintro %R' %Mt' %fa'' %f'' %⟨hret, hpath, hf, hmiss, hroot, -⟩ Hpc HR HB Hst
    have hnone : st.get? fa x = none := (hget fa'' hpath).trans (look_root hf hmiss hroot)
    ihave ⟨Hra, Ha0, Hsp, Hsv, Hcl⟩ := scan_exit_regs hsv hret $$ HR
    ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt') hs64 hsep $$ HB
    iapply Hk $$ Hpc Hra
    iexists 0#64
    iframe Ha0 Hsp Hcl Hsv Hst
    unfold getOut
    rw [hnone]
    isplitl [Hstk]
    · unfold stackScratch envGetNeed; iexact Hstk
    isplitr
    · ipureintro; rfl
    · unfold slot24 blockOwn; iapply ownSet_forget $$ Hout
  · -- a hit in frame `fa'`: copy the value out, return 1
    unfold scanHitK
    iintro %fa' %f %Gm %img %j %v %R %Mt %B₁ %B₂
      %⟨hpath, hf, hj, hne, hF, h8, hB, hinv', hlay, hdisj⟩ Hpc HR HS #Hb #Hp #HGe Hclose
    have hlt : j < f.vars.length := by
      rcases Nat.lt_or_ge j f.vars.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hj
    have hvj : f.vars[j] = (x, v) := by simpa [List.getElem?_eq_getElem hlt] using hj
    have hsome : st.get? fa x = some v :=
      (hget fa' hpath).trans (look_hit hf (firstMatch_of_index hj hne))
    obtain ⟨hcap, -, -, hv1, hv2, -, hvw⟩ := hF.lay.slot hlt
    have hdv : out.toNat + 24 ≤ Gm.pv ∨ Gm.vblk.1 + Gm.vblk.2 ≤ out.toNat := by
      have := interval_apart (a := out.toNat) (n := 24) (b := Gm.vblk.1) (m := Gm.vblk.2)
        (by omega) (by omega) fun c h1 h2 => hF.sepOut c (by
          unfold frameS InExt; exact .inr ⟨hcap, .inr ⟨h1, h2⟩⟩)
      exact this.imp (fun h => hv1 ▸ h) id
    have hwo : 0x80000000 ≤ out.toNat ∧ out.toNat + 24 ≤ 0x100000000 ∧
        htifLo + 16 ≤ out.toNat ∧ out.toNat % 8 = 0 :=
      ⟨hslot.lo, hslot.hi, hslot.htif, hslot.align⟩
    have h21 : (R 21).toNat = out.toNat := by rw [hF.out]
    rw [show (getSite live hl).hit = 0x80002c70#64 from rfl]
    iapply wp_span Wp (get_hit hl (G := Gm) hsp.lo hsp.hi hr hF.stack hF.lay hlt h8 hF.env h21
      hwo hdv hsep)
    iframe Ht Hgp Hpc HR HS
    iintro %pc4 %R4 %Mt4 %⟨rfl, hret, hco⟩ Hpc HR HS
    have himg : ∀ a, frameS Gm a → imgM Mt4 a = img a := fun a ha =>
      (hco.frame a (hF.sepOut a ha)).trans (hF.img a ha)
    ihave ⟨HB, HF⟩ := get_split hdisj himg $$ HS
    ihave Hst := storeRepr_closeSame N hf hinv' hlay $$ [Hclose HF]
    · iframe Hclose HF Hb Hp HGe
    rw [← hB]
    ihave ⟨#Hname, #Hval⟩ := bindings_get N img Gm.pn Gm.pv f.vars hlt $$ Hb
    ihave ⟨Hra, Ha0, Hsp, Hsv, Hcl⟩ := scan_exit_regs hsv hret $$ HR
    ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt4) hs64 hsep $$ HB
    iapply Hk $$ Hpc Hra
    iexists 1#64
    iframe Ha0 Hsp Hcl Hsv Hst
    unfold getOut
    rw [hsome]
    isplitl [Hstk]
    · unfold stackScratch envGetNeed; iexact Hstk
    isplitr
    · ipureintro; rfl
    unfold valAt
    iexists (imgM Mt4)
    iframe Hout
    have w : ∀ o, o + 8 ≤ 24 → ldv .ld Mt4 (out.toNat + o) = ldv .ld Mt (Gm.pv + 24 * j + o) →
        imgW (imgM Mt4) (out.toNat + o) = imgW img (Gm.pv + 24 * j + o) := fun o ho h => by
      rw [← ldv_ld_img, h, ldv_ld_img]
      exact imgW_agree fun k hk => by
        have := hF.img _ (frameS_val hF.lay hlt (j := o + k) (by omega))
        rwa [show Gm.pv + 24 * j + (o + k) = Gm.pv + 24 * j + o + k by omega] at this
    unfold valImg
    rw [show out.toNat = out.toNat + 0 from rfl, w 0 (by omega) hco.w0, w 8 (by omega) hco.w1,
      w 16 (by omega) hco.w2]
    rw [show v = (f.vars[j]).2 by rw [hvj]]
    iexact Hval

end Main

end VsaIris.Interp

#print axioms VsaIris.Interp.envGet_spec
