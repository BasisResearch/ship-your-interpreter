import Vsa.Compiler.SimClosure

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem ChainL.up {F : FrMap} {s : Store} :
    ∀ {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → ∀ i, i < Γ.length → ChainL F s (anc s a i) (Γ.drop i)
  | _, _, h, 0, _ => h
  | _, _, .top _ _ _, i + 1, hi => by simp at hi
  | _, _, .cons hfr hpar _ hc, i + 1, hi => by
    simp only [anc, hfr, hpar, List.drop_succ_cons]
    exact ChainL.up hc i (by simp at hi ⊢; omega)

theorem anc_succ_of {s : Store} {a b : Addr} {fr : Frame} (hfr : s.frames[a]? = some fr)
    (hpar : fr.parent = some b) (i : Nat) : anc s a (i + 1) = anc s b i := by
  simp only [anc, hfr, hpar]

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_up {F : FrMap} {H : CloMap} {s : Store} {m : Mem} {hF h : Nat} (hs : StoreRel F H s m hF h) :
    ∀ (i : Nat) {a : Addr} {Γ : List (List String)}, ChainL F s a Γ → i < Γ.length → ∀ (pos : Nat) (L : GRegs)
      (o : Array String), Seg code pos (List.replicate i (.ld envR envR)) →
      Has L envR (BitVec.ofNat 64 (parOf F (some a))) →
      Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.pc = pcOf (pos + i) ∧ B.mem = m ∧ B.out = o ∧
        Keep [envR] L B.regs ∧ Has B.regs envR (BitVec.ofNat 64 (parOf F (some (anc s a i)))))
  | 0, _, _, _, _, pos, L, o, _, h9 => reach_here ⟨by simp, rfl, rfl, Keep.refl _ _, h9⟩
  | i + 1, _, _, .top _ _ _, hi, _, _, _, _, _ => by simp at hi
  | i + 1, a, _, .cons (b := b) (fr := fr) (f := f) (L := La) hfr hpar hF hc, hi, pos, L, o, hseg, h9 => by
    have hb : frameBase = 0x80100000 := rfl
    have he : frameEnd = 0x90000000 := rfl
    have ht : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨h1, h2, h3, h4⟩ := hs.region a f La hF
    have htop := hs.top
    unfold frSize at h2
    have hfa := hs.frame a fr f La hfr hF
    obtain ⟨fb, hFb⟩ := hc.head'
    have hpa : parOf F (some a) = f := by simp [parOf, hF]
    have hpb : parAddr F fr = parOf F (some b) := by rw [parAddr_eq_parOf, hpar]
    rw [hpa] at h9
    have k9 := has_mem h9 (by decide); have e9 := srcVal_of_has h9
    simp only [envR] at k9 e9
    have n0 : (BitVec.ofNat 64 f).toNat = f := toNat_ofNat_lt (by omega)
    simp only [List.replicate_succ] at hseg
    obtain ⟨s1, s2⟩ := (show Seg code pos ([Ins.ld envR envR] ++ List.replicate i (.ld envR envR)) from hseg).append
    apply run_whole hR.fits s1
    wp_simp [k9, e9, n0]
    refine ⟨by unfold LdOK; omega, ?_⟩
    rw [hfa.parent, hpb]
    refine reaches_mono (run_up hs i hc (by simp at hi ⊢; omega) (pos + 1) _ o s2 (by reg_simp [])) ?_
    rintro B ⟨g1, g2, g3, g4, g5⟩
    refine ⟨by rw [g1]; congr 1 <;> omega, g2, g3, ?_, by rw [anc_succ_of hfr hpar]; exact g5⟩
    exact (Keep.gset (Keep.refl _ L) (by decide)).trans g4

theorem run_exitTo {T : List String} {V : View} {st : St} {d : Nat} {env : Addr} {C : GCtx} {sp fs pos : Nat}
    {A : AM} (hm : MS code T V st d env C.Γ sp fs A) (hA : A.pc = pcOf pos) (hC : CtxOK C)
    {t : Option (Nat × Nat)} (ht : ∀ p dt, t = some (p, dt) → dt ≤ C.blk ∧ PosOK p)
    (hseg : Seg code pos (exitTo C.blk pos t)) (hP : PosOK (pos + (exitTo C.blk pos t).length)) :
    Reaches code A (fun B => ExitAt code T V st d env C sp fs t B ∧ B.mem = A.mem ∧ B.out = A.out ∧
      Keep [envR] A.regs B.regs) := by
  obtain ⟨pc0, L, m, o⟩ := A
  simp only at hA; subst hA
  cases t with
  | none =>
    have hp0 : PosOK pos := posOK_le hP (by simp)
    apply run_jumps hR.fits hseg
    wp_simp [exitTo, hp0]
    exact reach_here ⟨rfl, rfl, rfl, Keep.refl _ _⟩
  | some pt =>
    obtain ⟨p, dt⟩ := pt
    obtain ⟨hdt, hpp⟩ := ht p dt rfl
    have hblk := hC.blk
    simp only [exitTo] at hseg hP
    obtain ⟨s1, s2⟩ := hseg.append
    simp only [List.length_append, List.length_replicate, List.length_singleton] at s2 hP
    refine ex_bind (run_up hR hm.rel (C.blk - dt) hm.chn (by omega) pos L o s1 hm.henv) ?_
    rintro ⟨pc1, L1, m1, o1⟩ ⟨hpc1, hm1, ho1, hk1, h9⟩
    simp only at hpc1 hm1 ho1 hk1 h9; subst hpc1 hm1 ho1
    have hpj : PosOK (pos + (C.blk - dt)) := posOK_le hP (by omega)
    apply run_jumps hR.fits s2
    wp_simp [hpj, hpp]
    refine reach_here ⟨⟨rfl, ?_⟩, rfl, rfl, hk1⟩
    exact {
      rel := hm.rel
      img := hm.img
      clo := hm.clo
      chn := hm.chn.up _ (by omega)
      out := hm.out
      ho := hk1.has (by decide) hm.ho
      hf := hk1.has (by decide) hm.hf
      henv := h9
      hsp := hk1.has (by decide) hm.hsp
      hdep := hk1.has (by decide) hm.hdep
      stk := hm.stk
      hfal := hm.hfal }

end

end Vsa.Compiler
