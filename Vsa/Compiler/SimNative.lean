import Vsa.Compiler.SimCallE

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def prClob : List Nat := t6 :: dpClob

theorem DpFrame.refl (m : Mem) : DpFrame m m := fun _ _ _ _ => rfl

theorem DpFrame.trans {m1 m2 m3 : Mem} (h1 : DpFrame m1 m2) (h2 : DpFrame m2 m3) : DpFrame m1 m3 :=
  fun a h h' h'' => (h2 a h h' h'').trans (h1 a h h' h'')

theorem DpFrame.above {m m' : Mem} (hd : DpFrame m m') {lo hi : Nat} (hlo : frameBase ≤ lo) : Agree m m' lo hi := by
  have hs : scratchStr = 0x80090000 := rfl
  have hb : bufBase = 0x80080000 := rfl
  have hf : frameBase = 0x80100000 := rfl
  exact fun a h1 _ h3 => hd a h3 (.inr (by omega)) (.inr (by omega))

theorem DpFrame.obj {m m' : Mem} (hd : DpFrame m m') (h : Nat) : ObjAgree m m' h := by
  have hob : objBase = 0x90000000 := rfl
  have hf : frameBase = 0x80100000 := rfl
  exact fun a ha h1 h2 => hd.above (lo := objBase) (hi := h) (by omega) a h1 h2 ha

theorem intercalate_cons' (a : String) (l : List String) :
    String.intercalate " " (a :: l) = a ++ (if l = [] then "" else " " ++ String.intercalate " " l) := by
  cases l with
  | nil => simp
  | cons b l => simp [String.intercalate_cons_cons, String.append_assoc]

theorem printArgs_cons (s : Store) (v : Value) (vs : List Value) :
    printArgs s (v :: vs) = v.display s ++ (if vs = [] then "" else " " ++ printArgs s vs) := by
  simp only [printArgs, List.map_cons, intercalate_cons', List.map_eq_nil_iff]

theorem InTmps.tail {H : CloMap} {m : Mem} {h sp t : Nat} {v : Value} {vs : List Value}
    (hv : InTmps H m h sp t (v :: vs)) : InTmp H m h sp t v ∧ InTmps H m h sp (t + 1) vs :=
  ⟨by simpa using hv 0 (by simp), fun j hj => by
    have := hv (j + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this⟩

theorem InTmps.frame {H : CloMap} {m m' : Mem} {h sp t : Nat} {vs : List Value}
    (hv : InTmps H m h sp t vs) (hag : Agree m m' stackLo stackHi) (ho : ObjAgree m m' h) (hsp : stackLo ≤ sp)
    (hal : sp % 16 = 0) (htop : sp + 16 + 16 * (t + vs.length) ≤ stackHi) : InTmps H m' h sp t vs := by
  intro j hj
  have := hv j hj
  unfold InTmp at this ⊢
  rw [hag _ (by omega) (by omega) (by omega), hag _ (by omega) (by omega) (by omega)]
  exact this.mono ho (Nat.le_refl _)

def plLen (t n : Nat) : Nat := (printLoopG 0 t n).length

theorem printLoopG_len : ∀ (p t n : Nat), (printLoopG p t n).length = plLen t n
  | _, _, 0 => rfl
  | p, t, n + 1 => by
    simp only [plLen, printLoopG, List.length_append]
    rw [printLoopG_len (p + _) (t + 1) n, printLoopG_len (0 + _) (t + 1) n]
    simp

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_printLoop {H : CloMap} {s : Store} {m0 : Mem} {h sp d fs : Nat} (hst : StackOK d sp fs) (hc : CloOK H s m0 h)
    (hh : h ≤ objEnd) : ∀ (vs : List Value) (t pos : Nat) (L : GRegs) (m : Mem) (o : Array String),
      Seg code pos (printLoopG pos t vs.length) → PosOK (pos + (printLoopG pos t vs.length).length) →
      Has L spR (BitVec.ofNat 64 sp) → 16 + 16 * (t + vs.length) ≤ fs → InTmps H m h sp t vs →
      ObjAgree m0 m h → FixedOK m →
      Reaches code ⟨pcOf pos, L, m, o⟩ (fun B => B.pc = pcOf (pos + (printLoopG pos t vs.length).length) ∧
        ostr B.out = ostr o ++ printArgs s vs ∧ DpFrame m B.mem ∧ Keep prClob L B.regs)
  | [], t, pos, L, m, o, _, _, _, _, _, _, _ =>
    reach_here ⟨by simp [printLoopG], by simp [printArgs], DpFrame.refl _, Keep.refl _ _⟩
  | v :: vs, t, pos, L, m, o, hseg, hP, hsp, htmp, hv, ho0, hfx => by
    have hb := hst.bounds
    simp only [List.length_cons] at htmp
    obtain ⟨hv0, hvs⟩ := hv.tail
    simp only [List.length_cons, printLoopG] at hseg hP ⊢
    obtain ⟨s1, s4⟩ := hseg.append
    obtain ⟨s1, s3⟩ := s1.append
    obtain ⟨s1, s2⟩ := s1.append
    have e4 : (loadTmp t).length = 4 := by simp [loadTmp]
    simp only [List.length_append, e4, List.length_singleton] at s2 s3 s4 hP ⊢
    have hq : PosOK (pos + 4 + 1) := posOK_le hP (by omega)
    refine run_loadTmp hR.fits s1 hsp hst (by omega) fun L1 hk1 g10 g11 => ?_
    apply run_whole hR.fits s2
    wp_simp [hq]
    refine ex_bind (run_dp hR (L := gset L1 1 (pcOf (pos + 4 + 1))) (m := m) (o := o)
      (by reg_simp []; exact g10) (by reg_simp []; exact g11) (by reg_simp []) (pcOf_aligned hq) hfx
      (dispW_of_repr (s := s) hv0 (hc.transport ho0 (Nat.le_refl _)) hh)) ?_
    rintro ⟨pc2, L2, m2, o2⟩ ⟨hpc2, hd2, ho2, hk2⟩
    simp only at hpc2 hd2 ho2 hk2; subst hpc2
    have hk12 : Keep prClob L L2 := hk1.mono (by decide) |>.trans
      ((Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide)))
    have hsp2 : Has L2 spR (BitVec.ofNat 64 sp) := hk12.has (by decide) hsp
    have hl : stackLo = 0xE0000000 := rfl
    have hf : frameBase = 0x80100000 := rfl
    have hfs := hst.top
    have hvs2 := hvs.frame (hd2.above (by omega)) (hd2.obj h) hb.1 hb.2.2 (by omega)
    have hfx2 : FixedOK m2 := fun i hi => (hfx i hi).transport (fun a h1 h2 h3 => hd2 a h3 (by
      have := fixed_bound i hi; have hs : scratchStr = 0x80090000 := rfl
      have hob : objBase = 0x90000000 := rfl; omega) (by
      have := fixed_bound i hi; have hs : bufBase = 0x80080000 := rfl
      have hob : objBase = 0x90000000 := rfl; omega))
    have ho02 : ObjAgree m0 m2 h := ho0.trans (hd2.obj h) (Nat.le_refl _)
    by_cases hv0' : vs = []
    · subst hv0'
      simp only [List.length_nil, if_true, List.length_nil, Nat.add_zero, printLoopG] at s3 s4 hP ⊢
      refine reach_here ⟨rfl, ?_, hd2, hk12⟩
      rw [ho2, printArgs_cons, String.ofList_toList]; simp
    · have hn : vs.length ≠ 0 := fun e => hv0' (List.length_eq_zero_iff.mp e)
      simp only [hn, if_false] at s3 s4 hP ⊢
      have hlp : (putc ' ').length = 23 := by decide
      simp only [hlp] at s4 hP ⊢
      apply run_whole hR.fits s3
      wp_simp [putc]
      refine reaches_pc (q' := pos + 28) (by omega) ?_
      have s4' := s4.cast (pos' := pos + 28) (by omega)
      simp only [printLoopG_len] at hP ⊢
      refine reaches_mono (run_printLoop hst hc hh vs (t + 1) (pos + 28) _ m2 _ s4'
        (by rw [printLoopG_len]; exact posOK_le hP (by omega))
        (by reg_simp []; exact hsp2) (by omega) hvs2 ho02 hfx2) ?_
      rintro B ⟨hpcB, hoB, hdB, hkB⟩
      refine ⟨by rw [hpcB, printLoopG_len]; congr 1 <;> omega, ?_, hd2.trans hdB, ?_⟩
      · rw [hoB, ostr_push, ho2, printArgs_cons, if_neg hv0', String.ofList_toList]
        have : toString (Char.ofNat (BitVec.ofNat 8 ' '.toNat).toNat) = " " := by decide
        rw [this]; simp [String.append_assoc]
      · exact hk12.trans (Keep.trans (by reg_simp []; exact Keep.refl _ _) hkB)

end

end Vsa.Compiler
