import Vsa.Compiler.RTItos
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure RTLoaded (code : List Ins) : Prop where
  fits : Fits code
  err : Seg code errPos errCode
  ps : Seg code psPos (psCode psPos)
  it : Seg code itPos (itCode itPos)
  cp : Seg code cpPos (cpCode cpPos)
  sc : Seg code scPos (scCode scPos)
  tr : Seg code trPos (trCode trPos)
  nf : Seg code nfPos (nfCode nfPos)
  dp : Seg code dpPos (dpCode dpPos)
  cs : Seg code csPos (csCode csPos)
  cc : Seg code ccPos (ccCode ccPos)
  add : Seg code addPos (addCode addPos)
  sub : Seg code subPos (subCode subPos)
  mul : Seg code mulPos (mulCode mulPos)
  div : Seg code divPos (divCode divPos)
  mod : Seg code modPos (modCode modPos)
  cmp : Seg code cmpPos (cmpCode cmpPos)
  eq : Seg code eqPos (eqCode eqPos)

def FixedOK (m : Mem) : Prop :=
  ∀ i (h : i < fixedStrs.length), StrW m (fixedAddr i) (fixedStrs[i]'h).toList

def natDisp (p : BitVec 64) : String :=
  if p = 0 then "<native fn print>" else if p = 1 then "<native fn println>" else "<native fn assert>"

def DispW (m : Mem) (t p : BitVec 64) (cs : List Char) : Prop :=
  if t = 2 then cs = (intToString p.toInt).toList
  else if t = 3 then StrW m p.toNat cs
  else if t = 4 then ∃ d, rdW m (p.toNat + 16) = BitVec.ofNat 64 d ∧ StrW m d cs ∧
    tohostAddr + 16 ≤ p.toNat ∧ p.toNat + 32 ≤ 2 ^ 32
  else if t = 1 then cs = (if p = 0 then "false" else "true").toList
  else if t = 5 then cs = (natDisp p).toList
  else cs = "null".toList

def dpClob : List Nat := [ra, t0, t1, t2, a0, a1, a2, a3, a6, a7, s2, s3, s4, s5, s6, s9, s10]

def DpFrame (m m' : Mem) : Prop :=
  ∀ a, a % 8 = 0 → (a + 8 ≤ scratchStr ∨ scratchStr + 168 ≤ a) →
    (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) → rdW m' a = rdW m a

theorem ItDest_scratch : ItDest scratchStr := ⟨by decide, by decide, by decide, by decide⟩

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem dp_ret {L L' : GRegs} {m : Mem} {o : Array String} {r : BitVec 64}
    (h26 : Has L' s10 r) (hal : r.toNat % 4 = 0) (hk : Keep dpClob L L') :
    Reaches code ⟨pcOf (dpPos + 124), L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Keep dpClob L B.regs) := by
  have k26 := has_mem h26 (by decide); have e26 := srcVal_of_has h26
  simp only [s10] at k26 e26
  apply run_seg hR.fits hR.dp 124 (dpPos + 124) rfl [mv ra s10, ret] (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [k26, e26]
  refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_⟩⟩
  reg_simp; exact hk

theorem dp_ps {L L' : GRegs} {m : Mem} {o : Array String} {r : BitVec 64} (j : Nat)
    (hJ : (dpCode dpPos)[j + 1]? = some (J (dpPos + j + 1) (dpPos + 124))) (hj : j + 1 < 126)
    {p : Nat} {cs : List Char} (h11 : Has L' a1 (BitVec.ofNat 64 p)) (hs : StrW m p cs)
    (h26 : Has L' s10 r) (hal : r.toNat % 4 = 0) (hk : Keep dpClob L L') :
    Reaches code ⟨pcOf psPos, gset L' 1 (pcOf (dpPos + j + 1)), m, o⟩ (fun B => B.pc = r ∧
      B.mem = m ∧ ostr B.out = ostr o ++ String.ofList cs ∧ Keep dpClob L B.regs) := by
  have hpos : PosOK (dpPos + j + 1) :=
    posOK_lt (by simp only [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]; omega)
  refine ex_bind (run_ps hR.fits hR.ps (h11.set_other (by decide)) (Has.set_self _ _ (by decide) (by decide))
    (pcOf_aligned hpos) hs) ?_
  rintro B ⟨hpc, hm, ho, hkb⟩
  obtain ⟨pc, L'', m'', o''⟩ := B
  simp only at hpc hm ho hkb; subst hpc hm
  have hk2 : Keep dpClob L L'' := (hk.trans (((Keep.refl _ _).gset (by decide)).trans (hkb.mono (by decide))))
  refine run_J hR.fits (hR.dp.get (j := j + 1) hJ) hpos (posOK_lt (by decide)) ?_
  refine reaches_mono (dp_ret hR (hkb.has (by decide) (h26.set_other (by decide))) hal hk2) ?_
  rintro B ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, by rw [h3]; exact ho, h4⟩

theorem run_dp {L : GRegs} {m : Mem} {o : Array String} {t p r : BitVec 64} {cs : List Char}
    (h10 : Has L a0 t) (h11 : Has L a1 p) (hr : Has L ra r) (hal : r.toNat % 4 = 0)
    (hfx : FixedOK m) (hd : DispW m t p cs) :
    Reaches code ⟨pcOf dpPos, L, m, o⟩ (fun B => B.pc = r ∧ DpFrame m B.mem ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep dpClob L B.regs) := by
  have hpd : ∀ {B : AM}, B.pc = r ∧ B.mem = m ∧ ostr B.out = ostr o ++ String.ofList cs ∧
      Keep dpClob L B.regs → B.pc = r ∧ DpFrame m B.mem ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep dpClob L B.regs :=
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, by rw [h2]; intro _ _ _ _; rfl, h3, h4⟩
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k1 := has_mem hr (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  simp only [a0, a1, ra] at k10 k11 k1 e10 e11 e1
  have hpn : p = BitVec.ofNat 64 p.toNat := by simp
  have hfs : ∀ i (hi : i < fixedStrs.length), StrW m (fixedAddr i) (fixedStrs[i]'hi).toList := hfx

  have hL : ∀ L', Keep dpClob L L' → Has L' s10 r → Has L' a1 p → True := fun _ _ _ _ => trivial

  apply run_seg hR.fits hR.dp 0 dpPos (by simp) ([mv s10 ra,
     mvi t0 2, Br .eq a0 t0 (dpPos + 2) (dpPos + 24),
     mvi t0 3, Br .eq a0 t0 (dpPos + 4) (dpPos + 49),
     mvi t0 4, Br .eq a0 t0 (dpPos + 6) (dpPos + 51),
     mvi t0 1, Br .eq a0 t0 (dpPos + 8) (dpPos + 55),
     mvi t0 5, Br .eq a0 t0 (dpPos + 10) (dpPos + 82)] ++
    liN a1 (fixedAddr 0) ++ [Call (dpPos + 22) psPos]) (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
  have hK : ∀ L', Keep dpClob L L' → ∀ v, Keep dpClob L (gset L' 5 v) :=
    fun L' h v => h.gset (by decide)
  have hK0 : Keep dpClob L (gset L 26 r) := (Keep.refl _ _).gset (by decide)
  split
  ·
    next ht =>
    have hcs : cs = (intToString p.toInt).toList := by
      unfold DispW at hd; rw [if_pos (by rw [ht]; rfl)] at hd; exact hd
    apply run_seg hR.fits hR.dp 24 (dpPos + 24) rfl
      (liN a2 scratchStr ++ [Call (dpPos + 35) itPos]) (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
    refine ex_bind (run_it hR.fits hR.it (by reg_simp; exact h11) (by reg_simp)
      (Has.set_self _ _ (by decide) (by decide)) (pcOf_aligned (posOK_lt (by decide))) ItDest_scratch) ?_
    rintro B ⟨hpc, ho, hstr, h13, hk, hfr⟩
    obtain ⟨pc, L2, m2, o2⟩ := B
    simp only at hpc ho hstr h13 hk hfr; subst hpc ho
    have hk2 : Keep dpClob L L2 := Keep.trans (by reg_simp; exact Keep.refl _ _) (hk.mono (by decide))
    have g26 : Has L2 s10 r := hk.has (by decide) (by reg_simp)
    apply run_seg hR.fits hR.dp 36 (dpPos + 36) rfl
      (liN a1 scratchStr ++ [Call (dpPos + 47) psPos]) (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
    refine reaches_mono (dp_ps hR 47 (by decide) (by decide) (Has.set_self _ _ (by decide) (by decide))
      (hcs ▸ hstr) (g26.set_other (by decide)) hal ((hk2.gset (by decide)))) ?_
    rintro B ⟨h1, h2, h3, h4⟩
    have hl20 := intToString_len_le p
    exact ⟨h1, fun a ha h5 h6 => by
      rw [h2]; exact hfr a ha (by rcases h5 with h5 | h5; exact .inl h5; exact .inr (by omega)) h6, h3, h4⟩
  · next ht2 =>
  have hd' := hd
  unfold DispW at hd'
  simp only [show (2 : BitVec 64) = 2#64 from rfl, show (3 : BitVec 64) = 3#64 from rfl,
    show (4 : BitVec 64) = 4#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
    show (5 : BitVec 64) = 5#64 from rfl, if_neg ht2] at hd'
  split
  ·
    next ht3 =>
    rw [if_pos ht3] at hd'
    apply run_seg hR.fits hR.dp 49 (dpPos + 49) rfl [Call (dpPos + 49) psPos] (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
    exact reaches_mono (dp_ps hR 49 (by decide) (by decide) (by reg_simp; rw [← hpn]; exact h11) hd'
      (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
  · next ht3 =>
  rw [if_neg ht3] at hd'
  split
  ·
    next ht4 =>
    rw [if_pos ht4] at hd'
    obtain ⟨d, hdd, hds, hp1, hp2⟩ := hd'
    have hp16 : (p + 16#64).toNat = p.toNat + 16 := by
      rw [BitVec.toNat_add]; simp; omega
    apply run_seg hR.fits hR.dp 51 (dpPos + 51) rfl [addi a1 a1 16, .ld a1 a1, Call (dpPos + 53) psPos]
      (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, hp16, hdd, k11, e11]
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ?_⟩
    exact reaches_mono (dp_ps hR 53 (by decide) (by decide) (by reg_simp) hds
      (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
  · next ht4 =>
  rw [if_neg ht4] at hd'
  split
  ·
    next ht1 =>
    rw [if_pos ht1] at hd'
    apply run_seg hR.fits hR.dp 55 (dpPos + 55) rfl
      ([Br .eq a1 0 (dpPos + 55) (dpPos + 69)] ++ liN a1 (fixedAddr 1) ++ [Call (dpPos + 67) psPos])
      (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k11, e11]
    split
    · next hp0 =>
      rw [if_pos hp0] at hd'
      apply run_seg hR.fits hR.dp 69 (dpPos + 69) rfl
        (liN a1 (fixedAddr 2) ++ [Call (dpPos + 80) psPos]) (by decide)
        (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
      exact reaches_mono (dp_ps hR 80 (by decide) (by decide) (by reg_simp)
        (hd' ▸ hfs 2 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
    · next hp0 =>
      rw [if_neg hp0] at hd'
      exact reaches_mono (dp_ps hR 67 (by decide) (by decide) (by reg_simp)
        (hd' ▸ hfs 1 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
  · next ht1 =>
  rw [if_neg ht1] at hd'
  split
  ·
    next ht5 =>
    rw [if_pos ht5] at hd'
    apply run_seg hR.fits hR.dp 82 (dpPos + 82) rfl
      ([Br .eq a1 0 (dpPos + 82) (dpPos + 98), mvi t0 1, Br .eq a1 t0 (dpPos + 84) (dpPos + 111)] ++
        liN a1 (fixedAddr 5) ++ [Call (dpPos + 96) psPos])
      (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k11, e11]
    unfold natDisp at hd'
    simp only [show (1 : BitVec 64) = 1#64 from rfl] at hd'
    split
    · next hp0 =>
      rw [if_pos hp0] at hd'
      apply run_seg hR.fits hR.dp 98 (dpPos + 98) rfl
        (liN a1 (fixedAddr 3) ++ [Call (dpPos + 109) psPos]) (by decide)
        (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
      exact reaches_mono (dp_ps hR 109 (by decide) (by decide) (by reg_simp)
        (hd' ▸ hfs 3 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
    · next hp0 =>
      rw [if_neg hp0] at hd'
      split
      · next hp1 =>
        rw [if_pos hp1] at hd'
        apply run_seg hR.fits hR.dp 111 (dpPos + 111) rfl
          (liN a1 (fixedAddr 4) ++ [Call (dpPos + 122) psPos]) (by decide)
          (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
        wp_simp [dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
        exact reaches_mono (dp_ps hR 122 (by decide) (by decide) (by reg_simp)
          (hd' ▸ hfs 4 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
      · next hp1 =>
        rw [if_neg hp1] at hd'
        exact reaches_mono (dp_ps hR 96 (by decide) (by decide) (by reg_simp)
          (hd' ▸ hfs 5 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)
  ·
    next ht5 =>
    rw [if_neg ht5] at hd'
    exact reaches_mono (dp_ps hR 22 (by decide) (by decide) (by reg_simp)
      (hd' ▸ hfs 0 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)

structure StrBelow (m : Mem) (h q : Nat) (cs : List Char) : Prop where
  str : StrW m q cs
  lo : objBase ≤ q
  hi : q + 8 + 8 * cs.length ≤ h

def CatW (m : Mem) (h : Nat) (t p : BitVec 64) (cs : List Char) : Prop :=
  if t = 3 then StrBelow m h p.toNat cs
  else if t = 2 then cs = (intToString p.toInt).toList
  else if t = 4 then ∃ d, rdW m (p.toNat + 24) = BitVec.ofNat 64 d ∧ StrBelow m h d cs ∧
    objBase ≤ p.toNat ∧ p.toNat + 32 ≤ h ∧ p.toNat % 8 = 0
  else if t = 1 then cs = (if p = 0 then "false" else "true").toList
  else if t = 5 then cs = "<native fn>".toList
  else cs = "null".toList

def csClob : List Nat := [ra, t0, t1, t2, a0, a1, a2, a3, a6, a7, s4, s5, s6, s9, s11, hpO]

structure CsRet (m m' : Mem) (h h' q : Nat) (cs : List Char) (L L' : GRegs) : Prop where
  ptr : Has L' a1 (BitVec.ofNat 64 q)
  str : StrBelow m' h' q cs
  hp : Has L' hpO (BitVec.ofNat 64 h')
  grow : h ≤ h' ∧ h' ≤ h + 168
  room : h' ≤ objEnd
  al : h' % 8 = 0
  frame : ∀ a, a % 8 = 0 → (a + 8 ≤ h ∨ h' ≤ a) → (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
    rdW m' a = rdW m a
  keep : Keep csClob L L'

structure ObjPtr (h : Nat) : Prop where
  lo : objBase ≤ h
  hi : h ≤ objEnd
  al : h % 8 = 0

theorem cs_ret {L' : GRegs} {m : Mem} {o : Array String} {r : BitVec 64}
    (h27 : Has L' s11 r) (hal : r.toNat % 4 = 0) :
    Reaches code ⟨pcOf (csPos + 81), L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      B.regs = gset L' ra r) := by
  have k27 := has_mem h27 (by decide); have e27 := srcVal_of_has h27
  simp only [s11] at k27 e27
  apply run_seg hR.fits hR.cs 81 (csPos + 81) rfl [mv ra s11, ret] (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [k27, e27]
  exact ⟨hal, reach_here ⟨rfl, rfl, rfl, rfl⟩⟩

theorem run_cs {L : GRegs} {m : Mem} {o : Array String} {t p r : BitVec 64} {h : Nat}
    {cs : List Char} (h10 : Has L a0 t) (h11 : Has L a1 p) (hr : Has L ra r)
    (h8 : Has L hpO (BitVec.ofNat 64 h)) (hal : r.toNat % 4 = 0) (hh : ObjPtr h)
    (hfx : FixedOK m) (hfb : fixedAddr 7 + 40 ≤ h) (hc : CatW m h t p cs) :
    Reaches code ⟨pcOf csPos, L, m, o⟩ (fun B => B.out = o ∧
      ((B.pc = r ∧ ∃ h' q, CsRet m B.mem h h' q cs L B.regs) ∨
        (B.pc = pcOf errPos ∧ objEnd < h + 168))) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have hbb : bufBase = 0x80080000 := rfl
  obtain ⟨hh1, hh2, hh3⟩ := hh
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k1 := has_mem hr (by decide); have k8 := has_mem h8 (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  have e8 := srcVal_of_has h8
  simp only [a0, a1, ra, hpO] at k10 k11 k1 k8 e10 e11 e1 e8
  have hpn : p = BitVec.ofNat 64 p.toNat := by simp
  have hfs : ∀ i (hi : i < fixedStrs.length), StrBelow m h (fixedAddr i) (fixedStrs[i]'hi).toList :=
    fun i hi => ⟨hfx i hi, by
      have : i < 8 := hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide, by
      have : fixedAddr i + 8 + 8 * (fixedStrs[i]'hi).toList.length ≤ fixedAddr 7 + 40 := by
        have : i < 8 := hi
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
          rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> revert hi <;> decide
      omega⟩

  have hdone : ∀ q L', StrBelow m h q cs → Has L' s11 r → Has L' a1 (BitVec.ofNat 64 q) →
      Has L' hpO (BitVec.ofNat 64 h) → Keep csClob L L' →
      Reaches code ⟨pcOf (csPos + 81), L', m, o⟩ (fun B => B.out = o ∧
        ((B.pc = r ∧ ∃ h' q, CsRet m B.mem h h' q cs L B.regs) ∨
          (B.pc = pcOf errPos ∧ objEnd < h + 168))) := by
    intro q L' hq h27 h11' h8' hk
    refine reaches_mono (cs_ret hR h27 hal) ?_
    rintro B ⟨h1, h2, h3, h4⟩
    refine ⟨h3, .inl ⟨h1, h, q, ?_, by rw [h2]; exact hq, ?_, ⟨Nat.le_refl _, by omega⟩, hh2, hh3,
      fun a _ _ _ => by rw [h2], ?_⟩⟩
    · rw [h4]; exact h11'.set_other (by decide)
    · rw [h4]; exact h8'.set_other (by decide)
    · rw [h4]; exact hk.gset (by decide)
  have hc' := hc
  unfold CatW at hc'
  simp only [show (2 : BitVec 64) = 2#64 from rfl, show (3 : BitVec 64) = 3#64 from rfl,
    show (4 : BitVec 64) = 4#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
    show (5 : BitVec 64) = 5#64 from rfl] at hc'
  apply run_seg hR.fits hR.cs 0 csPos (by simp) ([mv s11 ra,
     mvi t0 3, Br .eq a0 t0 (csPos + 2) (csPos + 81),
     mvi t0 2, Br .eq a0 t0 (csPos + 4) (csPos + 23),
     mvi t0 4, Br .eq a0 t0 (csPos + 6) (csPos + 41),
     mvi t0 1, Br .eq a0 t0 (csPos + 8) (csPos + 44),
     mvi t0 5, Br .eq a0 t0 (csPos + 10) (csPos + 69)] ++
    liN a1 (fixedAddr 0) ++ [J (csPos + 22) (csPos + 81)]) (by decide)
    (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
  wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
  split
  ·
    next ht3 =>
    rw [if_pos ht3] at hc'
    exact hdone _ _ hc' (by reg_simp) (by reg_simp; rw [← hpn]; exact h11) (by reg_simp; exact h8)
      (by reg_simp; exact Keep.refl _ _)
  · next ht3 =>
  rw [if_neg ht3] at hc'
  split
  ·
    next ht2 =>
    rw [if_pos ht2] at hc'
    apply run_seg hR.fits hR.cs 23 (csPos + 23) rfl
      ([addi t1 hpO 168] ++ liN t2 objEnd ++ [Br .lt t2 t1 (csPos + 35) errPos, mv a2 hpO,
        Call (csPos + 37) itPos]) (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k8, e8]
    split
    · next hov => exact reach_here ⟨rfl, .inr ⟨rfl, by omega⟩⟩
    · next hov =>
      have hid : ItDest h := ⟨by omega, by omega, hh3, .inr (by omega)⟩
      refine ex_bind (run_it hR.fits hR.it (by reg_simp; try exact h11) (by reg_simp; try exact h8)
        (Has.set_self _ _ (by decide) (by decide)) (pcOf_aligned (posOK_lt (by decide))) hid) ?_
      rintro B ⟨hpc, ho, hstr, h13, hk, hfr⟩
      obtain ⟨pc, L2, m2, o2⟩ := B
      simp only at hpc ho hstr h13 hk hfr; subst hpc ho
      rw [← hc'] at hstr h13
      have g8 : Has L2 hpO (BitVec.ofNat 64 h) := hk.has (by decide) (by reg_simp; exact h8)
      have g27 : Has L2 s11 r := hk.has (by decide) (by reg_simp)
      have k8' := has_mem g8 (by decide); have e8' := srcVal_of_has g8
      have k13 := has_mem h13 (by decide); have e13 := srcVal_of_has h13
      simp only [hpO, a3] at k8' e8' k13 e13
      apply run_seg hR.fits hR.cs 38 (csPos + 38) rfl [mv a1 hpO, mv hpO a3, J (csPos + 40) (csPos + 81)]
        (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k8', e8', k13, e13]
      have hlen := intToString_length p.toInt
      have hK := digits_len p
      rw [← hc'] at hlen
      have hcl : cs.length ≤ 20 := by split at hlen <;> omega
      refine reaches_mono (cs_ret hR (by reg_simp; try exact g27) hal) ?_
      rintro B ⟨h1, h2, h3, h4⟩
      refine ⟨h3, .inl ⟨h1, h + 8 + 8 * cs.length, h, ?_, ⟨by rw [h2]; exact hstr, by omega, by omega⟩, ?_,
        ⟨by omega, by omega⟩, by omega, by omega, fun a ha h5 h6 => by
          rw [h2]; exact hfr a ha (by rw [← hc']; exact h5) h6, ?_⟩⟩
      · rw [h4]; reg_simp
      · rw [h4]; reg_simp
      · rw [h4]; reg_simp
        exact Keep.trans (by reg_simp; exact Keep.refl _ _) (hk.mono (by decide))
  · next ht2 =>
  rw [if_neg ht2] at hc'
  split
  ·
    next ht4 =>
    rw [if_pos ht4] at hc'
    obtain ⟨d, hdd, hds, hp1, hp2, -⟩ := hc'
    have hp24 : (p + 24#64).toNat = p.toNat + 24 := by rw [BitVec.toNat_add]; simp; omega
    apply run_seg hR.fits hR.cs 41 (csPos + 41) rfl [addi a1 a1 24, .ld a1 a1, J (csPos + 43) (csPos + 81)]
      (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, hp24, hdd, k11, e11]
    refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ?_⟩
    exact hdone _ _ hds (by reg_simp) (by reg_simp) (by reg_simp; exact h8)
      (by reg_simp; exact Keep.refl _ _)
  · next ht4 =>
  rw [if_neg ht4] at hc'
  split
  ·
    next ht1 =>
    rw [if_pos ht1] at hc'
    apply run_seg hR.fits hR.cs 44 (csPos + 44) rfl
      ([Br .eq a1 0 (csPos + 44) (csPos + 57)] ++ liN a1 (fixedAddr 1) ++ [J (csPos + 56) (csPos + 81)])
      (by decide) (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos, k11, e11]
    split
    · next hp0 =>
      rw [if_pos hp0] at hc'
      apply run_seg hR.fits hR.cs 57 (csPos + 57) rfl
        (liN a1 (fixedAddr 2) ++ [J (csPos + 68) (csPos + 81)]) (by decide)
        (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
      exact hdone _ _ (hc' ▸ hfs 2 (by decide)) (by reg_simp) (by reg_simp) (by reg_simp; exact h8)
        (by reg_simp; exact Keep.refl _ _)
    · next hp0 =>
      rw [if_neg hp0] at hc'
      exact hdone _ _ (hc' ▸ hfs 1 (by decide)) (by reg_simp) (by reg_simp) (by reg_simp; exact h8)
        (by reg_simp; exact Keep.refl _ _)
  · next ht1 =>
  rw [if_neg ht1] at hc'
  split
  ·
    next ht5 =>
    rw [if_pos ht5] at hc'
    apply run_seg hR.fits hR.cs 69 (csPos + 69) rfl
      (liN a1 (fixedAddr 6) ++ [J (csPos + 80) (csPos + 81)]) (by decide)
      (KP := fun _ _ _ => False) (fun _ _ _ h => h.elim)
    wp_simp [csPos, dpPos, nfPos, trPos, scPos, cpPos, itPos, psPos]
    exact hdone _ _ (hc' ▸ hfs 6 (by decide)) (by reg_simp) (by reg_simp) (by reg_simp; exact h8)
      (by reg_simp; exact Keep.refl _ _)
  ·
    next ht5 =>
    rw [if_neg ht5] at hc'
    exact hdone _ _ (hc' ▸ hfs 0 (by decide)) (by reg_simp) (by reg_simp) (by reg_simp; exact h8)
      (by reg_simp; exact Keep.refl _ _)

def ccMem (m : Mem) (p q h : Nat) (xs ys : List Char) : Mem :=
  copyW (copyW (applyW m (h, 8, BitVec.ofNat 64 (xs.length + ys.length))) (p + 8) (h + 8) xs.length)
    (q + 8) (h + 8 + 8 * xs.length) ys.length

theorem ccMem_facts {m : Mem} {p q h : Nat} {xs ys : List Char} (hx : StrW m p xs) (hy : StrW m q ys)
    (hxb : p + 8 + 8 * xs.length ≤ h) (hyb : q + 8 + 8 * ys.length ≤ h) (hh : h % 8 = 0)
    (hlo : tohostAddr + 16 ≤ h) (hhi : h + 8 + 8 * (xs.length + ys.length) ≤ 2 ^ 32) :
    StrW (ccMem m p q h xs ys) h (xs ++ ys) ∧
      ∀ a, a % 8 = 0 → (a + 8 ≤ h ∨ h + 8 + 8 * (xs.length + ys.length) ≤ a) →
        rdW (ccMem m p q h xs ys) a = rdW m a := by
  have hpa := hx.al; have hqa := hy.al
  have R : ∀ a, a % 8 = 0 → rdW (ccMem m p q h xs ys) a =
      if h + 8 + 8 * xs.length ≤ a ∧ a < h + 8 + 8 * xs.length + 8 * ys.length then
        rdW m (q + 8 + (a - (h + 8 + 8 * xs.length)))
      else if h + 8 ≤ a ∧ a < h + 8 + 8 * xs.length then rdW m (p + 8 + (a - (h + 8)))
      else if a = h then BitVec.ofNat 64 (xs.length + ys.length) else rdW m a := by
    intro a ha
    unfold ccMem
    rw [rdW_copyW _ _ _ (by omega) _ _ ha]
    split
    · rw [rdW_copyW _ _ _ (by omega) _ _ (by omega), if_neg (by omega), rdW_upd hh (by omega),
        if_neg (by omega)]
    · rw [rdW_copyW _ _ _ (by omega) _ _ ha]
      split
      · rw [rdW_upd hh (by omega), if_neg (by omega)]
      · rw [rdW_upd hh ha]
  refine ⟨⟨hlo, by simp; omega, hh, ?_, ?_, ?_⟩, ?_⟩
  · rw [R h hh, if_neg (by omega), if_neg (by omega), if_pos rfl]; simp
  · intro i hi
    rw [R _ (by omega)]
    simp only [List.length_append] at hi
    by_cases h1 : i < xs.length
    · rw [if_neg (by omega), if_pos (by omega), List.getElem_append_left h1]
      rw [show p + 8 + (h + 8 + 8 * i - (h + 8)) = p + 8 + 8 * i by omega]
      exact hx.chars i h1
    · rw [if_pos (by omega), List.getElem_append_right (by omega)]
      rw [show q + 8 + (h + 8 + 8 * i - (h + 8 + 8 * xs.length)) = q + 8 + 8 * (i - xs.length) by omega]
      exact hy.chars _ (by omega)
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hx.small c hc
    · exact hy.small c hc
  · intro a ha hout
    rw [R a ha, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def ccClob : List Nat := [ra, t0, t2, t3, t4, t5, t6, a1, a4, a5, a6, a7, s11, hpO]

structure CcRet (m m' : Mem) (h : Nat) (cs : List Char) (L L' : GRegs) : Prop where
  ptr : Has L' a1 (BitVec.ofNat 64 h)
  str : StrW m' h cs
  hp : Has L' hpO (BitVec.ofNat 64 (h + 8 + 8 * cs.length))
  room : h + 8 + 8 * cs.length ≤ objEnd
  frame : ∀ a, a % 8 = 0 → (a + 8 ≤ h ∨ h + 8 + 8 * cs.length ≤ a) → rdW m' a = rdW m a
  keep : Keep ccClob L L'

theorem run_cc {L : GRegs} {m : Mem} {o : Array String} {r : BitVec 64} {p q h : Nat}
    {xs ys : List Char} (h11 : Has L a1 (BitVec.ofNat 64 p)) (h13 : Has L a3 (BitVec.ofNat 64 q))
    (hr : Has L ra r) (h8 : Has L hpO (BitVec.ofNat 64 h)) (hal : r.toNat % 4 = 0) (hh : ObjPtr h)
    (hx : StrBelow m h p xs) (hy : StrBelow m h q ys) :
    Reaches code ⟨pcOf ccPos, L, m, o⟩ (fun B => B.out = o ∧
      ((B.pc = r ∧ CcRet m B.mem h (xs ++ ys) L B.regs) ∨
        (B.pc = pcOf errPos ∧ objEnd < h + 8 + 8 * (xs.length + ys.length)))) := by
  obtain ⟨hob, hoe, ht⟩ := obj_consts
  obtain ⟨hh1, hh2, hh3⟩ := hh
  obtain ⟨hxs, -, hxb⟩ := hx; obtain ⟨hys, -, hyb⟩ := hy
  have := hxs.lo; have := hxs.al; have := hys.lo; have := hys.al
  apply run_at' hR.fits hR.cc 0 ccPos rfl
  wp_simp [rt_pos, ccCode, h11.wp, h13.wp, hr.wp, h8.wp, toNat_ofNat_lt, hxs.len, hys.len,
    show h ≠ tohostAddr by omega]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ⟨by omega, by omega, .inr (by omega)⟩, ?_⟩
  split
  · next hov => exact reach_here ⟨rfl, .inr ⟨rfl, by omega⟩⟩
  · next hov =>
  refine ⟨⟨by omega, by omega, by omega, hh3⟩, ?_⟩
  have hcp1 : CopyOK (p + 8) (h + 8) xs.length :=
    ⟨by omega, by omega, .inr (by omega), by omega, by omega, by omega, by omega, .inr (by omega)⟩
  refine ex_bind (run_cp hR.fits hR.cp (by reg_simp) (by reg_simp) (by reg_simp)
    (Has.set_self _ _ (by decide) (by decide)) (pcOf_aligned (posOK_lt (by decide))) hcp1) ?_
  rintro ⟨pc, L2, m2, o2⟩ ⟨rfl, rfl, rfl, h15, h16, hk⟩
  have g13 : Has L2 a3 (BitVec.ofNat 64 q) := hk.has (by decide) (by reg_simp; exact h13)
  have g29 : Has L2 t4 (BitVec.ofNat 64 ys.length) := hk.has (by decide) (by reg_simp)
  have g14 : Has L2 a4 (BitVec.ofNat 64 h) := hk.has (by decide) (by reg_simp)
  have g27 : Has L2 s11 r := hk.has (by decide) (by reg_simp)
  apply run_at' hR.fits hR.cc 25 (ccPos + 25) rfl
  wp_simp [rt_pos, ccCode, g13.wp, g29.wp]
  have hcp2 : CopyOK (q + 8) (h + 8 + 8 * xs.length) ys.length :=
    ⟨by omega, by omega, .inr (by omega), by omega, by omega, by omega, by omega, .inr (by omega)⟩
  refine ex_bind (run_cp hR.fits hR.cp (by reg_simp) (by reg_simp; exact h15) (by reg_simp)
    (Has.set_self _ _ (by decide) (by decide)) (pcOf_aligned (posOK_lt (by decide))) hcp2) ?_
  rintro ⟨pc, L3, m3, o3⟩ ⟨rfl, rfl, rfl, h15', h16', hk'⟩
  have g14' : Has L3 a4 (BitVec.ofNat 64 h) := hk'.has (by decide) (by reg_simp; exact g14)
  have g27' : Has L3 s11 r := hk'.has (by decide) (by reg_simp; exact g27)
  apply run_at' hR.fits hR.cc 28 (ccPos + 28) rfl
  wp_simp [rt_pos, ccCode, h15'.wp, g14'.wp, g27'.wp]
  obtain ⟨hstr, hfr⟩ := ccMem_facts hR hxs hys hxb hyb hh3 (by omega) (by omega)
  refine ⟨hal, reach_here ⟨rfl, .inl ⟨rfl, ?_, hstr, ?_, by simp; omega, fun a ha h1 => ?_, ?_⟩⟩⟩
  · reg_simp
  · reg_simp; simp only [List.length_append]; bv_eq
  · have := hfr a ha (by simpa using h1); exact this
  · reg_simp
    refine Keep.trans (Keep.trans ?_ (hk.mono (by decide))) (Keep.trans ?_ (hk'.mono (by decide)))
    · reg_simp; exact Keep.refl _ _
    · reg_simp; exact Keep.refl _ _

end

end Vsa.Compiler
