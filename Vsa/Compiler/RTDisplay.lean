import Vsa.Compiler.RTItos

/-!
# `display`: printing a value

`run_dp`: from `dpPos` with a value pair `(a0, a1)`, the routine appends the
text `DispW` assigns to the pair, writing memory only in the integer scratch
object and the digit buffer.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The runtime routines and the error exit are at their positions. -/
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

/-- The runtime's fixed strings are in memory. -/
def FixedOK (m : Mem) : Prop :=
  ∀ i (h : i < fixedStrs.length), StrW m (fixedAddr i) (fixedStrs[i]'h).toList

/-- How a native prints. -/
def natDisp (p : BitVec 64) : String :=
  if p = 0 then "<native fn print>" else if p = 1 then "<native fn println>" else "<native fn assert>"

/-- What `display` prints for the pair `(t, p)` in memory `m`. -/
def DispW (m : Mem) (t p : BitVec 64) (cs : List Char) : Prop :=
  if t = 2 then cs = (intToString p.toInt).toList
  else if t = 3 then StrW m p.toNat cs
  else if t = 4 then ∃ d, rdW m (p.toNat + 16) = BitVec.ofNat 64 d ∧ StrW m d cs ∧
    tohostAddr + 16 ≤ p.toNat ∧ p.toNat + 32 ≤ 2 ^ 32
  else if t = 1 then cs = (if p = 0 then "false" else "true").toList
  else if t = 5 then cs = (natDisp p).toList
  else cs = "null".toList

/-- Registers `display` may change. -/
def dpClob : List Nat := [ra, t0, t1, t2, a0, a1, a2, a3, a6, a7, s2, s3, s4, s5, s6, s9, s10]

/-- Memory `display` may write: the scratch object and the digit buffer. -/
def DpFrame (m m' : Mem) : Prop :=
  ∀ a, a % 8 = 0 → (a + 8 ≤ scratchStr ∨ scratchStr + 168 ≤ a) →
    (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) → rdW m' a = rdW m a

theorem ItDest_scratch : ItDest scratchStr := ⟨by decide, by decide, by decide, by decide⟩

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

/-- The shared return of `display`. -/
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

/-- `printstr` called from `display` at `dpPos + j`, followed by the jump to the return. -/
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

/-- **`display`.** -/
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
  -- registers after the prologue
  have hL : ∀ L', Keep dpClob L L' → Has L' s10 r → Has L' a1 p → True := fun _ _ _ _ => trivial
  -- the prologue dispatch
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
  · -- integer
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
    exact ⟨h1, fun a ha h5 h6 => by rw [h2]; exact hfr a ha h5 h6, h3, h4⟩
  · next ht2 =>
  have hd' := hd
  unfold DispW at hd'
  simp only [show (2 : BitVec 64) = 2#64 from rfl, show (3 : BitVec 64) = 3#64 from rfl,
    show (4 : BitVec 64) = 4#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
    show (5 : BitVec 64) = 5#64 from rfl, if_neg ht2] at hd'
  split
  · -- string
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
  · -- closure
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
  · -- boolean
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
  · -- native
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
  · -- null
    next ht5 =>
    rw [if_neg ht5] at hd'
    exact reaches_mono (dp_ps hR 22 (by decide) (by decide) (by reg_simp)
      (hd' ▸ hfs 0 (by decide)) (by reg_simp) hal (by reg_simp; exact Keep.refl _ _)) (fun B hB => hpd hB)

end

end Vsa.Compiler
