import Vsa.Compiler.RTBase
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def trW (t p : BitVec 64) : BitVec 64 :=
  if t = 0 then 0 else if t.toInt < 3 then (if p = 0 then 0 else 1) else 1

section
variable {code : List Ins} (hfit : Fits code)
include hfit

theorem run_tr (hseg : Seg code trPos (trCode trPos)) {L : GRegs} {m : Mem}
    {o : Array String} {t p r : BitVec 64}
    (h10 : Has L a0 t) (h11 : Has L a1 p) (hr : Has L ra r) (hal : r.toNat % 4 = 0) :
    Reaches code ⟨pcOf trPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 (trW t p) ∧ Keep [t0, a0] L B.regs) := by
  have hK : ∀ v L', Keep [t0, a0] L L' → Keep [t0, a0] L (gset L' 10 v) :=
    fun v L' h => h.gset (by decide)
  have hF : ∀ L', Keep [t0, a0] L L' → trW t p = 0 →
      Reaches code ⟨pcOf 136, L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 (trW t p) ∧ Keep [t0, a0] L B.regs) := by
    intro L' hL' hz
    apply run_at' hfit hseg 8 136 rfl
    wp_simp [trCode, rt_pos, (hL'.has (r := ra) (by decide) hr).wp]
    refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ hL'⟩⟩
    rw [hz]; exact Has.set_self _ _ (by decide) (by decide)
  apply run_at' hfit hseg 0 trPos rfl
  wp_simp [trCode, rt_pos, h10.wp, h11.wp, hr.wp]
  split
  · next ht => exact hF L (Keep.refl _ _) (by simp [trW, ht])
  · next ht =>
    split
    · next hlt =>
      apply run_at' hfit hseg 5 133 rfl
      wp_simp [trCode, rt_pos, h10.wp, h11.wp, hr.wp]
      split
      · next hp =>
        exact hF _ ((Keep.refl _ _).gset (by decide))
          (by unfold trW; rw [if_neg ht, if_pos (by omega), if_pos hp])
      · next hp =>
        refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ ((Keep.refl _ _).gset (by decide))⟩⟩
        have : trW t p = 1 := by unfold trW; rw [if_neg ht, if_pos (by omega), if_neg hp]
        rw [this]; exact Has.set_self _ _ (by decide) (by decide)
    · next hlt =>
      refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ ((Keep.refl _ _).gset (by decide))⟩⟩
      have : trW t p = 1 := by unfold trW; rw [if_neg ht, if_neg (by omega)]
      rw [this]; exact Has.set_self _ _ (by decide) (by decide)

def psClob : List Nat := [t0, t1, t2, s2, s3]

def PsInv (L0 : GRegs) (m : Mem) (o : Array String) (p : Nat) (cs : List Char) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf 16 ∧ A.mem = m ∧ j ≤ cs.length ∧ Has A.regs t0 (BitVec.ofNat 64 j) ∧
    Has A.regs t1 (BitVec.ofNat 64 (p + 8 + 8 * (cs.length - j))) ∧ Has A.regs ra r ∧
    Keep psClob L0 A.regs ∧ ostr A.out = ostr o ++ String.ofList (cs.take (cs.length - j))

theorem run_ps (hseg : Seg code psPos (psCode psPos)) {L : GRegs} {m : Mem} {o : Array String}
    {p : Nat} {cs : List Char} {r : BitVec 64}
    (h11 : Has L a1 (BitVec.ofNat 64 p)) (hr : Has L ra r) (hal : r.toNat % 4 = 0)
    (hs : StrW m p cs) :
    Reaches code ⟨pcOf psPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep psClob L B.regs) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hlo := hs.lo; have hhi := hs.hi
  have hpn : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; omega

  have hloop : ∀ j A, PsInv L m o p cs r j A → Reaches code A (fun B => B.pc = r ∧ B.mem = m ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep psClob L B.regs) := by
    refine loop_run (fun j A hA => ?_) (fun A hA => ?_)
    · obtain ⟨hpc, hm, hj, h5, h6, h1, hk, ho⟩ := hA
      obtain ⟨pc, L', m', o'⟩ := A
      simp only at hpc hm h5 h6 h1 hk ho; subst hpc hm
      have hi : cs.length - (j + 1) < cs.length := by omega
      have hq : p + 8 + 8 * (cs.length - (j + 1)) < 2 ^ 64 := by omega
      have hqn : (BitVec.ofNat 64 (p + 8 + 8 * (cs.length - (j + 1)))).toNat
          = p + 8 + 8 * (cs.length - (j + 1)) := by rw [BitVec.toNat_ofNat]; omega
      have hc := hs.chars _ hi
      have hsm := hs.small _ (List.getElem_mem hi)
      have hpc : putcWord 0 + BitVec.ofNat 64 (cs[cs.length - (j + 1)]).toNat
          = putcWord (BitVec.ofNat 8 (cs[cs.length - (j + 1)]).toNat) := putcWord_add _ hsm
      have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h; simp at this; omega
      apply run_at' hfit hseg 2 16 rfl
      wp_simp [psCode, rt_pos, putcR, hqn, hc, h5.wp, h6.wp, h1.wp, hpc, hj0]
      refine ⟨⟨by omega, by omega, .inr (by omega)⟩, reach_here ⟨rfl, rfl, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact Has.set_self _ _ (by decide) (by decide)
      · have e : p + 8 + 8 * (cs.length - (j + 1)) + 8 = p + 8 + 8 * (cs.length - j) := by omega
        rw [e]; exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
      · refine Keep.has (S := psClob) ?_ (by decide) h1
        refine (((((((Keep.refl _ _).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_) <;> decide
      · refine (((((((hk.gset ?_).gset ?_).gset ?_).gset ?_).gset ?_).gset ?_)) <;> decide
      · rw [ostr_push, ho, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsm, Char.ofNat_toNat, toString_char,
          String.append_assoc, ← String.ofList_append]
        congr 2
        rw [show cs.length - j = cs.length - (j + 1) + 1 by omega, List.take_succ,
          List.getElem?_eq_getElem hi]
        rfl
    · obtain ⟨hpc, hm, hj, h5, h6, h1, hk, ho⟩ := hA
      obtain ⟨pc, L', m', o'⟩ := A
      simp only at hpc hm h5 h6 h1 hk ho; subst hpc hm
      apply run_at' hfit hseg 2 16 rfl
      wp_simp [psCode, rt_pos, putcR, h5.wp, h1.wp]
      apply run_at' hfit hseg 31 45 rfl
      wp_simp [psCode, rt_pos, h1.wp]
      refine ⟨hal, reach_here ⟨rfl, rfl, ?_, hk⟩⟩
      simpa using ho

  apply run_block hfit hseg 0 2 psPos rfl
    (KP := fun L' m' o' => PsInv L m o p cs r cs.length ⟨pcOf 16, L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by simp [psCode])
  wp_simp [psCode, rt_pos, hpn, h11.wp, hr.wp, hs.len]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, rfl, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
  · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Has.set_self _ _ (by decide) (by decide)
  · exact ((hr.set_other (by decide)).set_other (by decide))
  · exact (((Keep.refl _ _).gset (by decide)).gset (by decide))
  · simp

def cpClob : List Nat := [t0, a5, a6, a7]

def CpInv (L0 : GRegs) (m : Mem) (o : Array String) (s d n : Nat) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf cpPos ∧ A.mem = copyW m s d (n - j) ∧ A.out = o ∧ j ≤ n ∧
    Has A.regs a7 (BitVec.ofNat 64 j) ∧ Has A.regs a6 (BitVec.ofNat 64 (s + 8 * (n - j))) ∧
    Has A.regs a5 (BitVec.ofNat 64 (d + 8 * (n - j))) ∧ Has A.regs ra r ∧ Keep cpClob L0 A.regs

structure CopyOK (s d n : Nat) : Prop where
  src_lo : 0x80000000 ≤ s
  src_hi : s + 8 * n ≤ 2 ^ 32
  src_ht : s + 8 * n ≤ tohostAddr ∨ tohostAddr + 8 ≤ s
  dst_lo : tohostAddr + 16 ≤ d
  dst_hi : d + 8 * n ≤ 2 ^ 32
  dst_al : d % 8 = 0
  src_al : s % 8 = 0
  disj : d + 8 * n ≤ s ∨ s + 8 * n ≤ d

theorem run_cp (hseg : Seg code cpPos (cpCode cpPos)) {L : GRegs} {m : Mem} {o : Array String}
    {s d n : Nat} {r : BitVec 64}
    (h16 : Has L a6 (BitVec.ofNat 64 s)) (h15 : Has L a5 (BitVec.ofNat 64 d))
    (h17 : Has L a7 (BitVec.ofNat 64 n)) (hr : Has L ra r) (hal : r.toNat % 4 = 0)
    (hok : CopyOK s d n) :
    Reaches code ⟨pcOf cpPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = copyW m s d n ∧ B.out = o ∧
      Has B.regs a5 (BitVec.ofNat 64 (d + 8 * n)) ∧ Has B.regs a6 (BitVec.ofNat 64 (s + 8 * n)) ∧
      Keep cpClob L B.regs) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hd8 := hok.dst_al
  refine loop_run (I := CpInv L m o s d n r) (fun j A hA => ?_) (fun A hA => ?_) n _
    ⟨rfl, by simp [copyW], rfl, Nat.le_refl _, h17, by simpa using h16, by simpa using h15, hr,
      Keep.refl _ _⟩
  · obtain ⟨hpc, hm, ho, hj, h7, h6, h5, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h7 h6 h5 h1 hk; subst hpc hm ho
    have hsn : (BitVec.ofNat 64 (s + 8 * (n - (j + 1)))).toNat = s + 8 * (n - (j + 1)) :=
      toNat_ofNat_lt (by have := hok.src_hi; omega)
    have hdn : (BitVec.ofNat 64 (d + 8 * (n - (j + 1)))).toNat = d + 8 * (n - (j + 1)) :=
      toNat_ofNat_lt (by have := hok.dst_hi; omega)
    have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := ofNat_ne_zero (by omega) (by have := hok.dst_hi; omega)
    have hsrc : rdW (copyW m s d (n - (j + 1))) (s + 8 * (n - (j + 1))) =
        rdW m (s + 8 * (n - (j + 1))) := by
      have := hok.disj; have := hok.src_al
      rw [rdW_copyW m s d hd8 _ _ (by omega), if_neg (by omega)]
    apply run_at' hfit hseg 0 cpPos rfl
    wp_simp [cpCode, rt_pos, h7.wp, h6.wp, h5.wp, hsn, hdn, hj0, hsrc]
    have hne : d + 8 * (n - (j + 1)) ≠ tohostAddr := by have := hok.dst_lo; omega
    rw [if_neg hne]
    have e : n - j = n - (j + 1) + 1 := by omega
    have := hok.src_lo; have := hok.src_hi; have := hok.src_ht; have := hok.dst_lo
    have := hok.dst_hi; have := hok.src_al
    refine ⟨⟨by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      reach_here ⟨rfl, by rw [e]; rfl, rfl, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      simp (disch := decide) only [has_gset, keep_gset, a5, a6, a7, ra, cpClob, t0, reduceIte,
        Nat.reduceEqDiff]
    · congr 1; omega
    · congr 1; omega
    · exact h1
    · exact hk
  · obtain ⟨hpc, hm, ho, hj, h7, h6, h5, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h7 h6 h5 h1 hk; subst hpc hm ho
    apply run_at' hfit hseg 0 cpPos rfl
    wp_simp [cpCode, rt_pos, h7.wp]
    apply run_at' hfit hseg 7 (cpPos + 7) rfl
    wp_simp [cpCode, rt_pos, h1.wp]
    exact ⟨hal, reach_here ⟨rfl, by simp, rfl, by simpa [a5] using h5, by simpa [a6] using h6, hk⟩⟩

def scClob : List Nat := [t0, t1, t2, t3, t4, t5, a0]

def ScInv (L0 : GRegs) (m : Mem) (o : Array String) (p q : Nat) (xs ys : List Char)
    (r : BitVec 64) (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf (scPos + 4) ∧ A.mem = m ∧ A.out = o ∧ j ≤ xs.length ∧
    xs.length - j ≤ ys.length ∧ xs.take (xs.length - j) = ys.take (xs.length - j) ∧
    Has A.regs t0 (BitVec.ofNat 64 j) ∧
    Has A.regs t1 (BitVec.ofNat 64 (ys.length - (xs.length - j))) ∧
    Has A.regs t2 (BitVec.ofNat 64 (p + 8 + 8 * (xs.length - j))) ∧
    Has A.regs t3 (BitVec.ofNat 64 (q + 8 + 8 * (xs.length - j))) ∧
    Has A.regs ra r ∧ Keep scClob L0 A.regs

theorem run_sc (hseg : Seg code scPos (scCode scPos)) {L : GRegs} {m : Mem} {o : Array String}
    {p q : Nat} {xs ys : List Char} {r : BitVec 64}
    (h11 : Has L a1 (BitVec.ofNat 64 p)) (h13 : Has L a3 (BitVec.ofNat 64 q))
    (hr : Has L ra r) (hal : r.toNat % 4 = 0) (hx : StrW m p xs) (hy : StrW m q ys) :
    Reaches code ⟨pcOf scPos, L, m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 (BitVec.ofInt 64 (cmpL xs ys)) ∧ Keep scClob L B.regs) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hxl := hx.lo; have hxh := hx.hi; have hyl := hy.lo; have hyh := hy.hi

  have hexit : ∀ (e : Nat) (v : Int), (e = 16 ∧ v = -1 ∨ e = 18 ∧ v = 1 ∨ e = 20 ∧ v = 0) →
      cmpL xs ys = v → ∀ L', Has L' ra r → Keep scClob L L' →
      Reaches code ⟨pcOf (scPos + e), L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 (BitVec.ofInt 64 (cmpL xs ys)) ∧ Keep scClob L B.regs) := by
    intro e v he hv L' h1 hk
    rw [hv]
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · apply run_at' hfit hseg _ _ rfl
      wp_simp [scCode, rt_pos, h1.wp]
      refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, ?_⟩⟩ <;>
        simp (disch := decide) only [has_gset, keep_gset, a0, reduceIte, BitVec.reduceOfInt, hk] <;> rfl
  have hcmp : ∀ i, i ≤ xs.length → i ≤ ys.length → xs.take i = ys.take i →
      cmpL xs ys = cmpL (xs.drop i) (ys.drop i) := fun i h1 h2 h3 => (cmpL_drop i xs ys h3 h1 h2).symm

  have hloop := loop_run' (code := code) (I := ScInv L m o p q xs ys r)
    (Q := fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 (BitVec.ofInt 64 (cmpL xs ys)) ∧ Keep scClob L B.regs)
    (fun j A hA => ?_) (fun A hA => ?_)
  rotate_left
  ·
    obtain ⟨hpc, hm, ho, hj, hi, htk, h5, h6, h7, h28, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h5 h6 h7 h28 h1 hk; subst hpc hm ho
    generalize hI : xs.length - (j + 1) = i at *
    have hix : i < xs.length := by omega
    have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := ofNat_ne_zero (by omega) (by omega)
    apply run_at' hfit hseg 4 (scPos + 4) rfl
    wp_simp [scCode, rt_pos, h5.wp, h6.wp, h7.wp, h28.wp, h1.wp, hj0]
    by_cases hyi : ys.length - i = 0
    · have hyi' : ys.length = i := by omega
      rw [if_pos (by rw [hyi]; rfl)]
      refine reaches_mono (hexit 18 1 (.inr (.inl ⟨rfl, rfl⟩)) ?_ L' h1 hk) (fun B hB => .inr hB)
      have hyd : ys.drop i = [] := List.drop_eq_nil_of_le (by omega)
      rw [hcmp i (by omega) (by omega) htk, hyd, List.drop_eq_getElem_cons hix]
      rfl
    · rw [if_neg (ofNat_ne_zero (by omega) (by omega))]
      have hiy : i < ys.length := by omega
      have hcx := hx.chars i hix; have hcy := hy.chars i hiy
      have hsx := hx.small _ (List.getElem_mem hix); have hsy := hy.small _ (List.getElem_mem hiy)
      have hn1 : (BitVec.ofNat 64 (p + 8 + 8 * i)).toNat = p + 8 + 8 * i := toNat_ofNat_lt (by omega)
      have hn2 : (BitVec.ofNat 64 (q + 8 + 8 * i)).toNat = q + 8 + 8 * i := toNat_ofNat_lt (by omega)
      simp (disch := first | decide | omega) only [hn1, hn2, hcx, hcy, toInt_ofNat_small]
      refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ⟨by omega, by omega, .inr (by omega)⟩, ?_⟩
      have hd : cmpL xs ys = cmpL (xs[i] :: xs.drop (i + 1)) (ys[i] :: ys.drop (i + 1)) := by
        rw [hcmp i (by omega) (by omega) htk, List.drop_eq_getElem_cons hix,
          List.drop_eq_getElem_cons hiy]
      split
      · next hlt =>
        refine reaches_mono (hexit 16 (-1) (.inl ⟨rfl, rfl⟩) ?_ _ ?_ ?_) (fun B hB => .inr hB)
        · rw [hd, cmpL_cons, if_pos (by omega)]
        · reg_simp; exact h1
        · reg_simp; exact hk
      · next hlt =>
        split
        · next hgt =>
          refine reaches_mono (hexit 18 1 (.inr (.inl ⟨rfl, rfl⟩)) ?_ _ ?_ ?_) (fun B hB => .inr hB)
          · rw [hd, cmpL_cons, if_neg (by omega), if_pos (by omega)]
          · reg_simp; exact h1
          · reg_simp; exact hk
        · next hgt =>
          have heq : xs[i] = ys[i] := by
            have e : xs[i].toNat = ys[i].toNat := by omega
            rw [← Char.ofNat_toNat xs[i], ← Char.ofNat_toNat ys[i], e]
          refine reach_here (.inl ⟨rfl, rfl, rfl, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
          · have e : xs.length - j = i + 1 := by omega
            rw [e]
            exact take_succ_eq htk hix hiy heq
          all_goals reg_simp
          all_goals first | exact h1 | exact hk | bv_eq
  ·
    obtain ⟨hpc, hm, ho, hj, hi, htk, h5, h6, h7, h28, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h5 h6 h7 h28 h1 hk; subst hpc hm ho
    simp only [Nat.sub_zero] at hi htk h6
    apply run_at' hfit hseg 4 (scPos + 4) rfl
    wp_simp [scCode, rt_pos, h5.wp, h6.wp]
    apply run_block hfit hseg 15 1 (scPos + 15) rfl
      (KP := fun L'' m'' o'' => L'' = L' ∧ m'' = m' ∧ o'' = o' ∧ ¬ ys.length - xs.length = 0)
      (fun L'' m'' o'' h => by
        obtain ⟨rfl, rfl, rfl, hyi⟩ := h
        refine hexit 16 (-1) (.inl ⟨rfl, rfl⟩) ?_ _ h1 hk
        have hxd : xs.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
        rw [hcmp xs.length (by omega) hi htk, hxd, List.drop_eq_getElem_cons (by omega)]
        rfl) (by simp [scCode])
    wp_simp [scCode, rt_pos, h5.wp, h6.wp]
    by_cases hyi : ys.length - xs.length = 0
    · rw [if_pos (by rw [hyi]; rfl)]
      refine hexit 20 0 (.inr (.inr ⟨rfl, rfl⟩)) ?_ L' h1 hk
      have hxd : xs.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
      have hyd : ys.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
      rw [hcmp xs.length (by omega) hi htk, hxd, hyd]
      rfl
    · rw [if_neg (ofNat_ne_zero (by omega) (by omega))]
      exact hyi

  have hpn : (BitVec.ofNat 64 p).toNat = p := toNat_ofNat_lt (by omega)
  have hqn : (BitVec.ofNat 64 q).toNat = q := toNat_ofNat_lt (by omega)
  apply run_block hfit hseg 0 4 scPos rfl
    (KP := fun L' m' o' => ScInv L m o p q xs ys r xs.length ⟨pcOf (scPos + 4), L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by simp [scCode])
  wp_simp [scCode, rt_pos, h11.wp, h13.wp, hpn, hqn, hx.len, hy.len]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ⟨by omega, by omega, .inr (by omega)⟩,
    rfl, rfl, rfl, Nat.le_refl _, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals reg_simp [Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
  · exact hr
  · exact Keep.refl _ _

def nfClob : List Nat := [t0, t1, t2, t3, t4, a4, hpF]

def NfInv (L0 : GRegs) (m : Mem) (o : Array String) (f par n : Nat) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf (nfPos + 20) ∧ A.mem = tagsW (applyW m (f, 8, BitVec.ofNat 64 par)) (f + 8) (n - j) ∧
    A.out = o ∧ j ≤ n ∧
    Has A.regs t4 (BitVec.ofNat 64 j) ∧ Has A.regs t2 (BitVec.ofNat 64 (f + 8 + 16 * (n - j))) ∧
    Has A.regs t3 6#64 ∧ Has A.regs t0 (BitVec.ofNat 64 (f + 8 + 16 * n)) ∧
    Has A.regs a4 (BitVec.ofNat 64 f) ∧ Has A.regs ra r ∧ Keep nfClob L0 A.regs ∧
    f + 8 + 16 * n ≤ frameEnd

structure FrameRoom (f n : Nat) : Prop where
  lo : frameBase ≤ f
  al : f % 8 = 0
  hi : f + 8 + 16 * n ≤ frameEnd

theorem run_nf (hseg : Seg code nfPos (nfCode nfPos)) {L : GRegs} {m : Mem} {o : Array String}
    {f par n : Nat} {r : BitVec 64}
    (h15 : Has L a5 (BitVec.ofNat 64 n)) (h16 : Has L a6 (BitVec.ofNat 64 par))
    (h23 : Has L hpF (BitVec.ofNat 64 f)) (hr : Has L ra r) (hal : r.toNat % 4 = 0)
    (hf : frameBase ≤ f ∧ f % 8 = 0 ∧ f ≤ frameEnd) (hn : n ≤ 1000) :
    Reaches code ⟨pcOf nfPos, L, m, o⟩ (fun B =>
      (B.pc = r ∧ f + 8 + 16 * n ≤ frameEnd ∧
        B.mem = tagsW (applyW m (f, 8, BitVec.ofNat 64 par)) (f + 8) n ∧ B.out = o ∧
        Has B.regs a4 (BitVec.ofNat 64 f) ∧ Has B.regs hpF (BitVec.ofNat 64 (f + 8 + 16 * n)) ∧
        Keep nfClob L B.regs) ∨
      (B.pc = pcOf errPos ∧ frameEnd < f + 8 + 16 * n)) := by
  obtain ⟨hfb, hfe, ht⟩ := frame_consts
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hloop := loop_run (code := code) (I := NfInv L m o f par n r)
    (Q := fun B => (B.pc = r ∧ f + 8 + 16 * n ≤ frameEnd ∧
        B.mem = tagsW (applyW m (f, 8, BitVec.ofNat 64 par)) (f + 8) n ∧ B.out = o ∧
        Has B.regs a4 (BitVec.ofNat 64 f) ∧ Has B.regs hpF (BitVec.ofNat 64 (f + 8 + 16 * n)) ∧
        Keep nfClob L B.regs) ∨ (B.pc = pcOf errPos ∧ frameEnd < f + 8 + 16 * n))
    (fun j A hA => ?_) (fun A hA => ?_)
  rotate_left
  · obtain ⟨hpc, hm, ho, hj, h29, h7, h28, h5, h14, h1, hk, hroom⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h29 h7 h28 h5 h14 h1 hk; subst hpc hm ho
    have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := ofNat_ne_zero (by omega) (by omega)
    have han : (BitVec.ofNat 64 (f + 8 + 16 * (n - (j + 1)))).toNat = f + 8 + 16 * (n - (j + 1)) :=
      toNat_ofNat_lt (by omega)
    apply run_at' hfit hseg 20 (nfPos + 20) rfl
    wp_simp [nfCode, rt_pos, h29.wp, h7.wp, h28.wp, hj0, han]
    rw [if_neg (by omega)]
    have e : n - j = n - (j + 1) + 1 := by omega
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, reach_here ⟨rfl, by rw [e]; rfl, rfl, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hroom⟩⟩
    all_goals reg_simp
    all_goals first | exact h1 | exact hk | exact h28 | exact h5 | exact h14 | bv_eq
  · obtain ⟨hpc, hm, ho, hj, h29, h7, h28, h5, h14, h1, hk, hroom⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h29 h7 h28 h5 h14 h1 hk; subst hpc hm ho
    apply run_at' hfit hseg 20 (nfPos + 20) rfl
    wp_simp [nfCode, rt_pos, h29.wp]
    apply run_at' hfit hseg 25 (nfPos + 25) rfl
    wp_simp [nfCode, rt_pos, h5.wp, h1.wp]
    refine ⟨hal, reach_here (.inl ⟨rfl, by omega, by simp, rfl, ?_, ?_, ?_⟩)⟩
    all_goals reg_simp
    all_goals first | exact h14 | exact hk | bv_eq

  have hfn : (BitVec.ofNat 64 f).toNat = f := toNat_ofNat_lt (by omega)
  apply run_block hfit hseg 0 20 nfPos rfl
    (KP := fun L' m' o' => NfInv L m o f par n r n ⟨pcOf (nfPos + 20), L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by len_ok [nfCode])
  wp_simp [nfCode, rt_pos, h15.wp, h16.wp, h23.wp, hfn]
  split
  · next hc => exact reach_here (.inr ⟨rfl, by omega⟩)
  · next hc =>
    rw [if_neg (by omega)]
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, rfl, by simp [tagsW], rfl, Nat.le_refl _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
    all_goals reg_simp [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    all_goals first | exact hr | exact Keep.refl _ _ | bv_eq

end

end Vsa.Compiler
