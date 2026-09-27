import Vsa.Compiler.RTBase

/-!
# Leaf runtime routines: truthiness and string printing

`run_tr`: `truthy` leaves `trW tag payload` in `a0`. `run_ps`: `printstr`
appends the characters of a string object to the console.
-/

namespace Vsa.Compiler

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Truthiness of a value word pair. -/
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
  have k10 := has_mem h10 (by decide); have k11 := has_mem h11 (by decide)
  have k1 := has_mem hr (by decide)
  have e10 := srcVal_of_has h10; have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  simp only [a0, a1, ra] at k10 k11 k1 e10 e11 e1
  have hK : ∀ v L', Keep [t0, a0] L L' → Keep [t0, a0] L (gset L' 10 v) :=
    fun v L' h => h.gset (by decide)
  have hF : ∀ L', Keep [t0, a0] L L' → trW t p = 0 →
      Reaches code ⟨pcOf 136, L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 (trW t p) ∧ Keep [t0, a0] L B.regs) := by
    intro L' hL' hz
    have k1' : 1 ∈ keysG L' := by
      rw [show (1 : Nat) = ra from rfl]; exact has_mem (hL'.has (by decide) hr) (by decide)
    have e1' : srcVal 1 L' = r := srcVal_of_has (hL'.has (r := ra) (by decide) hr)
    apply run_at' hfit hseg 8 136 rfl
    wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k1', e1']
    refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, hK _ _ hL'⟩⟩
    rw [hz]; exact Has.set_self _ _ (by decide) (by decide)
  apply run_at' hfit hseg 0 trPos rfl
  wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
  split
  · next ht => exact hF L (Keep.refl _ _) (by simp [trW, ht])
  · next ht =>
    split
    · next hlt =>
      apply run_at' hfit hseg 5 133 rfl
      wp_simp [trCode, trPos, scPos, cpPos, itPos, psPos, k10, k11, k1, e10, e11, e1]
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

/-- Registers `printstr` may change. -/
def psClob : List Nat := [t0, t1, t2, s2, s3]

/-- The `printstr` loop head with `j` characters left. -/
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
  -- the loop
  have hloop : ∀ j A, PsInv L m o p cs r j A → Reaches code A (fun B => B.pc = r ∧ B.mem = m ∧
      ostr B.out = ostr o ++ String.ofList cs ∧ Keep psClob L B.regs) := by
    refine loop_run (fun j A hA => ?_) (fun A hA => ?_)
    · obtain ⟨hpc, hm, hj, h5, h6, h1, hk, ho⟩ := hA
      obtain ⟨pc, L', m', o'⟩ := A
      simp only at hpc hm h5 h6 h1 hk ho; subst hpc hm
      have k5 := has_mem h5 (by decide); have k6 := has_mem h6 (by decide)
      have k1 := has_mem h1 (by decide)
      have e5 := srcVal_of_has h5; have e6 := srcVal_of_has h6; have e1 := srcVal_of_has h1
      simp only [t0, t1, ra] at k5 k6 k1 e5 e6 e1
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
      wp_simp [psCode, psPos, putcR, hqn, hc, k5, k6, k1, e5, e6, e1, hpc, hj0]
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
      have k5 := has_mem h5 (by decide); have k1 := has_mem h1 (by decide)
      have e5 := srcVal_of_has h5; have e1 := srcVal_of_has h1
      simp only [t0, ra] at k5 k1 e5 e1
      apply run_at' hfit hseg 2 16 rfl
      wp_simp [psCode, psPos, putcR, k5, k1, e5]
      apply run_at' hfit hseg 31 45 rfl
      wp_simp [psCode, psPos, k1, e1]
      refine ⟨hal, reach_here ⟨rfl, rfl, ?_, hk⟩⟩
      simpa using ho
  -- entry
  have k11 := has_mem h11 (by decide); have k1 := has_mem hr (by decide)
  have e11 := srcVal_of_has h11; have e1 := srcVal_of_has hr
  simp only [a1, ra] at k11 k1 e11 e1
  apply run_block hfit hseg 0 2 psPos rfl
    (KP := fun L' m' o' => PsInv L m o p cs r cs.length ⟨pcOf 16, L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by simp [psCode])
  wp_simp [psCode, psPos, hpn, k11, k1, e11, e1, hs.len]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, rfl, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Has.set_self _ _ (by decide) (by decide)).set_other (by decide)
  · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Has.set_self _ _ (by decide) (by decide)
  · exact ((hr.set_other (by decide)).set_other (by decide))
  · exact (((Keep.refl _ _).gset (by decide)).gset (by decide))
  · simp

/-! ## `copy` -/

/-- Registers `copy` may change. -/
def cpClob : List Nat := [t0, a5, a6, a7]

/-- The `copy` loop head with `j` words left. -/
def CpInv (L0 : GRegs) (m : Mem) (o : Array String) (s d n : Nat) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf cpPos ∧ A.mem = copyW m s d (n - j) ∧ A.out = o ∧ j ≤ n ∧
    Has A.regs a7 (BitVec.ofNat 64 j) ∧ Has A.regs a6 (BitVec.ofNat 64 (s + 8 * (n - j))) ∧
    Has A.regs a5 (BitVec.ofNat 64 (d + 8 * (n - j))) ∧ Has A.regs ra r ∧ Keep cpClob L0 A.regs

/-- The source words are readable, the target words writable, and the two disjoint. -/
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
    have k7 := has_mem h7 (by decide); have k6 := has_mem h6 (by decide)
    have k5 := has_mem h5 (by decide)
    have e7 := srcVal_of_has h7; have e6 := srcVal_of_has h6; have e5 := srcVal_of_has h5
    simp only [a5, a6, a7] at k7 k6 k5 e7 e6 e5
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
    wp_simp [cpCode, cpPos, scPos, itPos, psPos, k7, k6, k5, e7, e6, e5, hsn, hdn, hj0, hsrc]
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
    have k7 := has_mem h7 (by decide); have k1 := has_mem h1 (by decide)
    have e7 := srcVal_of_has h7; have e1 := srcVal_of_has h1
    simp only [a7, ra] at k7 k1 e7 e1
    apply run_at' hfit hseg 0 cpPos rfl
    wp_simp [cpCode, cpPos, scPos, itPos, psPos, k7, e7]
    apply run_at' hfit hseg 7 (cpPos + 7) rfl
    wp_simp [cpCode, cpPos, scPos, itPos, psPos, k1, e1]
    exact ⟨hal, reach_here ⟨rfl, by simp, rfl, by simpa [a5] using h5, by simpa [a6] using h6, hk⟩⟩

/-! ## `strcmp` -/

/-- Registers `strcmp` may change. -/
def scClob : List Nat := [t0, t1, t2, t3, t4, t5, a0]

/-- The `strcmp` loop head after `i` equal characters; `j` characters of the
left string remain. -/
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
  -- the three exits
  have hexit : ∀ (e : Nat) (v : Int), (e = 16 ∧ v = -1 ∨ e = 18 ∧ v = 1 ∨ e = 20 ∧ v = 0) →
      cmpL xs ys = v → ∀ L', Has L' ra r → Keep scClob L L' →
      Reaches code ⟨pcOf (scPos + e), L', m, o⟩ (fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
        Has B.regs a0 (BitVec.ofInt 64 (cmpL xs ys)) ∧ Keep scClob L B.regs) := by
    intro e v he hv L' h1 hk
    have k1 := has_mem h1 (by decide); have e1 := srcVal_of_has h1
    simp only [ra] at k1 e1
    rw [hv]
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · apply run_at' hfit hseg _ _ rfl
      wp_simp [scCode, scPos, cpPos, itPos, psPos, k1, e1]
      refine ⟨hal, reach_here ⟨rfl, rfl, rfl, ?_, ?_⟩⟩ <;>
        simp (disch := decide) only [has_gset, keep_gset, a0, reduceIte, BitVec.reduceOfInt, hk] <;> rfl
  have hcmp : ∀ i, i ≤ xs.length → i ≤ ys.length → xs.take i = ys.take i →
      cmpL xs ys = cmpL (xs.drop i) (ys.drop i) := fun i h1 h2 h3 => (cmpL_drop i xs ys h3 h1 h2).symm
  -- the loop
  have hloop := loop_run' (code := code) (I := ScInv L m o p q xs ys r)
    (Q := fun B => B.pc = r ∧ B.mem = m ∧ B.out = o ∧
      Has B.regs a0 (BitVec.ofInt 64 (cmpL xs ys)) ∧ Keep scClob L B.regs)
    (fun j A hA => ?_) (fun A hA => ?_)
  rotate_left
  · -- one character
    obtain ⟨hpc, hm, ho, hj, hi, htk, h5, h6, h7, h28, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h5 h6 h7 h28 h1 hk; subst hpc hm ho
    have k5 := has_mem h5 (by decide); have k6 := has_mem h6 (by decide)
    have k7 := has_mem h7 (by decide); have k28 := has_mem h28 (by decide)
    have k1 := has_mem h1 (by decide)
    have e5 := srcVal_of_has h5; have e6 := srcVal_of_has h6; have e7 := srcVal_of_has h7
    have e28 := srcVal_of_has h28; have e1 := srcVal_of_has h1
    simp only [t0, t1, t2, t3, ra] at k5 k6 k7 k28 k1 e5 e6 e7 e28 e1
    generalize hI : xs.length - (j + 1) = i at *
    have hix : i < xs.length := by omega
    have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := ofNat_ne_zero (by omega) (by omega)
    apply run_at' hfit hseg 4 (scPos + 4) rfl
    wp_simp [scCode, scPos, cpPos, itPos, psPos, k5, k6, k7, k28, k1, e5, e6, e7, e28, e1, hj0]
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
  · -- left exhausted
    obtain ⟨hpc, hm, ho, hj, hi, htk, h5, h6, h7, h28, h1, hk⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h5 h6 h7 h28 h1 hk; subst hpc hm ho
    have k5 := has_mem h5 (by decide); have k6 := has_mem h6 (by decide)
    have e5 := srcVal_of_has h5; have e6 := srcVal_of_has h6
    simp only [t0, t1] at k5 k6 e5 e6
    simp only [Nat.sub_zero] at hi htk h6 e6
    apply run_at' hfit hseg 4 (scPos + 4) rfl
    wp_simp [scCode, scPos, cpPos, itPos, psPos, k5, k6, e5, e6]
    apply run_block hfit hseg 15 1 (scPos + 15) rfl
      (KP := fun L'' m'' o'' => L'' = L' ∧ m'' = m' ∧ o'' = o' ∧ ¬ ys.length - xs.length = 0)
      (fun L'' m'' o'' h => by
        obtain ⟨rfl, rfl, rfl, hyi⟩ := h
        refine hexit 16 (-1) (.inl ⟨rfl, rfl⟩) ?_ _ h1 hk
        have hxd : xs.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
        rw [hcmp xs.length (by omega) hi htk, hxd, List.drop_eq_getElem_cons (by omega)]
        rfl) (by simp [scCode])
    wp_simp [scCode, scPos, cpPos, itPos, psPos, k5, k6, e5, e6]
    by_cases hyi : ys.length - xs.length = 0
    · rw [if_pos (by rw [hyi]; rfl)]
      refine hexit 20 0 (.inr (.inr ⟨rfl, rfl⟩)) ?_ L' h1 hk
      have hxd : xs.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
      have hyd : ys.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
      rw [hcmp xs.length (by omega) hi htk, hxd, hyd]
      rfl
    · rw [if_neg (ofNat_ne_zero (by omega) (by omega))]
      exact hyi
  -- entry
  have k11 := has_mem h11 (by decide); have k13 := has_mem h13 (by decide)
  have e11 := srcVal_of_has h11; have e13 := srcVal_of_has h13
  simp only [a1, a3] at k11 k13 e11 e13
  have hpn : (BitVec.ofNat 64 p).toNat = p := toNat_ofNat_lt (by omega)
  have hqn : (BitVec.ofNat 64 q).toNat = q := toNat_ofNat_lt (by omega)
  apply run_block hfit hseg 0 4 scPos rfl
    (KP := fun L' m' o' => ScInv L m o p q xs ys r xs.length ⟨pcOf (scPos + 4), L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by simp [scCode])
  wp_simp [scCode, scPos, cpPos, itPos, psPos, k11, k13, e11, e13, hpn, hqn, hx.len, hy.len]
  refine ⟨⟨by omega, by omega, .inr (by omega)⟩, ⟨by omega, by omega, .inr (by omega)⟩,
    rfl, rfl, rfl, Nat.le_refl _, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals reg_simp [Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
  · exact hr
  · exact Keep.refl _ _

/-! ## `newframe` -/

/-- Registers `newframe` may change. -/
def nfClob : List Nat := [t0, t1, t2, t3, t4, a4, hpF]

/-- The `newframe` loop head with `j` slots left. -/
def NfInv (L0 : GRegs) (m : Mem) (o : Array String) (f par n : Nat) (r : BitVec 64)
    (j : Nat) (A : AM) : Prop :=
  A.pc = pcOf (nfPos + 20) ∧ A.mem = tagsW (applyW m (f, 8, BitVec.ofNat 64 par)) (f + 8) (n - j) ∧
    A.out = o ∧ j ≤ n ∧
    Has A.regs t4 (BitVec.ofNat 64 j) ∧ Has A.regs t2 (BitVec.ofNat 64 (f + 8 + 16 * (n - j))) ∧
    Has A.regs t3 6#64 ∧ Has A.regs t0 (BitVec.ofNat 64 (f + 8 + 16 * n)) ∧
    Has A.regs a4 (BitVec.ofNat 64 f) ∧ Has A.regs ra r ∧ Keep nfClob L0 A.regs ∧
    f + 8 + 16 * n ≤ frameEnd

/-- The frame region has room for a frame of `n` slots at `f`. -/
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
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hfb : frameBase = 0x80100000 := rfl
  have hfe : frameEnd = 0x90000000 := rfl
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
    have k29 := has_mem h29 (by decide); have k7 := has_mem h7 (by decide)
    have k28 := has_mem h28 (by decide)
    have e29 := srcVal_of_has h29; have e7 := srcVal_of_has h7; have e28 := srcVal_of_has h28
    simp only [t2, t3, t4] at k29 k7 k28 e29 e7 e28
    have hj0 : BitVec.ofNat 64 (j + 1) ≠ 0 := ofNat_ne_zero (by omega) (by omega)
    have han : (BitVec.ofNat 64 (f + 8 + 16 * (n - (j + 1)))).toNat = f + 8 + 16 * (n - (j + 1)) :=
      toNat_ofNat_lt (by omega)
    apply run_at' hfit hseg 20 (nfPos + 20) rfl
    wp_simp [nfCode, nfPos, trPos, scPos, cpPos, itPos, psPos, k29, k7, k28, e29, e7, e28, hj0, han]
    rw [if_neg (by omega)]
    have e : n - j = n - (j + 1) + 1 := by omega
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, reach_here ⟨rfl, by rw [e]; rfl, rfl, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hroom⟩⟩
    all_goals reg_simp
    all_goals first | exact h1 | exact hk | exact h28 | exact h5 | exact h14 | bv_eq
  · obtain ⟨hpc, hm, ho, hj, h29, h7, h28, h5, h14, h1, hk, hroom⟩ := hA
    obtain ⟨pc, L', m', o'⟩ := A
    simp only at hpc hm ho h29 h7 h28 h5 h14 h1 hk; subst hpc hm ho
    have k29 := has_mem h29 (by decide); have k5 := has_mem h5 (by decide)
    have k1 := has_mem h1 (by decide)
    have e29 := srcVal_of_has h29; have e5 := srcVal_of_has h5; have e1 := srcVal_of_has h1
    simp only [t0, t4, ra] at k29 k5 k1 e29 e5 e1
    apply run_at' hfit hseg 20 (nfPos + 20) rfl
    wp_simp [nfCode, nfPos, trPos, scPos, cpPos, itPos, psPos, k29, e29]
    apply run_at' hfit hseg 25 (nfPos + 25) rfl
    wp_simp [nfCode, nfPos, trPos, scPos, cpPos, itPos, psPos, k5, e5, k1, e1]
    refine ⟨hal, reach_here (.inl ⟨rfl, by omega, by simp, rfl, ?_, ?_, ?_⟩)⟩
    all_goals reg_simp
    all_goals first | exact h14 | exact hk | bv_eq
  -- entry
  have k15 := has_mem h15 (by decide); have k16 := has_mem h16 (by decide)
  have k23 := has_mem h23 (by decide)
  have e15 := srcVal_of_has h15; have e16 := srcVal_of_has h16; have e23 := srcVal_of_has h23
  simp only [a5, a6, hpF] at k15 k16 k23 e15 e16 e23
  have hfn : (BitVec.ofNat 64 f).toNat = f := toNat_ofNat_lt (by omega)
  apply run_block hfit hseg 0 20 nfPos rfl
    (KP := fun L' m' o' => NfInv L m o f par n r n ⟨pcOf (nfPos + 20), L', m', o'⟩)
    (fun L' m' o' h => hloop _ _ h) (by len_ok [nfCode])
  wp_simp [nfCode, nfPos, trPos, scPos, cpPos, itPos, psPos, k15, k16, k23, e15, e16, e23, hfn]
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
