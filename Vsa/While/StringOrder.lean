import Vsa.Sim.StrcmpSpecW3

open Vsa.Sim

namespace Vsa.While

theorem char_lt_iff (a b : Char) : (a < b) ↔ a.toNat < b.toNat := by
  show a.val < b.val ↔ _
  rw [UInt32.lt_iff_toNat_lt]; rfl

theorem byteVal_cons_zero (a : Char) (as : List Char) : byteVal (a :: as) 0 = a.toNat := rfl

theorem sss_nil_nil : strcmpSpecSign [] [] = 0 := by decide

theorem sss_nil_cons (b : Char) (bs : List Char) (hb : 0 < b.toNat) :
    strcmpSpecSign [] (b :: bs) = -1 := by
  have hpre : BytePrefix [] (b :: bs) 0 := by intro i hi; omega
  have hbne : byteVal [] 0 ≠ byteVal (b :: bs) 0 := by
    rw [byteVal_cons_zero]; unfold byteVal; simp; omega
  rw [strcmpSpecSign_at [] (b :: bs) 0 hpre hbne, byteVal_cons_zero]
  unfold isign byteVal; simp; omega

theorem sss_cons_nil (a : Char) (as : List Char) (ha : 0 < a.toNat) :
    strcmpSpecSign (a :: as) [] = 1 := by
  have hpre : BytePrefix (a :: as) [] 0 := by intro i hi; omega
  have hbne : byteVal (a :: as) 0 ≠ byteVal [] 0 := by
    rw [byteVal_cons_zero]; unfold byteVal; simp; omega
  rw [strcmpSpecSign_at (a :: as) [] 0 hpre hbne, byteVal_cons_zero]
  unfold isign byteVal; simp; omega

theorem sss_head_ne (a b : Char) (as bs : List Char) (hne : a.toNat ≠ b.toNat) :
    strcmpSpecSign (a :: as) (b :: bs) = isign a.toNat b.toNat := by
  have hpre : BytePrefix (a :: as) (b :: bs) 0 := by intro i hi; omega
  have hbne : byteVal (a :: as) 0 ≠ byteVal (b :: bs) 0 := by
    rw [byteVal_cons_zero, byteVal_cons_zero]; exact hne
  rw [strcmpSpecSign_at (a :: as) (b :: bs) 0 hpre hbne, byteVal_cons_zero, byteVal_cons_zero]

theorem sss_head_eq (a b : Char) (as bs : List Char) (heq : a.toNat = b.toNat) :
    strcmpSpecSign (a :: as) (b :: bs) = strcmpSpecSign as bs := by
  have hpre : ∀ i, i < 1 → byteVal (a :: as) i = byteVal (b :: bs) i := by
    intro i hi
    have : i = 0 := by omega
    subst this; rw [byteVal_cons_zero, byteVal_cons_zero]; exact heq
  have h := strcmpSpecSign_drop (a :: as) (b :: bs) 1 hpre
  simp only [List.drop_succ_cons, List.drop_zero] at h; exact h.symm

def AllNonzero (cs : List Char) : Prop := ∀ c ∈ cs, 0 < c.toNat

theorem allNonzero_tail {a : Char} {as : List Char} (h : AllNonzero (a :: as)) :
    AllNonzero as := fun c hc => h c (List.mem_cons_of_mem a hc)
theorem allNonzero_head {a : Char} {as : List Char} (h : AllNonzero (a :: as)) :
    0 < a.toNat := h a (List.mem_cons_self ..)

theorem strcmpSpecSign_neg_iff_lex :
    ∀ (csa csb : List Char), AllNonzero csa → AllNonzero csb →
      (strcmpSpecSign csa csb < 0 ↔ List.Lex (·<·) csa csb)
  | [], [], _, _ => by
    rw [sss_nil_nil]; constructor
    · intro h; exact absurd h (by decide)
    · intro h; cases h
  | [], b :: bs, _, hb => by
    rw [sss_nil_cons b bs (allNonzero_head hb)]
    constructor
    · intro _; exact List.Lex.nil
    · intro _; decide
  | a :: as, [], ha, _ => by
    rw [sss_cons_nil a as (allNonzero_head ha)]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; cases h
  | a :: as, b :: bs, ha, hb => by
    by_cases heq : a.toNat = b.toNat
    ·
      have hab : a = b := Char.ext (UInt32.toNat_inj.mp heq)
      rw [sss_head_eq a b as bs heq]
      rw [strcmpSpecSign_neg_iff_lex as bs (allNonzero_tail ha) (allNonzero_tail hb)]
      subst hab
      constructor
      · intro h; exact List.Lex.cons h
      · intro h; cases h with
        | rel hr => exact absurd (char_lt_iff a a |>.mp hr) (by omega)
        | cons h => exact h
    ·
      rw [sss_head_ne a b as bs heq]
      constructor
      · intro h

        have hlt : a.toNat < b.toNat := by
          unfold isign at h
          by_cases h1 : a.toNat < b.toNat
          · exact h1
          · rw [if_neg h1, if_neg heq] at h; exact absurd h (by decide)
        exact List.Lex.rel ((char_lt_iff a b).mpr hlt)
      · intro h
        cases h with
        | rel hr =>
          have hlt : a.toNat < b.toNat := (char_lt_iff a b).mp hr
          unfold isign; rw [if_pos hlt]; decide
        | cons h =>

          exact absurd rfl heq

theorem strcmpSpecSign_pos_iff_lex :
    ∀ (csa csb : List Char), AllNonzero csa → AllNonzero csb →
      (0 < strcmpSpecSign csa csb ↔ List.Lex (·<·) csb csa)
  | [], [], _, _ => by
    rw [sss_nil_nil]; constructor
    · intro h; exact absurd h (by decide)
    · intro h; cases h
  | [], b :: bs, _, hb => by
    rw [sss_nil_cons b bs (allNonzero_head hb)]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; cases h
  | a :: as, [], ha, _ => by
    rw [sss_cons_nil a as (allNonzero_head ha)]
    constructor
    · intro _; exact List.Lex.nil
    · intro _; decide
  | a :: as, b :: bs, ha, hb => by
    by_cases heq : a.toNat = b.toNat
    · have hab : a = b := Char.ext (UInt32.toNat_inj.mp heq)
      rw [sss_head_eq a b as bs heq]
      rw [strcmpSpecSign_pos_iff_lex as bs (allNonzero_tail ha) (allNonzero_tail hb)]
      subst hab
      constructor
      · intro h; exact List.Lex.cons h
      · intro h; cases h with
        | rel hr => exact absurd (char_lt_iff a a |>.mp hr) (by omega)
        | cons h => exact h
    · rw [sss_head_ne a b as bs heq]
      constructor
      · intro h
        have hgt : b.toNat < a.toNat := by
          unfold isign at h
          by_cases h1 : a.toNat < b.toNat
          · rw [if_pos h1] at h; exact absurd h (by decide)
          · rw [if_neg h1, if_neg heq] at h; omega
        exact List.Lex.rel ((char_lt_iff b a).mpr hgt)
      · intro h
        cases h with
        | rel hr =>
          have hgt : b.toNat < a.toNat := (char_lt_iff b a).mp hr
          unfold isign
          rw [if_neg (by omega), if_neg heq]; decide
        | cons h => exact absurd rfl heq

theorem isign_range (a b : Nat) : isign a b = -1 ∨ isign a b = 0 ∨ isign a b = 1 := by
  unfold isign
  by_cases h1 : a < b
  · rw [if_pos h1]; exact Or.inl rfl
  · rw [if_neg h1]; by_cases h2 : a = b
    · rw [if_pos h2]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h2]; exact Or.inr (Or.inr rfl)

theorem strcmpSpecSign_range (csa csb : List Char) :
    strcmpSpecSign csa csb = -1 ∨ strcmpSpecSign csa csb = 0 ∨ strcmpSpecSign csa csb = 1 :=
  isign_range _ _

theorem list_lex_trichotomy (csa csb : List Char) :
    csa < csb ∨ csa = csb ∨ csb < csa :=
  @Std.Trichotomous.rel_or_eq_or_rel_swap (List Char) (·<·) _ csa csb

theorem eq_of_strcmpSpecSign_zero_ascii (csa csb : List Char)
    (ha : AllNonzero csa) (hb : AllNonzero csb) (h : strcmpSpecSign csa csb = 0) :
    csa = csb := by
  rcases list_lex_trichotomy csa csb with hlt | heq | hgt
  · have := (strcmpSpecSign_neg_iff_lex csa csb ha hb).mpr hlt; omega
  · exact heq
  · have := (strcmpSpecSign_pos_iff_lex csa csb ha hb).mpr hgt; omega

theorem strcmpSpecSign_self_zero (cs : List Char) (h : AllNonzero cs) :
    strcmpSpecSign cs cs = 0 := by
  rcases Int.lt_trichotomy (strcmpSpecSign cs cs) 0 with hn | hz | hp
  · exact absurd ((strcmpSpecSign_neg_iff_lex cs cs h h).mp hn) (List.lt_irrefl cs)
  · exact hz
  · exact absurd ((strcmpSpecSign_pos_iff_lex cs cs h h).mp hp) (List.lt_irrefl cs)

end Vsa.While
