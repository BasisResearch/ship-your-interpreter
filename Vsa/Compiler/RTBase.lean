import Vsa.Compiler.RTCode
import Vsa.Compiler.PrintInt

/-!
# Proof support for the runtime

Register frames (`Keep`), aligned doubleword memory (`rdW_upd`), string objects
(`StrW`), the `wp_simp` normal form for `WP` goals, and entry points into a
routine's code at an interior label (`Seg.drop`).
-/

namespace Vsa.Compiler

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Segments -/

theorem Seg.drop {code : List Ins} {pos : Nat} {c : List Ins} (h : Seg code pos c) (k : Nat) :
    Seg code (pos + k) (c.drop k) := by
  intro j hj
  simp only [List.length_drop] at hj
  rw [Nat.add_assoc, h (k + j) (by omega)]
  simp

/-- Run a routine's code from its interior label `k`. -/
theorem run_at {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k : Nat) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P (b + k) (c.drop k) (fun _ _ _ => False) L m o) :
    Reaches code ⟨pcOf (b + k), L, m, o⟩ P :=
  WP_sound hfit _ _ _ L m o (hseg.drop k) (fun _ _ _ h => h.elim) h

/-- `run_at` with the label written as an absolute index. -/
theorem run_at' {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k j : Nat) (hj : b + k = j) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P j (c.drop k) (fun _ _ _ => False) L m o) :
    Reaches code ⟨pcOf j, L, m, o⟩ P := by
  subst hj; exact run_at hfit hseg k h

theorem sext_zero12 : (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide

theorem zero_add64 (x : BitVec 64) : 0#64 + x = x := by simp

theorem zero_add64' (x : BitVec 64) : (0 : BitVec 64) + x = x := by simp

theorem ofNat_add_lit (a k : Nat) (hk : k < 2 ^ 63) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a + k) := BitVec.ofNat_add_ofNat ..

theorem ofNat_add_neg (a k : Nat) (hk : 2 ^ 63 ≤ k ∧ k < 2 ^ 64) (ha : 2 ^ 64 - k ≤ a) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a - (2 ^ 64 - k)) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem sext_lo (n : Nat) (h : n < 2048) :
    (sign_extend (BitVec.ofNat 12 n) : BitVec 64) = BitVec.ofNat 64 n := by
  have := sext12_ofInt (n : Int) (by omega) (by omega)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast] at this; exact this

theorem sext_hi (n : Nat) (h1 : 2048 ≤ n) (h2 : n < 4096) :
    (sign_extend (BitVec.ofNat 12 n) : BitVec 64) = BitVec.ofNat 64 (n + (2 ^ 64 - 4096)) := by
  have e : BitVec.ofNat 12 n = BitVec.ofInt 12 ((n : Int) - 4096) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
  rw [e, sext12_ofInt _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega

theorem toInt_ofNat_small (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega

theorem toInt_ofNat_big (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toInt = (n : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_bmod]; simp [Int.bmod]; omega

/-- Run the `n` instructions at label `k` of a routine, then continue with `K`. -/
theorem run_block {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k n j : Nat) (hj : b + k = j)
    {KP : GRegs → Mem → Array String → Prop}
    (hK : ∀ L m o, KP L m o → Reaches code ⟨pcOf (j + n), L, m, o⟩ P)
    (hn : n ≤ (c.drop k).length)
    {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P j ((c.drop k).take n) KP L m o) :
    Reaches code ⟨pcOf j, L, m, o⟩ P := by
  subst hj
  have hs : Seg code (b + k) ((c.drop k).take n) := by
    have := (hseg.drop k)
    intro i hi
    simp only [List.length_take] at hi
    rw [this i (by omega)]
    simp [List.getElem?_take, show i < n by omega]
  have hlen : ((c.drop k).take n).length = n := by
    rw [List.length_take]; exact Nat.min_eq_left hn
  exact WP_sound hfit _ _ _ L m o hs (fun L' m' o' h' => by rw [hlen]; exact hK L' m' o' h') h

theorem reach_here {code : List Ins} {A : AM} {Q : AM → Prop} (h : Q A) : Reaches code A Q :=
  ⟨A, Star.refl _ _, h⟩

/-- The console text of an output array. -/
def ostr (o : Array String) : String := String.join o.toList

theorem ostr_push (o : Array String) (s : String) : ostr (o.push s) = ostr o ++ s := by
  simp [ostr, String.join_append]

theorem toString_char (c : Char) : toString c = String.ofList [c] :=
  String.toList_inj.mp (by rw [String.toList_ofList]; exact String.toList_singleton c)

/-! ## Register frames -/

/-- `L'` agrees with `L` outside the registers `S`. -/
def Keep (S : List Nat) (L L' : GRegs) : Prop := ∀ r, r ∉ S → lookupG r L' = lookupG r L

theorem Keep.refl (S : List Nat) (L : GRegs) : Keep S L L := fun _ _ => rfl

theorem Keep.trans {S : List Nat} {L L' L'' : GRegs} (h1 : Keep S L L') (h2 : Keep S L' L'') :
    Keep S L L'' := fun r hr => (h2 r hr).trans (h1 r hr)

theorem Keep.mono {S S' : List Nat} {L L' : GRegs} (h : Keep S L L') (hs : ∀ r ∈ S, r ∈ S') :
    Keep S' L L' := fun r hr => h r (fun h' => hr (hs r h'))

theorem Keep.gset {S : List Nat} {L L' : GRegs} {rd : Nat} {v : BitVec 64} (h : Keep S L L')
    (hrd : rd ∈ S) : Keep S L (gset L' rd v) := fun r hr => by
  rw [lookupG_set, if_neg (fun e => hr (by rw [e]; exact hrd))]; exact h r hr

theorem Keep.lib {S : List Nat} {L L' : GRegs} {v : BitVec 64} (h : Keep S L L')
    (hs : ∀ r ∈ clobbered, r ∈ S) : Keep S L ((10, v) :: eraseAll clobbered L') := fun r hr => by
  have h10 : r ≠ 10 := fun e => hr (hs r (by subst e; simp [clobbered]))
  simp only [lookupG, if_neg (Ne.symm h10)]
  rw [lookupG_eraseAll, if_neg (fun h' => hr (hs r h'))]
  exact h r hr

theorem Keep.has {S : List Nat} {L L' : GRegs} (h : Keep S L L') {r : Nat} {v : BitVec 64}
    (hr : r ∉ S) (hv : Has L r v) : Has L' r v := by
  obtain ⟨h31, (⟨rfl, rfl⟩ | ⟨hne, hl⟩)⟩ := hv
  · exact Has.zero _
  · exact ⟨h31, .inr ⟨hne, by rw [h r hr, hl]⟩⟩

theorem has_mem {L : GRegs} {n : Nat} {v : BitVec 64} (h : Has L n v) (hn : n ≠ 0) :
    n ∈ keysG L := by
  obtain ⟨-, (⟨rfl, -⟩ | ⟨-, hl⟩)⟩ := h
  · exact absurd rfl hn
  · exact mem_keysG_of_lookup hl

/-! ## Aligned doublewords -/

theorem rdW_upd {m : Mem} {a b : Nat} {v : BitVec 64} (ha : a % 8 = 0) (hb : b % 8 = 0) :
    rdW (applyW m (a, 8, v)) b = if b = a then v else rdW m b := by
  split
  · next h => subst h; exact rdW_write m b v
  · next h => exact rdW_write_other m b a v (by omega)

/-- `m'` agrees with `m` on the aligned words of `[lo, hi)`. -/
def Agree (m m' : Mem) (lo hi : Nat) : Prop :=
  ∀ a, lo ≤ a → a + 8 ≤ hi → a % 8 = 0 → rdW m' a = rdW m a

theorem Agree.refl (m : Mem) (lo hi : Nat) : Agree m m lo hi := fun _ _ _ _ => rfl

theorem Agree.trans {m m' m'' : Mem} {lo hi : Nat} (h1 : Agree m m' lo hi) (h2 : Agree m' m'' lo hi) :
    Agree m m'' lo hi := fun a h h' h'' => (h2 a h h' h'').trans (h1 a h h' h'')

theorem Agree.mono {m m' : Mem} {lo hi lo' hi' : Nat} (h : Agree m m' lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : Agree m m' lo' hi' := fun a ha hb hc => h a (by omega) (by omega) hc

theorem Agree.upd_out {m : Mem} {lo hi a : Nat} {v : BitVec 64} (ha : a % 8 = 0)
    (hout : a + 8 ≤ lo ∨ hi ≤ a) : Agree m (applyW m (a, 8, v)) lo hi := fun b h1 h2 h3 => by
  rw [rdW_upd ha h3, if_neg (by omega)]

/-! ## String objects -/

/-- The string object at `p` holds the characters `cs`. -/
structure StrW (m : Mem) (p : Nat) (cs : List Char) : Prop where
  lo : tohostAddr + 16 ≤ p
  hi : p + 8 + 8 * cs.length ≤ 2 ^ 32
  al : p % 8 = 0
  len : rdW m p = BitVec.ofNat 64 cs.length
  chars : ∀ i (h : i < cs.length), rdW m (p + 8 + 8 * i) = BitVec.ofNat 64 cs[i].toNat
  small : ∀ c ∈ cs, c.toNat < 256

theorem StrW.transport {m m' : Mem} {p : Nat} {cs : List Char} (h : StrW m p cs)
    (hag : Agree m m' p (p + 8 + 8 * cs.length)) : StrW m' p cs where
  lo := h.lo
  hi := h.hi
  al := h.al
  len := by rw [hag p (Nat.le_refl _) (by omega) h.al]; exact h.len
  chars i hi := by
    rw [hag (p + 8 + 8 * i) (by omega) (by omega) (by have := h.al; omega)]; exact h.chars i hi
  small := h.small

/-! ## Loops -/

theorem loop_run {code : List Ins} {I : Nat → AM → Prop} {Q : AM → Prop}
    (step : ∀ n A, I (n + 1) A → Reaches code A (I n)) (base : ∀ A, I 0 A → Reaches code A Q) :
    ∀ n A, I n A → Reaches code A Q
  | 0, A, h => base A h
  | n + 1, A, h => ex_bind (step n A h) (fun B hB => loop_run step base n B hB)

/-! ## Normal form of `WP` goals -/

/-- Compute a `WP` goal: unfold the instructions, evaluate register reads and
writes, branch and jump targets, and discharge decidable side conditions. -/
syntax "wp_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wp_simp) => `(tactic| wp_simp [])
  | `(tactic| wp_simp [$xs,*]) => `(tactic|
      simp (disch := first | decide | omega) only [WP, List.drop, List.take, List.drop_zero, List.drop_append,
        List.drop_eq_nil_of_le, List.length_append, List.length_cons, List.length_nil, putcR, List.cons_append, List.nil_append,
        srcVal_gset, keysG_gset, srcVal_zero, sext_ofInt12, brT_bOff_of, BrOK_bOff_of, jT_jOff_of,
        JOK_jOff_of, guard_eq, guard_ne, guard_lt, guard_ge, SrcOK, reduceIte, Nat.reduceEqDiff,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceMul, Nat.reducePow,
        ofNat_add_lit, ofNat_add_neg, true_and, and_true,
        true_or, or_true, false_or, or_false, decide_eq_true_eq, BitVec.zero_add, BitVec.add_zero,
        sext_zero12, zero_add64, zero_add64', sext_lo, sext_hi, BitVec.reduceOfInt, BitVec.reduceAdd, toInt_ofNat_small, toInt_ofNat_big,
        WP_li_iff, li_length_small, li_length_big, List.append_assoc, Nat.add_sub_cancel,
        tohostW_toNat, putcWord_low,
        Br, J, Call, mvi, addi, ret, mv, a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, t3, t4, t5,
        t6, s2, s3, s4, s5, s6, s9, s10, s11, ra, spR, hpO, envR, hpF, depR, $xs,*])

end Vsa.Compiler
