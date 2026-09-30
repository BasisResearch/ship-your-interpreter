import Vsa.Compiler.Frag

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa.Sim Vsa.While

def outStr (A : AM) : String := String.join A.out.toList

theorem outStr_push (A : AM) (pc : BitVec 64) (L : GRegs) (m : Mem) (s : String) :
    outStr ⟨pc, L, m, A.out.push s⟩ = outStr A ++ s := by
  simp [outStr, String.join_append]

theorem join_push (arr : Array String) (s : String) :
    String.join (arr.push s).toList = String.join arr.toList ++ s := by
  simp [String.join_append]

def digitsLE (N : Nat) : List Nat :=
  if N < 10 then [N] else N % 10 :: digitsLE (N / 10)
termination_by N
decreasing_by omega

theorem digitsLE_small {N : Nat} (h : N < 10) : digitsLE N = [N] := by
  rw [digitsLE, if_pos h]

theorem digitsLE_big {N : Nat} (h : ¬ N < 10) : digitsLE N = N % 10 :: digitsLE (N / 10) := by
  rw [digitsLE, if_neg h]

theorem natDigits_eq : ∀ (f N : Nat), N < f →
    natDigits f N = ((digitsLE N).map Nat.digitChar).reverse
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, N, h => by
    by_cases hN : N < 10
    · simp [natDigits, hN, digitsLE_small hN]
    · rw [natDigits, if_neg hN, digitsLE_big hN, natDigits_eq f (N / 10) (by omega)]
      simp

theorem foldl_push (l : List Char) (s : String) :
    l.foldl String.push s = s ++ l.foldl String.push "" := by
  induction l generalizing s with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons]
    rw [ih (s.push c), ih ("".push c), String.push_eq_append, String.push_eq_append,
      String.append_assoc]
    simp

theorem natToString_eq (N : Nat) :
    natToString N = ((digitsLE N).map Nat.digitChar).reverse.foldl String.push "" := by
  rw [natToString, natDigits_eq (N + 1) N (by omega)]

theorem intToString_eq (m : Int) :
    intToString m = (if m < 0 then "-" else "") ++ natToString m.natAbs := by
  cases m with
  | ofNat k =>
    simp only [intToString, Int.ofNat_eq_natCast, Int.natAbs_natCast]
    rw [if_neg (by omega)]
    simp
  | negSucc k =>
    simp only [intToString]
    rw [if_pos (Int.negSucc_lt_zero k)]
    rfl

theorem digitsLE_length_le : ∀ (k N : Nat), N < 10 ^ (k + 1) → (digitsLE N).length ≤ k + 1
  | 0, N, h => by rw [digitsLE_small (by simpa using h)]; simp
  | k + 1, N, h => by
    by_cases hN : N < 10
    · rw [digitsLE_small hN]; simp
    · rw [digitsLE_big hN]
      have := digitsLE_length_le k (N / 10) (by rw [Nat.pow_succ] at h; omega)
      simp; omega

theorem digitsLE_lt (N : Nat) : ∀ d ∈ digitsLE N, d < 10 := by
  by_cases hN : N < 10
  · rw [digitsLE_small hN]; simpa using hN
  · rw [digitsLE_big hN]
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact digitsLE_lt (N / 10) d hd
termination_by N
decreasing_by omega

theorem char_digit (d : Nat) (h : d < 10) : Char.ofNat (48 + d) = Nat.digitChar d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem toInt_ofInt_small (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) :
    (BitVec.ofInt 64 z).toInt = z := by
  rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp <;> omega

theorem putcWord_add (c : Nat) (hc : c < 256) :
    putcWord 0 + BitVec.ofNat 64 c = putcWord (BitVec.ofNat 8 c) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (putcWord 0).toNat = 0x0101000000000000 := by decide
  rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat]
  simp only [putcWord, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.zeroExtend,
    BitVec.toNat_setWidth]
  have e1 : c % 2 ^ 8 % 2 ^ 64 = c := by omega
  have e2 : (72339069014638592 : Nat) % 2 ^ 64 = 2 ^ 8 * 282574488338432 := by decide
  have e3 : (72339069014638592 + c % 2 ^ 64) % 2 ^ 64 = 2 ^ 8 * 282574488338432 + c := by omega
  rw [e1, e2, e3, Nat.two_pow_add_eq_or_of_lt (show c < 2 ^ 8 by omega)]

theorem pcOf_back (k n : Nat) (hk : PosOK k) (hn : n ≤ k) (hn2 : 4 * n < 2 ^ 12) :
    pcOf k + (sign_extend (evenB (BitVec.ofInt 13 (-4 * (n : Int)))) : BitVec 64) = pcOf (k - n) := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hj : (BitVec.ofInt 13 (-4 * (n : Int))).toInt = -4 * (n : Int) := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp <;> omega
  have he : (BitVec.ofInt 13 (-4 * (n : Int))).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofInt]; omega
  rw [evenB_self _ he, add_sext, pcOf_toNat (by omega), pcOf_eq_ofInt, hj]
  congr 1; push_cast; omega

theorem step_br_back {code : List Ins} {k : Nat} {A : AM} (hfit : Fits code) {op : BrOp}
    {r1 r2 n : Nat} {v w : BitVec 64}
    (hk : code[k]? = some (.br op r1 r2 (BitVec.ofInt 13 (-4 * (n : Int))))) (hA : A.pc = pcOf k)
    (h1 : Has A.regs r1 v) (h2 : Has A.regs r2 w) (hkk : PosOK k) (hn : n ≤ k) (hn2 : 4 * n < 2 ^ 12) :
    astep code A = some (.run ⟨if guardB op.bop v w then pcOf (k - n) else pcOf (k + 1),
      A.regs, A.mem, A.out⟩) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hb : codeBase = 0x80004800 := rfl
  rw [step_br hfit hk hA h1 h2 (by rw [pcOf_back k n hkk hn hn2, pcOf_toNat (by unfold PosOK at hkk; omega)]; omega),
    pcOf_back k n hkk hn hn2]

theorem sext_small (c : Int) (h1 : -2048 ≤ c) (h2 : c < 2048) :
    (sign_extend (BitVec.ofInt 12 c) : BitVec 64) = BitVec.ofInt 64 c := sext12_ofInt c h1 h2

def libRegs (L : GRegs) (r : BitVec 64) : GRegs :=
  (10, r) :: eraseAll clobbered (gset (gset L 12 0) 13 0)

theorem Has.gs_self (L : GRegs) (rd : Nat) (v : BitVec 64) (h : 1 ≤ rd ∧ rd ≤ 31) :
    Has (gset L rd v) rd v := Has.set_self L v h.1 h.2

theorem Has.gs {L : GRegs} {n rd : Nat} {v w : BitVec 64} (hne : n ≠ rd) (h : Has L n v) :
    Has (gset L rd w) n v := h.set_other hne

theorem Has.lib_self (L : GRegs) (r : BitVec 64) :
    Has ((10, r) :: eraseAll clobbered (gset (gset L 12 0) 13 0)) 10 r :=
  ⟨by decide, .inr ⟨by decide, by simp [libRegs, lookupG]⟩⟩

theorem Has.lib {L : GRegs} {n : Nat} {v r : BitVec 64}
    (hn : n ≠ 1 ∧ n ≠ 5 ∧ n ≠ 10 ∧ n ≠ 11 ∧ n ≠ 12 ∧ n ≠ 13) (h : Has L n v) :
    Has ((10, r) :: eraseAll clobbered (gset (gset L 12 0) 13 0)) n v := by
  obtain ⟨h31, (⟨rfl, rfl⟩ | ⟨hne, hl⟩)⟩ := h
  · exact Has.zero _
  · refine ⟨h31, .inr ⟨hne, ?_⟩⟩
    simp only [lookupG]
    rw [if_neg (by omega), lookupG_eraseAll, if_neg (by simp [clobbered]; omega),
      lookupG_set, if_neg (by omega), lookupG_set, if_neg (by omega), hl]

syntax "has_core" : tactic
syntax "has_tac" : tactic
macro_rules
  | `(tactic| has_tac) => `(tactic| ((try dsimp only [a0, a1, s2, s3, s4, s5, s6, s11, ra]); has_core))
macro_rules
  | `(tactic| has_core) => `(tactic| first
      | with_reducible exact Has.gs_self _ _ _ (by decide)
      | with_reducible exact Has.lib_self _ _
      | (with_reducible apply Has.gs (by decide)); has_core
      | (with_reducible apply Has.lib (by decide)); has_core
      | with_reducible exact Has.zero _
      | assumption)

theorem step_addi_eq {code : List Ins} {k : Nat} {A : AM} (hfit : Fits code) {rd rs : Nat}
    {imm : BitVec 12} {v w : BitVec 64}
    (hk : code[k]? = some (.addi rd rs imm)) (hA : A.pc = pcOf k)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hs : Has A.regs rs v) (hw : v + (sign_extend imm : BitVec 64) = w) :
    astep code A = some (.run ⟨pcOf (k + 1), gset A.regs rd w, A.mem, A.out⟩) := by
  rw [step_addi hfit hk hA hrd hs, hw]

theorem sext_zero : (sign_extend (0 : BitVec 12) : BitVec 64) = 0 := by decide

theorem add_sext_zero (x : BitVec 64) : x + (sign_extend (0 : BitVec 12) : BitVec 64) = x := by
  rw [sext_zero]; simp

theorem ofNat_add_sext (a c : Nat) (hc : c < 2048) (ha : a + c < 2 ^ 64) :
    BitVec.ofNat 64 a + (sign_extend (BitVec.ofNat 12 c) : BitVec 64) = BitVec.ofNat 64 (a + c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, sext12_small _ (by simp; omega)]
  simp; omega

theorem ofNat_sub_sext (a c : Nat) (hc : c ≤ 2048) (hca : c ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a + (sign_extend (BitVec.ofInt 12 (-(c : Int))) : BitVec 64)
      = BitVec.ofNat 64 (a - c) := by
  rw [sext12_ofInt _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code 14 printCode)
include hfit hseg

theorem print_posOK {k : Nat} (hk : k ≤ 100) : PosOK k := by
  have h : code[14 + 85]? = some (.jalr ra) := hseg.get (by rfl)
  have hl : 14 + 85 < code.length := by
    rcases Nat.lt_or_ge (14 + 85) code.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  unfold Fits at hfit; unfold PosOK; omega

omit hfit in
theorem pI {j k : Nat} {i : Ins} (hk : 14 + j = k) (h : printCode[j]? = some i) :
    code[k]? = some i := hk ▸ hseg.get h

omit hfit in
theorem pS {j k len : Nat} {s : List Ins} (hk : 14 + j = k) (h : (printCode.drop j).take len = s) :
    Seg code k s := hk ▸ h ▸ hseg.sub j len

end

theorem zopz_ge (v : BitVec 64) : guardB BrOp.ge.bop v 0 = decide (v.toInt ≥ 0) := by
  simp [guardB, BrOp.bop, zopz0zKzJ_s]

theorem guard_ne_zero (v : BitVec 64) : guardB BrOp.ne.bop v 0 = !(v == 0) := rfl

theorem abs_digit (t : Int) :
    (BitVec.ofInt 64 (t.tmod 10)).toInt = t.tmod 10 := by
  have h1 := Int.natAbs_tmod t 10
  have h2 : (t.tmod 10).natAbs < 10 := by rw [h1]; simp; omega
  rcases Int.natAbs_eq (t.tmod 10) with h | h <;> apply toInt_ofInt_small <;> omega

theorem libRes_mod (x : BitVec 64) :
    libRes modPC x 10 = some (BitVec.ofInt 64 (x.toInt.tmod 10)) := by
  simp [libRes, show modPC ≠ mulPC by decide, show modPC ≠ divPC by decide]

theorem libRes_div (x : BitVec 64) :
    libRes divPC x 10 = some (BitVec.ofInt 64 (x.toInt.tdiv 10)) := by
  simp [libRes, show divPC ≠ mulPC by decide]

theorem tdiv_word (x : BitVec 64) :
    (BitVec.ofInt 64 (x.toInt.tdiv 10)).toInt = x.toInt.tdiv 10 ∧
      (x.toInt.tdiv 10).natAbs = x.toInt.natAbs / 10 := by
  have h2 : (x.toInt.tdiv 10).natAbs = x.toInt.natAbs / 10 := by
    rw [Int.natAbs_tdiv]; rfl
  refine ⟨?_, h2⟩
  have hb1 := BitVec.le_toInt x
  have hb2 : x.toInt < 2 ^ (64 - 1) := BitVec.toInt_lt
  rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 by decide] at hb1 hb2
  rcases Int.natAbs_eq (x.toInt.tdiv 10) with h | h <;>
  rcases Int.natAbs_eq x.toInt with h' | h' <;> apply toInt_ofInt_small <;> omega

theorem tdiv_word_zero (x : BitVec 64) :
    BitVec.ofInt 64 (x.toInt.tdiv 10) = 0 ↔ x.toInt.natAbs < 10 := by
  obtain ⟨h1, h2⟩ := tdiv_word x
  constructor
  · intro h
    have : (BitVec.ofInt 64 (x.toInt.tdiv 10)).toInt = 0 := by rw [h]; rfl
    rw [h1] at this
    have : (x.toInt.tdiv 10).natAbs = 0 := by rw [this]; rfl
    omega
  · intro h
    apply BitVec.eq_of_toInt_eq
    rw [h1]
    have : (x.toInt.tdiv 10).natAbs = 0 := by omega
    rw [Int.natAbs_eq_zero.mp this]; rfl

theorem ofNat_sub_neg (a c : Nat) (hca : c ≤ a) (ha : a < 2 ^ 64) (hc : c < 2048) :
    BitVec.ofNat 64 a + BitVec.ofInt 64 (-(c : Int)) = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem take_succ_rev (ds : List Nat) (i : Nat) (h : i < ds.length) :
    ((ds.take (i + 1)).map Nat.digitChar).reverse
      = Nat.digitChar ds[i]! :: ((ds.take i).map Nat.digitChar).reverse := by
  have : ds.take (i + 1) = ds.take i ++ [ds[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  rw [this, List.map_append, List.reverse_append, getElem!_pos ds i h]
  rfl

theorem toString_eq_push (c : Char) : toString c = "".push c := rfl

section
variable {code : List Ins} (hfit : Fits code) (hseg : Seg code 14 printCode)
include hfit hseg

theorem run_abs {A : AM} {v : BitVec 64} (hA : A.pc = pcOf 57) (h10 : Has A.regs a0 v)
    (hv : -10 < v.toInt ∧ v.toInt < 10) :
    Reaches code A fun B => B.pc = pcOf 59 ∧ B.mem = A.mem ∧ B.out = A.out ∧
      Has B.regs a0 (BitVec.ofNat 64 v.toInt.natAbs) ∧
      ∀ n w, n ≠ a0 → Has A.regs n w → Has B.regs n w := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have e := step_br hfit (pI hseg (j := 43) (k := 57) rfl rfl) hA h10 (Has.zero _)
    (by rw [pcOf_skip _ _ (P _ (by decide)) (by decide), pcOf_toNat (by decide)]; decide)
  rw [pcOf_skip _ _ (P _ (by decide)) (by decide), zopz_ge] at e
  by_cases hs : v.toInt ≥ 0
  · rw [if_pos (by simpa using hs)] at e
    refine ⟨_, Star.single e, rfl, rfl, rfl, ?_, fun n w _ h => h⟩
    have : v = BitVec.ofNat 64 v.toInt.natAbs := by
      rw [← BitVec.ofInt_natCast, Int.natAbs_of_nonneg hs, BitVec.ofInt_toInt]
    rw [← this]; exact h10
  · rw [if_neg (by simpa using hs)] at e
    refine ex_step e ?_
    have e2 := step_sub hfit (pI hseg (j := 44) (k := 57 + 1) rfl rfl) rfl (A := ⟨_, A.regs, A.mem, A.out⟩)
      (by decide) (Has.zero _) h10
    refine ⟨_, Star.single e2, rfl, rfl, rfl, ?_, fun n w hn h => h.gs hn⟩
    have : 0 - v = BitVec.ofNat 64 v.toInt.natAbs := by
      rw [← BitVec.ofInt_natCast, Int.ofNat_natAbs_of_nonpos (by omega)]
      rw [BitVec.ofInt_neg, BitVec.ofInt_toInt]; simp
    rw [← this]; exact Has.gs_self _ _ _ (by decide)

theorem run_digit {A : AM} {x r : BitVec 64} {j : Nat}
    (hA : A.pc = pcOf 52) (h4 : Has A.regs s4 x) (h5 : Has A.regs s5 (BitVec.ofNat 64 j))
    (h6 : Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * j))) (h11 : Has A.regs s11 r)
    (hj : j < 20) :
    Reaches code A fun B => B.pc = (if BitVec.ofInt 64 (x.toInt.tdiv 10) = 0 then pcOf 70 else pcOf 52) ∧
      Has B.regs s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) ∧
      Has B.regs s5 (BitVec.ofNat 64 (j + 1)) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (j + 1))) ∧ Has B.regs s11 r ∧
      B.mem = applyW A.mem (bufBase + 8 * j, 8, BitVec.ofNat 64 (x.toInt.natAbs % 10 + 48)) ∧
      B.out = A.out := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  refine ex_step (step_addi_eq hfit (pI hseg (j := 38) (k := 52) rfl rfl) hA (by decide) h4
    (add_sext_zero x)) ?_
  refine ex_step (step_addi_eq hfit (pI hseg (j := 39) (k := 52 + 1) rfl rfl) rfl (by decide)
    (Has.zero _) (w := 10) (by decide)) ?_
  refine ex_trans (run_libc hfit (pS hseg (j := 40) (len := 3) (k := 52 + 1 + 1) rfl rfl) rfl
    (P _ (by decide)) (.inr (.inr rfl)) (by has_tac) (by has_tac) (libRes_mod x)) ?_
  obtain ⟨B1, s1, hpc1, hm1, ho1, h10', hpres⟩ := run_abs hfit hseg
    (A := ⟨pcOf (52 + 1 + 1 + 3), _, _, _⟩) rfl (Has.lib_self _ _)
    (by rw [abs_digit x.toInt]; have := Int.natAbs_tmod x.toInt 10
        have h2 : (x.toInt.tmod 10).natAbs < 10 := by rw [this]; simp; omega
        rcases Int.natAbs_eq (x.toInt.tmod 10) with h | h <;> omega)
  refine ex_trans s1 ?_
  simp only at hm1 ho1
  have hd : (BitVec.ofInt 64 (x.toInt.tmod 10)).toInt.natAbs = x.toInt.natAbs % 10 := by
    rw [abs_digit x.toInt, Int.natAbs_tmod]; rfl
  rw [hd] at h10'
  have g4 := hpres s4 x (by decide) (by has_tac)
  have g5 := hpres s5 _ (by decide) (by has_tac)
  have g6 := hpres s6 _ (by decide) (by has_tac)
  have g11 := hpres s11 r (by decide) (by has_tac)
  have hdl : x.toInt.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)

  refine ex_step (step_addi_eq hfit (pI hseg (j := 45) (k := 59) rfl rfl) hpc1 (by decide) h10'
    (ofNat_add_sext _ 48 (by decide) (by omega))) ?_

  refine ex_step (step_sd hfit (pI hseg (j := 46) (k := 59 + 1) rfl rfl) rfl
    (a := BitVec.ofNat 64 (bufBase + 8 * j)) (by has_tac) (by has_tac)
    (by rw [BitVec.toNat_ofNat]; unfold StOK; omega)) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 47) (k := 59 + 1 + 1) rfl rfl) rfl (by decide)
    (by has_tac) (ofNat_add_sext _ 8 (by decide) (by omega))) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 48) (k := 59 + 1 + 1 + 1) rfl rfl) rfl (by decide)
    (by has_tac) (ofNat_add_sext _ 1 (by decide) (by omega))) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 49) (k := 59 + 1 + 1 + 1 + 1) rfl rfl) rfl
    (by decide) (by has_tac) (add_sext_zero x)) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 50) (k := 59 + 1 + 1 + 1 + 1 + 1) rfl rfl) rfl
    (by decide) (Has.zero _) (w := 10) (by decide)) ?_

  refine ex_trans (run_libc hfit (pS hseg (j := 51) (len := 3) (k := 59 + 1 + 1 + 1 + 1 + 1 + 1)
    rfl rfl) rfl (P _ (by decide)) (.inr (.inl rfl)) (by has_tac) (by has_tac) (libRes_div x)) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 54) (k := 59 + 1 + 1 + 1 + 1 + 1 + 1 + 3) rfl rfl)
    rfl (by decide) (Has.lib_self _ _) (add_sext_zero _)) ?_

  refine ex_step (step_br_back hfit (pI hseg (j := 55) (k := 69)
    (i := .br .ne s4 0 (BitVec.ofInt 13 (-4 * ((17 : Nat) : Int)))) rfl rfl) rfl
    (Has.gs_self _ s4 (BitVec.ofInt 64 (x.toInt.tdiv 10)) (by decide)) (Has.zero _)
    (P _ (by decide)) (by decide) (by decide)) ?_
  rw [guard_ne_zero]
  refine ⟨_, Star.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h0 : BitVec.ofInt 64 (x.toInt.tdiv 10) = 0
    · simp [h0]
    · simp [h0]
  · has_tac
  · has_tac
  · rw [show bufBase + 8 * (j + 1) = bufBase + 8 * j + 8 by omega]; has_tac
  · has_tac
  · simp only [hm1, BitVec.toNat_ofNat]
    congr 2
    omega
  · simp only [ho1]

theorem run_digits : ∀ (N : Nat) (x : BitVec 64) (j : Nat) (ds : List Nat) (A : AM) (r : BitVec 64),
    x.toInt.natAbs = N →
    A.pc = pcOf 52 → Has A.regs s4 x → Has A.regs s5 (BitVec.ofNat 64 j) →
    Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * j)) → Has A.regs s11 r →
    ds.length = j → (ds ++ digitsLE N).length ≤ 19 →
    Reaches code A fun B => B.pc = pcOf 70 ∧
      Has B.regs s5 (BitVec.ofNat 64 (ds ++ digitsLE N).length) ∧
      Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (ds ++ digitsLE N).length)) ∧
      Has B.regs s11 r ∧ B.out = A.out ∧
      (∀ q, j ≤ q → q < (ds ++ digitsLE N).length →
        rdW B.mem (bufBase + 8 * q) = BitVec.ofNat 64 ((ds ++ digitsLE N)[q]! + 48)) ∧
      (∀ a, (a + 8 ≤ bufBase + 8 * j ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro x j ds A r hN hA h4 h5 h6 h11 hj hlen
  have hb : bufBase = 0x80080000 := rfl
  have hjl : j + (digitsLE N).length ≤ 19 := by simpa [hj] using hlen
  have hpos : 1 ≤ (digitsLE N).length := by
    unfold digitsLE; split <;> simp
  obtain ⟨B1, s1, hpc1, h4', h5', h6', h11', hm1, ho1⟩ :=
    run_digit hfit hseg hA h4 h5 h6 h11 (by omega)
  have hw := rdW_write A.mem (bufBase + 8 * j) (BitVec.ofNat 64 (N % 10 + 48))
  by_cases hsmall : N < 10
  · rw [if_pos ((tdiv_word_zero x).mpr (by omega))] at hpc1
    have hdl : digitsLE N = [N] := digitsLE_small hsmall
    rw [hdl] at hlen ⊢
    refine ⟨B1, s1, hpc1, ?_, ?_, h11', ho1, ?_, ?_⟩
    · simpa [hj] using h5'
    · simpa [hj] using h6'
    · intro q hq1 hq2
      simp [hj] at hq2
      have : q = j := by omega
      subst this
      rw [hm1, hN]
      simp [hj, Nat.mod_eq_of_lt hsmall] at hw ⊢
      rw [hw]
    · intro a ha
      rw [hm1]
      exact rdW_write_other _ _ _ _ (by omega)
  · rw [if_neg (fun h => hsmall (hN ▸ (tdiv_word_zero x).mp h))] at hpc1
    have hdl : digitsLE N = N % 10 :: digitsLE (N / 10) := digitsLE_big hsmall
    obtain ⟨hx1, hx'⟩ := tdiv_word x
    have := ih (N / 10) (by omega) _ (j + 1) (ds ++ [N % 10]) B1 r (by rw [hx1, hx', hN]) hpc1 h4' h5' h6'
      h11' (by simp [hj]) (by rw [hdl] at hlen; simpa using hlen)
    obtain ⟨B, s2, hpc, h5f, h6f, h11f, hof, hcells, hframe⟩ := this
    have heq : ds ++ [N % 10] ++ digitsLE (N / 10) = ds ++ digitsLE N := by rw [hdl]; simp
    rw [heq] at h5f h6f hcells
    refine ⟨B, s1.trans s2, hpc, h5f, h6f, h11f, hof.trans ho1, ?_, ?_⟩
    · intro q hq1 hq2
      by_cases hqj : q = j
      · subst hqj
        rw [hframe _ (by omega), hm1, hN, hw]
        congr 2
        rw [hdl]; simp [hj]
      · exact hcells q (by omega) hq2
    · intro a ha
      rw [hframe a (by omega), hm1]
      exact rdW_write_other _ _ _ _ (by omega)

theorem run_out1 {A : AM} {i d : Nat} {r : BitVec 64}
    (hA : A.pc = pcOf 70) (h5 : Has A.regs s5 (BitVec.ofNat 64 (i + 1)))
    (h6 : Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (i + 1)))) (h11 : Has A.regs s11 r)
    (hi : i < 20) (hd : d < 10) (hcell : rdW A.mem (bufBase + 8 * i) = BitVec.ofNat 64 (d + 48)) :
    Reaches code A fun B => B.pc = (if i = 0 then pcOf 98 else pcOf 70) ∧
      Has B.regs s5 (BitVec.ofNat 64 i) ∧ Has B.regs s6 (BitVec.ofNat 64 (bufBase + 8 * i)) ∧
      Has B.regs s11 r ∧ B.mem = A.mem ∧ outStr B = outStr A ++ toString (Nat.digitChar d) := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hb : bufBase = 0x80080000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl

  refine ex_step (step_addi_eq hfit (pI hseg (j := 56) (k := 70) rfl rfl) hA (by decide) h6
    (w := BitVec.ofNat 64 (bufBase + 8 * i))
    (by rw [show (sign_extend (-8 : BitVec 12) : BitVec 64) = BitVec.ofInt 64 (-((8 : Nat) : Int))
          by decide, ofNat_sub_neg _ 8 (by omega) (by omega) (by decide),
          show bufBase + 8 * (i + 1) - 8 = bufBase + 8 * i by omega])) ?_

  refine ex_step (step_ld hfit (pI hseg (j := 57) (k := 70 + 1) rfl rfl) rfl (by decide)
    (by has_tac) (by rw [BitVec.toNat_ofNat]; unfold LdOK; omega)) ?_

  refine ex_trans (run_li hfit (pS hseg (j := 58) (len := 11) (k := 70 + 1 + 1) (s := li s3 (putcWord 0)) rfl rfl) rfl
    (by decide)) ?_
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bufBase + 8 * i < 2 ^ 64 by omega), hcell]

  refine ex_step (step_add hfit (pI hseg (j := 69) (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length)
    rfl rfl) rfl (by decide) (by has_tac) (by has_tac)) ?_
  rw [putcWord_add _ (by omega)]

  refine ex_trans (run_li hfit (pS hseg (j := 70) (len := 11)
    (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length + 1) (s := li s2 tohostW) rfl rfl) rfl (by decide)) ?_

  refine ex_step ((step_htif hfit (pI hseg (j := 81) (k := 70 + 1 + 1 + (li s3 (putcWord 0)).length + 1
    + (li s2 tohostW).length) rfl rfl) rfl (by has_tac) (by has_tac) tohostW_toNat).trans
    (htifOut_putc _ _)) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 82) (k := 96) rfl rfl) (pcOf_succ _) (by decide)
    (by has_tac) (w := BitVec.ofNat 64 i)
    (by rw [show (sign_extend (-1 : BitVec 12) : BitVec 64) = BitVec.ofInt 64 (-((1 : Nat) : Int))
          by decide, ofNat_sub_neg _ 1 (by omega) (by omega) (by decide)]; rfl)) ?_

  refine ex_step (step_br_back hfit (pI hseg (j := 83) (k := 97)
    (i := .br .ne s5 0 (BitVec.ofInt 13 (-4 * ((27 : Nat) : Int)))) rfl rfl) rfl
    (Has.gs_self _ s5 (BitVec.ofNat 64 i) (by decide)) (Has.zero _)
    (P _ (by decide)) (by decide) (by decide)) ?_
  rw [guard_ne_zero]
  refine ⟨_, Star.refl _ _, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · by_cases h0 : i = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 i ≠ 0 := by
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp at this; omega
      simp [h0]
      intro h; exact absurd h this
  · has_tac
  · has_tac
  · has_tac
  · simp only [outStr_push]
    congr 2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.add_comm, char_digit d hd]

theorem run_outs : ∀ (i : Nat) (A : AM) (ds : List Nat) (r : BitVec 64),
    A.pc = pcOf 70 → Has A.regs s5 (BitVec.ofNat 64 (i + 1)) →
    Has A.regs s6 (BitVec.ofNat 64 (bufBase + 8 * (i + 1))) → Has A.regs s11 r →
    i < 20 → i < ds.length →
    (∀ q, q ≤ i → ds[q]! < 10 ∧ rdW A.mem (bufBase + 8 * q) = BitVec.ofNat 64 (ds[q]! + 48)) →
    Reaches code A fun B => B.pc = pcOf 98 ∧ Has B.regs s11 r ∧ B.mem = A.mem ∧
      outStr B = outStr A ++ ((ds.take (i + 1)).map Nat.digitChar).reverse.foldl String.push "" := by
  intro i
  induction i with
  | zero =>
    intro A ds r hA h5 h6 h11 _ hl hc
    obtain ⟨hd, hcell⟩ := hc 0 (by omega)
    obtain ⟨B, s, hpc, _, _, h11', hm, ho⟩ := run_out1 hfit hseg hA h5 h6 h11 (by omega) hd hcell
    refine ⟨B, s, by simpa using hpc, h11', hm, ?_⟩
    rw [ho, take_succ_rev ds 0 hl]
    simp only [List.take_zero, List.map_nil, List.reverse_nil, List.foldl_cons, List.foldl_nil]
    rw [toString_eq_push]
  | succ i ih =>
    intro A ds r hA h5 h6 h11 hi hl hc
    obtain ⟨hd, hcell⟩ := hc (i + 1) (by omega)
    obtain ⟨B1, s1, hpc, h5', h6', h11', hm, ho⟩ :=
      run_out1 hfit hseg hA h5 h6 h11 (by omega) hd hcell
    rw [if_neg (by omega)] at hpc
    obtain ⟨B, s2, hpc2, h11f, hm2, ho2⟩ := ih B1 ds r hpc h5' h6' h11' (by omega) (by omega)
      (fun q hq => by rw [hm]; exact hc q (by omega))
    refine ⟨B, s1.trans s2, hpc2, h11f, hm2.trans hm, ?_⟩
    rw [ho2, ho, take_succ_rev ds (i + 1) hl, List.foldl_cons, foldl_push _ ("".push _),
      String.append_assoc, toString_eq_push]

theorem run_prologue {A : AM} {n r : BitVec 64} (hA : A.pc = pcOf 14)
    (ha0 : Has A.regs a0 n) (hra : Has A.regs ra r) :
    Reaches code A fun B => B.pc = pcOf 40 ∧ Has B.regs s4 n ∧ Has B.regs s11 r ∧ B.mem = A.mem ∧
      outStr B = outStr A ++ (if n.toInt < 0 then "-" else "") := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  refine ex_step (step_addi_eq hfit (pI hseg (j := 0) (k := 14) rfl rfl) hA (by decide) hra
    (add_sext_zero r)) ?_
  refine ex_step (step_addi_eq hfit (pI hseg (j := 1) (k := 14 + 1) rfl rfl) rfl (by decide)
    (by has_tac) (add_sext_zero n)) ?_
  have e := step_br hfit (pI hseg (j := 2) (k := 16) (i := .br .ge s4 0 (bSkip 23)) rfl rfl)
    (A := ⟨pcOf (14 + 1 + 1), gset (gset A.regs s11 r) s4 n, A.mem, A.out⟩) rfl
    (Has.gs_self _ s4 n (by decide)) (Has.zero _)
    (by rw [pcOf_skip _ _ (P _ (by decide)) (by decide), pcOf_toNat (by decide)]; decide)
  rw [pcOf_skip _ _ (P _ (by decide)) (by decide), zopz_ge] at e
  by_cases hs : n.toInt ≥ 0
  · rw [if_pos (by simpa using hs)] at e
    refine ⟨_, Star.single e, rfl, by has_tac, by has_tac, rfl, ?_⟩
    rw [if_neg (by omega)]; simp [outStr]
  · rw [if_neg (by simpa using hs)] at e
    have r1 := run_putcW hfit (c := BitVec.ofNat 8 45)
      (pS hseg (j := 3) (len := 23) (k := 16 + 1)
        (s := li s3 (putcWord (BitVec.ofNat 8 45)) ++ li s2 tohostW ++ [.sd s3 s2]) rfl rfl)
      (A := ⟨pcOf (16 + 1), gset (gset A.regs s11 r) s4 n, A.mem, A.out⟩) rfl
    refine ⟨_, Star.step e r1, rfl, by has_tac, by has_tac, rfl, ?_⟩
    rw [if_pos (by omega), outStr_push]
    rfl

theorem run_print' {A : AM} {n r : BitVec 64} {k : Nat} (hA : A.pc = pcOf 14)
    (ha0 : Has A.regs a0 n) (hra : Has A.regs ra r) (hr : r = pcOf k) (hk : PosOK k) :
    Reaches code A fun B => B.pc = r ∧ outStr B = outStr A ++ intToString n.toInt ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a := by
  have P := fun k (hk : k ≤ 100) => print_posOK hfit hseg hk
  have hb : bufBase = 0x80080000 := rfl
  obtain ⟨B1, s1, hpc1, h4, h11, hm1, ho1⟩ := run_prologue hfit hseg hA ha0 hra
  refine ex_trans s1 ?_

  refine ex_trans (run_li hfit (pS hseg (j := 26) (len := 11) (k := 40)
    (s := li s6 (BitVec.ofNat 64 bufBase)) rfl rfl) hpc1 (by decide)) ?_

  refine ex_step (step_addi_eq hfit (pI hseg (j := 37) (k := 40 + (li s6 (BitVec.ofNat 64 bufBase)).length)
    rfl rfl) rfl (by decide) (Has.zero _) (w := BitVec.ofNat 64 0) (by decide)) ?_

  have hN : n.toInt.natAbs ≤ 2 ^ 63 := by
    have hb1 := BitVec.le_toInt n
    have hb2 : n.toInt < 2 ^ (64 - 1) := BitVec.toInt_lt
    rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 by decide] at hb1 hb2
    omega
  have hlen : (digitsLE n.toInt.natAbs).length ≤ 19 :=
    digitsLE_length_le 18 _ (by omega)
  refine ex_bind (run_digits hfit hseg n.toInt.natAbs n 0 [] _ r rfl rfl (by has_tac) (by has_tac)
      (by simp only [Nat.mul_zero, Nat.add_zero]; has_tac) (by has_tac) rfl (by simpa using hlen)) ?_
  rintro B2 ⟨hpc2, h5, h6, h11', ho2, hcells, hframe⟩
  simp only [List.nil_append] at h5 h6 hcells
  have hpos : 1 ≤ (digitsLE n.toInt.natAbs).length := by
    unfold digitsLE; split <;> simp
  obtain ⟨J, hJ⟩ : ∃ J, (digitsLE n.toInt.natAbs).length = J + 1 := ⟨_, (Nat.sub_add_cancel hpos).symm⟩
  rw [hJ] at h5 h6 hcells
  refine ex_bind (run_outs hfit hseg J B2 (digitsLE n.toInt.natAbs) r hpc2 h5 h6 h11' (by omega)
      (by omega) (fun q hq => ⟨digitsLE_lt _ _ (by
          rw [getElem!_pos _ q (by omega)]; exact List.getElem_mem (by omega)),
        hcells q (by omega) (by omega)⟩)) ?_
  rintro B3 ⟨hpc3, h11'', hm3, ho3⟩

  refine ex_step (step_addi_eq hfit (pI hseg (j := 84) (k := 98) rfl rfl) hpc3 (by decide) h11''
    (add_sext_zero r)) ?_

  have hb' : codeBase = 0x80004800 := rfl
  have ht' : tohostAddr = 0x8001ad00 := rfl
  refine ex_step (step_jalr hfit (pI hseg (j := 85) (k := 98 + 1) rfl rfl) rfl
    (Has.gs_self _ ra r (by decide)) (by rw [hr, pcOf_toNat (by unfold PosOK at hk; omega)]; omega)) ?_
  refine ⟨_, Star.refl _ _, rfl, ?_, ?_⟩
  · show outStr B3 = _
    rw [ho3]
    have hB2 : outStr B2 = outStr B1 := by simp [outStr, ho2]
    rw [hB2, ho1, intToString_eq, natToString_eq, String.append_assoc, ← hJ, List.take_length]
  · intro a ha
    show rdW B3.mem a = rdW A.mem a
    rw [hm3, hframe a (by omega), ← hm1]

end

theorem run_print {code : List Ins} {k : Nat} (hfit : Fits code) (hseg : Seg code printPos printCode)
    {A : AM} {n r : BitVec 64} (hA : A.pc = pcOf printPos)
    (ha0 : Has A.regs a0 n) (hra : Has A.regs ra r) (hr : r = pcOf k) (hk : PosOK k) :
    Reaches code A fun B => B.pc = r ∧ outStr B = outStr A ++ intToString n.toInt ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a :=
  run_print' hfit hseg hA ha0 hra hr hk

#print axioms run_print

end Vsa.Compiler
