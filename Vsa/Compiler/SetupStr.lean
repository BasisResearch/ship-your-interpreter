import Vsa.Compiler.StuckAll

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem strOff_succ : ∀ (T : List String) (i : Nat), i < T.length →
    strOff T (i + 1) = strOff T i + strSize (T.getD i "")
  | [], _, h => absurd h (by simp)
  | s :: ss, 0, _ => by simp only [Nat.zero_add, strOff]; cases ss <;> simp [strOff]
  | s :: ss, i + 1, h => by
    simp only [strOff, List.getD_cons_succ]
    rw [strOff_succ ss i (by simpa using h)]
    omega

theorem strOff_mono (T : List String) : ∀ {i j : Nat}, i ≤ j → strOff T i ≤ strOff T j := by
  induction T with
  | nil => intro i j _; simp [strOff]
  | cons s ss ih =>
    intro i j hij
    cases i with
    | zero => simp [strOff]
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simp only [strOff]; have := ih (i := i) (j := j) (by omega); omega

theorem strOff_al : ∀ (T : List String) (i : Nat), strOff T i % 8 = 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | s :: ss, i + 1 => by simp only [strOff, strSize]; have := strOff_al ss i; omega

theorem strOff_len : ∀ (T : List String) (i : Nat), T.length ≤ i → strOff T i = strOff T T.length
  | [], _, _ => by simp [strOff]
  | s :: ss, 0, h => absurd h (by simp)
  | s :: ss, i + 1, h => by
    simp only [strOff, List.length_cons]
    rw [strOff_len ss i (by simpa using h)]

section
variable {code : List Ins} (hfit : Fits code)
include hfit

theorem run_chars {a : Nat} (ha : a % 8 = 0) (hlo : tohostAddr + 16 ≤ a) :
    ∀ (cs : List Char) (j q : Nat) (L : GRegs) (m : Mem) (o : Array String),
    (∀ c ∈ cs, c.toNat < 256) → a + 8 * (j + 1 + cs.length) ≤ 2 ^ 32 →
    Seg code q (cs.flatMap fun c => [addi t0 t0 8, mvi t1 c.toNat, .sd t1 t0]) →
    PosOK (q + 3 * cs.length) → Has L t0 (BitVec.ofNat 64 (a + 8 * j)) →
    Reaches code ⟨pcOf q, L, m, o⟩ (fun B => B.pc = pcOf (q + 3 * cs.length) ∧ B.out = o ∧
      Keep [t0, t1] L B.regs ∧
      (∀ i (h : i < cs.length), rdW B.mem (a + 8 * (j + 1 + i)) = BitVec.ofNat 64 cs[i].toNat) ∧
      (∀ b, b % 8 = 0 → b + 8 ≤ a + 8 * (j + 1) ∨ a + 8 * (j + 1 + cs.length) ≤ b → rdW B.mem b = rdW m b))
  | [], j, q, L, m, o, _, _, _, _, _ =>
    reach_here ⟨by simp, rfl, Keep.refl _ _, fun i h => absurd h (by simp), fun _ _ _ => rfl⟩
  | c :: cs, j, q, L, m, o, hs, hb, hseg, hP, h8 => by
    have hc : c.toNat < 256 := hs c (by simp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    simp only [List.flatMap_cons] at hseg
    obtain ⟨s1, s2⟩ := hseg.append
    simp only [List.length_cons, List.length_nil] at s2 hb hP
    have k8 := has_mem h8 (by decide); have e8 := srcVal_of_has h8
    simp only [t0] at k8 e8
    have n1 : (BitVec.ofNat 64 (a + 8 * j) + BitVec.signExtend 64 (BitVec.ofInt 12 8)) =
        BitVec.ofNat 64 (a + 8 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (BitVec.signExtend 64 (BitVec.ofInt 12 8)).toNat = 8 := by decide
      rw [this]; omega
    have n2 : (BitVec.ofNat 64 (a + 8 * j + 8)).toNat = a + 8 * j + 8 := toNat_ofNat_lt (by omega)
    have o2 : StOK (a + 8 * j + 8) := by unfold StOK; omega
    have t2 : a + 8 * j + 8 ≠ tohostAddr := by omega
    have hq : PosOK (q + 3) := posOK_le hP (by omega)
    apply run_whole hfit s1
    wp_simp [k8, e8, n1, n2, o2, t2, BitVec.ofInt_natCast]
    refine reaches_mono (run_chars ha hlo cs (j + 1) (q + 3) _ _ o (fun c' h => hs c' (by simp [h]))
      (by omega) s2 (by rw [show q + (0 + 1 + 1 + 1) + 3 * cs.length = q + 3 * (cs.length + 1) by omega]; exact hP)
      ?_) ?_
    · rw [show a + 8 * (j + 1) = a + 8 * j + 8 by omega]; reg_simp []
    rintro B ⟨hpc, ho, hk, hch, hfr⟩
    refine ⟨by rw [hpc]; congr 1; omega, ho, ?_, ?_, ?_⟩
    · exact (Keep.gset (Keep.gset (Keep.refl _ L) (by decide)) (by decide)).trans hk
    · intro i hi
      cases i with
      | zero =>
        rw [hfr _ (by omega) (.inl (by omega)), rdW_upd (by omega) (by omega), if_pos (by omega)]
        simp
      | succ i =>
        have := hch i (by simpa using hi)
        rw [show a + 8 * (j + 1 + (i + 1)) = a + 8 * (j + 1 + 1 + i) by omega, this]
        simp
    · intro b hb8 hbr
      rw [hfr b hb8 (by omega), rdW_upd (by omega) hb8, if_neg (by omega)]

theorem run_strObj {s : String} {a q : Nat} (ha : a % 8 = 0) (hlo : tohostAddr + 16 ≤ a)
    (hhi : a + 8 + 8 * s.length ≤ 2 ^ 32) (hs : Latin1 s) (hseg : Seg code q (strObjCode s a))
    (hP : PosOK (q + (strObjCode s a).length)) {L : GRegs} {m : Mem} {o : Array String} :
    Reaches code ⟨pcOf q, L, m, o⟩ (fun B => B.pc = pcOf (q + (strObjCode s a).length) ∧ B.out = o ∧
      Keep [t0, t1] L B.regs ∧ StrW B.mem a s.toList ∧
      ∀ b, b % 8 = 0 → b + 8 ≤ a ∨ a + 8 + 8 * s.length ≤ b → rdW B.mem b = rdW m b) := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hlen : (s.toList.flatMap fun c => [addi t0 t0 8, mvi t1 c.toNat, .sd t1 t0]).length = 3 * s.length := by
    rw [← String.length_toList]
    induction s.toList with
    | nil => rfl
    | cons c cs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega
  unfold strObjCode at hseg hP ⊢
  obtain ⟨s12, s3⟩ := hseg.append
  simp only [List.length_append, hlen] at hP s3 ⊢
  have n0 : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have o0 : StOK a := by unfold StOK; omega
  have t0' : a ≠ tohostAddr := by omega
  have e1 : (liN t0 a).length = (li 5 (BitVec.ofNat 64 a)).length := rfl
  have e2 : (liN t1 s.length).length = (li 6 (BitVec.ofNat 64 s.length)).length := rfl
  simp only [List.length_singleton] at s3 hP ⊢
  have s3' := s3.cast (pos' := q + ((li 5 (BitVec.ofNat 64 a)).length + ((li 6 (BitVec.ofNat 64 s.length)).length
    + 1))) (by omega)
  apply run_whole hfit s12
  wp_simp [liN, n0, o0, t0']
  refine reaches_mono (run_chars hfit ha hlo s.toList 0 _ _ _ o hs (by simp only [String.length_toList]; omega)
    s3' (by rw [String.length_toList]; exact posOK_le hP (by omega)) ?_) ?_
  · rw [show a + 8 * 0 = a by omega]; reg_simp []
  rintro B ⟨hpc, ho, hk, hch, hfr⟩
  refine ⟨by rw [hpc, String.length_toList]; congr 1; omega, ho, ?_, ?_, ?_⟩
  · exact (Keep.gset (Keep.gset (Keep.refl _ L) (by decide)) (by decide)).trans hk
  · refine ⟨hlo, by rw [String.length_toList]; omega, ha, ?_, fun i hi => ?_, hs⟩
    · rw [hfr _ ha (.inl (by omega)), rdW_upd ha ha, if_pos rfl, String.length_toList]
    · rw [show a + 8 + 8 * i = a + 8 * (0 + 1 + i) by omega]; exact hch i hi
  · intro b hb8 hbr
    rw [hfr b hb8 (by rw [String.length_toList]; omega), rdW_upd ha hb8, if_neg (by omega)]

theorem run_strTab (T : List String) (hL : ∀ s ∈ T, Latin1 s) (hT : objBase + strOff T T.length ≤ objEnd) :
    ∀ n, n ≤ T.length → ∀ (q : Nat) (L : GRegs) (m : Mem) (o : Array String),
      Seg code q ((List.range n).flatMap fun i => strObjCode (T.getD i "") (objBase + strOff T i)) →
      PosOK (q + ((List.range n).flatMap fun i => strObjCode (T.getD i "") (objBase + strOff T i)).length) →
      Reaches code ⟨pcOf q, L, m, o⟩ (fun B =>
        B.pc = pcOf (q + ((List.range n).flatMap fun i => strObjCode (T.getD i "") (objBase + strOff T i)).length) ∧
        B.out = o ∧ Keep [t0, t1] L B.regs ∧
        (∀ i < n, StrW B.mem (objBase + strOff T i) (T.getD i "").toList) ∧
        ∀ b, b % 8 = 0 → b + 8 ≤ objBase ∨ objBase + strOff T n ≤ b → rdW B.mem b = rdW m b) := by
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  intro n
  induction n with
  | zero =>
    intro _ q L m o _ _
    exact reach_here ⟨by simp, rfl, Keep.refl _ _, fun i hi => absurd hi (by omega),
      fun _ _ _ => rfl⟩
  | succ n ih =>
    intro hn q L m o hseg hP
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      at hseg hP ⊢
    obtain ⟨s1, s2⟩ := hseg.append
    simp only [List.length_append] at hP s2 ⊢
    have hsn := strOff_succ T n (by omega)
    have hle := strOff_mono T (show n + 1 ≤ T.length by omega)
    have hal := strOff_al T n
    have hmem : T.getD n "" ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    refine ex_bind (ih (by omega) q L m o s1 (posOK_le hP (by omega))) ?_
    rintro ⟨pc1, L1, m1, o1⟩ ⟨hpc1, ho1, hk1, hstr1, hfr1⟩
    simp only at hpc1 ho1 hk1 hstr1 hfr1; subst hpc1 ho1
    refine reaches_mono (run_strObj hfit (by omega) (by omega) (by unfold strSize at hsn; omega) (hL _ hmem) s2
      (by rw [Nat.add_assoc]; exact hP)) ?_
    rintro B ⟨hpc, ho, hk, hstr, hfr⟩
    refine ⟨by rw [hpc, Nat.add_assoc], ho, hk1.trans (hk.mono (fun _ h => h)), fun i hi => ?_, fun b hb8 hbr => ?_⟩
    · by_cases hin : i = n
      · subst hin; exact hstr
      · have hi' : i < n := by omega
        have hsi := strOff_succ T i (by omega)
        have hmi := strOff_mono T (show i + 1 ≤ n by omega)
        refine (hstr1 i hi').transport fun b hb1 hb2 hb3 => ?_
        rw [hfr b hb3 (.inl (by unfold strSize at hsi; rw [String.length_toList] at hb2; omega))]
    · rw [hfr b hb8 (by unfold strSize at hsn; omega), hfr1 b hb8 (by omega)]

end

end Vsa.Compiler
