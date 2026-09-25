import VsaIris.Vsa.Fprintf.Digits

/-!
# `%lld` in `_vfprintf_r` (lane N5)

From the `%` of `"%lld"` (`0x800192c0`): the conversion parse reads `l`, `l`
(the quad flag), `d` through the jump table at `0x8001a288`, loads the
`long long` argument from `ap` (advancing it by 8), stores the sign byte
(`'-'` or 0) at `sp + 167` and leaves the magnitude (the argument or its
negation, read unsigned) in `s10` at `0x8000b414` (`lld_head`, post
`LldHead`). `SnprintfSpec.intToString_of_bv` is the same sign split.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio Vsa.While
open scoped VsaIris.Sym.Stdout

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The sign of a `long long` argument (top bit set). -/
abbrev isNeg (v : BitVec 64) : Prop := 2 ^ 63 ≤ v.toNat

/-- The magnitude `_vfprintf_r` formats: the argument, or its negation. -/
def lldMag (v : BitVec 64) : BitVec 64 := if isNeg v then 0#64 - v else v

/-- The sign byte at `sp + 167`. -/
def lldSign (v : BitVec 64) : BitVec 8 := if isNeg v then 45#8 else 0#8

/-- The memory after `lld_head`: the sign byte cleared, `ap` advanced, then
`'-'` for a negative argument. -/
def lldMt (Mt : Mem) (sp ap v : BitVec 64) : Mem :=
  if isNeg v then writeLog (writeLog (writeLog Mt [((sp + 167#64).toNat, 1, 0#64)])
    [((sp + 24#64).toNat, 8, ap + 8#64)]) [((sp + 167#64).toNat, 1, 45#64)]
  else writeLog (writeLog Mt [((sp + 167#64).toNat, 1, 0#64)]) [((sp + 24#64).toNat, 8, ap + 8#64)]

/-- The format bytes and jump-table words `%lld` reads (data view). -/
structure LldFmt (Dt : Mem) (DA : List Nat) : Prop where
  fmtDA : Cover (· ∈ DA) 0x800192c1 0x800192c4
  tabDA : Cover (· ∈ DA) 0x8001a288 0x8001a3f4
  l1 : ldv .lbu Dt 0x800192c1 = 0x6c#64
  l2 : ldv .lbu Dt 0x800192c2 = 0x6c#64
  d : ldv .lbu Dt 0x800192c3 = 0x64#64
  tabL : ldv .lw Dt 0x8001a3b8 = 18446744073709491228#64
  tabD : ldv .lw Dt 0x8001a398 = 18446744073709489368#64

/-- The registers `lld_head` keeps. -/
abbrev lldKeep : List Nat := [1, 2, 5, 6, 7, 9, 10, 11, 12, 16, 18, 19, 21, 23, 27, 30, 31]

/-- The state at `0x8000b414`: magnitude in `s10`, precision `-1`, flags
`0x20`, format pointer past the `d`, sign byte and advanced `ap` stored. -/
structure LldHead (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp ap v : BitVec 64) : Prop where
  mag : R' 26 = lldMag v
  prec : R' 22 = 18446744073709551615#64
  fmt : R' 24 = 0x800192c4#64
  s0 : R' 8 = 0#64
  s4 : R' 20 = 32#64
  t3 : R' 28 = 32#64
  t4 : R' 29 = 0#64
  keep : ∀ x ∈ lldKeep, R' x = R x
  mem : Mt' = lldMt Mt sp ap v

set_option hygiene false in
/-- `LldHead` from the flat register facts of a finished run. -/
macro "lld_close " hk:term " : " sg:term : tactic => `(tactic| (
  refine $hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f26]; unfold lldMag; simp [$sg:term]
  · exact f22
  · exact f24
  · exact f8
  · exact f20
  · exact f28
  · exact f29
  · intro x hx
    simp only [lldKeep, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> assumption
  · unfold lldMt; simp [$sg:term]))

theorem zero_le_toInt_iff (v : BitVec 64) : ((0#64).toInt ≤ v.toInt) = ¬ isNeg v := by
  apply propext
  rw [BitVec.toInt_zero, BitVec.toInt_eq_toNat_cond v]
  unfold isNeg
  simp only [Nat.reducePow]
  split <;> omega

#ix_piece lldHead_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp ap v : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (h2 : R 2 = sp) (h25 : R 25 = 0x800192c0#64) (hF : LldFmt Dt DA)
    (hap : ldv .ld Mt (sp + 24#64).toNat = ap) (hv : ldv .ld Mt ap.toNat = v)
    (hk : ∀ R' Mt', LldHead R R' Mt Mt' sp ap v →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b414#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9fc#64 R Mt by
  have hDA := hF.fmtDA; have hDT := hF.tabDA
  have hf1 := hF.l1; have hf2 := hF.l2; have hf3 := hF.d; have htl := hF.tabL; have htd := hF.tabD
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hf1, hf2, hf3, htl, htd, BitVec.add_assoc,
    ofNat_add_ofNat] at 2147529708

#ix_piece lldHead_2 from lldHead_1 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hf1, hf2, hf3, htl, htd, BitVec.add_assoc,
    ofNat_add_ofNat] at 2147529708

#ix_piece lldHead_3 from lldHead_2 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hf1, hf2, hf3, htl, htd, BitVec.add_assoc,
    ofNat_add_ofNat] at 2147529708

#ix_piece lldHead_4 from lldHead_3 by
  have hb := zero_le_toInt_iff v
  by_cases hneg : isNeg v
  · simp only [hneg, not_true_eq_false] at hb
    nf_go 1 [14] hlive using [h2, h25, hap, hv, hf1, hf2, hf3, htl, htd, hb, BitVec.add_assoc,
      ofNat_add_ofNat] at 2147529748
    nx_flat
    lld_close hk : hneg
  · simp only [hneg, not_false_eq_true] at hb
    nf_go 1 [14] hlive using [h2, h25, hap, hv, hf1, hf2, hf3, htl, htd, hb, BitVec.add_assoc,
      ofNat_add_ofNat] at 2147529748
    nx_flat
    lld_close hk : hneg

/-! **`lld_head`**: `0x8000a9fc` (the `%` of `"%lld"`) → `0x8000b414`, post `LldHead`. -/
#ix_chain lld_head := [lldHead_1, lldHead_2, lldHead_3, lldHead_4]

/-! ## The magnitude's digits (`0x8000b414` → `0x8000b444`) -/

/-- `subw` of two addresses a small distance apart. -/
theorem subw_near {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) (hab : a - b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 (a - b) := by
  have e : BitVec.extractLsb 31 0 (BitVec.ofNat 64 a) - BitVec.extractLsb 31 0 (BitVec.ofNat 64 b) =
      BitVec.ofNat 32 (a - b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 (a - b)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat]; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The bytes the magnitude step writes: the spill slots `[sp + 32, sp + 128)` and
the conversion buffer `[sp + 248, sp + 348)`. -/
def MagReg (sp : Nat) (a : Nat) : Prop :=
  (sp + 32 ≤ a ∧ a < sp + 128) ∨ (sp + 248 ≤ a ∧ a < sp + 348)

/-- The registers the magnitude step keeps. -/
abbrev magKeep : List Nat := [2, 7, 9, 16, 17, 18, 19, 21, 22, 23, 24, 28, 29, 31]

/-- The state at `0x8000b444`: the digits of `m` end at `sp + 348`, `s9` at
the first, `a3 = a4` their count, `t5` the sign byte, `t1 = 0`, the slot
`sp + 32` cleared. -/
structure LldMag (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp m : BitVec 64) : Prop where
  ptr : R' 25 = BitVec.ofNat 64 (sp.toNat + 348 - (digBytes m.toNat).length)
  a3 : R' 13 = BitVec.ofNat 64 (digBytes m.toNat).length
  a4 : R' 14 = BitVec.ofNat 64 (digBytes m.toNat).length
  t5 : R' 30 = ldv .lbu Mt (sp + 167#64).toNat
  t1 : R' 6 = 0#64
  keep : ∀ x ∈ magKeep, R' x = R x
  digits : ∀ i (h : i < (digBytes m.toNat).length),
    imgM Mt' (sp.toNat + 348 - (digBytes m.toNat).length + i) = (digBytes m.toNat)[i]
  zero32 : ldv .ld Mt' (sp + 32#64).toNat = 0#64
  frame : Frame Mt' Mt (MagReg sp.toNat)

theorem sp_lit {sp : BitVec 64} {k : Nat} (h : sp.toNat + k < 2 ^ 64) :
    (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := toNat_add_lit h

/-- **A magnitude of at most 9**: one digit at `sp + 347`. -/
theorem lldMag_small (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp m : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h26 : R 26 = m) (h22 : R 22 = 18446744073709551615#64) (hm9 : m.toNat ≤ 9)
    (hk : ∀ R' Mt', LldMag R R' Mt Mt' sp m →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b444#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b414#64 R Mt := by
  have hb : (m.toNat ≤ 9) = True := eq_true hm9
  have hmw : m = BitVec.ofNat 64 m.toNat := by simp
  have hdw : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (m + 48#64)) =
      BitVec.zeroExtend 64 (BitVec.ofNat 8 (48 + m.toNat)) := by
    have := digit_word m.toNat (by omega)
    rwa [← hmw] at this
  have hL := digBytes_small m.toNat hm9
  have hLl : (digBytes m.toNat).length = 1 := by rw [hL]; rfl
  nx_run hlive using [h2, h26, h22, hb, hdw] at 2147529796
  have e347 : (sp + 347#64).toNat = sp.toNat + 347 := sp_lit (by omega)
  have e32 : (sp + 32#64).toNat = sp.toNat + 32 := sp_lit (by omega)
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rsimp; rw [hLl]; apply BitVec.eq_of_toNat_eq; rw [e347, BitVec.toNat_ofNat]; omega
  · rsimp; rw [hLl]
  · rsimp; rw [hLl]
  · rsimp
  · rsimp
  · have := fun x (_ : x ∈ magKeep) => (rfl : R x = R x)
    keep_chain this
  · intro i hi
    rw [hLl] at hi
    obtain rfl : i = 0 := by omega
    simp only [List.getElem_of_eq hL, List.getElem_cons_zero]
    rw [imgM_store_miss _ _ (by rw [e32, hLl]; omega), show sp.toNat + 348 - (digBytes m.toNat).length + 0
      = (sp + 347#64).toNat by rw [e347, hLl]; omega]
    exact imgM_sb_zext _ _ _
  · exact ldv_store_hit _ _ _
  · refine ((Frame.refl _ _).snoc fun b h1 h2 => ?_).snoc fun b h1 h2 => ?_
    · rw [e347] at h1 h2; unfold MagReg; omega
    · rw [e32] at h1 h2; unfold MagReg; omega

/-- `sext.w` of a small count. -/
theorem sextw_ofNat {L : Nat} (h : L < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 L)) = BitVec.ofNat 64 L := by
  have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 L)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- **A magnitude above 9**: the frame spills, the decimal loop
(`vfp_digits`), the reloads. -/
theorem lldMag_big (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp m : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h26 : R 26 = m) (h22 : R 22 = 18446744073709551615#64) (h28 : R 28 = 32#64)
    (h29 : R 29 = 0#64) (hm9 : ¬ m.toNat ≤ 9)
    (hk : ∀ R' Mt', LldMag R R' Mt Mt' sp m →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b444#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b414#64 R Mt := by
  have hb : (m.toNat ≤ 9) = False := eq_false hm9
  nx_run hlive using [h2, h26, h22, h28, h29, hb] at 2147535488
  have e348 : sp + 348#64 = BitVec.ofNat 64 (sp.toNat + 348) := by
    apply BitVec.eq_of_toNat_eq; rw [sp_lit (by omega), BitVec.toNat_ofNat]; omega
  have hL20 := digBytes_len m.toNat m.isLt
  have hL1 := digBytes_pos m.toNat
  refine vfp_digits hlive hlive' hsub hs1 hs2 hs3 hs4 hal m.toNat (sp.toNat + 348) _ _ m.isLt (by omega)
    (by omega) (by rsimp; exact h2) (by rsimp) (by rsimp; simp) (by rsimp; exact e348)
    fun R1 Mt1 e25 hk1 hF1 hd => ?_
  have eo : ∀ k : Nat, k ≤ 400 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have hlo : ∀ (kd : MKind) (k : Nat), k ≤ 240 → widthOfM kd ≤ 8 →
      ldv kd Mt1 (sp + BitVec.ofNat 64 k).toNat = _ := fun kd k hk hw =>
    hF1.ldv kd (fun j hj h => by unfold DigReg at h; rw [eo k (by omega)] at h; omega)
  have l120 := hlo .ld 120 (by omega) (by decide)
  have l112 := hlo .ld 112 (by omega) (by decide)
  have l40 := hlo .ld 40 (by omega) (by decide)
  have l48 := hlo .ld 48 (by omega) (by decide)
  have l104 := hlo .ld 104 (by omega) (by decide)
  have l32 := hlo .ld 32 (by omega) (by decide)
  have l167 := hlo .lbu 167 (by omega) (by decide)
  simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_miss, ldv_lbu_miss] at l120 l112 l40 l48 l104 l32 l167
  rw [e348] at l120
  have k2 : R1 2 = sp := by rw [hk1 2 (by decide)]; rsimp; exact h2
  have hsw := subw_near (a := sp.toNat + 348) (b := sp.toNat + 348 - (digBytes m.toNat).length)
    (by omega) (by omega) (by omega)
  rw [show sp.toNat + 348 - (sp.toNat + 348 - (digBytes m.toNat).length) = (digBytes m.toNat).length by omega]
    at hsw
  have hLt : (BitVec.ofNat 64 (digBytes m.toNat).length).toInt = (digBytes m.toNat).length :=
    toInt_ofNat_small (by omega)
  have hbl1 : ((18446744073709551615#64).toInt < (BitVec.ofNat 64 (digBytes m.toNat).length).toInt) = True :=
    eq_true (by rw [hLt, show (18446744073709551615#64).toInt = -1 by decide]; omega)
  nx_run hlive using [k2, e25, l120, l112, l40, l48, l104, l32, l167, hsw, hbl1] at 2147529796
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rsimp; exact e25
  · rsimp
  · rsimp; exact sextw_ofNat (by omega)
  · rsimp
  · rsimp
  · intro x hx
    simp only [magKeep, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
      first | exact h22.symm | exact h29.symm | exact h28.symm | rfl | (rw [hk1 _ (by decide)]; rsimp)
  · intro i hi
    rw [imgM_store_miss _ _ (by rw [eo 32 (by omega)]; omega), imgM_store_miss _ _ (by rw [eo 40 (by omega)]; omega),
      imgM_store_miss _ _ (by rw [eo 96 (by omega)]; omega)]
    exact hd i hi
  · exact ldv_store_hit _ _ _
  · refine ((Frame.trans ?_ (hF1.mono fun a h => by unfold DigReg at h; unfold MagReg; omega)).snoc
      fun b h1 h2 => ?_).snoc (fun b h1 h2 => ?_) |>.snoc fun b h1 h2 => ?_
    · repeat (refine Frame.snoc ?_ ?_)
      all_goals first | exact Frame.refl _ _ | (intro b h1 h2; rw [eo _ (by omega)] at h1 h2; unfold MagReg; omega)
    all_goals (rw [eo _ (by omega)] at h1 h2; unfold MagReg; omega)

/-- **The magnitude's digits** (`0x8000b414` → `0x8000b444`), post `LldMag`. -/
theorem lld_mag (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp m : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h26 : R 26 = m) (h22 : R 22 = 18446744073709551615#64) (h28 : R 28 = 32#64)
    (h29 : R 29 = 0#64)
    (hk : ∀ R' Mt', LldMag R R' Mt Mt' sp m →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b444#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b414#64 R Mt := by
  by_cases hm9 : m.toNat ≤ 9
  · exact lldMag_small hlive hs1 hs2 hs3 hs4 hal h2 h26 h22 hm9 fun R' Mt' h =>
      hk R' Mt' h
  · exact lldMag_big hlive hlive' hsub hs1 hs2 hs3 hs4 hal h2 h26 h22 h28 h29 hm9 hk

end VsaIris.Sym.Fp
