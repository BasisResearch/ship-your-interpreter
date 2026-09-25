import VsaIris.Vsa.Fprintf.Print

/-!
# `%lld`'s pieces (lane N5)

From `0x8000b444` (`LldMag`: the digits `ds` end at `sp + 348`, the sign byte
`sg` at `sp + 167`) `_vfprintf_r` checks the width and precision (none),
appends the sign piece when `sg ≠ 0`, then the digits, counts them, and
calls `__sprint_r` at `0x8000b8c4` (`lld_stage`; `vfp_print` goes on).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

/-- `subw 0, k` of a small positive count, as an integer. -/
theorem negw_toInt {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 31) :
    (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 k))).toInt = -(k : Int) := by
  have ht : (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 k)).toNat = 4294967296 - k := by
    rw [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_cond, ht, if_neg (by omega)]
  omega

/-- `subw -1, k` of a small count, as an integer. -/
theorem subw_m1_toInt {k : Nat} (h : k < 2 ^ 31) :
    (BitVec.signExtend 64 (4294967295#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 k))).toInt = -1 - (k : Int) := by
  have ht : (4294967295#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 k)).toNat = 4294967295 - k := by
    rw [BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_cond, ht, if_neg (by omega)]
  omega

/-- The `%lld` pieces: the sign byte when there is one, then the digits
ending at `sp + 348`. -/
def lldIovs (sp : Nat) (sg : BitVec 8) (ds : List (BitVec 8)) : List (Nat × List (BitVec 8)) :=
  (if sg = 0#8 then [] else [(sp + 167, [sg])]) ++ [(sp + 348 - ds.length, ds)]

/-- The count `%lld` adds. -/
def lldCnt (sg : BitVec 8) (ds : List (BitVec 8)) : Nat := (if sg = 0#8 then 0 else 1) + ds.length

/-- The bytes `lld_stage` writes: the count, the slot at `sp + 48`, the
`uio`'s count and residual, the first two iovs. -/
def StageReg (sp : Nat) (a : Nat) : Prop :=
  (sp + 16 ≤ a ∧ a < sp + 24) ∨ (sp + 48 ≤ a ∧ a < sp + 56) ∨ (sp + 232 ≤ a ∧ a < sp + 248) ∨
    (sp + 352 ≤ a ∧ a < sp + 384)

#ix_piece lldStage_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp reent f : BitVec 64} {need cnt : Nat} {sg : BitVec 8} {ds : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hL1 : 1 ≤ ds.length) (hL2 : ds.length ≤ 20) (hcnt : cnt + 21 < 2 ^ 31)
    (hP : VfpPend R Mt sp reent f cnt [])
    (h25 : R 25 = BitVec.ofNat 64 (sp.toNat + 348 - ds.length)) (h13 : R 13 = BitVec.ofNat 64 ds.length)
    (h14 : R 14 = BitVec.ofNat 64 ds.length) (h30 : R 30 = BitVec.zeroExtend 64 sg) (h6 : R 6 = 0#64)
    (h22 : R 22 = 18446744073709551615#64) (h28 : R 28 = 32#64) (h29 : R 29 = 0#64)
    (hsg : ldv .lbu Mt (sp + 167#64).toNat = BitVec.zeroExtend 64 sg)
    (hk : ∀ R' Mt', VfpPend R' Mt' sp reent f (cnt + lldCnt sg ds) (lldIovs sp.toNat sg ds) →
      (∀ x ∈ [24], R' x = R x) → Frame Mt' Mt (StageReg sp.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b8c4#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b444#64 R Mt by
  have h2 := hP.spR; have h21 := hP.s5; have h23 := hP.s7
  have hres := hP.resid; have hic := hP.iovcnt; have hc16 := hP.count
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, piecesLen, List.map_nil, List.sum_nil] at h23 hres hic
  have e1 : BitVec.ofNat 64 ds.length + 1#64 = BitVec.ofNat 64 (ds.length + 1) := by
    apply BitVec.eq_of_toNat_eq; simp
  have e1' : 1#64 + BitVec.ofNat 64 ds.length = BitVec.ofNat 64 (ds.length + 1) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  have es := sextw_ofNat (L := ds.length + 1) (by omega)
  have es0 := sextw_ofNat (L := ds.length) (by omega)
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  have hawA := addw_ofNat' (a := ds.length) (b := cnt) (by omega)
  have hawB := addw_ofNat' (a := ds.length + 1) (b := cnt) (by omega)
  by_cases hs0 : sg = 0#8

#ix_piece lldStage_2 from lldStage_1 at 1 by
  have hz0 : BitVec.zeroExtend 64 sg = 0#64 := by rw [hs0]; decide
  have hpad0 : ((0#64).toInt < (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 ds.length))).toInt) = False :=
    eq_false (by rw [negw_toInt (by omega) (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hs6' : ((BitVec.signExtend 64 (4294967295#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 ds.length))).toInt ≤ (0#64).toInt) = True :=
    eq_true (by rw [subw_m1_toInt (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hbge0 : ((BitVec.ofNat 64 ds.length).toInt ≤ (0#64).toInt) = False :=
    eq_false (by rw [toInt_ofNat_small (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hzL1 : (BitVec.ofNat 64 ds.length = 0#64) = False := eq_false fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have hzL2 : (BitVec.ofNat 64 ds.length ≠ 0#64) = True := eq_true fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have haw := addw_ofNat' (a := cnt) (b := ds.length) (by omega)
  nf_go 2 [14] hlive using [h2, h21, h23, h25, h13, h14, h30, h6, h22, h28, h29, hres, hic, hc16, hsg, hz0,
    hpad0, hs6', hbge0, hzL1, hzL2, haw, es0, BitVec.add_assoc, BitVec.zero_add] at 2147530948

#ix_piece lldStage_2b from lldStage_2 by
  nf_go 2 [14] hlive using [h2, h21, h23, h25, h13, h14, h30, h6, h22, h28, h29, hres, hic, hc16, hsg, hz0,
    hpad0, hs6', hbge0, hzL1, hzL2, haw, es0, BitVec.add_assoc, BitVec.zero_add] at 2147530948

#ix_piece lldStage_2c from lldStage_2b by
  have hI : lldIovs sp.toNat sg ds = [(sp.toNat + 348 - ds.length, ds)] := by simp [lldIovs, hs0]
  have hC : cnt + lldCnt sg ds = ds.length + cnt := by simp [lldCnt, hs0]; omega
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
  all_goals simp (config := {failIfUnchanged := false}) only [hI, hC, List.length_singleton, piecesLen,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  · rsimp; exact f2.trans h2
  · rsimp; exact f9.trans hP.s1
  · rsimp; exact f18.trans hP.s2
  · rsimp; exact f19.trans hP.s3
  · rsimp; exact f21.trans h21
  · rsimp; first | rfl | (rw [f23]; rfl) | rw [f23]
  · nx_mem; exact hP.reent
  · nx_mem; exact hP.file
  · nx_mem; exact hawA
  · nx_mem; exact hP.base
  · nx_mem; rfl
  · nx_mem
  · intro j hj
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, List.length_singleton]
    refine ⟨?_, ?_⟩
    · rw [show (BitVec.ofNat 64 (sp.toNat + 352)).toNat = (sp + 352#64).toNat by rw [eo 352 (by omega)]; simp; omega]
      nx_mem
    · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 8)).toNat = (sp + 360#64).toNat by rw [eo 360 (by omega)]; simp; omega]
      nx_mem
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rsimp; exact f24
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ |
      (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
       unfold StageReg; omega)



#ix_piece lldStage_3 from lldStage_1 at 2 by
  have hz : (BitVec.zeroExtend 64 sg = 0#64) = False := eq_false fun h => zext8_ne hs0 (h.trans (by decide))
  have hz' : (BitVec.zeroExtend 64 sg ≠ 0#64) = True := eq_true fun h => by rw [hz] at h; exact h
  have hpad : ((0#64).toInt < (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 (ds.length + 1)))).toInt) = False :=
    eq_false (by rw [negw_toInt (by omega) (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hs6 : ((0#64).toInt < (BitVec.signExtend 64 (4294967295#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 ds.length))).toInt) = False :=
    eq_false (by rw [subw_m1_toInt (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hbge1 : ((BitVec.ofNat 64 (ds.length + 1)).toInt ≤ (0#64).toInt) = False :=
    eq_false (by rw [toInt_ofNat_small (by omega)]; simp only [BitVec.toInt_zero]; omega)
  have hz1 : (BitVec.ofNat 64 (ds.length + 1) = 0#64) = False := eq_false fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have hz2 : (BitVec.ofNat 64 (ds.length + 1) ≠ 0#64) = True := eq_true fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have haw := addw_ofNat' (a := cnt) (b := ds.length + 1) (by omega)
  nf_go 2 [14] hlive using [h2, h21, h23, h25, h13, h14, h30, h6, h22, h28, h29, hres, hic, hc16, hsg, hz, hz',
    e1, e1', es, hpad, hs6, hbge1, hz1, hz2, haw, BitVec.add_assoc] at 2147530948

#ix_piece lldStage_3b from lldStage_3 by
  nf_go 2 [14] hlive using [h2, h21, h23, h25, h13, h14, h30, h6, h22, h28, h29, hres, hic, hc16, hsg, hz, hz',
    e1, e1', es, hpad, hs6, hbge1, hz1, hz2, haw, BitVec.add_assoc] at 2147530948

#ix_piece lldStage_3c from lldStage_3b by
  have hI : lldIovs sp.toNat sg ds = [(sp.toNat + 167, [sg]), (sp.toNat + 348 - ds.length, ds)] := by
    simp [lldIovs, hs0]
  have hC : cnt + lldCnt sg ds = ds.length + 1 + cnt := by simp [lldCnt, hs0]; omega
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
  all_goals simp (config := {failIfUnchanged := false}) only [hI, hC, List.length_cons, List.length_nil, piecesLen,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, List.length_singleton]
  · rsimp; exact f2.trans h2
  · rsimp; exact f9.trans hP.s1
  · rsimp; exact f18.trans hP.s2
  · rsimp; exact f19.trans hP.s3
  · rsimp; exact f21.trans h21
  · rsimp
  · nx_mem; exact hP.reent
  · nx_mem; exact hP.file
  · nx_mem; exact hawB
  · nx_mem; exact hP.base
  · nx_mem; rfl
  · nx_mem; rw [Nat.add_comm]
  · intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, List.length_singleton]
      refine ⟨?_, ?_⟩
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352)).toNat = (sp + 352#64).toNat by rw [eo 352 (by omega)]; simp; omega]
        nx_mem; apply BitVec.eq_of_toNat_eq; rw [eo 167 (by omega)]; simp; omega
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 8)).toNat = (sp + 360#64).toNat by rw [eo 360 (by omega)]; simp; omega]
        nx_mem
    · simp only [Nat.mul_one, List.getElem_cons_succ, List.getElem_cons_zero]
      refine ⟨?_, ?_⟩
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 16)).toNat = (sp + 368#64).toNat by rw [eo 368 (by omega)]; simp; omega]
        nx_mem
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 16 + 8)).toNat = (sp + 376#64).toNat by rw [eo 376 (by omega)]; simp; omega]
        nx_mem
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rsimp; exact f24
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ |
      (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
       unfold StageReg; omega)



/-! **`lld_stage`**: `%lld`'s pieces staged, `0x8000b444` → `0x8000b8c4`. -/
#ix_tree lld_stage := lldStage_1 [lldStage_2 [lldStage_2b [lldStage_2c]], lldStage_3 [lldStage_3b [lldStage_3c]]]

end VsaIris.Sym.Fp
