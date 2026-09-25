import VsaIris.Vsa.Fprintf.LldConv

/-!
# `%s` in `_vfprintf_r` (lane N5, shared with N3)

From the `%` at `X` of a `%s`: the conversion parse (`s` through the jump
table), the argument `str` loaded from `ap` (non-null), its length through
`strlen` (the hook `hstr`: H3's run, `strlen_sw`), the string's iov appended
after the pending ones, the count, and on to `__sprint_r` at `0x8000b8c4`
(`s_stage`). The string bytes `bs` are the caller's (`strlen`'s result is
`bs.length`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

/-- The format bytes and jump-table word `%s` reads (data view). -/
structure SFmt (Dt : Mem) (DA : List Nat) (X : Nat) : Prop where
  fmtDA : Cover (· ∈ DA) (X + 1) (X + 2)
  tabDA : Cover (· ∈ DA) 0x8001a288 0x8001a3f4
  s : ldv .lbu Dt (X + 1) = 0x73#64
  tabS : ldv .lw Dt 0x8001a3d4 = 18446744073709490340#64

/-- A small count stored with `sw` and loaded with `lw`. -/
theorem lw_ofNat {k : Nat} (h : k < 2 ^ 31) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64) (BitVec.ofNat 32 ((BitVec.ofNat 64 k).toNat % 2 ^ 32)) =
      BitVec.ofNat 64 k := by
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  have hm : (BitVec.ofNat 32 ((BitVec.ofNat 64 k).toNat % 2 ^ 32)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem piecesLen_append (a b : List (Nat × List (BitVec 8))) :
    piecesLen (a ++ b) = piecesLen a + piecesLen b := by
  simp [piecesLen]

theorem piecesBytes_append (a b : List (Nat × List (BitVec 8))) :
    piecesBytes (a ++ b) = piecesBytes a ++ piecesBytes b := by
  simp [piecesBytes]

/-- The bytes `s_stage` writes: `ap`, the count, the spill slots, the sign
byte, the `uio`'s count and residual, the new iov. -/
def SReg (sp n : Nat) (a : Nat) : Prop :=
  (sp + 16 ≤ a ∧ a < sp + 56) ∨ (sp + 104 ≤ a ∧ a < sp + 112) ∨ a = sp + 167 ∨
    (sp + 232 ≤ a ∧ a < sp + 248) ∨ (sp + 352 + 16 * n ≤ a ∧ a < sp + 368 + 16 * n)

set_option hygiene false in
/-- The post of `s_stage` at `0x8000b8c4`, from the flat register facts and
the run's store chain. -/
local macro "s_close" : tactic => `(tactic| (
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · rsimp; exact f2.trans h2
  · rsimp; exact f9.trans hP.s1
  · rsimp; exact f18.trans hP.s2
  · rsimp; exact f19.trans hP.s3
  · rsimp; exact f21.trans h21
  · rsimp; rw [List.length_append, List.length_singleton]; first | exact f23 | skip
  · nx_mem; exact hP.reent
  · nx_mem; exact hP.file
  · nx_mem; first | (rw [Nat.add_comm]; done) | simp [hL0]
  · nx_mem; exact hP.base
  · nx_mem; rw [lw_ofNat (by omega)]; simp
  · nx_mem; rw [piecesLen_append]; first | (simp [piecesLen]; done) | simp [piecesLen, hL0]
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjn : j < iovs.length
    · rw [List.getElem_append_left hjn]
      obtain ⟨a1, a2⟩ := hP.arr j hjn
      exact ⟨by nx_mem; exact a1, by nx_mem; exact a2⟩
    · obtain rfl : j = iovs.length := by omega
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      refine ⟨?_, ?_⟩
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 16 * iovs.length)).toNat =
          (sp + BitVec.ofNat 64 (352 + 16 * iovs.length)).toNat by
          rw [toNat_add_lit (by simp; omega)]; simp; omega]
        nx_mem; simp
      · rw [show (BitVec.ofNat 64 (sp.toNat + 352 + 16 * iovs.length + 8)).toNat =
          (sp + BitVec.ofNat 64 (360 + 16 * iovs.length)).toNat by
          rw [toNat_add_lit (by simp; omega)]; simp; omega]
        nx_mem
        try simp [hL0]
  · rsimp; exact f24
  · nx_mem
  · nx_mem
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ |
      (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit,
        BitVec.toNat_ofNat] at h1 h2; unfold SReg; omega)))

#ix_piece sStage_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp reent f X ap str : BitVec 64} {need cnt : Nat} {iovs : List (Nat × List (BitVec 8))}
    {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hX1 : 0x80000000 ≤ X.toNat) (hX2 : X.toNat + 2 < 0x8001ad00)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (hn : iovs.length ≤ 6) (hlen : piecesLen iovs + bs.length < 2 ^ 30) (hpos : 0 < piecesLen iovs + bs.length)
    (hcnt : cnt + bs.length < 2 ^ 30)
    (hP : VfpPend R Mt sp reent f cnt iovs) (h25 : R 25 = X) (hF : SFmt Dt DA X.toNat)
    (hap : ldv .ld Mt (sp + 24#64).toNat = ap) (hv : ldv .ld Mt ap.toNat = str) (hs0 : str ≠ 0#64)
    (hstr : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 1 = 0x8000cfcc#64 → R0 10 = str →
      (∀ v : Nat → BitVec 64, SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000cfcc#64
        (upd (updAll R0 v [11, 12, 13, 14, 15, 16]) 10 (BitVec.ofNat 64 bs.length)) Mt0) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x80006cf0#64 R0 Mt0)
    (hk : ∀ R' Mt', VfpPend R' Mt' sp reent f (cnt + bs.length) (iovs ++ [(str.toNat, bs)]) →
      R' 24 = X + 2#64 → ldv .ld Mt' (sp + 32#64).toNat = 0#64 → ldv .ld Mt' (sp + 24#64).toNat = ap + 8#64 →
      Frame Mt' Mt (SReg sp.toNat iovs.length) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000b8c4#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9fc#64 R Mt by
  have h2 := hP.spR
  have hDA := hF.fmtDA; have hDT := hF.tabDA; have hf1 := hF.s; have hts := hF.tabS
  have eX : (X + 1#64).toNat = X.toNat + 1 := toNat_add_lit (by omega)
  have hs0' : (str = 0#64) = False := eq_false hs0
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536

#ix_piece sStage_2 from sStage_1 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536

#ix_piece sStage_3 from sStage_2 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536
  refine hstr _ _ (by rsimp) (by rsimp) fun v => ?_

#ix_piece sStage_4 from sStage_3 by
  have h21 := hP.s5; have h23 := hP.s7; have hres := hP.resid; have hic := hP.iovcnt; have hc16 := hP.count
  have hr0 := piecesLen_eq iovs
  have esL := sextw_ofNat (L := bs.length) (by omega)
  have hlt0 : ((BitVec.ofNat 64 bs.length).toInt < (0#64).toInt) = False :=
    eq_false (by rw [toInt_ofNat_small (by omega)]; simp only [BitVec.toInt_zero] <;> omega)
  have hrl : BitVec.ofNat 64 (piecesLen iovs) + BitVec.ofNat 64 bs.length =
      BitVec.ofNat 64 (piecesLen iovs + bs.length) := ofNat_add_ofNat _ _
  have hz1 : (BitVec.ofNat 64 (piecesLen iovs + bs.length) = 0#64) = False := eq_false fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have hz2 : (BitVec.ofNat 64 (piecesLen iovs + bs.length) ≠ 0#64) = True := eq_true fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have en1 : BitVec.ofNat 64 iovs.length + 1#64 = BitVec.ofNat 64 (iovs.length + 1) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have esn := sextw_ofNat (L := iovs.length + 1) (by omega)
  have hbl7 : ((7#64).toInt < (BitVec.ofNat 64 (iovs.length + 1)).toInt) = False :=
    eq_false (by rw [toInt_ofNat_small (by omega), toInt_ofNat_small (by omega)]; omega)
  have haw := addw_ofNat' (a := bs.length) (b := cnt) (by omega)
  have es7 : sp + BitVec.ofNat 64 (352 + 16 * iovs.length) + 16#64 = sp + BitVec.ofNat 64 (352 + 16 * (iovs.length + 1)) := by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; congr 2
  have e8 : sp + (BitVec.ofNat 64 (352 + 16 * iovs.length) + 8#64) = sp + BitVec.ofNat 64 (360 + 16 * iovs.length) := by
    rw [ofNat_add_ofNat, show 352 + 16 * iovs.length + 8 = 360 + 16 * iovs.length by omega]
  by_cases hL0 : bs.length = 0

#ix_piece sStage_5 from sStage_4 at 1 by
  have hL0' : BitVec.ofNat 64 bs.length = 0#64 := by rw [hL0]
  have esc := sextw_ofNat (L := cnt) (by omega)
  have hr1 : (BitVec.ofNat 64 (piecesLen iovs) = 0#64) = False := eq_false fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have hr2 : (BitVec.ofNat 64 (piecesLen iovs) ≠ 0#64) = True := eq_true fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esL, hlt0, hrl, hz1, hz2, en1, esn, hbl7, haw, es7, e8, hL0', hr1, hr2, esc,
    BitVec.add_assoc, BitVec.zero_add, BitVec.add_zero, BitVec.sub_self] at 2147530948

#ix_piece sStage_5b from sStage_5 by
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esL, hlt0, hrl, hz1, hz2, en1, esn, hbl7, haw, es7, e8, hL0', hr1, hr2, esc,
    BitVec.add_assoc, BitVec.zero_add, BitVec.add_zero, BitVec.sub_self] at 2147530948

#ix_piece sStage_5c from sStage_5b by
  s_close

#ix_piece sStage_6 from sStage_4 at 2 by
  have hpad : ((0#64).toInt < (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 bs.length))).toInt) = False :=
    eq_false (by rw [negw_toInt (by omega) (by omega)]; simp only [BitVec.toInt_zero] <;> omega)
  have hle : ((BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 (BitVec.ofNat 64 bs.length))).toInt ≤ (0#64).toInt) = True :=
    eq_true (by rw [negw_toInt (by omega) (by omega)]; simp only [BitVec.toInt_zero] <;> omega)
  have hbge : ((BitVec.ofNat 64 bs.length).toInt ≤ (0#64).toInt) = False :=
    eq_false (by rw [toInt_ofNat_small (by omega)]; simp only [BitVec.toInt_zero] <;> omega)
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esL, hlt0, hrl, hz1, hz2, en1, esn, hbl7, haw, es7, e8, hpad, hle,
    hbge, BitVec.add_assoc, BitVec.zero_add] at 2147530948

#ix_piece sStage_6b from sStage_6 by
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esL, hlt0, hrl, hz1, hz2, en1, esn, hbl7, haw, es7, e8, hpad, hle,
    hbge, BitVec.add_assoc, BitVec.zero_add] at 2147530948

#ix_piece sStage_6c from sStage_6b by
  s_close

/-! **`s_stage`**: `%s` from the `%` to `__sprint_r` at `0x8000b8c4`, the string's iov appended. -/
#ix_tree s_stage := sStage_1 [sStage_2 [sStage_3 [sStage_4 [sStage_5 [sStage_5b [sStage_5c]],
  sStage_6 [sStage_6b [sStage_6c]]]]]]

end VsaIris.Sym.Fp
