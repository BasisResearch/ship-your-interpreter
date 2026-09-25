import VsaIris.Vsa.Fprintf.SConv

/-!
# `%s` of an empty string with nothing pending (lane N3)

N5's `s_stage` for `bs = []` and no pending pieces: the residual stays 0, so
`_vfprintf_r` skips `__sprint_r` (`0x8000ab9c` falls through to `0x8000aba0`,
where a successful flush also lands) and goes back to the loop head
`0x8000a9b0` having printed nothing (`s_empty`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

#ix_piece sEmpty_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp reent f X ap str : BitVec 64} {need cnt : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hX1 : 0x80000000 ≤ X.toNat) (hX2 : X.toNat + 2 < 0x8001ad00)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (hcnt : cnt < 2 ^ 30)
    (hP : VfpPend R Mt sp reent f cnt []) (h25 : R 25 = X) (hF : SFmt Dt DA X.toNat)
    (hap : ldv .ld Mt (sp + 24#64).toNat = ap) (hv : ldv .ld Mt ap.toNat = str) (hs0 : str ≠ 0#64)
    (hstr : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 1 = 0x8000cfcc#64 → R0 10 = str →
      (∀ v : Nat → BitVec 64, SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000cfcc#64
        (upd (updAll R0 v [11, 12, 13, 14, 15, 16]) 10 0#64) Mt0) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x80006cf0#64 R0 Mt0)
    (hk : ∀ R' Mt', VfpLoop R' Mt' sp reent f (X + 2#64) cnt → ldv .ld Mt' (sp + 24#64).toNat = ap + 8#64 →
      ldv .ld Mt' (sp + 32#64).toNat = 0#64 → Frame Mt' Mt (SReg sp.toNat 0) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b0#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9fc#64 R Mt by
  have h2 := hP.spR
  have hDA := hF.fmtDA; have hDT := hF.tabDA; have hf1 := hF.s; have hts := hF.tabS
  have eX : (X + 1#64).toNat = X.toNat + 1 := toNat_add_lit (by omega)
  have hs0' : (str = 0#64) = False := eq_false hs0
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536

#ix_piece sEmpty_2 from sEmpty_1 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536

#ix_piece sEmpty_3 from sEmpty_2 by
  nf_go 1 [14] hlive using [h2, h25, hap, hv, hs0', hf1, hts, eX, BitVec.add_assoc] at 2147511536
  refine hstr _ _ (by rsimp) (by rsimp) fun v => ?_

#ix_piece sEmpty_4 from sEmpty_3 by
  have h21 := hP.s5; have h23 := hP.s7; have hres := hP.resid; have hic := hP.iovcnt; have hc16 := hP.count
  simp only [List.length_nil, piecesLen, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at h23 hres hic
  have esc := sextw_ofNat (L := cnt) (by omega)
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esc, BitVec.add_assoc, BitVec.zero_add,
    BitVec.add_zero, BitVec.sub_self] at 2147527088

#ix_piece sEmpty_5 from sEmpty_4 by
  nf_go 2 [14] hlive using [h2, h21, h23, hres, hic, hc16, esc, BitVec.add_assoc, BitVec.zero_add,
    BitVec.add_zero, BitVec.sub_self] at 2147527088

#ix_piece sEmpty_6 from sEmpty_5 by
  have hs9 := hP.s1; have hs18 := hP.s2; have hs19 := hP.s3
  rsimp
  simp (config := {failIfUnchanged := false}) only [*] at ⊢
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
  · rsimp; exact f2.trans h2
  · rsimp; exact f9.trans hs9
  · rsimp; exact f18.trans hs18
  · rsimp; exact f19.trans hs19
  · rsimp; exact f21.trans h21
  · rsimp
  · rsimp; exact f24
  · nx_mem; exact hP.reent
  · nx_mem; exact hP.file
  · nx_mem
  · nx_mem; exact hP.base
  · nx_mem; rfl
  · nx_mem
  · nx_mem
  · nx_mem
  · repeat (refine Frame.snoc ?_ ?_)
    all_goals first | exact Frame.refl _ _ | (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit, BitVec.toNat_ofNat] at h1 h2; unfold SReg; omega)

/-! **`s_empty`**: `%s` of `""` with nothing pending, from the `%` back to the loop head. -/
#ix_chain s_empty := [sEmpty_1, sEmpty_2, sEmpty_3, sEmpty_4, sEmpty_5, sEmpty_6]

end VsaIris.Sym.Fp
