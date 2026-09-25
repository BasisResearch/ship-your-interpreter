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

end VsaIris.Sym.Fp
