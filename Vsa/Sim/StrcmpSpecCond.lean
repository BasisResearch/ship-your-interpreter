import Vsa.Sim.StrcmpSpecW4

/-!
# `StrcmpSpecCond` — the `strcmp` spec with the word-path alignment derived from the test

`strcmp_full_pre` (`StrcmpSpecW4.lean`) demands `StrcmpWRegion` — including
8-alignment of BOTH payload pointers — unconditionally, although the word path is
taken only when the entry test `(pa ||| pb) &&& 7 = 0` succeeds.  A string
literal's payload (AST bytes) is not 8-aligned in general, so the unconditional
premise is unsatisfiable for the string cells.

This file states the entry as a named-field structure `StrcmpEntryCond` whose
word-region clause is the alignment-free `StrcmpWSlack` (the word loop's slack
geometry), derives both alignments from the entry test (`align8_of_test`), and
proves `strcmp_full_spec_cond` from the landed `strcmp_word_spec` /
`strcmp_byte_path`.  The byte-region clauses are derived (`StrcmpWSlack.toRegion`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

/-- `StrcmpWRegion` without its alignment field: the word loop may read up to 7
bytes past the NUL, so the payload needs 8 bytes of slack inside RAM and away
from the `strcmp` code and the HTIF window. -/
structure StrcmpWSlack (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  code : p.toNat + len + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ p.toNat
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

/-- The slack region plus the alignment the entry test supplies. -/
theorem StrcmpWSlack.toWRegion {p : BitVec 64} {len : Nat} (h : StrcmpWSlack p len)
    (hal : p.toNat % 8 = 0) : StrcmpWRegion p len :=
  ⟨h.lo, h.hi, h.nowrap, h.code, h.htif, hal⟩

/-- The slack region contains the byte-path region. -/
theorem StrcmpWSlack.toRegion {p : BitVec 64} {len : Nat} (h : StrcmpWSlack p len) :
    StrcmpRegion p len :=
  ⟨h.lo, by have := h.hi; omega, by have := h.nowrap; omega,
    (by rcases h.code with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h),
    (by rcases h.htif with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h)⟩

/-- The entry alignment test `(pa ||| pb) &&& 7 = 0` aligns both pointers to 8. -/
theorem align8_of_test {pa pb : BitVec 64}
    (hal : ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) = 0#64) :
    pa.toNat % 8 = 0 ∧ pb.toNat % 8 = 0 := by
  have h7 : (sign_extend (m := 64) (0x007#12) : BitVec 64) = 7#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [h7, BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at hal
  obtain ⟨ha, hb⟩ := hal
  have key : ∀ x : BitVec 64, x &&& 7#64 = 0#64 → x.toNat % 8 = 0 := by
    intro x hx
    have h1 := congrArg BitVec.toNat hx
    rw [BitVec.toNat_and] at h1
    have h72 : (7#64 : BitVec 64).toNat = 2^3 - 1 := by decide
    rw [h72, Nat.and_two_pow_sub_one_eq_mod] at h1
    simpa using h1
  exact ⟨key pa ha, key pb hb⟩

/-- The `strcmp` entry with the word-path geometry stated WITHOUT alignment:
`strcmp_full_pre` with its two `StrcmpWRegion` clauses weakened to
`StrcmpWSlack` and its two byte-region clauses dropped (derived). -/
structure StrcmpEntryCond (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some pa
  a1 : c.σ.regs.get? Register.x11 = some pb
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  ralign : r.toNat % 4 = 0
  cstra : CString m0 pa.toNat sa
  cstrb : CString m0 pb.toNat sb
  maskpin : MaskPinned m0
  wrega : ∀ cs, CStr m0 pa.toNat cs → StrcmpWSlack pa cs.length
  wregb : ∀ cs, CStr m0 pb.toNat cs → StrcmpWSlack pb cs.length
  frame : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- **`strcmp` total-correctness spec with the alignment derived from the entry
test.**  Aligned → `strcmp_word_spec` (the alignments come from the test);
misaligned → `strcmp_byte_path` (the byte regions come from the slack regions). -/
theorem strcmp_full_spec_cond (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (StrcmpEntryCond g pa pb r sa sb m0 o) (strcmp_post g r pa pb sa sb m0 o) := by
  intro c h
  obtain ⟨csa, hcstra, hsa⟩ := h.cstra
  obtain ⟨csb, hcstrb, hsb⟩ := h.cstrb
  by_cases hal : ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) = 0#64
  · obtain ⟨h8a, h8b⟩ := align8_of_test hal
    have hPreW : PreWCmp g pa pb r csa csb m0 o c :=
      ⟨h.good, h.loaded, h.mem, h.out, h.pc, h.a0, h.a1, h.ra, h.minstret, h.tick,
        (h.wrega csa hcstra).toWRegion h8a, (h.wregb csb hcstrb).toWRegion h8b,
        hcstra, hcstrb, h.maskpin, hal, h.frame⟩
    obtain ⟨c', hsteps, hDone⟩ := strcmp_word_spec g pa pb r csa csb m0 o h.ralign c hPreW
    obtain ⟨hG', hpc', hra', hmem', hout', htick', ⟨x, hx, hsign⟩, hframe'⟩ := hDone
    exact ⟨c', hsteps, hG', hpc', hra', hmem', hout', htick', hframe',
      csa, csb, x, hcstra, hcstrb, hsa, hsb, hx, hsign⟩
  · have hPreB : PreBCmp g pa pb r csa csb m0 o c :=
      ⟨h.good, h.loaded, h.mem, h.out, h.pc, h.a0, h.a1, h.ra, h.minstret, h.tick,
        (h.wrega csa hcstra).toRegion, (h.wregb csb hcstrb).toRegion,
        hcstra, hcstrb, hal, h.frame⟩
    obtain ⟨c', hsteps, hDone⟩ := strcmp_byte_path g pa pb r csa csb m0 o h.ralign c hPreB
    obtain ⟨hG', hpc', hra', hmem', hout', htick', ⟨x, hx, hsign⟩, hframe'⟩ := hDone
    exact ⟨c', hsteps, hG', hpc', hra', hmem', hout', htick', hframe',
      csa, csb, x, hcstra, hcstrb, hsa, hsb, hx, hsign⟩

#print axioms align8_of_test
#print axioms StrcmpWSlack.toRegion
#print axioms strcmp_full_spec_cond

end Vsa.Sim
