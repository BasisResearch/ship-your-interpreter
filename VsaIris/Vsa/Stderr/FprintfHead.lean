import VsaIris.Vsa.Stderr.VfpErr
import VsaIris.Vsa.Fprintf.SbFile

/-!
# `fprintf(stderr, fmt, p)` up to `_vfprintf_r`'s direct path (lane N3)

`fprintf` (`0x800061c0`) spills its variadic registers (`a2`–`a7` at
`sp + 32 …`, `ap = sp + 32`), loads `_impure_ptr` and calls `_vfprintf_r`;
`vfpEntry_run` and `vfpErr_run` take it to `0x8000a944`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

set_option hygiene false in
/-- A load of `stderr`'s or `_impure_data`'s fields through `vfpEntry_run`'s
frame (`hF`) and `fprintf`'s spills, down to the entry memory. -/
macro "fh_tr" : tactic => `(tactic| (
  refine (hF.ldv _ fun j hj => by
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, widthOfM]
    simp only [widthOfM] at hj
    nx_fdisch).trans ?_
  nx_mem))

#ix_piece fprintfHead_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s ra p : BitVec 64)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - 4096) (hal : s.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h2 : R 2 = s) (h10 : R 10 = 0x8001bbd8#64) (h11 : R 11 = 0x800195e0#64)
    (h12 : R 12 = p) (hDt : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    (hC : ConsoleMt Mt) (hE : ErrMt Mt) (hL : LocaleMt Mt)
    (hk : ∀ R' Mt', SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s 4096) Q t 0x8000a944#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s 4096) Q t
      0x800061c0#64 R Mt by
  nx_runB hlive using [h1, h2, h10, h11, h12, hDt, BitVec.add_assoc] at 0x8000a884

#ix_piece fprintfHead_02 from fprintfHead_01 by
  refine vfpEntry_run (hlive := hlive) (t := t) (s := s) (need := 4096) (hs3 := hs3) (hs4 := hs4)
    (ra := 0x80006204#64) (reent := 0x8001b538#64) (fp := 0x8001bbd8#64) (fmt := 0x800195e0#64)
    (ap := s + 18446744073709551568#64) (hs1 := ?hs1) (hs2 := ?hs2) (hal := ?hal) (h1 := ?h1)
    (h10 := ?h10) (h11 := ?h11) (h12 := ?h12) (h13 := ?h13) (hdec := ?hdec)
    (hdA := ⟨List.mem_append_right _ hdA.1, List.mem_append_right _ hdA.2⟩) (hdv := hdv)
    (hk := fun R' Mt' hV => ?_)
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2,
    BitVec.add_assoc, BitVec.reduceAdd]; done))
  case hs1 | hs2 | hal => simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2]; nx_fdisch
  case hdec => nx_mem; exact hL.decPoint
  have hF : Fp.Frame Mt' _ _ := hV.frame
  refine vfpErr_run (hlive := hlive) (t := t) (s := s) (need := 4096) (hs3 := hs3) (hs4 := hs4)
    (sp := s + 18446744073709550944#64) (hDt := hDt) (hs1 := ?hs1) (hs2 := ?hs2)
    (hal := ?hal) (h2 := ?h2) (h8 := ?h8) (h20 := ?h20) (hsinit := ?hsinit) (hflU := ?hflU)
    (hflS := ?hflS) (hmode := ?hmode) (hlock := ?hlock) (hfd := ?hfd) (hbase := ?hbase)
    (hk := fun R'' hH => ?_)
  case hs1 | hs2 | hal => nx_fdisch
  case h2 =>
    rw [hV.sp_eq]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  case h8 => rw [hV.s0]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  case h20 => rw [hV.s4]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  case hsinit => fh_tr; exact hC.sinit
  case hflU => fh_tr; exact hE.flagsU
  case hflS => fh_tr; exact hE.flagsS
  case hmode => fh_tr; exact hE.lockMode
  case hlock => fh_tr; exact hE.lock
  case hfd => fh_tr; exact hE.fd
  case hbase => fh_tr; exact hE.base
  exact hk _ _

end VsaIris.Sym
