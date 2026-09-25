import VsaIris.Vsa.Stderr.FwriteRun
import VsaIris.Vsa.Fprintf.Tac

/-!
# `__sprint_r` on `stderr` with one piece (lane N3)

`_vfprintf_r` flushes after each conversion and at the end
(`0x8000b8d0`, `0x8000cf9c`): `__sprint_r(reent, stderr, uio)` with the
`uio`'s one nonempty `iov` (`"%s\n"`: the string, then the newline) on the
set-up unbuffered `stderr`. `__sfvwrite_r`'s unbuffered path hands the piece
whole to `__swrite` (`swriteErr_run`); the residual reaches 0, `__sprint_r`
clears the `uio` and returns 0.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The memory after the flush: changed only in the call's stack window, the
`uio`'s count and residual, the flags halfword (rewritten, still `0x201a`) and
`errno`; the `uio` is cleared. -/
structure SprintPost (Mt Mt' : Mem) (sp : BitVec 64) : Prop where
  frame : ∀ a, ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat) → ¬ (sp.toNat + 232 ≤ a ∧ a < sp.toNat + 248) →
    ¬ (0x8001bbe8 ≤ a ∧ a < 0x8001bbea) → ¬ Stdio.errnoFoot a → imgM Mt' a = imgM Mt a
  flagsU : ldv .lhu Mt' 0x8001bbe8 = 0x201a#64
  flagsS : ldv .lh Mt' 0x8001bbe8 = 0x201a#64
  cnt : ldv .lw Mt' (sp + 232#64).toNat = 0#64
  res : ldv .ld Mt' (sp + 240#64).toNat = 0#64

set_option hygiene false in
/-- One piece of the flush run. -/
macro "sprint_step" : tactic => `(tactic| (nx_runB hlive using [h1, h2, h10, h11, h12, hres, hiov,
  hp, hk0, hk0z, ne_eq, not_false_eq_true, hfl, hbase, hwr, hck, BitVec.add_assoc, BitVec.zero_add, BitVec.reduceXOr]
  at 0x8000efd4))

set_option hygiene false in
/-- One piece of the flush run after a write returned. -/
macro "sprint_mid" : tactic => `(tactic| (nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19,
  rk20, rk21, rk22, rk23, rk24, rk25, rk26, rk27, h1, h2, h10, h11, h12, hres, hiov,
  hp, hk0, hk0z, ne_eq, not_false_eq_true, hfl, hbase, hwr, hck, BitVec.add_assoc,
  BitVec.zero_add, BitVec.reduceXOr, List.length_singleton] at 0x8000efd4))

#ix_piece sprintErr_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat) (ra sp p : BitVec 64) (bs : List (BitVec 8))
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0) (hk : bs.length < 2 ^ 30) (hbl0 : 0 < bs.length)
    (hk0z : (BitVec.ofNat 64 bs.length = 0#64) = False)
    (h1 : R 1 = ra) (h2 : R 2 = sp) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bbd8#64)
    (h12 : R 12 = sp + 224#64)
    (hres : ldv .ld Mt (sp + 240#64).toNat = BitVec.ofNat 64 bs.length)
    (hiov : ldv .ld Mt (sp + 224#64).toNat = sp + 352#64)
    (hp : ldv .ld Mt (sp + 352#64).toNat = p) (hk0 : ldv .ld Mt (sp + 360#64).toNat = BitVec.ofNat 64 bs.length)
    (hp1 : 0x80000000 ≤ p.toNat) (hp2 : p.toNat + bs.length ≤ 0x100000000)
    (hp3 : p.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat)
    (hpd : ∀ i, i < bs.length → (p.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ p.toNat + i) ∧
      ¬ stdioFoot (p.toNat + i) ∧ (p.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ p.toNat + i))
    (hpsrc : ∀ i (h : i < bs.length), p.toNat + i ∈ DA ∧ imgM Dt (p.toNat + i) = bs[i])
    (hfl : ldv .lh Mt 0x8001bbe8 = 0x201a#64) (hfd : ldv .lh Mt 0x8001bbea = 2#64) (hbase : ldv .ld Mt 0x8001bbf0 = 0x8001bc4f#64)
    (hwr : ldv .ld Mt 0x8001bc18 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64)
    (hfin : ∀ R' Mt', RetOK R R' 0#64 → SprintPost Mt Mt' sp →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s need) Q (t ++ putcs bs) ra R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000e8cc#64 R Mt by
  sprint_step

#ix_piece sprintErr_02 from sprintErr_01 by
  sprint_step

#ix_piece sprintErr_03 from sprintErr_02 by
  sprint_step

#ix_piece sprintErr_04 from sprintErr_03 by
  sprint_step

#ix_piece sprintErr_05 from sprintErr_04 by
  sprint_step

#ix_piece sprintErr_06 from sprintErr_05 by
  nx_clear_conds
  refine swriteErr_run (sp := sp + 18446744073709551488#64) (buf := p.toNat) (bs := bs)
    (ra := 0x8000df20#64) (s0 := 0x8001bbd8#64) (hlive := hlive) (hs3 := hs3) (hs4 := hs4)
    (hb1 := hp1) (hb2 := hp2) (hb3 := hp3) (hs1 := ?hs1) (hs2 := ?hs2) (hal := ?hal) (h1 := ?h1)
    (hra := by decide) (h8 := ?h8) (hbd := ?hbd) (hsrc := fun i hi => .inr ?_) (h11 := ?h11)
    (h12 := ?h12) (h13 := ?h13) (h2 := ?h2) (hfl := ?hfl) (hfd := ?hfd) (hk := fun R' hR => ?_)
  all_goals try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, h1, h2, h10, h11, h12, BitVec.add_assoc, BitVec.reduceAdd]; done)
  case hs1 | hs2 | hal => nx_fdisch
  case hbd =>
    intro i hi
    obtain ⟨h1', h2', h3'⟩ := hpd i hi
    simp only [stdioFoot, InRange] at h2'
    refine ⟨?_, by omega, h3'⟩
    nx_fdisch
  case h13 =>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [sext_extract32_small (by simp only [BitVec.toNat_ofNat]; omega)]
  case hfl => nx_mem; exact hfl
  case hfd => nx_mem; exact hfd
  · exact ⟨List.mem_append_right _ (hpsrc i hi).1, (hpsrc i hi).2⟩
  nx_ret hR
  sprint_mid

#ix_piece sprintErr_07 from sprintErr_06 by
  sprint_mid

#ix_piece sprintErr_09 from sprintErr_07 by
  sprint_mid

#ix_piece sprintErr_10 from sprintErr_09 by
  sprint_mid

#ix_piece sprintErr_11 from sprintErr_10 by
  nx_clear_conds
  try simp only [swriteErrMt]
  nx_forget (sp.toNat - 256) 256
  nx_compactR
  refine hfin _ _ (retOK_of ?_ ?_) ⟨fun a ha1 ha2 ha3 ha4 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · ret_keep
  · simp only [Stdio.errnoFoot, Stdio.InRange] at ha4
    simp (disch := nx_fdisch) only [imgM_store_miss, imgM_fillR_out]
  all_goals (nx_mem; try decide)

/-! **`sprintErr_run`**: `__sprint_r(reent, stderr, uio)`, one nonempty piece `bs`. -/
#ix_chain sprintErr_run := [sprintErr_01, sprintErr_02, sprintErr_03, sprintErr_04, sprintErr_05,
  sprintErr_06, sprintErr_07, sprintErr_09, sprintErr_10, sprintErr_11]

end VsaIris.Sym
