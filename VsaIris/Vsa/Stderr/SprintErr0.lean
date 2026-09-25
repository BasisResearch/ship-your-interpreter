import VsaIris.Vsa.Stderr.SprintErr

/-!
# `__sprint_r` on `stderr`, empty string (lane N3)

`sprintErr_run` for an empty `%s` argument: the first `iov` is empty, so
`__sfvwrite_r` fetches the newline's and writes only it.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

set_option hygiene false in
/-- One piece of the flush run. -/
macro "sprint0_step" : tactic => `(tactic| (nx_runB hlive using [h1, h2, h10, h11, h12, hres, hiov,
  hp, hk0, hq, hk1, ne_eq, not_false_eq_true, hfl, hbase, hwr, hck, BitVec.add_assoc,
  BitVec.zero_add, BitVec.reduceXOr] at 0x8000efd4))

set_option hygiene false in
/-- One piece of the flush run after the write returned. -/
macro "sprint0_mid" : tactic => `(tactic| (nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19,
  rk20, rk21, rk22, rk23, rk24, rk25, rk26, rk27, h1, h2, h10, h11, h12, hres, hiov,
  hp, hk0, hq, hk1, ne_eq, not_false_eq_true, hfl, hbase, hwr, hck, BitVec.add_assoc,
  BitVec.zero_add, BitVec.reduceXOr, List.length_singleton] at 0x8000efd4))

#ix_piece sprintErr0_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat) (ra sp p q : BitVec 64) (c : BitVec 8)
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h2 : R 2 = sp) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bbd8#64)
    (h12 : R 12 = sp + 224#64)
    (hres : ldv .ld Mt (sp + 240#64).toNat = 1#64)
    (hiov : ldv .ld Mt (sp + 224#64).toNat = sp + 352#64)
    (hp : ldv .ld Mt (sp + 352#64).toNat = p) (hk0 : ldv .ld Mt (sp + 360#64).toNat = 0#64)
    (hq : ldv .ld Mt (sp + 368#64).toNat = q) (hk1 : ldv .ld Mt (sp + 376#64).toNat = 1#64)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 1 ≤ 0x100000000)
    (hq3 : q.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ q.toNat)
    (hqd : (q.toNat < sp.toNat - 256 ∨ sp.toNat ≤ q.toNat) ∧ ¬ stdioFoot q.toNat ∧
      (q.toNat < 0x8001ba08 ∨ 0x8001ba0c ≤ q.toNat))
    (hqsrc : q.toNat ∈ DA ∧ imgM Dt q.toNat = c)
    (hfl : ldv .lh Mt 0x8001bbe8 = 0x201a#64) (hfd : ldv .lh Mt 0x8001bbea = 2#64)
    (hbase : ldv .ld Mt 0x8001bbf0 = 0x8001bc4f#64)
    (hwr : ldv .ld Mt 0x8001bc18 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64)
    (hfin : ∀ R' Mt', RetOK R R' 0#64 → SprintPost Mt Mt' sp →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s need) Q (t ++ putcs [c]) ra R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000e8cc#64 R Mt by
  sprint0_step

#ix_piece sprintErr0_02 from sprintErr0_01 by
  sprint0_step

#ix_piece sprintErr0_03 from sprintErr0_02 by
  sprint0_step

#ix_piece sprintErr0_04 from sprintErr0_03 by
  sprint0_step

#ix_piece sprintErr0_05 from sprintErr0_04 by
  sprint0_step

#ix_piece sprintErr0_06 from sprintErr0_05 by
  sprint0_step

#ix_piece sprintErr0_07 from sprintErr0_06 by
  nx_clear_conds
  refine swriteErr_run (sp := sp + 18446744073709551488#64) (buf := q.toNat) (bs := [c])
    (ra := 0x8000df20#64) (s0 := 0x8001bbd8#64) (hlive := hlive) (hs3 := hs3) (hs4 := hs4)
    (hb1 := hq1) (hb2 := hq2) (hb3 := hq3) (hs1 := ?hs1) (hs2 := ?hs2) (hal := ?hal) (h1 := ?h1)
    (hra := by decide) (h8 := ?h8) (hbd := ?hbd) (hsrc := fun i hi => .inr ?_) (h11 := ?h11)
    (h12 := ?h12) (h13 := ?h13) (h2 := ?h2) (hfl := ?hfl) (hfd := ?hfd) (hk := fun R' hR => ?_)
  all_goals try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, h1, h2, h10, h11, h12, BitVec.add_assoc, BitVec.reduceAdd,
    List.length_singleton]; done)
  case hs1 | hs2 | hal => nx_fdisch
  case hbd =>
    intro i hi
    obtain rfl : i = 0 := by simp only [List.length_singleton] at hi; omega
    obtain ⟨h1', h2', h3'⟩ := hqd
    simp only [stdioFoot, InRange] at h2'
    refine ⟨?_, by omega, by omega⟩
    nx_fdisch
  case hfl => nx_mem; exact hfl
  case hfd => nx_mem; exact hfd
  · obtain rfl : i = 0 := by simp only [List.length_singleton] at hi; omega
    exact ⟨List.mem_append_right _ hqsrc.1, hqsrc.2⟩
  nx_ret hR
  sprint0_mid

#ix_piece sprintErr0_08 from sprintErr0_07 by
  sprint0_mid

#ix_piece sprintErr0_09 from sprintErr0_08 by
  sprint0_mid

#ix_piece sprintErr0_10 from sprintErr0_09 by
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

/-! **`sprintErr0_run`**: `__sprint_r(reent, stderr, uio)`, pieces `[]` and `[c]`. -/
#ix_chain sprintErr0_run := [sprintErr0_01, sprintErr0_02, sprintErr0_03, sprintErr0_04,
  sprintErr0_05, sprintErr0_06, sprintErr0_07, sprintErr0_08, sprintErr0_09, sprintErr0_10]

end VsaIris.Sym
