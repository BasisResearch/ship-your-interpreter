import VsaIris.Vsa.Stderr.VfpErr
import VsaIris.Vsa.Fprintf.SbFile
import VsaIris.Vsa.Fprintf.Loop
import VsaIris.Vsa.Stderr.ErrOK

/-!
# `fprintf(stderr, fmt, p)` up to `_vfprintf_r`'s direct path (lane N3)

`fprintf` (`0x800061c0`) spills its variadic registers (`a2`–`a7` at
`sp + 32 …`, `ap = sp + 32`), loads `_impure_ptr` and calls `_vfprintf_r`;
`vfpEntry_run` and `vfpErr_run` take it to `0x8000a944`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The bytes a `fprintf(stderr, …)` run may change: the call's 4096-byte
stack window, `stderr`'s written fields, `errno`. -/
def FprReg (s : BitVec 64) (a : Nat) : Prop :=
  (s.toNat - 4096 ≤ a ∧ a < s.toNat) ∨ Stdio.errWritten a ∨ Stdio.errnoFoot a

theorem headReg_fprReg {s : BitVec 64} {a : Nat} (hs : 0x80100000 ≤ s.toNat - 4096)
    (hsp : (s + 18446744073709550944#64).toNat = s.toNat - 672)
    (h : Fp.HeadReg (s + 18446744073709550944#64).toNat a) : FprReg s a := by
  unfold Fp.HeadReg at h; rw [hsp] at h
  refine .inl ?_
  rcases h with h | h | h | h | h | h | h | h <;> exact ⟨by omega, by omega⟩

/-- The registers `_vfprintf_r` saves: the caller's, with `ra` its link into
`fprintf`. -/
def fprC (R : Nat → BitVec 64) (x : Nat) : BitVec 64 := if x = 1 then 0x80006204#64 else R x

/-- **`_vfprintf_r` at its loop head on `stderr`** (`sp = s - 672`): the loop
state, the locale, `stderr` set up for writing, the caller's registers
spilled, `ap` and the `%s` argument, `fprintf`'s link, and the memory changed
only inside `FprReg`. -/
structure FprLoop (R : Nat → BitVec 64) (M Mt : Mem) (s p ra : BitVec 64) (C : Nat → BitVec 64) :
    Prop where
  loop : Fp.VfpLoop R M (s + 18446744073709550944#64) 0x8001b538#64 0x8001bbd8#64 0x800195e0#64 0
  loc : Fp.LocMb M
  flagsU : ldv .lhu M 0x8001bbe8 = 0x201a#64
  flagsS : ldv .lh M 0x8001bbe8 = 0x201a#64
  fd : ldv .lh M 0x8001bbea = 2#64
  cursor : ldv .ld M 0x8001bbd8 = 0x8001bc4f#64
  base : ldv .ld M 0x8001bbf0 = 0x8001bc4f#64
  cookie : ldv .ld M 0x8001bc08 = 0x8001bbd8#64
  writer : ldv .ld M 0x8001bc18 = 0x8000efd4#64
  flags2 : ldv .lw M 0x8001bc88 = 0#64
  spills : Fp.VfpSpills M (s + 18446744073709550944#64) C
  ap : ldv .ld M (s + 18446744073709550944#64 + 24#64).toNat = s + 18446744073709551568#64
  arg : ldv .ld M (s + 18446744073709551568#64).toNat = p
  fra : ldv .ld M (s + 18446744073709551560#64).toNat = ra
  frame : Fp.Frame M Mt (FprReg s)

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
    (hk : ∀ R' Mt', FprLoop R' Mt' Mt s p ra (fprC R) →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s 4096) Q t 0x8000a9b0#64 R' Mt') :
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
  refine swp_congr (R' := upd R'' 3 0x8001b510#64) (fun r hr hne => upd_other _ _ (by
    intro e; subst e; revert hr; decide)) ?_
  refine Fp.vfp_head hlive (s := s) (need := 4096) (sp := s + 18446744073709550944#64) (by nx_fdisch)
    (by nx_fdisch) hs3 (by omega) (by nx_fdisch) ?_ (by simp [upd_apply]) fun R3 M3 hHP => ?_
  · rw [upd_other _ _ (by decide), hH.sp_eq, hV.sp_eq]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

set_option hygiene false in
/-- A load at the loop head back through `vfp_head`'s frame and
`vfpErr_run`'s explicit stores. -/
local macro "fl_head" : tactic => `(tactic| (
  refine (hHP.frame.ldv _ fun j hj => by
    simp only [widthOfM] at hj; unfold Fp.HeadReg; rw [hsp]; omega).trans ?_
  simp only [vfpErrMt, swsetupErrMt]
  nx_mem))

set_option hygiene false in
/-- …then back through `vfpEntry_run`'s frame and `fprintf`'s spills. -/
local macro "fl_entry" : tactic => `(tactic| (
  refine (hF.ldv _ fun j hj => by simp only [widthOfM] at hj ⊢; rw [hsp]; omega).trans ?_
  nx_mem))

#ix_piece fprintfHead_03 from fprintfHead_02 by
  have hsp : (s + 18446744073709550944#64).toNat = s.toNat - 672 := by
    rw [toNat_add_neg (by decide) (by omega)]
  have eR2 : R' 2 = s + 18446744073709550944#64 := by
    rw [hV.sp_eq]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eS := hV.sp_eq.symm.trans eR2
  rw [eS] at hV hF
  refine hk _ _ ⟨?loop, ?loc, ?flU, ?flS, ?fd, ?cur, ?base, ?ck, ?wr, ?fl2, ?sp, ?ap, ?arg, ?fra, ?frame⟩
  case loc => exact ⟨by fl_head; fl_entry; exact hL.mbtowc, by fl_head; fl_entry; exact hL.mbMax⟩
  case flU | flS | cur | base | fl2 => fl_head; all_goals first | rfl | decide
  case fd => fl_head; fl_entry; exact hE.fd
  case ck => fl_head; fl_entry; exact hE.cookie
  case wr => fl_head; fl_entry; exact hE.writer
  case loop =>
    have e8 : (upd R'' 3 0x8001b510#64) 8 = 0x8001b538#64 := by
      rw [upd_other _ _ (by decide), hH.s0, hV.s0]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have e20 : (upd R'' 3 0x8001b510#64) 20 = 0x8001bbd8#64 := by
      rw [upd_other _ _ (by decide), hH.s4, hV.s4]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have e22 : (upd R'' 3 0x8001b510#64) 22 = 0x800195e0#64 := by
      rw [upd_other _ _ (by decide), hH.s6, hV.s6]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have := hHP.loop; rwa [e8, e20, e22] at this
  case sp =>
    have kp : ∀ x ∈ [9, 18, 19, 21, 23, 24, 25, 26, 27], (upd R'' 3 0x8001b510#64) x = fprC R x := by
      intro x hx
      rw [upd_other _ _ (by intro e; subst e; revert hx; decide), hH.keep x hx, hV.keep x hx]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, fprC]
    refine ⟨?_, ?_, (hHP.s1).trans (kp 9 (by decide)), (hHP.s2).trans (kp 18 (by decide)),
      (hHP.s3).trans (kp 19 (by decide)), ?_, (hHP.s5).trans (kp 21 (by decide)), ?_,
      (hHP.s7).trans (kp 23 (by decide)), (hHP.s8).trans (kp 24 (by decide)),
      (hHP.s9).trans (kp 25 (by decide)), (hHP.s10).trans (kp 26 (by decide)),
      (hHP.s11).trans (kp 27 (by decide))⟩
    · fl_head; rw [hV.ra]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, fprC]
    · fl_head; rw [hV.s0v]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, fprC]
    · fl_head; rw [hV.s4v]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, fprC]
    · fl_head; rw [hV.s6v]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, fprC]
  case ap =>
    rw [toNat_add_lit (k := 24) (by omega)]
    fl_head; rw [hV.ap]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  case arg =>
    rw [show (s + 18446744073709551568#64).toNat = s.toNat - 48 from by rw [toNat_add_neg (by decide) (by omega)]]
    fl_head; fl_entry
  case fra =>
    rw [show (s + 18446744073709551560#64).toNat = s.toNat - 56 from by rw [toNat_add_neg (by decide) (by omega)]]
    fl_head; fl_entry
  case frame =>
    have F2 := hF.mono (Reg' := FprReg s) fun a ha => by unfold FprReg; rw [hsp] at ha; omega
    have F3 : Fp.Frame (vfpErrMt Mt' (s + 18446744073709550944#64)) Mt' (FprReg s) := by
      simp only [vfpErrMt, swsetupErrMt]
      repeat (refine Fp.Frame.snoc ?_ ?_)
      all_goals first | exact Fp.Frame.refl _ _ | (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [BitVec.add_assoc, BitVec.reduceAdd, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub] at h1 h2; unfold FprReg Stdio.errWritten; omega)
    have F4 : Fp.Frame M3 (vfpErrMt Mt' (s + 18446744073709550944#64)) (FprReg s) :=
      Fp.Frame.mono hHP.frame fun a ha => headReg_fprReg hs4 hsp ha
    refine ((Fp.Frame.trans ?_ F2).trans F3).trans F4
    repeat (refine Fp.Frame.snoc ?_ ?_)
    all_goals first | exact Fp.Frame.refl _ _ | (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub] at h1 h2; unfold FprReg; omega)

/-! **`fprintfHead_run`**: `fprintf(stderr, "%s\n", p)` from its entry to
`_vfprintf_r`'s loop head (`FprLoop`). -/
#ix_chain fprintfHead_run := [fprintfHead_01, fprintfHead_02, fprintfHead_03]

end VsaIris.Sym
