import VsaIris.Vsa.Stderr.SwsetupErr
import VsaIris.Vsa.Stderr.Mem
import VsaIris.Vsa.SymCompactTac
import VsaIris.Vsa.Stderr.ErrOK

/-!
# `fwrite(ptr, 1, n, stderr)`, the first write, as a printing run (lane N3)

`fwrite` → `_fwrite_r` (`__muldi3` for `1 * n`, orientation `__SORD`) →
`__sfvwrite_r`, whose `cantwrite` calls `__swsetup_r` (`swsetupErr_run`: sets
`__SWR`, `__smakebuf_r` installs `_nbuf` for the unbuffered stream) and then writes the
single `iov` in one chunk (`n < 2^30`) through `fp->_write = __swrite`
(`swriteErr_run`), then `__udivdi3` for the item count.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The memory after `fwrite(ptr, 1, n, stderr)`: the stack below `s`,
`errno` and `stderr`'s written fields changed; those fields as a written
unbuffered stream (`ErrWrittenFile`). -/
structure FwritePost (Mt Mt' : Mem) (s : BitVec 64) : Prop where
  frame : ∀ a, ¬ (s.toNat - 768 ≤ a ∧ a < s.toNat) → ¬ Stdio.errWritten a → ¬ Stdio.errnoFoot a →
    imgM Mt' a = imgM Mt a
  cursor : imgLE (imgM Mt') 0x8001bbd8 8 = 0x8001bc4f
  flags : imgLE (imgM Mt') 0x8001bbe8 2 = 0x201a
  base : imgLE (imgM Mt') 0x8001bbf0 8 = 0x8001bc4f
  lockMode : imgLE (imgM Mt') 0x8001bc88 4 = 0

theorem imgLE_fillR_out (M : Mem) {lo n a k : Nat} (g : Nat → BitVec 8)
    (h : a + k ≤ lo ∨ lo + n ≤ a) : imgLE (imgM (fillR M lo n g)) a k = imgLE (imgM M) a k :=
  imgLE_congr fun i hi => imgM_fillR_out M g (by omega)

set_option hygiene false in
/-- One piece of the run up to `__swrite`. -/
macro "fwrite_step" : tactic => `(tactic| (nx_runB hlive using [h1, h2, h10, h11, h12, h13, hDt,
  hC.sinit, hE.flagsU, hE.flagsS, hE.fd, hE.base, hE.cookie, hE.writer, hE.lock, hE.lockMode,
  BitVec.add_assoc, BitVec.zero_add, hn0, ldv_ld_and_640, BitVec.reduceXOr] at 0x8000f230))

set_option hygiene false in
/-- One piece of the run after `__swsetup_r` returns, up to `__swrite`. -/
macro "fwrite_mid" : tactic => `(tactic| (nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19,
  rk20, rk21, rk22, rk23, rk24, rk25, rk26, rk27, h1, h2, h10, h11, h12, h13, hDt,
  hC.sinit, hE.fd, hE.cookie, hE.writer, hE.lock, hE.lockMode,
  BitVec.add_assoc, BitVec.zero_add, hn0, BitVec.reduceXOr] at 0x8000efd4))

#ix_piece fwriteErr_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s ra ptr n : BitVec 64)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - 768) (hal : s.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0) (hn : n.toNat < 2 ^ 30) (hn0 : (n = 0#64) = False)
    (h1 : R 1 = ra) (h2 : R 2 = s) (h10 : R 10 = ptr) (h11 : R 11 = 1#64) (h12 : R 12 = n)
    (h13 : R 13 = 0x8001bbd8#64) {fl : BitVec 64} (hC : ConsoleMt fl Mt) (hE : ErrMt Mt)
    (hDt : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (bs : List (BitVec 8)) (hbn : n = BitVec.ofNat 64 bs.length) (hbl0 : 0 < bs.length)
    (hbl : bs.length < 2 ^ 30)
    (hb1 : 0x80000000 ≤ ptr.toNat) (hb2 : ptr.toNat + bs.length ≤ 0x100000000)
    (hb3 : ptr.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ ptr.toNat)
    (hbd : ∀ i, i < bs.length → (ptr.toNat + i < s.toNat - 768 ∨ s.toNat ≤ ptr.toNat + i) ∧
      ¬ stdioFoot (ptr.toNat + i) ∧ (ptr.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ ptr.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s 768) Mt Dt (accAddrs 0x8001b970 8 ++ DA) (ptr.toNat + i) bs[i])
    (hk : ∀ R' Mt', RetOK R R' n → FwritePost Mt Mt' s →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s 768) Q (t ++ putcs bs) ra R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s 768) Q t 0x80005260#64 R Mt by
  nx_runB hlive using [h1, h2, h10, h11, h12, h13, hDt,
  hC.sinit, hE.flagsU, hE.flagsS, hE.fd, hE.base, hE.cookie, hE.writer, hE.lock, hE.lockMode,
  BitVec.add_assoc, BitVec.zero_add, hn0, ldv_ld_and_640, BitVec.reduceXOr] at 0x8000f230

#ix_piece fwriteErr_02 from fwriteErr_01 by
  fwrite_step

#ix_piece fwriteErr_03 from fwriteErr_02 by
  fwrite_step

#ix_piece fwriteErr_04 from fwriteErr_03 by
  fwrite_step

#ix_piece fwriteErr_05 from fwriteErr_04 by
  fwrite_step

#ix_piece fwriteErr_06 from fwriteErr_05 by
  fwrite_step

#ix_piece fwriteErr_07 from fwriteErr_06 by
  refine swsetupErr_run (hlive := hlive) (t := t) (s := s) (need := 768) (hs3 := hs3) (hs4 := hs4)
    (hDt := hDt) (ra := 0x8000df74#64) (sp := s + 18446744073709551408#64) (h1 := ?h1) (h2 := ?h2)
    (hs1 := ?hs1) (hs2 := ?hs2) (hal := ?hal) (hra := ?hra)
    (h10 := ?h10) (h11 := ?h11) (hsinit := ?hsinit) (hflU := ?hflU) (hflS := ?hflS) (hfd := ?hfd)
    (hbase := ?hbase) (hk := fun R' hR => ?_)
  all_goals (try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h2, BitVec.add_assoc,
    BitVec.reduceAdd]; done))
  case hs1 | hs2 | hal => nx_fdisch
  case hra => decide
  case hsinit => nx_mem; exact hC.sinit
  case hflU | hflS => nx_mem; decide
  case hfd => nx_mem; exact hE.fd
  case hbase => nx_mem; exact hE.base

#ix_piece fwriteErr_08 from fwriteErr_07 by
  nx_ret hR
  fwrite_mid

#ix_piece fwriteErr_09 from fwriteErr_08 by
  fwrite_mid

#ix_piece fwriteErr_10 from fwriteErr_09 by
  fwrite_mid

#ix_piece fwriteErr_11 from fwriteErr_10 by
  fwrite_mid

#ix_piece fwriteErr_12 from fwriteErr_11 by
  fwrite_mid

#ix_piece fwriteErr_13 from fwriteErr_12 by
  fwrite_mid

#ix_piece fwriteErr_14 from fwriteErr_13 by
  fwrite_mid

#ix_piece fwriteErr_15 from fwriteErr_14 by
  nx_clear_conds
  refine swriteErr_run (sp := s + 18446744073709551408#64) (buf := ptr.toNat) (bs := bs)
    (ra := 0x8000df20#64) (s0 := 0x8001bbd8#64) hlive ?_ ?_ hs3 hs4 ?_ ?_ (by decide) ?_
    hb1 hb2 hb3 ?_ (fun i hi => ?_) ?_ ?_ ?_ ?_ ?_ ?_ (fun R' hR => ?_)
  all_goals try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, h1, h2, h10, h11, h12, h13, hbn, rk1, rk2, rk8, rk9, rk18, rk19, rk20, rk21,
    rk22, rk23, rk24, rk25, rk26, rk27]; done)
  case refine_1 => nx_addr
  case refine_2 => nx_addr
  case refine_3 => nx_addr
  case refine_6 =>
    intro i hi
    obtain ⟨h1', h2', h3'⟩ := hbd i hi
    simp only [stdioFoot, InRange] at h2'
    nx_addr
  case refine_7 =>
    repeat (refine ByteSrc.store ?_ _ ?_)
    exact hsrc i hi
    all_goals (obtain ⟨h1', h2', h3'⟩ := hbd i hi; simp only [stdioFoot, InRange] at h2'; nx_addr)
  case refine_10 =>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [sext_extract32_small (by omega), hbn]
  case refine_12 => nx_mem; decide
  case refine_13 => nx_mem; exact hE.fd

set_option hygiene false in
/-- A second callee's return (`__swrite` after `__swsetup_r`): the first
return's kept-register facts are saved as `sk<r>`, the new ones (`rk<r>`)
rewritten through them. -/
macro "nx_ret2 " h:ident : tactic => `(tactic| (
  have sk1 := rk1; have sk2 := rk2; have sk8 := rk8; have sk9 := rk9; have sk10 := rk10; have sk18 := rk18; have sk19 := rk19; have sk20 := rk20; have sk21 := rk21; have sk22 := rk22; have sk23 := rk23; have sk24 := rk24; have sk25 := rk25; have sk26 := rk26; have sk27 := rk27
  clear rk1 rk2 rk8 rk9 rk10 rk18 rk19 rk20 rk21 rk22 rk23 rk24 rk25 rk26 rk27
  nx_ret $h
  (try simp only [sk1, sk2, sk8, sk9, sk10, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27] at rk1 rk2 rk8 rk9 rk18 rk19 rk20 rk21 rk22 rk23 rk24 rk25 rk26 rk27)))

set_option hygiene false in
/-- One piece of the run after `__swrite` returns. -/
macro "fwrite_tail" : tactic => `(tactic| nx_runB hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19,
  rk20, rk21, rk22, rk23, rk24, rk25, rk26, rk27, h1, h2, hbn, hDt, hC.sinit, hE.lockMode,
  BitVec.add_assoc, BitVec.zero_add, BitVec.reduceXOr, BitVec.reduceAnd, BitVec.reduceOr])

#ix_piece fwriteErr_16 from fwriteErr_15 by
  nx_ret2 hR
  fwrite_tail

#ix_piece fwriteErr_17 from fwriteErr_16 by
  fwrite_tail

#ix_piece fwriteErr_18 from fwriteErr_17 by
  fwrite_tail

#ix_piece fwriteErr_19 from fwriteErr_18 by
  fwrite_tail

#ix_piece fwriteErr_20 from fwriteErr_19 by
  fwrite_tail

#ix_piece fwriteErr_21 from fwriteErr_20 by
  fwrite_tail

#ix_piece fwriteErr_22 from fwriteErr_21 by
  fwrite_tail

#ix_piece fwriteErr_23 from fwriteErr_22 by
  fwrite_tail

#ix_piece fwriteErr_24 from fwriteErr_23 by
  fwrite_tail

#ix_piece fwriteErr_25 from fwriteErr_24 by
  fwrite_tail

#ix_piece fwriteErr_26 from fwriteErr_25 by
  fwrite_tail

#ix_piece fwriteErr_27 from fwriteErr_26 by
  fwrite_tail

#ix_piece fwriteErr_28 from fwriteErr_27 by
  fwrite_tail

#ix_piece fwriteErr_29 from fwriteErr_28 by
  fwrite_tail

#ix_piece fwriteErr_30 from fwriteErr_29 by
  fwrite_tail

#ix_piece fwriteErr_31 from fwriteErr_30 by
  fwrite_tail

#ix_piece fwriteErr_32 from fwriteErr_31 by
  try simp only [swriteErrMt, swsetupErrMt]
  nx_forget (s.toNat - 768) 768
  nx_compactR

#ix_piece fwriteErr_33 from fwriteErr_32 by
  nx_clear_conds
  refine hk _ _ (retOK_of ?_ ?_) ⟨fun a ha1 ha2 ha3 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hbn]
  · ret_keep
  · simp only [Stdio.errWritten, Stdio.errnoFoot, Stdio.InRange] at ha2 ha3
    simp (disch := nx_fdisch) only [imgM_store_miss, imgM_fillR_out]
  all_goals (simp (disch := nx_fdisch) only [imgLE_store_miss, imgLE_fillR_out, imgLE_imgM_store,
    imgLE_store2_hit, imgLE_store4_hit]; try decide)



-- **`fwrite(ptr, 1, n, stderr)`**, the first write to `stderr` (`n = |bs|`,
-- `0 < n < 2^30`, the bytes owned or in the data view): prints `bs`, returns
-- `n`, leaves `stderr` a written unbuffered stream (`FwritePost`).
#ix_chain fwriteErr_run := [fwriteErr_01, fwriteErr_02, fwriteErr_03, fwriteErr_04, fwriteErr_05, fwriteErr_06, fwriteErr_07, fwriteErr_08, fwriteErr_09, fwriteErr_10, fwriteErr_11, fwriteErr_12, fwriteErr_13, fwriteErr_14, fwriteErr_15, fwriteErr_16, fwriteErr_17, fwriteErr_18, fwriteErr_19, fwriteErr_20, fwriteErr_21, fwriteErr_22, fwriteErr_23, fwriteErr_24, fwriteErr_25, fwriteErr_26, fwriteErr_27, fwriteErr_28, fwriteErr_29, fwriteErr_30, fwriteErr_31, fwriteErr_32, fwriteErr_33]

end VsaIris.Sym
