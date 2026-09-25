import VsaIris.Vsa.Stdout.Swrite

/-!
# `__sflush_r` on a write-mode `FILE` (lane N1)

`__sflush_r(reent, f)` with `__SWR` set writes `f`'s buffered bytes
`[_bf._base, _p)` through `f->_write` (`__swrite` on `stdout`'s cookie), resets
`_p` to the base and `_w` to `0` (unbuffered) or `_bf._size`, and returns 0.
Two `FILE`s reach it: `stdout` (one byte, from `__swbuf_r`) and
`__sbprintf`'s stack `FILE` (the formatted string, from `_fflush_r`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The memory after `__sflush_r(reent, f)` returns: its five spills, `_p`
reset to the base, `_w` to `0`, and `__swrite`'s effect (`swriteMt`). -/
@[nx_mt] abbrev sflushMt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  swriteMt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551576#64).toNat, 8, s3)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [((sp + 18446744073709551584#64).toNat, 8, s2)])
    [((sp + 18446744073709551592#64).toNat, 8, s1)]) [(f.toNat, 8, B)]) [((f + 12#64).toNat, 4, 0#64)])
    (sp + 18446744073709551568#64) 0x8000ed0c#64 f

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

#ix_seg sflush_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f F B ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfS : f.toNat = 0x8001bb20)
    (hfa : f.toNat % 8 = 0) (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = F) (hF8 : F &&& 8#64 ≠ 0#64)
    (hF3 : F &&& 3#64 ≠ 0#64)
    (hBl : ldv .ld Mt (f + 24#64).toNat = B)
    (hB0 : B ≠ 0#64) (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hwr : ldv .ld Mt (f + 64#64).toNat = 0x8000efd4#64)
    (hck : ldv .ld Mt (f + 48#64).toNat = 0x8001bb20#64)
    (hsfl : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 112 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < f.toNat ∨ f.toNat + 16 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb30 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i])
    (hti : (BitVec.ofNat 64 bs.length).toInt = bs.length)
    (hsw : ∀ B : BitVec 64, BitVec.signExtend 64 (BitVec.extractLsb 31 0 (B + BitVec.ofNat 64 bs.length) -
      BitVec.extractLsb 31 0 B) = BitVec.ofNat 64 bs.length)
 :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt
  by nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hBl, hP, hwr, hck, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.add_assoc, hsw, hti, BitVec.toInt_zero] at 2147544308

#ix_piece sflush_B from sflush_A by
  nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hBl, hP, hwr, hck, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.add_assoc, hsw, hti, BitVec.toInt_zero] at 2147545044

#ix_piece sflush_C from sflush_B by
  refine swrite_run (sp := sp + 18446744073709551568#64) (buf := B.toNat) (bs := bs)
    (ra := 0x8000ed0c#64) (s0 := f) hlive ?_ ?_ hs3 hs4 ?_ ?_ (by decide) ?_
    (by omega) (by omega) hb3 ?_ (fun i hi => ?_) ?_ ?_ ?_ ?_ ?_ ?_ (fun R' hR => ?_)
  all_goals try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]; done)
  all_goals try nx_addr
  · intro i hi; have := hbd i hi; nx_addr
  · repeat' (first | exact hsrc i hi | refine ByteSrc.store ?_ _ ?_)
    all_goals (have := hbd i hi; nx_addr)
  · nx_mem; exact hsfl
  · nx_mem; exact hsfd

#ix_piece sflush_D from sflush_C by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, BitVec.add_assoc]

#nx_chain sflush_chain := [sflush_A, sflush_B, sflush_C, sflush_D]

/-- **`__sflush_r(reent, stdout)`** with `stdout`'s one-byte buffer `bs` pending: prints it
through `__swrite`, resets `_p`/`_w`, returns 0. -/
theorem sflush_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f F B ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfS : f.toNat = 0x8001bb20)
    (hfa : f.toNat % 8 = 0) (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = F) (hF8 : F &&& 8#64 ≠ 0#64)
    (hF3 : F &&& 3#64 ≠ 0#64)
    (hBl : ldv .ld Mt (f + 24#64).toNat = B)
    (hB0 : B ≠ 0#64) (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hwr : ldv .ld Mt (f + 64#64).toNat = 0x8000efd4#64)
    (hck : ldv .ld Mt (f + 48#64).toNat = 0x8001bb20#64)
    (hsfl : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 112 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < f.toNat ∨ f.toNat + 16 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb30 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i])
    (hk : ∀ R', RetOK R R' 0#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q
      (t ++ putcs bs) ra R' (sflushMt Mt sp f B ra s0 s1 s2 s3)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt := by
  refine sflush_chain hlive hs1 hs2 hs3 hs4 hal hra h1 h8 h9 h18 h19 hfS hfa hn hn2 hB1 hb2 h10 h11 h2
    hF hF8 hF3 hBl hB0 hP hwr hck hsfl hsfd hb3 hbd hsrc (toInt_ofNat_small (by omega))
    (subw_add_ofNat hn2) ?_
  intros
  simp only [nx_mt, BitVec.add_assoc, BitVec.reduceAdd] at hk ⊢
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))


end VsaIris.Sym
