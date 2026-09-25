import VsaIris.Vsa.Fprintf.Move

/-!
# Flushing `__sbprintf`'s stack `FILE` (lane N5)

`__sbprintf` formats into a `FILE` on its own stack frame: flags `0x2008`
(`__SORD | __SWR`, fully buffered), a 1024-byte buffer, and `stdout`'s
`_cookie`/`_write` (`__swrite` on `stdout`). `__sfvwrite_r` flushes it when
the buffer fills, and `__sbprintf` flushes it at the end: `_fflush_r` takes
the (no-op) lock, `__sflush_r` writes `[_bf._base, _p)` through `__swrite`
(N1's `swrite_run`, the console loop), and resets `_p` to the base and `_w`
to `_bf._size` (the fully-buffered branch, `flags & 3 = 0`). N1's
`sflush_run` is the unbuffered `stdout` branch (`_w := 0`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

#ix_seg sflushF_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfa : f.toNat % 8 = 0) (hf1 : sp.toNat ≤ f.toNat) (hf2 : f.toNat + 184 ≤ s.toNat)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = 0x2008#64)
    (hBl : ldv .ld Mt (f + 24#64).toNat = B)
    (hB0 : B ≠ 0#64) (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hsz : ldv .lw Mt (f + 32#64).toNat = 1024#64)
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
      BitVec.extractLsb 31 0 B) = BitVec.ofNat 64 bs.length) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt
  by nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hBl, hP, hwr, hck, hsz, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc, hsw, hti, BitVec.toInt_zero] at 2147544308

#ix_piece sflushF_B from sflushF_A by
  nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hBl, hP, hwr, hck, hsz, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc, hsw, hti, BitVec.toInt_zero] at 2147545044

#ix_piece sflushF_C from sflushF_B by
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

#ix_piece sflushF_D from sflushF_C by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, BitVec.add_assoc]

#nx_chain sflushF_chain := [sflushF_A, sflushF_B, sflushF_C, sflushF_D]

/-- The memory after `__sflush_r(reent, f)` on the stack `FILE` returns: its
five spills, `_p` reset to the base, `_w` to `_bf._size`, and `__swrite`'s
effect (`swriteMt`). -/
abbrev sflushFMt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  swriteMt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551576#64).toNat, 8, s3)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [((sp + 18446744073709551584#64).toNat, 8, s2)])
    [((sp + 18446744073709551592#64).toNat, 8, s1)]) [(f.toNat, 8, B)]) [((f + 12#64).toNat, 4, 1024#64)])
    (sp + 18446744073709551568#64) 0x8000ed0c#64 f

/-- **`__sflush_r(reent, f)`** on `__sbprintf`'s stack `FILE` with `bs` pending:
prints them through `__swrite` on `stdout`, resets `_p`/`_w`, returns 0. -/
theorem sflushF_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfa : f.toNat % 8 = 0) (hf1 : sp.toNat ≤ f.toNat) (hf2 : f.toNat + 184 ≤ s.toNat)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = 0x2008#64)
    (hBl : ldv .ld Mt (f + 24#64).toNat = B)
    (hB0 : B ≠ 0#64) (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hsz : ldv .lw Mt (f + 32#64).toNat = 1024#64)
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
      (t ++ putcs bs) ra R' (sflushFMt Mt sp f B ra s0 s1 s2 s3)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt := by
  refine sflushF_chain hlive hs1 hs2 hs3 hs4 hal hra h1 h8 h9 h18 h19 hfa hf1 hf2 hn hn2 hB1 hb2 h10 h11 h2
    hF hBl hB0 hP hsz hwr hck hsfl hsfd hb3 hbd hsrc (toInt_ofNat_small (by omega))
    (subw_add_ofNat hn2) ?_
  intros
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))

/-- The memory after `__sflush_r(reent, f)` with nothing pending: the spills
and the reset `_p`/`_w`. -/
abbrev sflushF0Mt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551576#64).toNat, 8, s3)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [((sp + 18446744073709551584#64).toNat, 8, s2)])
    [((sp + 18446744073709551592#64).toNat, 8, s1)]) [(f.toNat, 8, B)]) [((f + 12#64).toNat, 4, 1024#64)]

/-- **`__sflush_r(reent, f)`** on the stack `FILE` with nothing pending:
prints nothing, returns 0. -/
theorem sflushF_run0 {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra s0 s1 s2 s3 : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfa : f.toNat % 8 = 0) (hf1 : sp.toNat ≤ f.toNat) (hf2 : f.toNat + 184 ≤ s.toNat)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = 0x2008#64)
    (hBl : ldv .ld Mt (f + 24#64).toNat = B)
    (hB0 : B ≠ 0#64) (hP : ldv .ld Mt f.toNat = B)
    (hsz : ldv .lw Mt (f + 32#64).toNat = 1024#64)
    (hk : ∀ R', RetOK R R' 0#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q
      t ra R' (sflushF0Mt Mt sp f B ra s0 s1 s2 s3)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt := by
  nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hBl, hP, hsz, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc, BitVec.sub_self, BitVec.toInt_zero]
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))

/-! ## `_fflush_r` on the stack `FILE` -/

/-- The common context of an `_fflush_r(reent, f)` call on `__sbprintf`'s
stack `FILE`: the stack window, the registers, the `FILE`'s fields, and the
boundary `stdout` fields `__swrite` reads. -/
structure FfCtx (s sp f B ra : BitVec 64) (need : Nat) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  hs1 : s.toNat - need + 256 ≤ sp.toNat
  hs2 : sp.toNat ≤ s.toNat
  hs3 : s.toNat ≤ 0x88000000
  hs4 : 0x80100000 ≤ s.toNat - need
  hal : sp.toNat % 16 = 0
  hra : ra.toNat % 4 = 0
  hfa : f.toNat % 8 = 0
  hf1 : sp.toNat ≤ f.toNat
  hf2 : f.toNat + 184 ≤ s.toNat
  h1 : R 1 = ra
  h10 : R 10 = 0x8001b538#64
  h11 : R 11 = f
  h2 : R 2 = sp
  hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64
  hF : ldv .lh Mt (f + 16#64).toNat = 0x2008#64
  hFu : ldv .lhu Mt (f + 16#64).toNat = 0x2008#64
  hlm : ldv .lw Mt (f + 176#64).toNat = 0#64
  hBl : ldv .ld Mt (f + 24#64).toNat = B
  hB0 : B ≠ 0#64
  hsz : ldv .lw Mt (f + 32#64).toNat = 1024#64
  hwr : ldv .ld Mt (f + 64#64).toNat = 0x8000efd4#64
  hck : ldv .ld Mt (f + 48#64).toNat = 0x8001bb20#64
  hsfl : ldv .lh Mt 0x8001bb30 = 0x200a#64
  hsfd : ldv .lh Mt 0x8001bb32 = 1#64

#ix_seg fflushF_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (C : FfCtx s sp f B ra need R Mt)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < f.toNat ∨ f.toNat + 16 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb30 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i]) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt
  by
    have := C.hs1; have := C.hs2; have := C.hs3; have := C.hs4; have := C.hal; have := C.hfa
    have := C.hf1; have := C.hf2
    nx_run hlive using [C.h1, C.h10, C.h11, C.h2, C.hsinit, C.hF, C.hlm, BitVec.reduceAnd, BitVec.reduceOr,
      BitVec.add_assoc] at 2147543920

#ix_piece fflushF_B from fflushF_A by
  refine sflushF_run (sp := sp + 18446744073709551584#64) (f := f) (B := B)
    (ra := 0x8000ee10#64) (s0 := R 8) (s1 := R 9) (s2 := R 18) (s3 := R 19) (bs := bs) hlive
    ?_ ?_ C.hs3 C.hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ C.hfa ?_ ?_ hn hn2 hB1 hb2 ?_ ?_ ?_ ?_ ?_ C.hB0
    ?_ ?_ ?_ ?_ ?_ ?_ hb3 ?_ ?_ (fun R' hR => ?_)
  all_goals try (nx_norm; done)
  all_goals try (have := C.hs1; have := C.hs2; have := C.hf1; have := C.hf2; have := C.hal; nx_addr)
  all_goals try ((try nx_norm); nx_mem; simp only [C.hF, C.hBl, hP, C.hsz, C.hwr, C.hck, C.hsfl, C.hsfd]; done)
  · intro i hi; have := hbd i hi; have := C.hs1; have := C.hs2; have := C.hf1; nx_addr
  · intro i hi
    repeat' (first | exact hsrc i hi | refine ByteSrc.store ?_ _ ?_)
    all_goals (have := hbd i hi; have := C.hs1; have := C.hs2; have := C.hf1; have := C.hf2; nx_addr)

#ix_piece fflushF_C from fflushF_B by
  nx_ret hR
  have := C.hra; have := C.h1
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, C.hlm, C.hF, C.hFu, C.h1, BitVec.add_assoc, BitVec.reduceAnd]

#nx_chain fflushF_chain := [fflushF_A, fflushF_B, fflushF_C]

/-- The memory after `_fflush_r(reent, f)` on the stack `FILE` returns. -/
abbrev fflushFMt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  writeLog (sflushFMt
    (writeLog (writeLog (writeLog (writeLog Mt [((sp + 18446744073709551608#64).toNat, 8, ra)])
      [((sp + 18446744073709551592#64).toNat, 8, 2147595576#64)])
      [((sp + 18446744073709551584#64).toNat, 8, f)])
      [((sp + 18446744073709551584#64).toNat, 8, f)])
    (sp + 18446744073709551584#64) f B (2147544592#64) s0 s1 s2 s3)
    [((sp + 18446744073709551584#64).toNat, 8, 0#64)]

/-- **`_fflush_r(reent, f)`** on `__sbprintf`'s stack `FILE` with `bs`
pending: prints them, returns 0. -/
theorem fflushF_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (C : FfCtx s sp f B ra need R Mt)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (hP : ldv .ld Mt f.toNat = B + BitVec.ofNat 64 bs.length)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < f.toNat ∨ f.toNat + 16 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb30 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i])
    (hk : ∀ R', RetOK R R' 0#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q
      (t ++ putcs bs) ra R' (fflushFMt Mt sp f B ra (R 8) (R 9) (R 18) (R 19))) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt := by
  apply fflushF_chain hlive C hn hn2 hB1 hb2 hP hb3 hbd hsrc
  intros
  have := C.h2
  refine hk _ (retOK_of ?_ ?_)
  · simp_all [upd_apply]
  · ret_keep


#ix_seg fflushF0_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra : BitVec 64} {need : Nat}
    (C : FfCtx s sp f B ra need R Mt) (hP : ldv .ld Mt f.toNat = B) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt
  by
    have := C.hs1; have := C.hs2; have := C.hs3; have := C.hs4; have := C.hal; have := C.hfa
    have := C.hf1; have := C.hf2
    nx_run hlive using [C.h1, C.h10, C.h11, C.h2, C.hsinit, C.hF, C.hlm, BitVec.reduceAnd, BitVec.reduceOr,
      BitVec.add_assoc] at 2147543920

#ix_piece fflushF0_B from fflushF0_A by
  refine sflushF_run0 (sp := sp + 18446744073709551584#64) (f := f) (B := B)
    (ra := 0x8000ee10#64) (s0 := R 8) (s1 := R 9) (s2 := R 18) (s3 := R 19) hlive
    ?_ ?_ C.hs3 C.hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ C.hfa ?_ ?_ ?_ ?_ ?_ ?_ ?_ C.hB0 ?_ ?_ (fun R' hR => ?_)
  all_goals try (nx_norm; done)
  all_goals try (have := C.hs1; have := C.hs2; have := C.hf1; have := C.hf2; have := C.hal; nx_addr)
  all_goals try ((try nx_norm); nx_mem; simp only [C.hF, C.hBl, hP, C.hsz]; done)

#ix_piece fflushF0_C from fflushF0_B by
  nx_ret hR
  have := C.hra; have := C.h1
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, C.hlm, C.hF, C.hFu, C.h1, BitVec.add_assoc, BitVec.reduceAnd]

#nx_chain fflushF0_chain := [fflushF0_A, fflushF0_B, fflushF0_C]

/-- The memory after `_fflush_r(reent, f)` on the stack `FILE` with nothing
pending. -/
abbrev fflushF0Mt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  writeLog (sflushF0Mt
    (writeLog (writeLog (writeLog (writeLog Mt [((sp + 18446744073709551608#64).toNat, 8, ra)])
      [((sp + 18446744073709551592#64).toNat, 8, 2147595576#64)])
      [((sp + 18446744073709551584#64).toNat, 8, f)])
      [((sp + 18446744073709551584#64).toNat, 8, f)])
    (sp + 18446744073709551584#64) f B (2147544592#64) s0 s1 s2 s3)
    [((sp + 18446744073709551584#64).toNat, 8, 0#64)]

/-- **`_fflush_r(reent, f)`** on the stack `FILE` with nothing pending: prints
nothing, returns 0. -/
theorem fflushF_run0 {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f B ra : BitVec 64} {need : Nat}
    (C : FfCtx s sp f B ra need R Mt) (hP : ldv .ld Mt f.toNat = B)
    (hk : ∀ R', RetOK R R' 0#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q
      t ra R' (fflushF0Mt Mt sp f B ra (R 8) (R 9) (R 18) (R 19))) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt := by
  apply fflushF0_chain hlive C hP
  intros
  have := C.h2
  refine hk _ (retOK_of ?_ ?_)
  · simp_all [upd_apply]
  · ret_keep

end VsaIris.Sym.Fp
