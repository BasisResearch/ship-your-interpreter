import VsaIris.Vsa.Stdout.Sflush

/-!
# `_fflush_r` on `stdout` (lane N1)

`_fflush_r(reent, stdout)`: `stdout` is not a string `FILE` (`__SSTR` clear)
and its lock mode is 0, so it takes the (no-op) recursive lock, runs
`__sflush_r` (`sflush_run`), and releases the lock. The lock calls are
`ret` stubs, which `nx_run` follows through the step table.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

#ix_seg fflush_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp B ra : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = sp)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64)
    (hF : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hlm : ldv .lw Mt 0x8001bbd0 = 0#64)
    (hlock : ldv .ld Mt 0x8001bbc0 = 0#64)
    (hBl : ldv .ld Mt 0x8001bb38 = B) (hB0 : B ≠ 0#64)
    (hP : ldv .ld Mt 0x8001bb20 = B + BitVec.ofNat 64 bs.length)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb20 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i]) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt
  by nx_run hlive using [h1, h10, h11, h2, hsinit, hF, hlm, hlock, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.add_assoc] at 2147543920

#ix_piece fflush_B from fflush_A by
  refine sflush_run (sp := sp + 18446744073709551584#64) (f := 0x8001bb20#64) (F := 0x200a#64) (B := B)
    (ra := 0x8000ee10#64) (s0 := R 8) (s1 := R 9) (s2 := R 18) (s3 := R 19) (bs := bs) hlive
    ?_ ?_ hs3 hs4 ?_ (by decide) ?_ ?_ ?_ ?_ ?_ (by decide) (by decide) hn hn2 hB1 hb2 ?_ ?_ ?_ ?_
    (by decide) (by decide) ?_ hB0 ?_ ?_ ?_ ?_ ?_ hb3 ?_ ?_ (fun R' hR => ?_)
  all_goals try (nx_norm; done)
  all_goals try nx_addr
  all_goals try ((try nx_norm); nx_mem; simp only [hsinit, hF, hlm, hlock, hBl, hP, hwr, hck, hsfd]; done)
  · intro i hi; have := hbd i hi; nx_addr
  · intro i hi
    repeat' (first | exact hsrc i hi | refine ByteSrc.store ?_ _ ?_)
    all_goals (have := hbd i hi; nx_addr)

#ix_piece fflush_C from fflush_B by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, hlm, hlock, hF, BitVec.add_assoc, BitVec.reduceAnd]

#nx_chain fflush_chain := [fflush_A, fflush_B, fflush_C]

/-- The memory after `_fflush_r(reent, stdout)` returns. -/
abbrev fflushMt (Mt : Mem) (sp B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  writeLog (sflushMt
    (writeLog (writeLog (writeLog (writeLog Mt [((sp + 18446744073709551608#64).toNat, 8, ra)])
      [((sp + 18446744073709551592#64).toNat, 8, 2147595576#64)])
      [((sp + 18446744073709551584#64).toNat, 8, 2147597088#64)])
      [((sp + 18446744073709551584#64).toNat, 8, 2147597088#64)])
    (sp + 18446744073709551584#64) (2147597088#64) B (2147544592#64) s0 s1 s2 s3)
    [((sp + 18446744073709551584#64).toNat, 8, 0#64)]

/-- **`_fflush_r(reent, stdout)`** with `bs` pending in `stdout`'s buffer:
prints it, returns 0. -/
theorem fflush_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp B ra : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bb20#64) (h2 : R 2 = sp)
    (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64)
    (hF : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hlm : ldv .lw Mt 0x8001bbd0 = 0#64)
    (hlock : ldv .ld Mt 0x8001bbc0 = 0#64)
    (hBl : ldv .ld Mt 0x8001bb38 = B) (hB0 : B ≠ 0#64)
    (hP : ldv .ld Mt 0x8001bb20 = B + BitVec.ofNat 64 bs.length)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hsfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb3 : B.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ B.toNat)
    (hbd : ∀ i, i < bs.length → (B.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001bb20 ∨ 0x8001bb32 ≤ B.toNat + i) ∧
      (B.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ B.toNat + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (B.toNat + i) bs[i])
    (hk : ∀ R', RetOK R R' 0#64 → SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q
      (t ++ putcs bs) ra R' (fflushMt Mt sp B ra (R 8) (R 9) (R 18) (R 19))) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000edcc#64 R Mt := by
  refine fflush_chain hlive hs1 hs2 hs3 hs4 hal hra h1 h10 h11 h2 hn hn2 hB1 hb2 hsinit hF hlm hlock
    hBl hB0 hP hwr hck hsfd hb3 hbd hsrc ?_
  intros
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))

end VsaIris.Sym
