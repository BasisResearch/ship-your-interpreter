import VsaIris.Vsa.Stdout.Swbuf

/-!
# `__sfvwrite_r` on `stdout` (lane N1)

`__sfvwrite_r(reent, stdout, uio)` with one iov of `n > 0` bytes of
persistent data (a C string): `stdout` is in write mode, has its buffer and is
unbuffered, so it hands the whole iov (`n ≤ 0x7ffffc00`) to the writer
(`__swrite`, `swrite_run`) in one call, which prints it and returns `n`; the
residual count reaches `0` and it returns `0`. With `n = 0` it returns `0` at
once.
-/

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The writer's chunk cap `0x7ffffc00` (`lui`/`xori`). -/
theorem sfv_cap : (18446744071562067968#64 ^^^ 18446744073709550592#64) = 2147482624#64 := by decide

#ix_seg sfv_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra u v : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hn0 : bs.length ≠ 0) (hn1 : bs.length ≤ 0x7ffffc00)
    (hu1 : sp.toNat ≤ u.toNat) (hu2 : u.toNat + 24 ≤ s.toNat) (hu8 : u.toNat % 8 = 0)
    (hv1 : sp.toNat ≤ v.toNat) (hv2 : v.toNat + 16 ≤ s.toNat) (hv8 : v.toNat % 8 = 0)
    (h1 : R 1 = ra) (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = u) (h2 : R 2 = sp)
    (hres : ldv .ld Mt (u + 16#64).toNat = BitVec.ofNat 64 bs.length) (hiov : ldv .ld Mt u.toNat = v)
    (hbuf : ldv .ld Mt v.toNat = BitVec.ofNat 64 buf)
    (hlen : ldv .ld Mt (v + 8#64).toNat = BitVec.ofNat 64 bs.length)
    (hF : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hB : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbo : ∀ i, i < bs.length → ¬ outS s need (buf + i))
    (hsrc : ∀ i (h : i < bs.length), buf + i ∈ DA ∧ imgM Dt (buf + i) = bs[i]) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000de8c#64 R Mt
  by nx_run hlive using [h1, h11, h12, h2, hres, hiov, hbuf, hlen, hF, hB, hwr, hck, sfv_cap, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc] at 2147545044

/-- `sext.w` of a small count. -/
theorem sextw_ofNat {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  have hm : (BitVec.extractLsb 31 0 (BitVec.ofNat 64 n)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]; omega

#ix_piece sfv_B from sfv_A by
  refine swrite_run (sp := sp + 18446744073709551520#64) (ra := 0x8000df20#64) (s0 := 0x8001bb20#64) (buf := buf) (bs := bs)
    hlive ?_ ?_ hs3 hs4 ?_ ?_ (by decide) ?_ hb1 hb2 hb3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun R' hR => ?_)
  all_goals try (nx_norm; done)
  all_goals try nx_addr
  all_goals try ((try nx_norm); nx_mem; simp only [hF, hfd]; done)
  · intro i hi
    have := hbo i hi
    simp only [outS, stdioFoot, InRange, impureW] at this
    nx_addr
  · exact fun i h => .inr (hsrc i h)
  · simp only [upd_apply]; simp
    exact sextw_ofNat (by omega)

#ix_piece sfv_C from sfv_B by
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, rk20, rk21, rk22, h1, hres, BitVec.add_assoc]

#nx_chain sfv_chain := [sfv_A, sfv_B, sfv_C]

#ix_seg sfv_Z {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra u : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hu1 : sp.toNat ≤ u.toNat) (hu2 : u.toNat + 24 ≤ s.toNat) (hu8 : u.toNat % 8 = 0)
    (h1 : R 1 = ra) (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = u) (h2 : R 2 = sp)
    (hres : ldv .ld Mt (u + 16#64).toNat = 0#64) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000de8c#64 R Mt
  by nx_run hlive using [h1, h11, h12, h2, hres, BitVec.add_assoc]

/-- The bytes `__sfvwrite_r` leaves alone: all but its frames (the `n`
bytes below `sp`), `errno` and `stdout`'s flags. -/
@[nx_mt] def sfvKeep (sp : BitVec 64) (n : Nat) (a : Nat) : Prop :=
  ¬ (sp.toNat - n ≤ a ∧ a < sp.toNat) ∧ ¬ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∧
    ¬ (0x8001bb30 ≤ a ∧ a < 0x8001bb32)

theorem MemKeep.mono {M M' : Mem} {P P' : Nat → Prop} (h : MemKeep M M' P) (hP : ∀ a, P' a → P a) :
    MemKeep M M' P' :=
  ⟨fun a ha => h.keep a (hP a ha)⟩

/-- **`__sfvwrite_r(reent, stdout, uio)`** with one iov of the bytes `bs`
(persistent data at `buf`): prints them, returns `0`. The memory keeps
`sfvKeep` off the residual count `uio_resid` (`u + 16`), and `stdout`'s flags
are back. -/
theorem sfvwrite_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra u : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 320 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (hu1 : sp.toNat ≤ u.toNat) (hu2 : u.toNat + 24 ≤ s.toNat) (hu8 : u.toNat % 8 = 0)
    (h1 : R 1 = ra) (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = u) (h2 : R 2 = sp)
    {v : BitVec 64} {buf : Nat} {bs : List (BitVec 8)} (hn1 : bs.length ≤ 0x7ffffc00)
    (hv1 : sp.toNat ≤ v.toNat) (hv2 : v.toNat + 16 ≤ s.toNat) (hv8 : v.toNat % 8 = 0)
    (hres : ldv .ld Mt (u + 16#64).toNat = BitVec.ofNat 64 bs.length) (hiov : ldv .ld Mt u.toNat = v)
    (hbuf : ldv .ld Mt v.toNat = BitVec.ofNat 64 buf)
    (hlen : ldv .ld Mt (v + 8#64).toNat = BitVec.ofNat 64 bs.length)
    (hF : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hFu : ldv .lhu Mt 0x8001bb30 = 0x200a#64)
    (hB : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64)
    (hwr : ldv .ld Mt 0x8001bb60 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64)
    (hfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbo : ∀ i, i < bs.length → ¬ outS s need (buf + i))
    (hsrc : ∀ i (h : i < bs.length), buf + i ∈ DA ∧ imgM Dt (buf + i) = bs[i])
    (hk : ∀ R' M', RetOK R R' 0#64 →
      MemKeep Mt M' (fun a => sfvKeep sp 256 a ∧ ¬ (u.toNat + 16 ≤ a ∧ a < u.toNat + 24)) →
      ldv .lh M' 0x8001bb30 = 0x200a#64 → ldv .lhu M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bs) ra R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000de8c#64 R Mt := by
  by_cases hn0 : bs.length = 0
  · obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hn0
    simp only [putcs_nil, String.append_empty] at hk
    refine sfv_Z hlive hs1 hs2 hs3 hs4 hal hra hu1 hu2 hu8 h1 h11 h12 h2 (by rw [hres]; rfl) ?_
    intros
    refine hk _ _ (retOK_of (by simp) (by ret_keep)) ⟨fun a _ => rfl⟩ hF hFu
  refine sfv_chain hlive hs1 hs2 hs3 hs4 hal hra hn0 hn1 hu1 hu2 hu8 hv1 hv2 hv8 h1 h11 h12 h2 hres
    hiov hbuf hlen hF hB hwr hck hfd hb1 hb2 hb3 hbo hsrc ?_
  intros
  refine hk _ _ (retOK_of (by simp [upd_apply]) (by ret_keep)) ⟨fun a ha => ?_⟩ ?_ ?_
  · obtain ⟨ha1, ha2⟩ := ha
    simp only [sfvKeep] at ha1
    simp (disch := nx_addr) only [imgM_store_miss]
  all_goals (nx_mem; decide)

end VsaIris.Sym
