import VsaIris.Vsa.Fprintf.SbFile

/-!
# `__sfvwrite_r` on `__sbprintf`'s stack `FILE` (lane N5)

The fully buffered branch (`flags = 0x2008`: neither `__SNBF` nor `__SLBF`
nor `__SSTR`). At the loop head `0x8000dfc0` the registers hold the `FILE`
(`s0`), the next `iov` (`s1`), the current piece's source and length (`s6`,
`s3`), `_p` (`a5`) and the flags (`a3`). One pass either fetches the next
`iov` (`s3 = 0`), copies `min(len, _w)` bytes into the buffer (`memmove`,
then `_fflush_r` when the buffer is full), or, with the buffer empty and
`len ≥ 1024`, writes `len - len % 1024` bytes straight through `__swrite`.
The pass ends at `0x8000e258`, which subtracts the bytes from the `uio`'s
residual and returns to the head, or leaves when it reaches zero.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- Registers the loop never writes (`sp`, `s0`, `s4`, `s5`, `s7`–`s11`). -/
abbrev sfvKeep : List Nat := [2, 8, 20, 21, 23, 24, 25, 26, 27]

/-- **The loop head's registers**: the next `iov` `nxt`, the current piece
(`L` bytes left at `src`), `_p`, the flags, and the kept registers as in the
loop's reference file `Rh` (which holds `FILE`, `uio`, `reent`, `INT_MAX`). -/
structure SfvRegs (R Rh : Nat → BitVec 64) (nxt L src : Nat) (P : BitVec 64) : Prop where
  nxt : R 9 = BitVec.ofNat 64 nxt
  len : R 19 = BitVec.ofNat 64 L
  src : R 22 = BitVec.ofNat 64 src
  p : R 15 = P
  flags : R 13 = 0x2008#64
  keep : ∀ x ∈ sfvKeep, R x = Rh x

/-- The loop's reference registers: `s0 = f`, `s4 = uio`, `s5 = reent`,
`s8 = INT_MAX`, `sp` below the frame. -/
structure SfvRef (Rh : Nat → BitVec 64) (f U sp : BitVec 64) : Prop where
  file : Rh 8 = f
  uio : Rh 20 = U
  reent : Rh 21 = 0x8001b538#64
  imax : Rh 24 = 0x7fffffff#64
  sp : Rh 2 = sp

/-- Register facts of a `SfvRegs`/`SfvRef` pair, as `nx_run` facts. -/
theorem SfvRegs.k2 {R Rh : Nat → BitVec 64} {nxt L src : Nat} {P : BitVec 64}
    (h : SfvRegs R Rh nxt L src P) {f U sp : BitVec 64} (hr : SfvRef Rh f U sp) :
    R 8 = f ∧ R 20 = U ∧ R 21 = 0x8001b538#64 ∧ R 24 = 0x7fffffff#64 ∧ R 2 = sp :=
  ⟨(h.keep 8 (by decide)).trans hr.file, (h.keep 20 (by decide)).trans hr.uio,
    (h.keep 21 (by decide)).trans hr.reent, (h.keep 24 (by decide)).trans hr.imax,
    (h.keep 2 (by decide)).trans hr.sp⟩

/-- A kept register set survives an update outside it. -/
theorem keep_upd {R Rh : Nat → BitVec 64} {xs : List Nat} {k : Nat} {v : BitVec 64} (hk : k ∉ xs)
    (h : ∀ x ∈ xs, R x = Rh x) : ∀ x ∈ xs, upd R k v x = Rh x := by
  intro x hx
  have hne : x ≠ k := fun e => hk (e ▸ hx)
  rw [upd_other _ _ hne]
  exact h x hx

/-- A kept register set through an `upd` chain outside it. -/
macro "keep_chain " h:term : tactic => `(tactic| ((repeat (refine keep_upd (by decide) ?_)); exact $h))

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **The pass's tail** (`0x8000e258`): `c` bytes handled; the residual drops
by `c`; back to the head with `L - c` bytes left at `src + c`, or out at
`0x8000e334` when the residual reaches zero. -/
theorem sfv_tail (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R Rh : Nat → BitVec 64} {s sp f U P : BitVec 64} {need nxt c L src resid : Nat}
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hU1 : s.toNat - need ≤ U.toNat) (hU2 : U.toNat + 24 ≤ s.toNat) (hUa : U.toNat % 8 = 0)
    (hf1 : s.toNat - need ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat)
    (hfU : U.toNat + 24 ≤ f.toNat ∨ f.toNat + 1208 ≤ U.toNat)
    (hc : c ≤ resid) (hr : resid < 2 ^ 63) (hcL : c ≤ L) (hL : L < 2 ^ 63) (hsrc : src + L < 2 ^ 64)
    (hRh : SfvRef Rh f U sp) (hR : SfvRegs R Rh nxt L src P) (h18 : R 18 = BitVec.ofNat 64 c)
    (hres : ldv .ld Mt (U + 16#64).toNat = BitVec.ofNat 64 resid)
    (hfl : ldv .lh Mt (f + 16#64).toNat = 0x2008#64) (hp : ldv .ld Mt f.toNat = P)
    (hkH : resid ≠ c → ∀ R', SfvRegs R' Rh nxt (L - c) (src + c) P →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000dfc0#64 R'
        (writeLog Mt [((U + 16#64).toNat, 8, BitVec.ofNat 64 (resid - c))]))
    (hkX : resid = c → ∀ R', (∀ x ∈ sfvKeep, R' x = Rh x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e334#64 R'
        (writeLog Mt [((U + 16#64).toNat, 8, BitVec.ofNat 64 (resid - c))])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e258#64 R Mt := by
  obtain ⟨h8, h20, _, _, _⟩ := hR.k2 hRh
  have h19 := hR.len; have h22 := hR.src
  have e1 : BitVec.ofNat 64 resid - BitVec.ofNat 64 c = BitVec.ofNat 64 (resid - c) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e2 : BitVec.ofNat 64 L - BitVec.ofNat 64 c = BitVec.ofNat 64 (L - c) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  nx_run hlive using [h8, h18, h19, h20, h22, hres, hfl, hp, e1, e2, ofNat_add_ofNat,
    BitVec.add_assoc] at 2147540928 2147541812
  · rename_i hb; rsimp at hb
    refine hkX ?_ _ (by keep_chain hR.keep)
    have := congrArg BitVec.toNat hb; simp only [BitVec.toNat_ofNat] at this; omega
  · rename_i hb; rsimp at hb
    refine hkH (fun e => hb (by rw [e, Nat.sub_self])) _ ⟨?_, ?_, ?_, ?_, ?_, by keep_chain hR.keep⟩
    all_goals rsimp
    all_goals first | exact hR.nxt | (rw [ldv_ld_miss _ _ (by nx_addr)]; exact hp)

/-- **The next `iov`** (`s3 = 0` at the head, `0x8000e0ac`): the piece at
`nxt` becomes current, `nxt` moves on by 16. -/
theorem sfv_fetch (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R Rh : Nat → BitVec 64} {s f U sp P : BitVec 64} {need nxt src src' L' : Nat}
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hn1 : s.toNat - need ≤ nxt) (hn2 : nxt + 16 ≤ s.toNat) (hna : nxt % 8 = 0)
    (hRh : SfvRef Rh f U sp) (hR : SfvRegs R Rh nxt 0 src P)
    (hs : ldv .ld Mt (BitVec.ofNat 64 nxt).toNat = BitVec.ofNat 64 src')
    (hl : ldv .ld Mt (BitVec.ofNat 64 (nxt + 8)).toNat = BitVec.ofNat 64 L')
    (hk : ∀ R', SfvRegs R' Rh (nxt + 16) L' src' P →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000dfc0#64 R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000dfc0#64 R Mt := by
  have h9 := hR.nxt; have h19 := hR.len
  have hnd : (BitVec.ofNat 64 nxt).toNat = nxt := by simp only [BitVec.toNat_ofNat]; omega
  have hn8 : (BitVec.ofNat 64 (nxt + 8)).toNat = nxt + 8 := by simp only [BitVec.toNat_ofNat]; omega
  have e0 : BitVec.ofNat 64 nxt + LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) =
      BitVec.ofNat 64 nxt := by rw [show LeanRV64DExecutable.Functions.sign_extend (m := 64) (0x000#12) = 0#64 by decide, BitVec.add_zero]
  refine it_8000dfc0 hlive (fun _ => ?_) (fun hc => absurd (by rw [h19]) hc)
  nx_run hlive using [h9, h19, e0, hs, hl, ofNat_add_ofNat] at 2147540928
  refine hk _ ⟨?_, ?_, ?_, ?_, ?_, by keep_chain hR.keep⟩
  all_goals rsimp
  all_goals first | exact hR.p | exact hR.flags

/-- `__sfvwrite_r`'s spills in its frame at `fp` (`sp - 96`): the entry's
`ra` and the saved registers it restores. -/
structure SfvSpills (M : Mem) (fp : BitVec 64) (R0 : Nat → BitVec 64) : Prop where
  ra : ldv .ld M (fp + 88#64).toNat = R0 1
  s0 : ldv .ld M (fp + 80#64).toNat = R0 8
  s1 : ldv .ld M (fp + 72#64).toNat = R0 9
  s2 : ldv .ld M (fp + 64#64).toNat = R0 18
  s3 : ldv .ld M (fp + 56#64).toNat = R0 19
  s4 : ldv .ld M (fp + 48#64).toNat = R0 20
  s5 : ldv .ld M (fp + 40#64).toNat = R0 21
  s6 : ldv .ld M (fp + 32#64).toNat = R0 22
  s7 : ldv .ld M (fp + 24#64).toNat = R0 23
  s8 : ldv .ld M (fp + 16#64).toNat = R0 24
  s9 : ldv .ld M (fp + 8#64).toNat = R0 25

/-- **The exit** (`0x8000e334`, the residual is zero): restore and return 0. -/
theorem sfv_exit (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R R0 : Nat → BitVec 64} {s fp : BitVec 64} {need : Nat}
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hf1 : s.toNat - need ≤ fp.toNat) (hf2 : fp.toNat + 96 ≤ s.toNat) (hfa : fp.toNat % 16 = 0)
    (h2 : R 2 = fp) (h0 : R0 2 = fp + 96#64) (hra : (R0 1).toNat % 4 = 0)
    (h26 : R 26 = R0 26) (h27 : R 27 = R0 27) (hsp : SfvSpills Mt fp R0)
    (hk : ∀ R', RetOK R0 R' 0#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (R0 1) R' Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e334#64 R Mt := by
  obtain ⟨e1, e8, e9, e18, e19, e20, e21, e22, e23, e24, e25⟩ := hsp
  nx_run hlive using [h2, e1, e8, e9, e18, e19, e20, e21, e22, e23, e24, e25, BitVec.add_assoc]
  refine hk _ (retOK_of (by rsimp) ?_)
  intro x hx h32 h10 hc
  simp only [iRegs, callClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx hc
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (rsimp; done)
    | (rsimp; first | rfl | assumption | exact h0.symm)
    | (exfalso; simp at hc; done)
    | (exfalso; simp at h32; done)
    | (exfalso; simp at h10; done)

end VsaIris.Sym.Fp
