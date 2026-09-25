import VsaIris.Vsa.Stdout.Swrite
import VsaIris.Vsa.Stderr.Mt

/-!
# `__swrite → _write_r → _write` on `stderr` (lane N3)

Lane N1's `swrite_run` for `stderr` (`0x8001bbd8`): after the first write set
it up its flags are `__SORD | __SRW | __SWR | __SNBF` (`0x201a`); `__swrite`
rewrites them without `__SOFF` (unchanged) and passes descriptor 2, which
`_write` ignores. The console grows by the bytes, `a0 = n`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- `nx_side` for `outS` with the byte hypothesis normalized first (`nx_hb`). -/
macro_rules
  | `(tactic| nx_side) => `(tactic| (
      intro b hb
      (try nx_hb hb)
      simp only [outS, impureW, stdioFoot, InRange] at ⊢
      (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd])
      omega))

/-- The memory after `__swrite(stderr, buf, n)` returns: `__swrite`'s `ra`
slot, the flags, `_write_r`'s `s0`/`ra` slots, `errno`. -/
abbrev swriteErrMt (Mt : Mem) (sp ra s0 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [(2147597288, 2, 8218#64)])
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551608#64).toNat, 8, ra)])
    [(2147596808, 4, 0#64)]

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **`__swrite(reent, stderr, buf, n)`** prints `bs` (`n = |bs|` bytes at
`buf`) and returns `n`. -/
theorem swriteErr_run (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra s0 : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 64 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (h1 : R 1 = ra)
    (hra : ra.toNat % 4 = 0) (h8 : R 8 = s0) (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbd : ∀ i, i < bs.length → (buf + i < sp.toNat - 64 ∨ sp.toNat ≤ buf + i) ∧
      (buf + i < 0x8001bbe8 ∨ 0x8001bbea ≤ buf + i) ∧ (buf + i < 0x8001ba08 ∨ 0x8001ba0c ≤ buf + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (buf + i) bs[i])
    (h11 : R 11 = 0x8001bbd8#64) (h12 : R 12 = BitVec.ofNat 64 buf)
    (h13 : R 13 = BitVec.ofNat 64 bs.length) (h2 : R 2 = sp)
    (hfl : ldv .lh Mt 0x8001bbe8 = 0x201a#64) (hfd : ldv .lh Mt 0x8001bbea = 2#64)
    (hk : ∀ R', RetOK R R' (BitVec.ofNat 64 bs.length) → SWPO live (stdioText ++ dataOf Dt DA) iRegs
      (outS s need) Q (t ++ putcs bs) ra R' (swriteErrMt Mt sp ra s0)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000efd4#64 R Mt := by
  nx_run hlive using [h11, h2, h1, h8, hfl, hfd, BitVec.reduceAnd, BitVec.reduceOr, BitVec.add_assoc] at 2147483708
  refine write_run' hlive buf bs hb1 hb2 hb3 (fun i hi => ?_) _ t (by simp [upd_apply, h12])
    (by simp [upd_apply, h13]) (by simp [upd_apply, hra] <;> decide) (fun v11 v13 v14 v15 v16 => ?_)
  · refine ((((hsrc i hi).store _ ?_).store _ ?_).store _ ?_).store _ ?_ |>.store _ ?_
    all_goals (have := hbd i hi; nx_addr)
  sx_norm
  nx_run hlive using [h13, h12, h2, h1, h8, BitVec.add_assoc]
  exact hk _ (retOK_of (by simp [upd_apply]) (by ret_keep))

end VsaIris.Sym
