import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.Stdout.Tac

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout VsaIris.Sym.Win

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

@[nx_mt] abbrev swriteMt (Mt : Mem) (sp ra s0 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [(2147597104, 2, 8202#64)])
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551608#64).toNat, 8, ra)])
    [(2147596808, 4, 0#64)]

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem swriteP (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra s0 : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
    (F : Nat) (fl fl' : BitVec 64) (hF : 0x8001ba68 ≤ F ∧ F + 24 ≤ 0x8001c168 ∧ F % 8 = 0)
    (hs1 : s.toNat - need + 64 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (h1 : R 1 = ra)
    (hra : ra.toNat % 4 = 0) (h8 : R 8 = s0) (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbd : ∀ i, i < bs.length → (buf + i < sp.toNat - 64 ∨ sp.toNat ≤ buf + i) ∧
      (buf + i < F + 16 ∨ F + 18 ≤ buf + i) ∧ (buf + i < 0x8001ba08 ∨ 0x8001ba0c ≤ buf + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (buf + i) bs[i])
    (h11 : R 11 = BitVec.ofNat 64 F) (h12 : R 12 = BitVec.ofNat 64 buf)
    (h13 : R 13 = BitVec.ofNat 64 bs.length) (h2 : R 2 = sp)
    (hfl : ldv .lh Mt (F + 16) = fl) (hap : fl &&& 256#64 = 0#64) (hfl' : fl &&& 18446744073709547519#64 = fl')
    (hk : ∀ R', RetOK R R' (BitVec.ofNat 64 bs.length) → SWPO live (stdioText ++ dataOf Dt DA) iRegs
      (outS s need) Q (t ++ putcs bs) ra R' (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [(F + 16, 2, fl')])
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551608#64).toNat, 8, ra)])
    [(2147596808, 4, 0#64)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000efd4#64 R Mt := by
  have hF16 : (BitVec.ofNat 64 F + 16#64).toNat = F + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  nx_win sp 64 0; nx_run hlive using [h11, h2, h1, h8, hF16, hfl, hap, BitVec.reduceAnd, BitVec.reduceOr, BitVec.add_assoc] at 2147483708
  refine write_run' hlive buf bs hb1 hb2 hb3 (fun i hi => ?_) _ t (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h13]) (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide) (fun v11 v13 v14 v15 v16 => ?_)
  · refine ((((hsrc i hi).store _ ?_).store _ ?_).store _ ?_).store _ ?_ |>.store _ ?_
    all_goals (have := hbd i hi; nx_addr)
  sx_norm
  nx_run hlive using [h13, h12, h2, h1, h8, hF16, hfl', BitVec.add_assoc]
  exact hk _ (retOK_of (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, writeRegs]) (by ret_keep))

theorem swrite_run (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp ra s0 : BitVec 64} {need : Nat} {buf : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 64 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (h1 : R 1 = ra)
    (hra : ra.toNat % 4 = 0) (h8 : R 8 = s0) (hb1 : 0x80000000 ≤ buf) (hb2 : buf + bs.length ≤ 0x100000000)
    (hb3 : buf + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ buf)
    (hbd : ∀ i, i < bs.length → (buf + i < sp.toNat - 64 ∨ sp.toNat ≤ buf + i) ∧
      (buf + i < 0x8001bb30 ∨ 0x8001bb32 ≤ buf + i) ∧ (buf + i < 0x8001ba08 ∨ 0x8001ba0c ≤ buf + i))
    (hsrc : ∀ i (h : i < bs.length), ByteSrc (outS s need) Mt Dt DA (buf + i) bs[i])
    (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = BitVec.ofNat 64 buf)
    (h13 : R 13 = BitVec.ofNat 64 bs.length) (h2 : R 2 = sp)
    (hfl : ldv .lh Mt 0x8001bb30 = 0x200a#64) (hfd : ldv .lh Mt 0x8001bb32 = 1#64)
    (hk : ∀ R', RetOK R R' (BitVec.ofNat 64 bs.length) → SWPO live (stdioText ++ dataOf Dt DA) iRegs
      (outS s need) Q (t ++ putcs bs) ra R' (swriteMt Mt sp ra s0)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000efd4#64 R Mt :=
  swriteP hlive 0x8001bb20 0x200a#64 8202#64 (by decide) hs1 hs2 hs3 hs4 hal h1 hra h8 hb1 hb2 hb3 hbd
    hsrc h11 h12 h13 h2 hfl (by decide) (by decide) hk

end VsaIris.Sym
