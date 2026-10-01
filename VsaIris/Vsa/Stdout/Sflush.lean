import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.Stdout.Swrite
import VsaIris.Vsa.SymCompactTac

namespace VsaIris.Sym

open scoped VsaIris.Sym.Stdout VsaIris.Sym.Win

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

@[nx_mt] abbrev sflushPMt (Mt : Mem) (sp f B w ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  swriteMt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551576#64).toNat, 8, s3)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [((sp + 18446744073709551584#64).toNat, 8, s2)])
    [((sp + 18446744073709551592#64).toNat, 8, s1)]) [(f.toNat, 8, B)]) [((f + 12#64).toNat, 4, w)])
    (sp + 18446744073709551568#64) 0x8000ed0c#64 f

@[nx_mt] abbrev sflushMt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  sflushPMt Mt sp f B 0#64 ra s0 s1 s2 s3

set_option hygiene false in
macro "sflush_go" "[" xs:term,* "]" : tactic => `(tactic| (
  nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hF8, hBl, hP, hwr, hck, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc, hsw, hti, BitVec.toInt_zero, $xs,*] at 2147544308
  nx_run hlive using [h10, h11, h2, h1, h8, h9, h18, h19, hF, hF8, hBl, hP, hwr, hck, BitVec.reduceAnd,
    BitVec.reduceOr, BitVec.add_assoc, hsw, hti, BitVec.toInt_zero, $xs,*] at 2147545044
  nx_clear_conds))

set_option hygiene false in
macro "sflush_tail" : tactic => `(tactic| (
  refine swrite_run (sp := sp + 18446744073709551568#64) (buf := B.toNat) (bs := bs)
    (ra := 0x8000ed0c#64) (s0 := f) hlive ?_ ?_ hs3 hs4 ?_ ?_ (by decide) ?_
    (by omega) (by omega) hb3 ?_ (fun i hi => ?_) ?_ ?_ ?_ ?_ ?_ ?_ (fun R' hR => ?_)
  all_goals try (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]; done)
  all_goals try nx_addr
  · intro i hi; have := hbd i hi; nx_addr
  · repeat' (first | refine ByteSrc.store ?_ _ ?_ | exact hsrc i hi)
    all_goals (have := hbd i hi; nx_addr)
  · nx_mem; exact hsfl
  · nx_mem; exact hsfd
  nx_ret hR
  nx_run hlive using [rk1, rk2, rk8, rk9, rk10, rk18, rk19, BitVec.add_assoc]
  nx_clear_conds
  simp only [nx_mt, BitVec.add_assoc, BitVec.reduceAdd] at hk ⊢
  exact hk _ (retOK_of (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]) (by ret_keep))))

#ix_seg sflushP_A {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f F B w ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h8 : R 8 = s0) (h9 : R 9 = s1) (h18 : R 18 = s2) (h19 : R 19 = s3)
    (hfa : f.toNat % 8 = 0) (hn : 0 < bs.length) (hn2 : bs.length < 2 ^ 31)
    (hB1 : 0x80000000 ≤ B.toNat) (hb2 : B.toNat + bs.length ≤ 0x88000000)
    (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h2 : R 2 = sp)
    (hF : ldv .lh Mt (f + 16#64).toNat = F) (hF8 : F &&& 8#64 ≠ 0#64)
    (hcase : (sp.toNat ≤ f.toNat ∧ f.toNat + 184 ≤ s.toNat ∧ F &&& 3#64 = 0#64 ∧
        ldv .lw Mt (f + 32#64).toNat = w) ∨ (f.toNat = 0x8001bb20 ∧ F &&& 3#64 ≠ 0#64 ∧ w = 0#64))
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
      (t ++ putcs bs) ra R' (sflushPMt Mt sp f B w ra s0 s1 s2 s3)) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt
  by
    have hti : (BitVec.ofNat 64 bs.length).toInt = bs.length := toInt_ofNat_small (by omega)
    have hsw := subw_add_ofNat hn2
    nx_win sp 128 0
    rcases hcase with ⟨hf1, hf2, hF3, hw⟩ | ⟨hfS, hF3, rfl⟩
    case' inl => nx_win f 0 184; sflush_go [hF3, hw]
    case' inr => sflush_go [hF3]

#ix_piece sflushP_B1 from sflushP_A at 1 by sflush_tail

#ix_piece sflushP_B2 from sflushP_A at 2 by sflush_tail

set_option hygiene false in
macro "sflushP%" hc:term:max : term => `(sflushP_A
  hlive hs1 hs2 hs3 hs4 hal hra h1 h8 h9 h18 h19 hfa hn hn2 hB1 hb2 h10 h11 h2 hF hF8 $hc hBl hB0
  hP hwr hck hsfl hsfd hb3 hbd hsrc hk
  (sflushP_B1 hlive hs1 hs2 hs3 hs4 hal hra h1 h8 h9 h18 h19 hfa hn hn2 hB1 hb2 h10 h11 h2 hF hF8 $hc hBl hB0
  hP hwr hck hsfl hsfd hb3 hbd hsrc hk)
  (sflushP_B2 hlive hs1 hs2 hs3 hs4 hal hra h1 h8 h9 h18 h19 hfa hn hn2 hB1 hb2 h10 h11 h2 hF hF8 $hc hBl hB0
  hP hwr hck hsfl hsfd hb3 hbd hsrc hk))

theorem sflush_run {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String} {Mt : Mem}
    {R : Nat → BitVec 64} {s sp f F B ra s0 s1 s2 s3 : BitVec 64} {need : Nat} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 128 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x8001c168 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : ra.toNat % 4 = 0)
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
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000eb70#64 R Mt :=
  sflushP% (.inr ⟨hfS, hF3, rfl⟩)

namespace Fp

abbrev sflushFMt (Mt : Mem) (sp f B ra s0 s1 s2 s3 : BitVec 64) : Mem :=
  swriteMt (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551600#64).toNat, 8, s0)]) [((sp + 18446744073709551576#64).toNat, 8, s3)])
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [((sp + 18446744073709551584#64).toNat, 8, s2)])
    [((sp + 18446744073709551592#64).toNat, 8, s1)]) [(f.toNat, 8, B)]) [((f + 12#64).toNat, 4, 1024#64)])
    (sp + 18446744073709551568#64) 0x8000ed0c#64 f

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
  have hs4 : 0x8001c168 ≤ s.toNat - need := by omega
  have hF8 : (0x2008#64 : BitVec 64) &&& 8#64 ≠ 0#64 := by decide
  exact sflushP% (.inl ⟨hf1, hf2, by decide, hsz⟩)

end Fp

end VsaIris.Sym
