import VsaIris.Interp.CallCloHead
import VsaIris.Interp.SeqLoopClosure
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

#ix_seg CloB_run0 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s fr : BitVec 64} {argc : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h10 : R 10 = fr) (h2 : R 2 = s + 18446744073709550528#64)
    (hA : ldv .ld Mt (s.toNat - 1088) = BitVec.ofNat 64 argc) :
    IW live m [] (InExt (s.toNat - 1088, 1088)) Q 0x800032c0#64 R Mt
  by ix_run hlive using [h10, h2, hA, hsf] at 0x800032dc 0x80003328

#ix_seg CloB_runL {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s q prm pa off : BitVec 64} {qa qp : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hp1 : 0x80000000 ≤ qp) (hp2 : qp + 8 ≤ 0x100000000)
    (hp3 : qp + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ qp)
    (h8 : R 8 = pa) (h21 : R 21 = q) (h15 : R 15 = off) (h2 : R 2 = s + 18446744073709550528#64)
    (hprm : ldv .ld m (q + 16#64).toNat = prm)
    (hpo : (prm + off).toNat = qp)
    (hq0 : pa.toNat = qa)
    (hq8 : (pa + LeanRV64DExecutable.Functions.sign_extend 8#12).toNat = qa + 8)
    (hq16 : (pa + LeanRV64DExecutable.Functions.sign_extend 16#12).toNat = qa + 16)
    (hqa1 : s.toNat - 1088 + 240 ≤ qa) (hqa2 : qa + 24 ≤ s.toNat - 1088 + 1008) (hqa3 : qa % 8 = 0) :
    IW live m (accAddrs (q.toNat + 16) 8 ++ accAddrs qp 8)
      (InExt (s.toNat - 1088, 1088)) Q 0x800032dc#64 R Mt
  by sym_run hlive using [h8, h21, h15, h2, hprm, hpo, hq0, hq8, hq16, hsf] at 0x80003310

#ix_seg CloB_runR {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s v22 : BitVec 64} {j argc : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hj : j < argc) (hc : argc ≤ 32)
    (h2 : R 2 = s + 18446744073709550528#64) (h22 : R 22 = BitVec.ofNat 64 (8 * argc))
    (hO : ldv .ld Mt (s.toNat - 1088) = BitVec.ofNat 64 (8 * j))
    (h1024 : ldv .ld Mt (s + 18446744073709550528#64 + 1024#64).toNat = v22) :
    IW live m [] (InExt (s.toNat - 1088, 1088)) Q 0x80003314#64 R Mt
  by ix_run hlive using [h2, h22, hO, h1024, hsf] at 0x800032dc 0x80003328

#ix_seg CloB_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {S : Nat → Prop} {q bod : BitVec 64} {count : Nat}
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hb1 : 0x80000000 ≤ bod.toNat) (hb2 : bod.toNat + 20 ≤ 0x100000000)
    (hb3 : bod.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ bod.toNat) (hcnt : count < 2 ^ 31)
    (h21 : R 21 = q)
    (hbod : ldv .ld m (q + 32#64).toNat = bod)
    (hct : ldv .lw m (bod + 16#64).toNat = BitVec.ofNat 64 count) :
    IW live m (accAddrs (q.toNat + 32) 8 ++ accAddrs (bod.toNat + 16) 4) S Q 0x8000332c#64 R Mt
  by sym_run hlive using [h21, hbod, hct] at 0x80003354 0x80003954

#ix_seg CloX_runN {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s inp : BitVec 64} {dep : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hi1 : tohostAddr + 16 ≤ inp.toNat) (hi2 : inp.toNat + 480 ≤ 0x88000000)
    (hi3 : inp.toNat + 12 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp.toNat + 8) (hia : inp.toNat % 8 = 0)
    (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64)
    (hdep : ldv .lw Mt (inp + 8#64).toNat = BitVec.ofNat 64 dep) :
    IW live m [] (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b) Q
      0x80003954#64 R Mt
  by sym_run hlive using [h18, h2, hdep, hsf] at 0x80003964

#ix_seg CloX_runE {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s ret v8 v9 v18 v19 v21 v23 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19)
    (hS5 : ldv .ld Mt (s + 18446744073709550528#64 + 1032#64).toNat = v21)
    (hS7 : ldv .ld Mt (s + 18446744073709550528#64 + 1016#64).toNat = v23) :
    IW live m [] (InExt (s.toNat - 1088, 1088)) Q 0x80003968#64 R Mt
  by sym_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hS5, hS7, hsf, hal]

#ix_seg CloX_runX {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s inp : BitVec 64} {dep : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hi1 : tohostAddr + 16 ≤ inp.toNat) (hi2 : inp.toNat + 480 ≤ 0x88000000)
    (hi3 : inp.toNat + 12 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp.toNat + 8) (hia : inp.toNat % 8 = 0)
    (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64)
    (hdep : ldv .lw Mt (inp + 8#64).toNat = BitVec.ofNat 64 dep) :
    IW live m [] (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b)
      Q 0x8000337c#64 R Mt
  by sym_run hlive using [h18, h2, hdep, hsf] at 0x80003ce8 0x80003960 0x8000339c

#ix_seg CloX_runC {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s sret ret v8 v9 v18 v19 v21 v23 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hr1 : sret.toNat % 8 = 0) (hr2 : tohostAddr + 16 ≤ sret.toNat)
    (hr3 : sret.toNat + 24 ≤ 0x100000000)
    (hr4 : sret.toNat + 24 ≤ s.toNat - 1088 ∨ s.toNat ≤ sret.toNat)
    (hal : ret.toNat % 4 = 0)
    (h9 : R 9 = sret) (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19)
    (hS5 : ldv .ld Mt (s + 18446744073709550528#64 + 1032#64).toNat = v21)
    (hS7 : ldv .ld Mt (s + 18446744073709550528#64 + 1016#64).toNat = v23) :
    IW live m [] (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (sret.toNat, 24) b)
      Q 0x8000339c#64 R Mt
  by sym_run hlive using [h9, h2, hRA, hS0, hS1, hS2, hS3, hS5, hS7, hsf, hal]

#ix_seg CloE_runD {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s inp : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hi1 : tohostAddr + 16 ≤ inp.toNat) (hi2 : inp.toNat + 480 ≤ 0x88000000)
    (hi3 : inp.toNat + 12 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp.toNat + 8) (hia : inp.toNat % 8 = 0)
    (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64) :
    IW live m [] (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b) Q
      0x80003ca4#64 R Mt
  by sym_run hlive using [h18, h2, hsf] at 0x80003cc4

#ix_seg CloE_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s q nam : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (h21 : R 21 = q) (h2 : R 2 = s + 18446744073709550528#64)
    (hnam : ldv .ld m (q + 8#64).toNat = nam) :
    IW live m (accAddrs (q.toNat + 8) 8) (InExt (s.toNat - 1088, 1088)) Q 0x80003d60#64 R Mt
  by sym_run hlive using [h21, h2, hnam, hsf] at 0x80003d84

#ix_seg CloE_runA2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {S : Nat → Prop} :
    IW live m [] S Q 0x80003d88#64 R Mt
  by sym_run hlive at 0x80003da0

end VsaIris.Interp
