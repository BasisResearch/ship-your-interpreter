import VsaIris.Interp.Arm

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg BinaryAddIntT_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk6 : ldv .lw m aX.toNat = 6#64) (hk6u : ldv .lwu m aX.toNat = 6#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk6, hk6u, hsf] at 0x800034f8

#ix_seg BinaryAddIntT_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp aR w1 kL : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h18 : R 18 = inp)
    (hright : ldv .ld m (aX + 24#64).toNat = aR)
    (hA : ldv .ld Mt (s.toNat - 1088) = aE)
    (hK : ldv .lw Mt (s + 18446744073709550528#64 + 120#64).toNat = kL)
    (hP : ldv .ld Mt (s + 18446744073709550528#64 + 128#64).toNat = w1) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800034fc#64 R Mt
  by ix_run hlive using [h8, h2, h18, hright, hA, hK, hP, hsf] at 0x80003518

#ix_seg BinaryAddIntT_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s sret w1 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret) (h19 : R 19 = w1)
    (hop : ldv .lw m (aX + 8#64).toNat = 11#64)
    (hKL : ldv .ld Mt (s.toNat - 1088) = 2#64)
    (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000351c#64 R Mt
  by ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x800038d4

#ix_seg BinaryAddIntT_run4 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800038d8#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]

end VsaIris.Interp
