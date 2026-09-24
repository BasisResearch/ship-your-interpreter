import VsaIris.Interp.LoopKit

/-!
# The call arguments loop (lane E6), both modes

INTERP_DESIGN.md §4.3; statements in `SpecLoop.lean` (`evalArgsT_body`,
`evalArgsP_body`). `eval_expr`'s call arm fills `args[32]` (`sp+240`):

```
800031dc ld a2,16(s0); … ld a2,0(a2)        args[i]'s node
800031fc sd a5,24(sp); … sd a6,16(sp); sd a3,8(sp); sd a4,0(sp)
80003220 jal eval_expr                       (slot sp+64)
80003224 … sd the three words to a4-768 = sp+240+24i; addi a6,a6,1
80003250 bne a6,a5 → 800031dc                (else 80003254)
```
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a call node and its argument array a run reads. -/
abbrev argsView (a arr argc : Nat) : List Nat := accAddrs (a + 16) 8 ++ accAddrs arr (8 * argc)

#ix_seg ArgsLoop_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s arr pA : BitVec 64} {idx argc : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (ha1 : 0x80000000 ≤ arr.toNat) (ha2 : arr.toNat + 8 * argc ≤ 0x100000000)
    (ha3 : arr.toNat + 8 * argc ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat)
    (hidx : idx < argc) (hc : argc ≤ 32)
    (h8 : R 8 = aX) (h16 : R 16 = BitVec.ofNat 64 idx) (h2 : R 2 = s + 18446744073709550528#64)
    (harr : ldv .ld m (aX + 16#64).toNat = arr)
    (hel : ldv .ld m (arr + BitVec.ofNat 64 idx <<< 3).toNat = pA) :
    IW live m (argsView aX.toNat arr.toNat argc) (InExt (s.toNat - 1088, 1088)) Q 0x800031dc#64 R Mt
  by ix_run hlive using [h8, h16, h2, harr, hel, hsf] at 0x80003220

#ix_seg ArgsLoop_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s slotA : BitVec 64} {q : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hA : ldv .ld Mt (s + 18446744073709550528#64).toNat = slotA)
    (hq0 : (slotA + 18446744073709550848#64).toNat = q)
    (hq8 : (slotA + 18446744073709550856#64).toNat = q + 8)
    (hq16 : (slotA + 18446744073709550864#64).toNat = q + 16)
    (hq1 : s.toNat - 1088 + 240 ≤ q) (hq2 : q + 24 ≤ s.toNat - 1088 + 1008) :
    IW live m [] (InExt (s.toNat - 1088, 1088)) Q 0x80003224#64 R Mt
  by ix_run hlive using [h2, hA, hsf, hq0, hq8, hq16] at 0x800031dc 0x80003254

end VsaIris.Interp
#check @VsaIris.Interp.ArgsLoop_runA
#check @VsaIris.Interp.ArgsLoop_runB
