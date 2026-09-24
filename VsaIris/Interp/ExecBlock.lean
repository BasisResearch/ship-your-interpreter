import VsaIris.Interp.ExecEnv
import VsaIris.Interp.SeqLoop

/-!
# `exec_stmt`'s block arm: runs and node facts (lane E5)

`0x8000418c`: `mv a0,s3; jal env_new` (`0x80004190`), then `lw a5,16(s0)` (the
count), `mv s3,a0` (the new frame), `li a6,0`, `blez a5` to the shared exit
(`0x80004090`: `li a0,0`) or on to the statement loop's head `0x800041a4`
(lane G's `blockSeqT_body`/`blockSeqP_body`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg BlockArm_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (hk : ldv .lw m aS.toNat = 2#64) (hku : ldv .lwu m aS.toNat = 2#64) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, hk, hku] at 0x80004190

#ix_seg BlockArm_runE {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hc : ldv .lw m (aS + 16#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004194#64 R Mt
  by ix_run hlive using [h8, hc] at 0x8000409c

#ix_seg BlockArm_runL {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64} {count : Nat}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hc : ldv .lw m (aS + 16#64).toNat = BitVec.ofNat 64 count) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004194#64 R Mt
  by ix_run hlive using [h8, hc] at 0x800041a4 0x80004090

end VsaIris.Interp
