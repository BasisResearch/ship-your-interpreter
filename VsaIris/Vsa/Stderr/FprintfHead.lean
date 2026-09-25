import VsaIris.Vsa.Stderr.VfpErr

/-!
# `fprintf(stderr, fmt, p)` up to `_vfprintf_r`'s direct path (lane N3)

`fprintf` (`0x800061c0`) spills its variadic registers (`a2`–`a7` at
`sp + 32 …`, `ap = sp + 32`), loads `_impure_ptr` and calls `_vfprintf_r`;
`vfpEntry_run` and `vfpErr_run` take it to `0x8000a944`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

#ix_piece fprintfHead_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s ra p : BitVec 64)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - 4096) (hal : s.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h2 : R 2 = s) (h10 : R 10 = 0x8001bbd8#64) (h11 : R 11 = 0x800195e0#64)
    (h12 : R 12 = p) (hDt : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hk : ∀ R' Mt', SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s 4096) Q t 0x8000a884#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s 4096) Q t
      0x800061c0#64 R Mt by
  nx_runB hlive using [h1, h2, h10, h11, h12, hDt, BitVec.add_assoc] at 0x8000a884
  exact hk _ _

end VsaIris.Sym
