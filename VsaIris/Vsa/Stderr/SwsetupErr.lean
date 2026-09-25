import VsaIris.Vsa.Stderr.Swrite
import VsaIris.Vsa.Stderr.Mem
import VsaIris.Vsa.SymCompactTac

/-!
# `__swsetup_r` on `stderr`, the first write (lane N3)

`fwrite` and `fprintf` on `stderr` both reach `__swsetup_r(reent, stderr)`
(`0x8000f230`) with the stream oriented and idle (flags
`__SORD | __SRW | __SNBF`, `0x2012`, no buffer). It sets `__SWR`, and
`__smakebuf_r` → `__swhatbuf_r` → `_fstat_r` → `_fstat` installs the one-byte
unbuffered buffer `_nbuf` (`stderr + 119`); `_w` stays 0. `swsetupErr_run`
hands the caller the written stream as named facts (`SwsetupPost`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

/-- The memory after `__swsetup_r(reent, stderr)` returns: its `ra` slot and
`__smakebuf_r`'s spill of `fp`, the flags (`0x201a`), `_p` and `_bf._base`
(`_nbuf`, `stderr + 119`), `_bf._size = 1`, `_w = 0`. -/
abbrev swsetupErrMt (Mt : Mem) (sp ra : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [((sp + 18446744073709551608#64).toNat, 8, ra)]) [(0x8001bbe8, 2, 0x201a#64)])
    [((sp + 18446744073709551584#64).toNat, 8, 0x8001bbd8#64)]) [(0x8001bbd8, 8, 0x8001bc4f#64)])
    [(0x8001bbf0, 8, 0x8001bc4f#64)]) [(0x8001bbf8, 4, 1#64)]) [(0x8001bbe4, 4, 0#64)]

set_option hygiene false in
/-- One piece of the setup run. -/
macro "swsetup_step" : tactic => `(tactic| (nx_runB hlive using [h1, h2, h10, h11, hDt, hsinit,
  hflU, hflS, hfd, hbase, BitVec.add_assoc, BitVec.zero_add, ldv_ld_and_640, BitVec.reduceXOr]))

#ix_piece swsetupErr_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat) (ra sp : BitVec 64)
    (hs1 : s.toNat - need + 384 ≤ sp.toNat) (hs2 : sp.toNat ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0)
    (h1 : R 1 = ra) (h2 : R 2 = sp) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bbd8#64)
    (hDt : ldv .ld Dt 0x8001b970 = 0x8001b538#64)
    (hsinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64)
    (hflU : ldv .lhu Mt 0x8001bbe8 = 0x2012#64) (hflS : ldv .lh Mt 0x8001bbe8 = 0x2012#64)
    (hfd : ldv .lh Mt 0x8001bbea = 2#64) (hbase : ldv .ld Mt 0x8001bbf0 = 0#64)
    (hk : ∀ R', RetOK R R' 0#64 →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t ra R'
        (swsetupErrMt Mt sp ra)) :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000f230#64 R Mt by
  swsetup_step

#ix_piece swsetupErr_02 from swsetupErr_01 by
  swsetup_step

#ix_piece swsetupErr_03 from swsetupErr_02 by
  nx_compactR
  simp only [swsetupErrMt] at hk
  refine hk _ (retOK_of ?_ ?_)
  · simp [upd_apply]
  · ret_keep

/-! **`swsetupErr_run`**: `__swsetup_r(reent, stderr)` on the oriented idle stream. -/
#ix_chain swsetupErr_run := [swsetupErr_01, swsetupErr_02, swsetupErr_03]

end VsaIris.Sym
