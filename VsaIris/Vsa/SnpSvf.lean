import VsaIris.Vsa.SnpPrint

/-!
# `_svfprintf_r` on `snprintf`'s string `FILE`

`_svfprintf_r(ptr, fp, fmt, ap)` at `sp = s - 272` (its frame `[s - 864,
s - 272)`). The prologue asks the locale for the decimal point (`strlen(".")`)
and clears the multibyte state; the format loop scans literal runs with the
locale's `mbtowc` (`__ascii_mbtowc`), prints each run and each conversion as
iovec pieces, and flushes them through `__ssprint_r` (`ssprint_nw`).
-/

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

#ix_piece svfPro_p1 {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (R : Nat → BitVec 64) (Mt : Mem) (hs1 : 0x8001c168 + 1024 ≤ s) (hs2 : s ≤ 0x88000000)
    (hsa : s % 16 = 0)
    (h2 : R 2 = BitVec.ofNat 64 (s - 272)) (h11 : R 11 = BitVec.ofNat 64 (s - 264))
    (hdp : ldv .ld Mt 0x8001b898 = 0x80019770#64)
    (hdot : InDA DA 0x80019770 0x80019778) (hdw : ldv .ld Dt 0x80019770 = 0x2e#64)
    (eS : BitVec.ofNat 64 (s - 272 + 18446744073709551024) = BitVec.ofNat 64 (s - 864)) :
    NW live Dt DA (snpS s dst n) Q 0x80007654#64 R Mt by
  nx_run [16] hlive using [ofNat_add_ofNat, h2, h11, hdp, hdw, eS]

#check @svfPro_p1

end VsaIris.Sym
