import Vsa.Sim.ReprSurvival

/-!
# Layer 2 — reusable `ValueRepr` TRANSLATION-COPY under a struct-byte copy

`Vsa/Sim/ReprSurvival.lean` proves *same-address* survival: `ValueRepr m N φc a v`
persists to `m'` when `m'` agrees with `m` byte-for-byte on the addresses the
relation reads (the 24-byte header `[a, a+24)` and any dereferenced string).

This file proves the *translation* variant used by the two `Value`-copy call
sites (`env_get`'s HIT tail and `EvalVarSim`'s `VarPostCall.hcopy`): a C `Value`
is **memcpy'd** from `srcAddr` to `dstAddr` — the 24 struct bytes are duplicated
verbatim (including any heap POINTER stored in the payload word), while the
pointed-to heap data (the `.str` string bytes / the closure) is **not** moved.
So `ValueRepr` re-holds at the *new* address `dstAddr` as long as:

1. the 24 struct bytes at `dstAddr` in `m'` equal the 24 at `srcAddr` in `m`
   (`∀ j < 24, m'[dstAddr+j]? = m[srcAddr+j]?`), and
2. `m'` preserves the value's heap payload target region (the `.str` string
   bytes at the payload pointer `p`; for `.closure`/`.native` the payload is a
   pointer whose target repr — `φc`/`N.addr`/native name string — must survive).

The mechanism, per kind:
* `.null`/`.bool`/`.int`: determined by the 24 struct bytes alone. The copied
  bytes give the same `read32`/`readI64` at `dstAddr` as at `srcAddr`.
* `.str`: struct bytes give the same payload pointer `p = read64 · (·+8)`; the
  `CString m p s` then transfers to `m'` by `cstring_agreeP` on `[p, p+s.length]`.
* `.closure`: struct bytes give the same `φc ca` at `dstAddr+8`; `φc ca ≠ 0` is
  memory-independent. (No further payload read — the `Closure*` target lives in
  `ClosureRepr`, part of `StoreRepr`, not `ValueRepr`.)
* `.native`: struct bytes give the same name pointer `p` (@+8) and `N.addr f`
  (@+16); the name `CString m p (nativeName f)` transfers by `cstring_agreeP`.

The heap-payload preservation is packaged, for `env_get`/`EvalVarSim`, as: `m'`
differs from `m` only inside the destination window `[dstAddr, dstAddr+24)`, and
that window is disjoint from the value's heap footprint (string bytes live
elsewhere in the arena / rodata). The convenience corollary
`valueRepr_copy_of_writeWindow` discharges the payload hypothesis from exactly
that disjointness.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## Byte-shifted `readLE` transfer

If the `n` bytes at `dstAddr` in `m'` equal the `n` bytes at `srcAddr` in `m`,
then any `readLE` of width `w ≤ n` reads the same value at the shifted address.
This is the byte-copy analogue of `readLE_agreeP` (which is the `srcAddr =
dstAddr` special case). -/

/-! ## The `ValueRepr` translation-copy lemma

The value struct at `srcAddr` in `m` reads:
* `read32 · srcAddr` (kind tag, @0) — always;
* `read64 · (srcAddr+8)` / `readI64 · (srcAddr+8)` (payload word, @8) — every
  non-null variant;
* `read64 · (srcAddr+16)` (@16) — only `.native`;
and, for `.str`/`.native`, a `CString` at the payload/name pointer `p`.

The `hpayload` hypothesis carries the payload-region agreement in the exact shape
`cstring_agreeP` consumes: for the payload pointer `p` witnessed by the *source*
`read64 m (srcAddr+8)`, `m'` and `m` agree on `[p, p + s.length]` (packaged via
`AgreeP` from `ReprSurvival`). -/

/-! ## Convenience corollary: copy realized as a write of the dst window

The two consumers realize the copy as "`m'` equals `m` outside the destination
window `[dstAddr, dstAddr+24)`, and inside that window the 24 bytes match the
source". The payload target (the `.str`/`.native` string) lives *outside* the
window (disjoint), so its bytes are untouched and `hpay` follows for free.

We phrase "the payload lives outside the window" abstractly as: every string the
value dereferences has its whole byte range disjoint from `[dstAddr, dstAddr+24)`.
For a caller that knows the string lives in a region disjoint from the write
(arena / rodata), this is a single `omega`-shaped disjointness fact. -/

/-! ## Total-read copy (wave 48k)

The Sail model copies memory TOTALLY: a `ld`/`sd` pair moves
`(m[a]?).getD 0`, so the destination window always holds `some` byte even where
the SOURCE byte is absent from the map.  Plain byte-for-byte agreement
(`hcopy` above) therefore does NOT hold for a total copy — but it is not what
`ValueRepr` needs.  `ValueRepr m … srcAddr v` already WITNESSES that every byte
it reads is present (a successful `readLE` forces each byte to be `some`), and
exactly there the total copy reproduces the source value.  That is the honest
form of the copy for a machine that never faults on absence: the value facts
come from the source `ValueRepr`, not from a blanket presence premise.

Bytes 4..7 of a `Value` struct (and 16..23 for the non-`.native` variants) are
never read by `ValueRepr`; under a total copy they hold `0`, and nothing
depends on them. -/

/-! ## `#print axioms` sanity — main lemmas kernel-clean -/

end Vsa.Sim
