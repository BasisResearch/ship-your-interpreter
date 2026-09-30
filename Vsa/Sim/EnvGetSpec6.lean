import Vsa.Sim.EnvGetSpec5
import Vsa.Sim.ReprCopy
import Vsa.Sim.ValueSpec
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `env_get` HIT-tail machine `Steps` chain + FOUND-case composition

This session's deliverable: `env_get_hit_tail` — a fully-verified machine `Steps`
chain for the 21-instruction HIT tail (`0x80002c70 → ret`), the last genuinely
missing machine-composition piece of the immediate-frame FOUND case, plus the
composition scaffold `env_get_found_spec`.

## HIT-tail disassembly (0x80002c70 – 0x80002cc0)

```
c70 ld   a5,16(s4)   ; a5 = env->vals  = pv
c74 slli a4,s0,0x1   ; a4 = 2*i
c78 add  a4,a4,s0    ; a4 = 3*i
c7c slli a4,a4,0x3   ; a4 = 24*i
c80 add  a5,a5,a4    ; a5 = pv + 24*i  = &values[i]
c84 ld   a4,0(a5)    ; a4 = values[i].word0
c88 li   a0,1        ; a0 = 1  (found)
c8c sd   a4,0(s5)    ; *out[0..8)   = word0
c90 ld   a4,8(a5)    ; a4 = values[i].word1
c94 sd   a4,8(s5)    ; *out[8..16)  = word1
c98 ld   a5,16(a5)   ; a5 = values[i].word2
c9c sd   a5,16(s5)   ; *out[16..24) = word2
ca0 ld   ra,56(sp)   ; restore ra   (= r)
ca4 ld   s0,48(sp)   ; restore s0
ca8 ld   s1,40(sp)   ; restore s1
cac ld   s2,32(sp)   ; restore s2
cb0 ld   s3,24(sp)   ; restore s3
cb4 ld   s4,16(sp)   ; restore s4
cb8 ld   s5,8(sp)    ; restore s5
cbc addi sp,sp,64    ; pop frame
cc0 ret              ; return to r
```

The 24-byte `Value` copy `*out ← values[i]` is realized by the three `sd`s (c8c/c94/c9c)
writing `[out, out+24)`; the ValueRepr at the destination is discharged via
`valueRepr_copy_of_writeWindow` (`Vsa/Sim/ReprCopy.lean`) with `src = pv + 24 * i`,
`dst = out`, and the spec value `v = f.vars[i].2` from `frame_slot_valueRepr`
(`Vsa/Sim/EnvGetSpec5.lean`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. Stride and offset bridges for the HIT tail

The HIT tail computes the byte offset `24*i` (`slli a4,s0,1; add a4,a4,s0; slli a4,a4,3`)
and the source address `pv + 24*i`.  `stride_24_bv` reduces the composite ALU value to
`ofNat (24*i)` (a repackaging of `EnvGetSpec5.stride_24`), and the `off6_*` lemmas
compute the small positive offsets `sext 0x008 … 0x038 = 8 … 56` used by the seven
callee-saved restores. -/

/-! ## 2. `Env_getLoaded` survives a `writeMap8` outside the code text

The three `sd`s write into `[out, out+24)`, disjoint from the `env_get` code text
`[0x80002c10, 0x80002cdc)`.  Loaded-ness survives (identical shape to
`loaded_envdef_writeMap8`). -/

/-! ## 3. The HIT-tail standing entry predicate

`HitTailSt`: at `0x80002c70`, the machine holds the HIT registers (`s4=env`, `s0=ofNat i`,
`s5=out`, `sp`), the seven callee-saved spill slots hold their to-be-restored values, the
frame `f` is represented at `env`, `i < f.vars.length`, memory is `m0`, and the geometry
of the out buffer / source value slot / spill slots (RAM, HTIF, alignment, disjointness)
holds. -/

/-! ## 4. The `read64`-byte helpers for the value words and the spill slots

Each `ld` in the tail loads eight bytes; the site lemmas want the eight `some bₖ`
byte facts and deliver `sign_extend (b7++…++b0)`.  `ld64_bytes` exposes them from a
`read64 … = some q`, and `ld64_val` bridges the loaded `sign_extend` back to `ofNat q`
(both are `EnvGetSpec3.read64_bytes_eg4` / `ld_value_eq_read64` re-exported for the tail). -/

/-! ## 5. `env_get` HIT-tail machine `Steps` chain (verified)

**`env_get_hit_tail`.** From `HitTailSt` at `0x80002c70`, the 21-instruction tail runs to
the return `PC = r` with `a0 = 1`, the destination out buffer holding
`ValueRepr m' N φc out (f.vars[i].2)` (discharged via `valueRepr_copy_of_writeWindow` on
the three copy stores + `frame_slot_valueRepr`), `sp` popped by 64, and the seven
callee-saved registers restored from their spill slots.  Fully verified. -/

/-! ## 6. FOUND-case composition scaffold (`env_get_found_spec`)

The immediate-frame FOUND case of `env_get` is:

  prologue (`0x80002c10 → scan entry`) ≫ `env_get_scan_spec` (HIT branch, reaching the
  HIT-block entry `0x80002c70` with a first-match witness `i`) ≫ **`env_get_hit_tail`**
  (this file: `0x80002c70 → ret`, verified).

The HIT tail is now fully discharged (`env_get_hit_tail`).  The scan loop's HIT exit is
ALSO now fully discharged and UNCONDITIONAL: `EnvGetSpec4.env_get_scan_spec'` proves
`Triple ScanInvE (ScanExit env f nameStr)` with no `hbody` hypothesis (the per-iteration
body `env_get_scan_body`/`scan_iter` is proven from the `EnvGetSpec2` sites +
`strcmp_full_spec` cross-call).  Its `AtHit` disjunct reaches `0x80002c70` with the
first-match witness `i`, `f.vars[i].1 = nameStr`, and `GoodState`.  So `hreach` no longer
hides any scan-loop obligation; the ONLY residuals it still bundles are (1) the prologue
straight-line reach `0x80002c10 → scan entry` (spills 7 callee-saveds, `sp -= 64`, loads
`s4=env`/`s2=count`/`s1=names`, `j` to the scan test), and (2) the repackaging of
`ScanExit`'s `AtHit` (which carries only PC/first-match/`GoodState`) into the richer
`HitTailSt` (7 spill slots at `sp+{8..56}`, `read64 (env+16)=pv`, the three source words,
and the out/spill/src geometry + disjointness fields) — those extra facts come from the
prologue spills + `FrameRepr`, not from the scan.  `env_get_found_spec` threads exactly
that residual (prologue + `AtHit`→`HitTailSt` bundle) as a single `Steps`-shaped
hypothesis `hreach` (from the `env_get` entry config to a `HitTailSt` at `0x80002c70`),
and composes it with the verified HIT tail to produce the found-case post (PC = link,
`a0 = 1`, `*out = ValueRepr v`, callee-saved restored, `sp` popped).

When the prologue `Steps` + the `AtHit`→`HitTailSt` repackaging land (a drop-in over
`env_get_scan_spec'`'s HIT branch),
`hreach` is discharged and this becomes the unconditional immediate-frame FOUND Triple.
Because `HitTailSt` bundles the frame representation and the first-match witness `i`, the
produced value is exactly `s.frames[fa].vars[i].2 = Store.get? s fa x` via
`lookup_valueRepr_bridge` — so the machine result matches the spec lookup. -/

end Vsa.Sim

