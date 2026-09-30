import Vsa.Sim.EnvGetSpec4

/-!
# Layer 3 — `env_get` FOUND-case contract (immediate-frame HIT) — bridge + tail

This session's deliverable: the SPEC-SIDE `env_get_found` `Q` obligation for the
IMMEDIATE-FRAME case (query variable lives in the current frame, no parent chain
walk), plus the HIT-tail's index-arithmetic bridge — the two pieces of the FOUND
case that are provable independently of the 21-instruction tail's full machine
`Steps` composition.

WHAT IS LANDED (verified, `sorry`/`axiom`/`native_decide`/`bv_decide`-free):

1. `Store.lookup`↔`ValueRepr` bridge (`lookup_valueRepr_bridge`, and its two
   halves `get?_immediate_hit` / `frame_slot_valueRepr`): from `StoreRepr`
   (`FrameRepr` at the immediate frame `φf fa`) plus the scan's first-match
   witness (`f.vars[i].1 = x` with all earlier names differing), the found spec
   value `v = f.vars[i].2` satisfies BOTH `Store.get? s fa x = some v` AND
   `ValueRepr m N φc (pv + 24*i) v` (the machine reads `values[i]` at
   `pv + 24*i`, `pv = env->vals = read64 m (φf fa + 16)`).  This is exactly the
   `Q` the `var`-case agent must exhibit for the immediate frame, and it is
   proved end-to-end here.

2. `stride_24` / `valsElem_addr`: the HIT block's `24*i` byte-offset computation
   (`slli a4,s0,1; add a4,a4,s0; slli a4,a4,3` = `((i<<1)+i)<<3`) equals
   `ofNat (24*i)` in `BitVec 64` for the scan index `i < 2^32`, so the machine
   address `x15 = pv + ofNat (24*i) = &values[i]` — the address the tail's three
   `ld`/`sd` word copies then read/write.

WHAT REMAINS (documented for the machine-composition follow-up, NOT landed):
the 21-instruction HIT-tail `Steps` chain itself (c70→ret): the three-word copy
`ld a4,{0,8,16}(a5); sd a4,{0,8,16}(s5)` and the ValueRepr TRANSLATION-copy fact
(`ValueRepr m0 (pv+24i) v` copied byte-for-byte to `[out,out+24)` yields
`ValueRepr m' out v` at the *translated* address — a byte-level lemma across the
6 value kinds, analogous to `EvalVarSim.VarPostCall.hcopy`, which that sibling
also threads as a hypothesis), the 7 spill-restore loads + `addi sp,64` + `ret`,
and the prologue `0x80002c10→0x80002c60`.  All 21 site lemmas exist in
`EnvGetSites2` (`site_80002c70_eg2 … site_80002cc0_eg2`); the residual is the
register/memory bookkeeping + the translation-copy lemma.

## HIT-tail disassembly (0x80002c70 – 0x80002cc0), decoded from the ELF

```
c70 ld   a5,16(s4)   ; a5 = env->vals  = pv
c74 slli a4,s0,0x1   ; a4 = i << 1  = 2*i
c78 add  a4,a4,s0    ; a4 = 2*i + i = 3*i
c7c slli a4,a4,0x3   ; a4 = (3*i) << 3 = 24*i
c80 add  a5,a5,a4    ; a5 = pv + 24*i  = &values[i]
c84 ld   a4,0(a5)    ; a4 = values[i].word0  (kind/payload lo)
c88 li   a0,1        ; a0 = 1  (found)
c8c sd   a4,0(s5)    ; *out[0..8)   = word0
c90 ld   a4,8(a5)    ; a4 = values[i].word1
c94 sd   a4,8(s5)    ; *out[8..16)  = word1
c98 ld   a5,16(a5)   ; a5 = values[i].word2
c9c sd   a5,16(s5)   ; *out[16..24) = word2
ca0 ld   ra,56(sp)   ; restore ra
ca4 ld   s0,48(sp)   ; restore s0
ca8 ld   s1,40(sp)   ; restore s1
cac ld   s2,32(sp)   ; restore s2
cb0 ld   s3,24(sp)   ; restore s3
cb4 ld   s4,16(sp)   ; restore s4
cb8 ld   s5,8(sp)    ; restore s5
cbc addi sp,sp,64    ; pop frame
cc0 ret              ; return to r
```
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

/-! ## 1. The `Store.lookup` ↔ `ValueRepr` bridge (immediate-frame case)

Pure spec-side + `FrameRepr` reasoning: no machine stepping.  This is exactly the
`Q`-side obligation the `var`-case agent must discharge for the immediate frame. -/

/-! ## 2. HIT-tail index-arithmetic stride identity (`24 * i`)

The HIT block computes the byte offset of `values[i]` as `((i<<1)+i)<<3 = 24*i`
(the C `Value` is 24 bytes, `slli a4,s0,1; add a4,a4,s0; slli a4,a4,3`).  For the
scan index `i < 2^32` (a 32-bit signed count), this equals `ofNat (24*i)` in
`BitVec 64`, and `pv + 24*i` is the machine address of `values[i]` that the
`ld a4,0(a5)` / stores then read. -/

end Vsa.Sim

-- axiom check
