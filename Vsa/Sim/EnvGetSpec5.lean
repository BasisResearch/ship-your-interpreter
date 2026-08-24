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

/-- **`Store.get?` on an immediate first-match.** If the store's frame at index
`fa` is `f`, and `f.vars` has a first-match for `x` at index `i` (all earlier
names differ, `f.vars[i].1 = x`), then `Store.get? s fa x = some (f.vars[i].2)`.
`fa < s.frames.size` (the frame is allocated) and there is at least one frame,
so the lookup gas `s.frames.size ≥ 1` suffices to fetch it. -/
theorem get?_immediate_hit (s : Store) (fa : Vsa.While.Addr) (x : String) (i : Nat)
    (hfa : fa < s.frames.size)
    (hi : i < s.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < i) →
      ¬ (s.frames[fa].vars[j]'(Nat.lt_trans hj hi)).1 = x)
    (hhit : (s.frames[fa].vars[i]).1 = x) :
    s.get? fa x = some (s.frames[fa].vars[i].2) := by
  -- gas = s.frames.size = (size-1)+1 ≥ 1
  have hpos : 0 < s.frames.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hfa
  obtain ⟨g, hg⟩ : ∃ g, s.frames.size = g + 1 := ⟨s.frames.size - 1, by omega⟩
  unfold Store.get?
  rw [hg]
  -- frame fetch
  have hfr : s.frames[fa]? = some s.frames[fa] := by
    rw [Array.getElem?_eq_getElem hfa]
  -- first match value; rewrite the pair to `(x, v)` using `f.vars[i].1 = x`
  have hfind0 : s.frames[fa].vars.find? (·.1 == x) = some (s.frames[fa].vars[i]) :=
    lookup_first_match s.frames[fa].vars x i hi hbelow hhit
  have hpair : s.frames[fa].vars[i] = (x, s.frames[fa].vars[i].2) := by
    rw [← hhit]
  have hfind : s.frames[fa].vars.find? (·.1 == x) = some (x, s.frames[fa].vars[i].2) := by
    rw [hfind0, hpair]
  exact lookup_hit_at s g fa x s.frames[fa] (s.frames[fa].vars[i].2) hfr hfind

/-- **`ValueRepr` of the found value** at `env->vals + 24*i`.  Straight off
`FrameRepr`'s slot-`i` conjunct: the value pointer `pv = read64 m (e+16)` and
`ValueRepr m N φc (pv + 24*i) (f.vars[i].2)`. -/
theorem frame_slot_valueRepr (m : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (f : Vsa.While.Frame) (i : Nat)
    (hFR : FrameRepr m N φf φc e f) (hi : i < f.vars.length) :
    ∃ pv, read64 m (e + 16) = some pv ∧ ValueRepr m N φc (pv + 24 * i) (f.vars[i].2) := by
  obtain ⟨_hcnt, _hcap, ⟨pn, pv, _hpn, hpv, hslots⟩, _hpar⟩ := hFR
  exact ⟨pv, hpv, (hslots i hi).2⟩

/-- **The combined immediate-frame FOUND bridge.**  From `StoreRepr` at frame
`fa` (`φf fa` its machine address) plus a first-match at index `i`, both the spec
verdict `Store.get? s fa x = some v` and the machine-visible witness
`ValueRepr m N φc (pv + 24*i) v` (with `pv = env->vals`) hold for the single
`v := s.frames[fa].vars[i].2`.  This is the `var`-case's `env_get_found` `Q` for
the immediate frame. -/
theorem lookup_valueRepr_bridge (m : Mem) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (s : Store) (fa : Vsa.While.Addr) (x : String) (i : Nat)
    (hSR : StoreRepr m N A φf φc s)
    (hfa : fa < s.frames.size)
    (hi : i < s.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < i) →
      ¬ (s.frames[fa].vars[j]'(Nat.lt_trans hj hi)).1 = x)
    (hhit : (s.frames[fa].vars[i]).1 = x) :
    ∃ v, s.get? fa x = some v ∧
      ∃ pv, read64 m (φf fa + 16) = some pv ∧ ValueRepr m N φc (pv + 24 * i) v := by
  refine ⟨s.frames[fa].vars[i].2, get?_immediate_hit s fa x i hfa hi hbelow hhit, ?_⟩
  exact frame_slot_valueRepr m N φf φc (φf fa) s.frames[fa] i (hSR.frames fa hfa) hi

/-! ## 2. HIT-tail index-arithmetic stride identity (`24 * i`)

The HIT block computes the byte offset of `values[i]` as `((i<<1)+i)<<3 = 24*i`
(the C `Value` is 24 bytes, `slli a4,s0,1; add a4,a4,s0; slli a4,a4,3`).  For the
scan index `i < 2^32` (a 32-bit signed count), this equals `ofNat (24*i)` in
`BitVec 64`, and `pv + 24*i` is the machine address of `values[i]` that the
`ld a4,0(a5)` / stores then read. -/

/-- `shift_bits_left v (extractLsb sh 5 0)` for a concrete small `sh` is `v <<< sh`. -/
theorem stride_24 (i : Nat) (h : i < 2^32) :
    (shift_bits_left
       ((shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0))
          + BitVec.ofNat 64 i)
       (Sail.BitVec.extractLsb (0x03#6) 5 0))
      = BitVec.ofNat 64 (24 * i) := by
  simp only [shift_bits_left]
  apply BitVec.eq_of_toNat_eq
  have hs1 : (Sail.BitVec.extractLsb (0x01#6) 5 0).toNat = 1 := by decide
  have hs3 : (Sail.BitVec.extractLsb (0x03#6) 5 0).toNat = 3 := by decide
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq']
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, hs1, hs3]
  simp only [Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : i < 2^64)]
  rw [Nat.mod_eq_of_lt (by omega : i * 2 < 2^64)]
  rw [Nat.mod_eq_of_lt (by omega : i * 2 + i < 2^64)]
  rw [Nat.mod_eq_of_lt (by omega : (i * 2 + i) * 8 < 2^64)]
  rw [Nat.mod_eq_of_lt (by omega : 24 * i < 2^64)]
  omega

/-- The `slli/add/slli/add` address computation lands `x15 = pv + ofNat (24*i)`,
i.e. `&values[i]`, when `x8 = ofNat i` (scan index) and `x15 = pv` (`env->vals`)
and `i < 2^32`.  Pure `BitVec` fact bridging the four ALU sites' composite value
`pv + (((i<<1)+i)<<3)` to `pv + ofNat (24*i)`. -/
theorem valsElem_addr (pv : BitVec 64) (i : Nat) (h : i < 2^32) :
    pv + (shift_bits_left
       ((shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0))
          + BitVec.ofNat 64 i)
       (Sail.BitVec.extractLsb (0x03#6) 5 0))
      = pv + BitVec.ofNat 64 (24 * i) := by
  rw [stride_24 i h]

end Vsa.Sim

-- axiom check
#print axioms Vsa.Sim.lookup_valueRepr_bridge
#print axioms Vsa.Sim.stride_24
#print axioms Vsa.Sim.get?_immediate_hit
#print axioms Vsa.Sim.frame_slot_valueRepr
#print axioms Vsa.Sim.valsElem_addr
