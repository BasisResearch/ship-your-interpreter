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

/-- The `slli;add;slli` chain lands `24*i` as a `BitVec`, given `x8 = ofNat i` and
`i < 2^32`. -/
theorem stride_24_bv (i : Nat) (h : i < 2^32) :
    (shift_bits_left
       ((shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0))
          + BitVec.ofNat 64 i)
       (Sail.BitVec.extractLsb (0x03#6) 5 0))
      = BitVec.ofNat 64 (24 * i) := stride_24 i h

/-- Small positive load offset: `(base + sext off).toNat = base.toNat + k` when
`sext off = k` (`k < 0x800`) and `base.toNat + k < 2^64`. -/
theorem off_pos_eg6 (base : BitVec 64) (off : BitVec 12) (k : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = k)
    (hnw : base.toNat + k < 2^64) :
    (base + sign_extend (m := 64) off).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, hoff, Nat.mod_eq_of_lt hnw]

/-- `read64` of a `writeMap8` window at a disjoint address passes through to `mem`
(byte-level from `getElem_writeMap8_disjoint`). -/
theorem read64_writeMap8_disjoint_eg6 (mem : Mem) (a a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-! ## 2. `Env_getLoaded` survives a `writeMap8` outside the code text

The three `sd`s write into `[out, out+24)`, disjoint from the `env_get` code text
`[0x80002c10, 0x80002cdc)`.  Loaded-ness survives (identical shape to
`loaded_envdef_writeMap8`). -/

theorem loaded_env_get_writeMap8_eg6 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80002c10 ∨ 0x80002cdc ≤ a8)
    (h : Env_getLoaded mem) : Env_getLoaded (writeMap8 mem a8 d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_getChunk0] at h0 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_getChunk1] at h1 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_getChunk2] at h2 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_getChunk3] at h3 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## 3. The HIT-tail standing entry predicate

`HitTailSt`: at `0x80002c70`, the machine holds the HIT registers (`s4=env`, `s0=ofNat i`,
`s5=out`, `sp`), the seven callee-saved spill slots hold their to-be-restored values, the
frame `f` is represented at `env`, `i < f.vars.length`, memory is `m0`, and the geometry
of the out buffer / source value slot / spill slots (RAM, HTIF, alignment, disjointness)
holds. -/
structure HitTailSt
    (g : (R : Register) → Option (RegisterType R))
    (env out sp r : BitVec 64) (rr r8 r9 r18 r19 r20 r21 : BitVec 64) (i : Nat) (pv : Nat)
    (w0 w1 w2 : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Env_getLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64)
  env4 : c.σ.regs.get? Register.x20 = some env    -- s4
  idx0 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)  -- s0
  out5 : c.σ.regs.get? Register.x21 = some out    -- s5
  sp2 : c.σ.regs.get? Register.x2 = some sp
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  -- frame representation and the value pointer
  frame : FrameRepr m0 N φf φc env.toNat f
  ilt : i < f.vars.length
  ismall : i < 2^32
  pv_eq : read64 m0 (env.toNat + 16) = some pv
  -- the three 8-byte words of the source value slot `values[i]` (the full 24-byte
  -- struct is initialized in the arena; ValueRepr only pins some of them, so their
  -- readability is carried explicitly).
  srcW0 : read64 m0 (pv + 24 * i) = some w0
  srcW1 : read64 m0 (pv + 24 * i + 8) = some w1
  srcW2 : read64 m0 (pv + 24 * i + 16) = some w2
  -- env->vals header slot [env+16, env+24) geometry (env lives in the arena)
  envLo : 0x80000000 ≤ env.toNat + 16
  envHi : env.toNat + 24 ≤ 0x100000000
  envWin : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  envAlign : (env.toNat + 16) % 8 = 0
  envNoWrap : env.toNat + 24 < 2^64
  -- out-buffer geometry
  outLo : 0x80000000 ≤ out.toNat
  outHi : out.toNat + 24 ≤ 0x100000000
  outWin : tohostAddr + 16 ≤ out.toNat
  outAlign : out.toNat % 8 = 0
  outCode : out.toNat + 24 ≤ 0x80002c10 ∨ 0x80002cdc ≤ out.toNat
  -- the seven callee-saved spill slots at [sp+8 .. sp+56]
  slotRa : read64 m0 (sp.toNat + 56) = some rr.toNat
  slotS0 : read64 m0 (sp.toNat + 48) = some r8.toNat
  slotS1 : read64 m0 (sp.toNat + 40) = some r9.toNat
  slotS2 : read64 m0 (sp.toNat + 32) = some r18.toNat
  slotS3 : read64 m0 (sp.toNat + 24) = some r19.toNat
  slotS4 : read64 m0 (sp.toNat + 16) = some r20.toNat
  slotS5 : read64 m0 (sp.toNat + 8) = some r21.toNat
  rr_eq : rr = r                       -- restored ra becomes the caller link r
  -- spill-window geometry (each slot in RAM, above HTIF, 8-aligned)
  spLo : 0x80000000 ≤ sp.toNat + 8
  spHi : sp.toNat + 64 ≤ 0x100000000
  spWin : tohostAddr + 16 ≤ sp.toNat + 8
  spAlign : sp.toNat % 8 = 0
  spNoWrap : sp.toNat + 64 < 2^64
  -- source value slot geometry (RAM, HTIF, aligned, no wrap)
  srcLo : 0x80000000 ≤ pv + 24 * i
  srcHi : pv + 24 * i + 24 ≤ 0x100000000
  srcWin : tohostAddr + 16 ≤ pv + 24 * i
  srcAlign : (pv + 24 * i) % 8 = 0
  srcNoWrap : pv + 24 * i + 24 < 2^64
  pvNoWrap : pv + 24 * i < 2^64
  -- disjointness: source value slot disjoint from destination out buffer
  src_out_disjoint : pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i
  -- disjointness: out buffer disjoint from the spill window (restores read old bytes)
  out_spill_disjoint : out.toNat + 24 ≤ sp.toNat + 8 ∨ sp.toNat + 64 ≤ out.toNat
  -- the found value's heap string payload (at `read64 m0 (pv+24i+8)`, if any) lives in a
  -- region disjoint from the destination out buffer `[out, out+24)` — the string is in
  -- the arena / rodata, the out buffer is the caller's sret slot.  This is the payload
  -- hypothesis `valueRepr_copy_of_writeWindow` consumes for the `.str`/`.native` kinds.
  payDisj : ∀ (p : Nat) (s : String), read64 m0 (pv + 24 * i + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k)
  -- return-address alignment
  rAlign : r.toNat % 4 = 0

/-! ## 4. The `read64`-byte helpers for the value words and the spill slots

Each `ld` in the tail loads eight bytes; the site lemmas want the eight `some bₖ`
byte facts and deliver `sign_extend (b7++…++b0)`.  `ld64_bytes` exposes them from a
`read64 … = some q`, and `ld64_val` bridges the loaded `sign_extend` back to `ofNat q`
(both are `EnvGetSpec3.read64_bytes_eg4` / `ld_value_eq_read64` re-exported for the tail). -/

theorem ld64_bytes (mem : Mem) (a q : Nat) (h : read64 mem a = some q) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem[a]? = some b0 ∧ mem[a+1]? = some b1 ∧ mem[a+2]? = some b2 ∧
      mem[a+3]? = some b3 ∧ mem[a+4]? = some b4 ∧ mem[a+5]? = some b5 ∧
      mem[a+6]? = some b6 ∧ mem[a+7]? = some b7 :=
  let ⟨b0,b1,b2,b3,b4,b5,b6,b7,e0,e1,e2,e3,e4,e5,e6,e7,_⟩ := read64_bytes_eg4 mem a q h
  ⟨b0,b1,b2,b3,b4,b5,b6,b7,e0,e1,e2,e3,e4,e5,e6,e7⟩

/-! ## 5. `env_get` HIT-tail machine `Steps` chain (verified)

**`env_get_hit_tail`.** From `HitTailSt` at `0x80002c70`, the 21-instruction tail runs to
the return `PC = r` with `a0 = 1`, the destination out buffer holding
`ValueRepr m' N φc out (f.vars[i].2)` (discharged via `valueRepr_copy_of_writeWindow` on
the three copy stores + `frame_slot_valueRepr`), `sp` popped by 64, and the seven
callee-saved registers restored from their spill slots.  Fully verified. -/
theorem env_get_hit_tail
    (g : (R : Register) → Option (RegisterType R))
    (env out sp r : BitVec 64) (rr r8 r9 r18 r19 r20 r21 : BitVec 64) (i : Nat) (pv : Nat)
    (w0 w1 w2 : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) (hi : i < f.vars.length)
    (hSt : HitTailSt g env out sp r rr r8 r9 r18 r19 r20 r21 i pv w0 w1 w2 f N φf φc m0 c) :
    ∃ (c' : Config) (m' : Mem),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some r ∧
      c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.regs.get? Register.x2 = some (sp + 64#64) ∧
      c'.σ.regs.get? Register.x8 = some r8 ∧
      c'.σ.regs.get? Register.x9 = some r9 ∧
      c'.σ.regs.get? Register.x18 = some r18 ∧
      c'.σ.regs.get? Register.x19 = some r19 ∧
      c'.σ.regs.get? Register.x20 = some r20 ∧
      c'.σ.regs.get? Register.x21 = some r21 ∧
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      ValueRepr m' N φc out.toNat (f.vars[i]'hi).2 ∧
      (∀ a : Nat, ¬ (out.toNat ≤ a ∧ a < out.toNat + 24) → m'[a]? = m0[a]?) ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have hmem := hSt.mem
  have hloaded0 : Env_getLoaded m0 := hmem ▸ hSt.loadedG
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- the value pointer `pv` and the FrameRepr slot-`i` ValueRepr at `pv + 24*i`.
  obtain ⟨pv', hpv', hvr⟩ := frame_slot_valueRepr m0 N φf φc env.toNat f i hSt.frame hi
  have hpvenv := hSt.pv_eq
  have hpveq : pv' = pv := by rw [hpv'] at hpvenv; injection hpvenv
  rw [hpveq] at hvr
  have hout := hSt.out5
  -- convenient RAM bound
  have hram2_32 : (0x100000000 : Nat) = 2^32 := by decide
  -- ============ c70: ld a5,16(s4) → x15 := ofNat pv (env->vals) ============
  -- the value pointer read via read64
  have henv16 : read64 m0 (env.toNat + 16) = some pv := hSt.pv_eq
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7, q0,q1,q2,q3,q4,q5,q6,q7⟩ := ld64_bytes m0 (env.toNat + 16) pv henv16
  -- FrameRepr gives env in RAM etc; we need the c70 load-address side conditions.
  -- env->vals slot [env+16, env+24) : use header geometry from src facts is not enough;
  -- derive from read64 (the slot is readable) + the header disjointness carried below.
  -- Compute the c70 load address = env + sext 0x10.
  have hc70addr : (env + sign_extend (m := 64) (0x010#12)).toNat = env.toNat + 16 :=
    off_pos_eg6 env (0x010#12) 16 (by decide) (by have := hSt.envNoWrap; omega)
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80002c70_eg2 c.σ c.tick c.steps (0x80002c70#64) vmi env
      p0 p1 p2 p3 p4 p5 p6 p7 hSt.good hSt.pc hmi hSt.env4 hSt.loadedG rfl
      (by rw [hc70addr]; exact hSt.envLo) (by rw [hc70addr]; have := hSt.envHi; omega)
      (by rw [hc70addr]; exact hSt.envWin) (by rw [hc70addr]; exact hSt.envAlign)
      (by rw [hc70addr, hmem]; exact q0) (by rw [hc70addr, hmem]; exact q1)
      (by rw [hc70addr, hmem]; exact q2) (by rw [hc70addr, hmem]; exact q3)
      (by rw [hc70addr, hmem]; exact q4) (by rw [hc70addr, hmem]; exact q5)
      (by rw [hc70addr, hmem]; exact q6) (by rw [hc70addr, hmem]; exact q7) hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = m0 := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002c74#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002c70#64) 4 = (0x80002c74#64:BitVec 64) from by decide] at this
  -- x15 = loaded value = ofNat pv
  have hpvval : (sign_extend (m := 64)
      ((((((((p7.append p6).append p5).append p4).append p3).append p2).append p1).append p0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 pv :=
    ld_value_eq_read64 m0 (env.toNat + 16) pv p0 p1 p2 p3 p4 p5 p6 p7 henv16 q0 q1 q2 q3 q4 q5 q6 q7
  have hx15_1 : σ1.regs.get? Register.x15 = some (BitVec.ofNat 64 pv) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hpvval] at this
  have hs0_1 : σ1.regs.get? Register.x8 = some (BitVec.ofNat 64 i) :=
    obs_alu_other' hobs1 Register.x8 (by decide) hSt.idx0
  have hs5_1 : σ1.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs1 Register.x21 (by decide) hout
  have hsp_1 : σ1.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs1 Register.x2 (by decide) hSt.sp2
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Env_getLoaded σ1.mem := by rw [hmem1e]; exact hloaded0
  -- ============ c74: slli a4,s0,1 → x14 := i<<1 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80002c74_eg2 σ1 i1 (c.steps+1) (0x80002c74#64) vmi1 (BitVec.ofNat 64 i) hG1 hpc1 hmi1 hs0_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = m0 := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002c78#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80002c74#64) 4 = (0x80002c78#64:BitVec 64) from by decide] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs0_2 : σ2.regs.get? Register.x8 = some (BitVec.ofNat 64 i) :=
    obs_alu_other' hobs2 Register.x8 (by decide) hs0_1
  have hx15_2 : σ2.regs.get? Register.x15 = some (BitVec.ofNat 64 pv) :=
    obs_alu_other' hobs2 Register.x15 (by decide) hx15_1
  have hs5_2 : σ2.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs2 Register.x21 (by decide) hs5_1
  have hsp_2 : σ2.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Env_getLoaded σ2.mem := by rw [hmem2e]; exact hloaded0
  -- ============ c78: add a4,a4,s0 → x14 := 3i ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80002c78_eg2 σ2 i2 (c.steps+1+1) (0x80002c78#64) vmi2 (BitVec.ofNat 64 i) _ hG2 hpc2 hmi2 hs0_2 hx14_2 hcode2 rfl hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = m0 := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002c7c#64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80002c78#64) 4 = (0x80002c7c#64:BitVec 64) from by decide] at this
  have hx14_3 : σ3.regs.get? Register.x14 = some (shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0) + BitVec.ofNat 64 i) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_3 : σ3.regs.get? Register.x15 = some (BitVec.ofNat 64 pv) :=
    obs_alu_other' hobs3 Register.x15 (by decide) hx15_2
  have hs5_3 : σ3.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs3 Register.x21 (by decide) hs5_2
  have hsp_3 : σ3.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Env_getLoaded σ3.mem := by rw [hmem3e]; exact hloaded0
  -- ============ c7c: slli a4,a4,3 → x14 := 24i ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80002c7c_eg2 σ3 i3 (c.steps+1+1+1) (0x80002c7c#64) vmi3 _ hG3 hpc3 hmi3 hx14_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3,i3,c.steps+1+1+1⟩ ⟨σ4,i4,c.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = m0 := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002c80#64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80002c7c#64) 4 = (0x80002c80#64:BitVec 64) from by decide] at this
  -- the 24i stride value = ofNat (24*i)
  have h24i : (shift_bits_left (shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0) + BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x03#6) 5 0)) = BitVec.ofNat 64 (24 * i) :=
    stride_24_bv i hSt.ismall
  have hx14_4 : σ4.regs.get? Register.x14 = some (BitVec.ofNat 64 (24 * i)) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [h24i] at this
  have hx15_4 : σ4.regs.get? Register.x15 = some (BitVec.ofNat 64 pv) :=
    obs_alu_other' hobs4 Register.x15 (by decide) hx15_3
  have hs5_4 : σ4.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs4 Register.x21 (by decide) hs5_3
  have hsp_4 : σ4.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hcode4 : Env_getLoaded σ4.mem := by rw [hmem4e]; exact hloaded0
  -- ============ c80: add a5,a5,a4 → x15 := ofNat (pv + 24i) ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_80002c80_eg2 σ4 i4 (c.steps+1+1+1+1) (0x80002c80#64) vmi4 _ _ hG4 hpc4 hmi4 hx14_4 hx15_4 hcode4 rfl hi4
  have hstep5 : Step ⟨σ4,i4,c.steps+1+1+1+1⟩ ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hstep5'
  have hmem5e : σ5.mem = m0 := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002c84#64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80002c80#64) 4 = (0x80002c84#64:BitVec 64) from by decide] at this
  have hpvnw := hSt.pvNoWrap
  have hpvlt : pv < 2^64 := by omega
  have h24ilt : 24 * i < 2^64 := by omega
  have hsrcaddr : (BitVec.ofNat 64 pv + BitVec.ofNat 64 (24 * i)) = BitVec.ofNat 64 (pv + 24 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hpvlt, Nat.mod_eq_of_lt h24ilt, Nat.mod_eq_of_lt hpvnw]
  have hx15_5 : σ5.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsrcaddr] at this
  have hs5_5 : σ5.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs5 Register.x21 (by decide) hs5_4
  have hsp_5 : σ5.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hcode5 : Env_getLoaded σ5.mem := by rw [hmem5e]; exact hloaded0
  -- source-slot byte facts for the three words
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7, ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7⟩ := ld64_bytes m0 (pv + 24 * i) w0 hSt.srcW0
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7, hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7⟩ := ld64_bytes m0 (pv + 24 * i + 8) w1 hSt.srcW1
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7, he0,he1,he2,he3,he4,he5,he6,he7⟩ := ld64_bytes m0 (pv + 24 * i + 16) w2 hSt.srcW2
  -- the c84 load address = x15 + sext 0 = pv+24i
  have hofpv : (BitVec.ofNat 64 (pv + 24 * i)).toNat = pv + 24 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSt.pvNoWrap]
  have hnw84 : (BitVec.ofNat 64 (pv + 24 * i)).toNat + 0 < 2^64 := by
    rw [hofpv]; have := hSt.pvNoWrap; omega
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]
    rfl
  have hc84addr : (BitVec.ofNat 64 (pv + 24 * i) + sign_extend (m := 64) (0x000#12)).toNat = pv + 24 * i := by
    rw [off_pos_eg6 (BitVec.ofNat 64 (pv + 24 * i)) (0x000#12) 0 hsext0 hnw84, hofpv]; omega
  have hsrc_align : (pv + 24 * i) % 8 = 0 := by
    have := hSt.srcAlign; exact this
  -- ============ c84: ld a4,0(a5) → x14 := ofNat w0 ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80002c84_eg2 σ5 i5 (c.steps+1+1+1+1+1) (0x80002c84#64) vmi5 (BitVec.ofNat 64 (pv + 24 * i))
      a0 a1 a2 a3 a4 a5 a6 a7 hG5 hpc5 hmi5 hx15_5 hcode5 rfl
      (by rw [hc84addr]; have := hSt.srcLo; omega) (by rw [hc84addr]; have := hSt.srcHi; omega)
      (by rw [hc84addr]; right; rw [htoh]; have := hSt.srcWin; rw [htoh] at this; omega)
      (by rw [hc84addr]; exact hsrc_align)
      (by rw [hc84addr, hmem5e]; exact ha0) (by rw [hc84addr, hmem5e]; exact ha1)
      (by rw [hc84addr, hmem5e]; exact ha2) (by rw [hc84addr, hmem5e]; exact ha3)
      (by rw [hc84addr, hmem5e]; exact ha4) (by rw [hc84addr, hmem5e]; exact ha5)
      (by rw [hc84addr, hmem5e]; exact ha6) (by rw [hc84addr, hmem5e]; exact ha7) hi5
  have hstep6 : Step ⟨σ5,i5,c.steps+1+1+1+1+1⟩ ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hstep6'
  have hmem6e : σ6.mem = m0 := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002c88#64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80002c84#64) 4 = (0x80002c88#64:BitVec 64) from by decide] at this
  have hw0val : (sign_extend (m := 64) ((((((((a7.append a6).append a5).append a4).append a3).append a2).append a1).append a0) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 w0 :=
    ld_value_eq_read64 m0 (pv + 24 * i) w0 a0 a1 a2 a3 a4 a5 a6 a7 hSt.srcW0 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hx14_6 : σ6.regs.get? Register.x14 = some (BitVec.ofNat 64 w0) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hw0val] at this
  have hx15_6 : σ6.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) :=
    obs_alu_other' hobs6 Register.x15 (by decide) hx15_5
  have hs5_6 : σ6.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs6 Register.x21 (by decide) hs5_5
  have hsp_6 : σ6.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs6 Register.x2 (by decide) hsp_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hcode6 : Env_getLoaded σ6.mem := by rw [hmem6e]; exact hloaded0
  -- ============ c88: li a0,1 → x10 := 1 ============
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80002c88_eg2 σ6 i6 (c.steps+1+1+1+1+1+1) (0x80002c88#64) vmi6 hG6 hpc6 hmi6 hcode6 rfl hi6
  have hstep7 : Step ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hstep7'
  have hmem7e : σ7.mem = m0 := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80002c8c#64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80002c88#64) 4 = (0x80002c8c#64:BitVec 64) from by decide] at this
  have ha0_7 : σ7.regs.get? Register.x10 = some (1#64 : BitVec 64) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = (1#64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_7 : σ7.regs.get? Register.x14 = some (BitVec.ofNat 64 w0) :=
    obs_alu_other' hobs7 Register.x14 (by decide) hx14_6
  have hx15_7 : σ7.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) :=
    obs_alu_other' hobs7 Register.x15 (by decide) hx15_6
  have hs5_7 : σ7.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs7 Register.x21 (by decide) hs5_6
  have hsp_7 : σ7.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hcode7 : Env_getLoaded σ7.mem := by rw [hmem7e]; exact hloaded0
  -- store-address helpers (out+0/+8/+16)
  have hout0 : (out + sign_extend (m := 64) (0x000#12)).toNat = out.toNat :=
    off_pos_eg6 out (0x000#12) 0 hsext0 (by have := out.isLt; omega)
  have hsext8 : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  have hsext16 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
  have hout8 : (out + sign_extend (m := 64) (0x008#12)).toNat = out.toNat + 8 :=
    off_pos_eg6 out (0x008#12) 8 hsext8 (by have := hSt.outHi; omega)
  have hout16 : (out + sign_extend (m := 64) (0x010#12)).toNat = out.toNat + 16 :=
    off_pos_eg6 out (0x010#12) 16 hsext16 (by have := hSt.outHi; omega)
  -- ============ c8c: sd a4,0(s5) → *out[0..8) := w0 ============
  obtain ⟨σ8, i8, hstep8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80002c8c_eg2 σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80002c8c#64) vmi7 out (BitVec.ofNat 64 w0)
      hG7 hpc7 hmi7 hs5_7 hx14_7 hcode7 rfl
      (by rw [hout0]; exact hSt.outLo) (by rw [hout0]; have := hSt.outHi; omega)
      (by rw [hout0]; exact hSt.outWin) (by rw [hout0]; exact hSt.outAlign) hi7
  have hstep8 : Step ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hstep8'
  have hm8def : σ8.mem = writeMap8 m0 out.toNat (sdData_val (BitVec.ofNat 64 w0)) := by
    rw [hmem8, mem_afterNextPC, mem_afterPrelude, hmem7e, hout0]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80002c90#64) := by
    have := obs_store_pc hobs8; rwa [show BitVec.addInt (0x80002c8c#64) 4 = (0x80002c90#64:BitVec 64) from by decide] at this
  have hx15_8 : σ8.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) :=
    obs_store_other' hobs8 Register.x15 (by decide) hx15_7
  have ha0_8 : σ8.regs.get? Register.x10 = some (1#64 : BitVec 64) :=
    obs_store_other' hobs8 Register.x10 (by decide) ha0_7
  have hs5_8 : σ8.regs.get? Register.x21 = some out :=
    obs_store_other' hobs8 Register.x21 (by decide) hs5_7
  have hsp_8 : σ8.regs.get? Register.x2 = some sp :=
    obs_store_other' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have houtCode8 : out.toNat + 8 ≤ 0x80002c10 ∨ 0x80002cdc ≤ out.toNat := by
    rcases hSt.outCode with h | h
    · left; omega
    · right; omega
  have hcode8 : Env_getLoaded σ8.mem := by
    rw [hm8def]; exact loaded_env_get_writeMap8_eg6 m0 out.toNat _ houtCode8 hloaded0
  -- word1 at pv+24i+8: read from σ8.mem = writeMap8 m0 out … ; disjoint ⇒ = m0 read
  have hdisj_src8_out : (pv + 24 * i + 8) + 8 ≤ out.toNat ∨ out.toNat + 8 ≤ (pv + 24 * i + 8) := by
    rcases hSt.src_out_disjoint with h | h
    · left; omega
    · right; omega
  have hw1_8 : read64 σ8.mem (pv + 24 * i + 8) = some w1 := by
    rw [hm8def, read64_writeMap8_disjoint_eg6 _ _ _ _ hdisj_src8_out]; exact hSt.srcW1
  obtain ⟨g0,g1,g2,g3,g4,g5,g6,g7, hg0,hg1,hg2,hg3,hg4,hg5,hg6,hg7⟩ := ld64_bytes σ8.mem (pv + 24 * i + 8) w1 hw1_8
  -- c90 load address = x15 + sext 8 = pv+24i+8
  have hc90addr : (BitVec.ofNat 64 (pv + 24 * i) + sign_extend (m := 64) (0x008#12)).toNat = pv + 24 * i + 8 := by
    rw [off_pos_eg6 (BitVec.ofNat 64 (pv + 24 * i)) (0x008#12) 8 hsext8 (by rw [hofpv]; have := hSt.srcNoWrap; omega), hofpv]
  -- ============ c90: ld a4,8(a5) → x14 := ofNat w1 ============
  obtain ⟨σ9, i9, hstep9', hi9, hG9, hmem9, hobs9⟩ :=
    site_80002c90_eg2 σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80002c90#64) vmi8 (BitVec.ofNat 64 (pv + 24 * i))
      g0 g1 g2 g3 g4 g5 g6 g7 hG8 hpc8 hmi8 hx15_8 hcode8 rfl
      (by rw [hc90addr]; have := hSt.srcLo; omega) (by rw [hc90addr]; have := hSt.srcHi; omega)
      (by rw [hc90addr]; right; rw [htoh]; have := hSt.srcWin; rw [htoh] at this; omega)
      (by rw [hc90addr]; have := hSt.srcAlign; omega)
      (by rw [hc90addr]; exact hg0) (by rw [hc90addr]; exact hg1)
      (by rw [hc90addr]; exact hg2) (by rw [hc90addr]; exact hg3)
      (by rw [hc90addr]; exact hg4) (by rw [hc90addr]; exact hg5)
      (by rw [hc90addr]; exact hg6) (by rw [hc90addr]; exact hg7) hi8
  have hstep9 : Step ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hstep9'
  have hm9def : σ9.mem = σ8.mem := hmem9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80002c94#64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80002c90#64) 4 = (0x80002c94#64:BitVec 64) from by decide] at this
  have hw1val : (sign_extend (m := 64) ((((((((g7.append g6).append g5).append g4).append g3).append g2).append g1).append g0) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 w1 :=
    ld_value_eq_read64 σ8.mem (pv + 24 * i + 8) w1 g0 g1 g2 g3 g4 g5 g6 g7 hw1_8 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  have hx14_9 : σ9.regs.get? Register.x14 = some (BitVec.ofNat 64 w1) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hw1val] at this
  have hx15_9 : σ9.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) :=
    obs_alu_other' hobs9 Register.x15 (by decide) hx15_8
  have ha0_9 : σ9.regs.get? Register.x10 = some (1#64 : BitVec 64) :=
    obs_alu_other' hobs9 Register.x10 (by decide) ha0_8
  have hs5_9 : σ9.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs9 Register.x21 (by decide) hs5_8
  have hsp_9 : σ9.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hcode9 : Env_getLoaded σ9.mem := by rw [hm9def]; exact hcode8
  -- ============ c94: sd a4,8(s5) → *out[8..16) := w1  (m9 = σ8.mem = writeMap8 m0 out w0) ============
  obtain ⟨σ10, i10, hstep10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80002c94_eg2 σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80002c94#64) vmi9 out (BitVec.ofNat 64 w1)
      hG9 hpc9 hmi9 hs5_9 hx14_9 hcode9 rfl
      (by rw [hout8]; have := hSt.outLo; omega) (by rw [hout8]; have := hSt.outHi; omega)
      (by rw [hout8]; have := hSt.outWin; rw [htoh] at *; omega) (by rw [hout8]; have := hSt.outAlign; omega) hi9
  have hstep10 : Step ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hstep10'
  have hm10def : σ10.mem = writeMap8 σ8.mem (out.toNat + 8) (sdData_val (BitVec.ofNat 64 w1)) := by
    rw [hmem10, mem_afterNextPC, mem_afterPrelude, hm9def, hout8]
  have hpc10 : σ10.regs.get? Register.PC = some (0x80002c98#64) := by
    have := obs_store_pc hobs10; rwa [show BitVec.addInt (0x80002c94#64) 4 = (0x80002c98#64:BitVec 64) from by decide] at this
  have hx15_10 : σ10.regs.get? Register.x15 = some (BitVec.ofNat 64 (pv + 24 * i)) :=
    obs_store_other' hobs10 Register.x15 (by decide) hx15_9
  have ha0_10 : σ10.regs.get? Register.x10 = some (1#64 : BitVec 64) :=
    obs_store_other' hobs10 Register.x10 (by decide) ha0_9
  have hs5_10 : σ10.regs.get? Register.x21 = some out :=
    obs_store_other' hobs10 Register.x21 (by decide) hs5_9
  have hsp_10 : σ10.regs.get? Register.x2 = some sp :=
    obs_store_other' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret hobs10
  have hcode10 : Env_getLoaded σ10.mem := by
    rw [hm10def]
    exact loaded_env_get_writeMap8_eg6 σ8.mem (out.toNat + 8) _
      (by rcases hSt.outCode with h | h <;> omega) hcode8
  -- word2 at pv+24i+16: read from σ10.mem = writeMap8 (writeMap8 m0 out w0) (out+8) w1 ; disjoint ⇒ m0
  have hdisj_src16_out0 : (pv + 24 * i + 16) + 8 ≤ out.toNat ∨ out.toNat + 8 ≤ (pv + 24 * i + 16) := by
    rcases hSt.src_out_disjoint with h | h
    · left; omega
    · right; omega
  have hdisj_src16_out8 : (pv + 24 * i + 16) + 8 ≤ out.toNat + 8 ∨ (out.toNat + 8) + 8 ≤ (pv + 24 * i + 16) := by
    rcases hSt.src_out_disjoint with h | h
    · left; omega
    · right; omega
  have hw2_10 : read64 σ10.mem (pv + 24 * i + 16) = some w2 := by
    rw [hm10def, read64_writeMap8_disjoint_eg6 _ _ _ _ hdisj_src16_out8, hm8def,
        read64_writeMap8_disjoint_eg6 _ _ _ _ hdisj_src16_out0]
    exact hSt.srcW2
  obtain ⟨k0,k1,k2,k3,k4,k5,k6,k7, hk0,hk1,hk2,hk3,hk4,hk5,hk6,hk7⟩ := ld64_bytes σ10.mem (pv + 24 * i + 16) w2 hw2_10
  have hc98addr : (BitVec.ofNat 64 (pv + 24 * i) + sign_extend (m := 64) (0x010#12)).toNat = pv + 24 * i + 16 := by
    rw [off_pos_eg6 (BitVec.ofNat 64 (pv + 24 * i)) (0x010#12) 16 hsext16 (by rw [hofpv]; have := hSt.srcNoWrap; omega), hofpv]
  -- ============ c98: ld a5,16(a5) → x15 := ofNat w2 ============
  obtain ⟨σ11, i11, hstep11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80002c98_eg2 σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80002c98#64) vmi10 (BitVec.ofNat 64 (pv + 24 * i))
      k0 k1 k2 k3 k4 k5 k6 k7 hG10 hpc10 hmi10 hx15_10 hcode10 rfl
      (by rw [hc98addr]; have := hSt.srcLo; omega) (by rw [hc98addr]; have := hSt.srcHi; omega)
      (by rw [hc98addr]; right; rw [htoh]; have := hSt.srcWin; rw [htoh] at this; omega)
      (by rw [hc98addr]; have := hSt.srcAlign; omega)
      (by rw [hc98addr]; exact hk0) (by rw [hc98addr]; exact hk1)
      (by rw [hc98addr]; exact hk2) (by rw [hc98addr]; exact hk3)
      (by rw [hc98addr]; exact hk4) (by rw [hc98addr]; exact hk5)
      (by rw [hc98addr]; exact hk6) (by rw [hc98addr]; exact hk7) hi10
  have hstep11 : Step ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep11'
  have hm11def : σ11.mem = σ10.mem := hmem11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80002c9c#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80002c98#64) 4 = (0x80002c9c#64:BitVec 64) from by decide] at this
  have hw2val : (sign_extend (m := 64) ((((((((k7.append k6).append k5).append k4).append k3).append k2).append k1).append k0) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 w2 :=
    ld_value_eq_read64 σ10.mem (pv + 24 * i + 16) w2 k0 k1 k2 k3 k4 k5 k6 k7 hw2_10 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  have hx15_11 : σ11.regs.get? Register.x15 = some (BitVec.ofNat 64 w2) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hw2val] at this
  have ha0_11 : σ11.regs.get? Register.x10 = some (1#64 : BitVec 64) :=
    obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  have hs5_11 : σ11.regs.get? Register.x21 = some out :=
    obs_alu_other' hobs11 Register.x21 (by decide) hs5_10
  have hsp_11 : σ11.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hcode11 : Env_getLoaded σ11.mem := by rw [hm11def]; exact hcode10
  -- ============ c9c: sd a5,16(s5) → *out[16..24) := w2 ============
  obtain ⟨σ12, i12, hstep12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80002c9c_eg2 σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80002c9c#64) vmi11 out (BitVec.ofNat 64 w2)
      hG11 hpc11 hmi11 hs5_11 hx15_11 hcode11 rfl
      (by rw [hout16]; have := hSt.outLo; omega) (by rw [hout16]; have := hSt.outHi; omega)
      (by rw [hout16]; have := hSt.outWin; rw [htoh] at *; omega) (by rw [hout16]; have := hSt.outAlign; omega) hi11
  have hstep12 : Step ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep12'
  have hm12def : σ12.mem = writeMap8 σ10.mem (out.toNat + 16) (sdData_val (BitVec.ofNat 64 w2)) := by
    rw [hmem12, mem_afterNextPC, mem_afterPrelude, hm11def, hout16]
  have hpc12 : σ12.regs.get? Register.PC = some (0x80002ca0#64) := by
    have := obs_store_pc hobs12; rwa [show BitVec.addInt (0x80002c9c#64) 4 = (0x80002ca0#64:BitVec 64) from by decide] at this
  have ha0_12 : σ12.regs.get? Register.x10 = some (1#64 : BitVec 64) :=
    obs_store_other' hobs12 Register.x10 (by decide) ha0_11
  have hsp_12 : σ12.regs.get? Register.x2 = some sp :=
    obs_store_other' hobs12 Register.x2 (by decide) hsp_11
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
  have hcode12 : Env_getLoaded σ12.mem := by
    rw [hm12def]
    exact loaded_env_get_writeMap8_eg6 σ10.mem (out.toNat + 16) _
      (by rcases hSt.outCode with h | h <;> omega) hcode10
  -- fully-unfolded final memory
  have hm12full : σ12.mem = writeMap8 (writeMap8 (writeMap8 m0 out.toNat (sdData_val (BitVec.ofNat 64 w0)))
      (out.toNat + 8) (sdData_val (BitVec.ofNat 64 w1))) (out.toNat + 16) (sdData_val (BitVec.ofNat 64 w2)) := by
    rw [hm12def, hm10def, hm8def]
  -- any 8-byte read disjoint from [out, out+24) passes through σ12.mem → m0
  have read64_final_disjoint : ∀ a : Nat, a + 8 ≤ out.toNat ∨ out.toNat + 24 ≤ a →
      read64 σ12.mem a = read64 m0 a := by
    intro a ha
    rw [hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by rcases ha with h | h <;> omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by rcases ha with h | h <;> omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by rcases ha with h | h <;> omega)]
  -- the seven spill-slot readbacks in σ12 (each disjoint from [out, out+24))
  have hdOut : ∀ k : Nat, sp.toNat + 8 ≤ sp.toNat + k → sp.toNat + k + 8 ≤ sp.toNat + 64 →
      (sp.toNat + k) + 8 ≤ out.toNat ∨ out.toNat + 24 ≤ (sp.toNat + k) := by
    intro k h1 h2
    rcases hSt.out_spill_disjoint with h | h
    · right; omega
    · left; omega
  have hsRa : read64 σ12.mem (sp.toNat + 56) = some rr.toNat := by
    rw [read64_final_disjoint _ (hdOut 56 (by omega) (by omega))]; exact hSt.slotRa
  have hsS0 : read64 σ12.mem (sp.toNat + 48) = some r8.toNat := by
    rw [read64_final_disjoint _ (hdOut 48 (by omega) (by omega))]; exact hSt.slotS0
  have hsS1 : read64 σ12.mem (sp.toNat + 40) = some r9.toNat := by
    rw [read64_final_disjoint _ (hdOut 40 (by omega) (by omega))]; exact hSt.slotS1
  have hsS2 : read64 σ12.mem (sp.toNat + 32) = some r18.toNat := by
    rw [read64_final_disjoint _ (hdOut 32 (by omega) (by omega))]; exact hSt.slotS2
  have hsS3 : read64 σ12.mem (sp.toNat + 24) = some r19.toNat := by
    rw [read64_final_disjoint _ (hdOut 24 (by omega) (by omega))]; exact hSt.slotS3
  have hsS4 : read64 σ12.mem (sp.toNat + 16) = some r20.toNat := by
    rw [read64_final_disjoint _ (hdOut 16 (by omega) (by omega))]; exact hSt.slotS4
  have hsS5 : read64 σ12.mem (sp.toNat + 8) = some r21.toNat := by
    rw [read64_final_disjoint _ (hdOut 8 (by omega) (by omega))]; exact hSt.slotS5
  -- byte facts for the seven spill slots
  obtain ⟨ra0,ra1,ra2,ra3,ra4,ra5,ra6,ra7, hra0,hra1,hra2,hra3,hra4,hra5,hra6,hra7⟩ := ld64_bytes σ12.mem (sp.toNat + 56) rr.toNat hsRa
  obtain ⟨s00,s01,s02,s03,s04,s05,s06,s07, hs00,hs01,hs02,hs03,hs04,hs05,hs06,hs07⟩ := ld64_bytes σ12.mem (sp.toNat + 48) r8.toNat hsS0
  obtain ⟨s10,s11,s12,s13,s14,s15,s16,s17, hs10',hs11',hs12',hs13',hs14',hs15',hs16',hs17'⟩ := ld64_bytes σ12.mem (sp.toNat + 40) r9.toNat hsS1
  obtain ⟨s20,s21,s22,s23,s24,s25,s26,s27, hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27⟩ := ld64_bytes σ12.mem (sp.toNat + 32) r18.toNat hsS2
  obtain ⟨s30,s31,s32,s33,s34,s35,s36,s37, hs30,hs31,hs32,hs33,hs34,hs35,hs36,hs37⟩ := ld64_bytes σ12.mem (sp.toNat + 24) r19.toNat hsS3
  obtain ⟨s40,s41,s42,s43,s44,s45,s46,s47, hs40,hs41,hs42,hs43,hs44,hs45,hs46,hs47⟩ := ld64_bytes σ12.mem (sp.toNat + 16) r20.toNat hsS4
  obtain ⟨s50,s51,s52,s53,s54,s55,s56,s57, hs50,hs51,hs52,hs53,hs54,hs55,hs56,hs57⟩ := ld64_bytes σ12.mem (sp.toNat + 8) r21.toNat hsS5
  -- restore-slot addresses (sp + sext off = sp + k)
  have hsext38 : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide
  have hsext30 : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
  have hsext28 : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
  have hsext20 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
  have hsext18 : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
  have hsext10 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
  have hspAddr : ∀ (off : BitVec 12) (k : Nat), (sign_extend (m := 64) off : BitVec 64).toNat = k →
      k ≤ 56 → (sp + sign_extend (m := 64) off).toNat = sp.toNat + k := by
    intro off k hoff hk
    exact off_pos_eg6 sp off k hoff (by have := hSt.spNoWrap; omega)
  have haRa : (sp + sign_extend (m := 64) (0x038#12)).toNat = sp.toNat + 56 := hspAddr _ 56 hsext38 (by omega)
  have haS0 : (sp + sign_extend (m := 64) (0x030#12)).toNat = sp.toNat + 48 := hspAddr _ 48 hsext30 (by omega)
  have haS1 : (sp + sign_extend (m := 64) (0x028#12)).toNat = sp.toNat + 40 := hspAddr _ 40 hsext28 (by omega)
  have haS2 : (sp + sign_extend (m := 64) (0x020#12)).toNat = sp.toNat + 32 := hspAddr _ 32 hsext20 (by omega)
  have haS3 : (sp + sign_extend (m := 64) (0x018#12)).toNat = sp.toNat + 24 := hspAddr _ 24 hsext18 (by omega)
  have haS4 : (sp + sign_extend (m := 64) (0x010#12)).toNat = sp.toNat + 16 := hspAddr _ 16 hsext10 (by omega)
  have haS5 : (sp + sign_extend (m := 64) (0x008#12)).toNat = sp.toNat + 8 := hspAddr _ 8 hsext8 (by omega)
  -- helpers: ofNat (x.toNat) = x, and the restore load value = ofNat (rX.toNat) = rX
  have hofnat_toNat : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  -- spill-slot geometry side conditions (each slot in RAM/aligned/HTIF)
  have hslotLo : ∀ k : Nat, 8 ≤ k → 0x80000000 ≤ sp.toNat + k := by
    intro k hk; have := hSt.spLo; omega
  have hslotHi : ∀ k : Nat, k + 8 ≤ 64 → sp.toNat + k + 8 ≤ 0x100000000 := by
    intro k hk; have := hSt.spHi; omega
  have hslotWin : ∀ k : Nat, 8 ≤ k → tohostAddr + 8 ≤ sp.toNat + k := by
    intro k hk; have := hSt.spWin; rw [htoh] at *; omega
  have hslotAlign : ∀ k : Nat, k % 8 = 0 → (sp.toNat + k) % 8 = 0 := by
    intro k hk; have := hSt.spAlign; omega
  -- ============ ca0: ld ra,56(sp) → x1 := rr ============
  obtain ⟨σ13, i13, hstep13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80002ca0_eg2 σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002ca0#64) vmi12 sp
      ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 hG12 hpc12 hmi12 hsp_12 hcode12 rfl
      (by rw [haRa]; exact hslotLo 56 (by omega)) (by rw [haRa]; exact hslotHi 56 (by omega))
      (by rw [haRa]; right; exact hslotWin 56 (by omega)) (by rw [haRa]; exact hslotAlign 56 (by omega))
      (by rw [haRa]; exact hra0) (by rw [haRa]; exact hra1) (by rw [haRa]; exact hra2) (by rw [haRa]; exact hra3)
      (by rw [haRa]; exact hra4) (by rw [haRa]; exact hra5) (by rw [haRa]; exact hra6) (by rw [haRa]; exact hra7) hi12
  have hstep13 : Step ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep13'
  have hm13e : σ13.mem = σ12.mem := hmem13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80002ca4#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80002ca0#64) 4 = (0x80002ca4#64:BitVec 64) from by decide] at this
  have hraw13 : (sign_extend (m := 64) ((((((((ra7.append ra6).append ra5).append ra4).append ra3).append ra2).append ra1).append ra0) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 rr.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 56) rr.toNat ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 hsRa hra0 hra1 hra2 hra3 hra4 hra5 hra6 hra7
  have hx1_13 : σ13.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hraw13, hofnat_toNat, hSt.rr_eq] at this; exact this
  have ha0_13 : σ13.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs13 Register.x10 (by decide) ha0_12
  have hsp_13 : σ13.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs13 Register.x2 (by decide) hsp_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hcode13 : Env_getLoaded σ13.mem := by rw [hm13e]; exact hcode12
  -- ============ ca4: ld s0,48(sp) → x8 := r8 ============
  obtain ⟨σ14, i14, hstep14', hi14, hG14, hmem14, hobs14⟩ :=
    site_80002ca4_eg2 σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002ca4#64) vmi13 sp
      s00 s01 s02 s03 s04 s05 s06 s07 hG13 hpc13 hmi13 hsp_13 hcode13 rfl
      (by rw [haS0]; exact hslotLo 48 (by omega)) (by rw [haS0]; exact hslotHi 48 (by omega))
      (by rw [haS0]; right; exact hslotWin 48 (by omega)) (by rw [haS0]; exact hslotAlign 48 (by omega))
      (by rw [haS0, hm13e]; exact hs00) (by rw [haS0, hm13e]; exact hs01) (by rw [haS0, hm13e]; exact hs02) (by rw [haS0, hm13e]; exact hs03)
      (by rw [haS0, hm13e]; exact hs04) (by rw [haS0, hm13e]; exact hs05) (by rw [haS0, hm13e]; exact hs06) (by rw [haS0, hm13e]; exact hs07) hi13
  have hstep14 : Step ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep14'
  have hm14e : σ14.mem = σ12.mem := by rw [hmem14]; exact hm13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80002ca8#64) := by
    have := obs_alu_pc hobs14; rwa [show BitVec.addInt (0x80002ca4#64) 4 = (0x80002ca8#64:BitVec 64) from by decide] at this
  have hraw14 : (sign_extend (m := 64) ((((((((s07.append s06).append s05).append s04).append s03).append s02).append s01).append s00) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r8.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 48) r8.toNat s00 s01 s02 s03 s04 s05 s06 s07 hsS0 hs00 hs01 hs02 hs03 hs04 hs05 hs06 hs07
  have hx8_14 : σ14.regs.get? Register.x8 = some r8 := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw14, hofnat_toNat] at this; exact this
  have ha0_14 : σ14.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs14 Register.x10 (by decide) ha0_13
  have hx1_14 : σ14.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs14 Register.x1 (by decide) hx1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs14 Register.x2 (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hcode14 : Env_getLoaded σ14.mem := by rw [hm14e]; exact hcode12
  -- ============ ca8: ld s1,40(sp) → x9 := r9 ============
  obtain ⟨σ15, i15, hstep15', hi15, hG15, hmem15, hobs15⟩ :=
    site_80002ca8_eg2 σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002ca8#64) vmi14 sp
      s10 s11 s12 s13 s14 s15 s16 s17 hG14 hpc14 hmi14 hsp_14 hcode14 rfl
      (by rw [haS1]; exact hslotLo 40 (by omega)) (by rw [haS1]; exact hslotHi 40 (by omega))
      (by rw [haS1]; right; exact hslotWin 40 (by omega)) (by rw [haS1]; exact hslotAlign 40 (by omega))
      (by rw [haS1, hm14e]; exact hs10') (by rw [haS1, hm14e]; exact hs11') (by rw [haS1, hm14e]; exact hs12') (by rw [haS1, hm14e]; exact hs13')
      (by rw [haS1, hm14e]; exact hs14') (by rw [haS1, hm14e]; exact hs15') (by rw [haS1, hm14e]; exact hs16') (by rw [haS1, hm14e]; exact hs17') hi14
  have hstep15 : Step ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep15'
  have hm15e : σ15.mem = σ12.mem := by rw [hmem15]; exact hm14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x80002cac#64) := by
    have := obs_alu_pc hobs15; rwa [show BitVec.addInt (0x80002ca8#64) 4 = (0x80002cac#64:BitVec 64) from by decide] at this
  have hraw15 : (sign_extend (m := 64) ((((((((s17.append s16).append s15).append s14).append s13).append s12).append s11).append s10) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r9.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 40) r9.toNat s10 s11 s12 s13 s14 s15 s16 s17 hsS1 hs10' hs11' hs12' hs13' hs14' hs15' hs16' hs17'
  have hx9_15 : σ15.regs.get? Register.x9 = some r9 := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw15, hofnat_toNat] at this; exact this
  have ha0_15 : σ15.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs15 Register.x10 (by decide) ha0_14
  have hx1_15 : σ15.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs15 Register.x1 (by decide) hx1_14
  have hx8_15 : σ15.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs15 Register.x8 (by decide) hx8_14
  have hsp_15 : σ15.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs15 Register.x2 (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hcode15 : Env_getLoaded σ15.mem := by rw [hm15e]; exact hcode12
  -- ============ cac: ld s2,32(sp) → x18 := r18 ============
  obtain ⟨σ16, i16, hstep16', hi16, hG16, hmem16, hobs16⟩ :=
    site_80002cac_eg2 σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cac#64) vmi15 sp
      s20 s21 s22 s23 s24 s25 s26 s27 hG15 hpc15 hmi15 hsp_15 hcode15 rfl
      (by rw [haS2]; exact hslotLo 32 (by omega)) (by rw [haS2]; exact hslotHi 32 (by omega))
      (by rw [haS2]; right; exact hslotWin 32 (by omega)) (by rw [haS2]; exact hslotAlign 32 (by omega))
      (by rw [haS2, hm15e]; exact hs20) (by rw [haS2, hm15e]; exact hs21) (by rw [haS2, hm15e]; exact hs22) (by rw [haS2, hm15e]; exact hs23)
      (by rw [haS2, hm15e]; exact hs24) (by rw [haS2, hm15e]; exact hs25) (by rw [haS2, hm15e]; exact hs26) (by rw [haS2, hm15e]; exact hs27) hi15
  have hstep16 : Step ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep16'
  have hm16e : σ16.mem = σ12.mem := by rw [hmem16]; exact hm15e
  have hpc16 : σ16.regs.get? Register.PC = some (0x80002cb0#64) := by
    have := obs_alu_pc hobs16; rwa [show BitVec.addInt (0x80002cac#64) 4 = (0x80002cb0#64:BitVec 64) from by decide] at this
  have hraw16 : (sign_extend (m := 64) ((((((((s27.append s26).append s25).append s24).append s23).append s22).append s21).append s20) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r18.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 32) r18.toNat s20 s21 s22 s23 s24 s25 s26 s27 hsS2 hs20 hs21 hs22 hs23 hs24 hs25 hs26 hs27
  have hx18_16 : σ16.regs.get? Register.x18 = some r18 := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw16, hofnat_toNat] at this; exact this
  have ha0_16 : σ16.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs16 Register.x10 (by decide) ha0_15
  have hx1_16 : σ16.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs16 Register.x1 (by decide) hx1_15
  have hx8_16 : σ16.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs16 Register.x8 (by decide) hx8_15
  have hx9_16 : σ16.regs.get? Register.x9 = some r9 :=
    obs_alu_other' hobs16 Register.x9 (by decide) hx9_15
  have hsp_16 : σ16.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs16 Register.x2 (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hcode16 : Env_getLoaded σ16.mem := by rw [hm16e]; exact hcode12
  -- ============ cb0: ld s3,24(sp) → x19 := r19 ============
  obtain ⟨σ17, i17, hstep17', hi17, hG17, hmem17, hobs17⟩ :=
    site_80002cb0_eg2 σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cb0#64) vmi16 sp
      s30 s31 s32 s33 s34 s35 s36 s37 hG16 hpc16 hmi16 hsp_16 hcode16 rfl
      (by rw [haS3]; exact hslotLo 24 (by omega)) (by rw [haS3]; exact hslotHi 24 (by omega))
      (by rw [haS3]; right; exact hslotWin 24 (by omega)) (by rw [haS3]; exact hslotAlign 24 (by omega))
      (by rw [haS3, hm16e]; exact hs30) (by rw [haS3, hm16e]; exact hs31) (by rw [haS3, hm16e]; exact hs32) (by rw [haS3, hm16e]; exact hs33)
      (by rw [haS3, hm16e]; exact hs34) (by rw [haS3, hm16e]; exact hs35) (by rw [haS3, hm16e]; exact hs36) (by rw [haS3, hm16e]; exact hs37) hi16
  have hstep17 : Step ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep17'
  have hm17e : σ17.mem = σ12.mem := by rw [hmem17]; exact hm16e
  have hpc17 : σ17.regs.get? Register.PC = some (0x80002cb4#64) := by
    have := obs_alu_pc hobs17; rwa [show BitVec.addInt (0x80002cb0#64) 4 = (0x80002cb4#64:BitVec 64) from by decide] at this
  have hraw17 : (sign_extend (m := 64) ((((((((s37.append s36).append s35).append s34).append s33).append s32).append s31).append s30) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r19.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 24) r19.toNat s30 s31 s32 s33 s34 s35 s36 s37 hsS3 hs30 hs31 hs32 hs33 hs34 hs35 hs36 hs37
  have hx19_17 : σ17.regs.get? Register.x19 = some r19 := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw17, hofnat_toNat] at this; exact this
  have ha0_17 : σ17.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs17 Register.x10 (by decide) ha0_16
  have hx1_17 : σ17.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs17 Register.x1 (by decide) hx1_16
  have hx8_17 : σ17.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs17 Register.x8 (by decide) hx8_16
  have hx9_17 : σ17.regs.get? Register.x9 = some r9 :=
    obs_alu_other' hobs17 Register.x9 (by decide) hx9_16
  have hx18_17 : σ17.regs.get? Register.x18 = some r18 :=
    obs_alu_other' hobs17 Register.x18 (by decide) hx18_16
  have hsp_17 : σ17.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs17 Register.x2 (by decide) hsp_16
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hcode17 : Env_getLoaded σ17.mem := by rw [hm17e]; exact hcode12
  -- ============ cb4: ld s4,16(sp) → x20 := r20 ============
  obtain ⟨σ18, i18, hstep18', hi18, hG18, hmem18, hobs18⟩ :=
    site_80002cb4_eg2 σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cb4#64) vmi17 sp
      s40 s41 s42 s43 s44 s45 s46 s47 hG17 hpc17 hmi17 hsp_17 hcode17 rfl
      (by rw [haS4]; exact hslotLo 16 (by omega)) (by rw [haS4]; exact hslotHi 16 (by omega))
      (by rw [haS4]; right; exact hslotWin 16 (by omega)) (by rw [haS4]; exact hslotAlign 16 (by omega))
      (by rw [haS4, hm17e]; exact hs40) (by rw [haS4, hm17e]; exact hs41) (by rw [haS4, hm17e]; exact hs42) (by rw [haS4, hm17e]; exact hs43)
      (by rw [haS4, hm17e]; exact hs44) (by rw [haS4, hm17e]; exact hs45) (by rw [haS4, hm17e]; exact hs46) (by rw [haS4, hm17e]; exact hs47) hi17
  have hstep18 : Step ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep18'
  have hm18e : σ18.mem = σ12.mem := by rw [hmem18]; exact hm17e
  have hpc18 : σ18.regs.get? Register.PC = some (0x80002cb8#64) := by
    have := obs_alu_pc hobs18; rwa [show BitVec.addInt (0x80002cb4#64) 4 = (0x80002cb8#64:BitVec 64) from by decide] at this
  have hraw18 : (sign_extend (m := 64) ((((((((s47.append s46).append s45).append s44).append s43).append s42).append s41).append s40) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r20.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 16) r20.toNat s40 s41 s42 s43 s44 s45 s46 s47 hsS4 hs40 hs41 hs42 hs43 hs44 hs45 hs46 hs47
  have hx20_18 : σ18.regs.get? Register.x20 = some r20 := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw18, hofnat_toNat] at this; exact this
  have ha0_18 : σ18.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs18 Register.x10 (by decide) ha0_17
  have hx1_18 : σ18.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs18 Register.x1 (by decide) hx1_17
  have hx8_18 : σ18.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs18 Register.x8 (by decide) hx8_17
  have hx9_18 : σ18.regs.get? Register.x9 = some r9 :=
    obs_alu_other' hobs18 Register.x9 (by decide) hx9_17
  have hx18_18 : σ18.regs.get? Register.x18 = some r18 :=
    obs_alu_other' hobs18 Register.x18 (by decide) hx18_17
  have hx19_18 : σ18.regs.get? Register.x19 = some r19 :=
    obs_alu_other' hobs18 Register.x19 (by decide) hx19_17
  have hsp_18 : σ18.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs18 Register.x2 (by decide) hsp_17
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hcode18 : Env_getLoaded σ18.mem := by rw [hm18e]; exact hcode12
  -- ============ cb8: ld s5,8(sp) → x21 := r21 ============
  obtain ⟨σ19, i19, hstep19', hi19, hG19, hmem19, hobs19⟩ :=
    site_80002cb8_eg2 σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cb8#64) vmi18 sp
      s50 s51 s52 s53 s54 s55 s56 s57 hG18 hpc18 hmi18 hsp_18 hcode18 rfl
      (by rw [haS5]; exact hslotLo 8 (by omega)) (by rw [haS5]; exact hslotHi 8 (by omega))
      (by rw [haS5]; right; exact hslotWin 8 (by omega)) (by rw [haS5]; exact hslotAlign 8 (by omega))
      (by rw [haS5, hm18e]; exact hs50) (by rw [haS5, hm18e]; exact hs51) (by rw [haS5, hm18e]; exact hs52) (by rw [haS5, hm18e]; exact hs53)
      (by rw [haS5, hm18e]; exact hs54) (by rw [haS5, hm18e]; exact hs55) (by rw [haS5, hm18e]; exact hs56) (by rw [haS5, hm18e]; exact hs57) hi18
  have hstep19 : Step ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep19'
  have hm19e : σ19.mem = σ12.mem := by rw [hmem19]; exact hm18e
  have hpc19 : σ19.regs.get? Register.PC = some (0x80002cbc#64) := by
    have := obs_alu_pc hobs19; rwa [show BitVec.addInt (0x80002cb8#64) 4 = (0x80002cbc#64:BitVec 64) from by decide] at this
  have hraw19 : (sign_extend (m := 64) ((((((((s57.append s56).append s55).append s54).append s53).append s52).append s51).append s50) : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 r21.toNat :=
    ld_value_eq_read64 σ12.mem (sp.toNat + 8) r21.toNat s50 s51 s52 s53 s54 s55 s56 s57 hsS5 hs50 hs51 hs52 hs53 hs54 hs55 hs56 hs57
  have hx21_19 : σ19.regs.get? Register.x21 = some r21 := by
    have := obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide); rw [hraw19, hofnat_toNat] at this; exact this
  have ha0_19 : σ19.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs19 Register.x10 (by decide) ha0_18
  have hx1_19 : σ19.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs19 Register.x1 (by decide) hx1_18
  have hx8_19 : σ19.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs19 Register.x8 (by decide) hx8_18
  have hx9_19 : σ19.regs.get? Register.x9 = some r9 :=
    obs_alu_other' hobs19 Register.x9 (by decide) hx9_18
  have hx18_19 : σ19.regs.get? Register.x18 = some r18 :=
    obs_alu_other' hobs19 Register.x18 (by decide) hx18_18
  have hx19_19 : σ19.regs.get? Register.x19 = some r19 :=
    obs_alu_other' hobs19 Register.x19 (by decide) hx19_18
  have hx20_19 : σ19.regs.get? Register.x20 = some r20 :=
    obs_alu_other' hobs19 Register.x20 (by decide) hx20_18
  have hsp_19 : σ19.regs.get? Register.x2 = some sp :=
    obs_alu_other' hobs19 Register.x2 (by decide) hsp_18
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hcode19 : Env_getLoaded σ19.mem := by rw [hm19e]; exact hcode12
  -- ============ cbc: addi sp,sp,64 → x2 := sp + 64 ============
  obtain ⟨σ20, i20, hstep20', hi20, hG20, hmem20, hobs20⟩ :=
    site_80002cbc_eg2 σ19 i19 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cbc#64) vmi19 sp
      hG19 hpc19 hmi19 hsp_19 hcode19 rfl hi19
  have hstep20 : Step ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep20'
  have hm20e : σ20.mem = σ12.mem := by rw [hmem20]; exact hm19e
  have hpc20 : σ20.regs.get? Register.PC = some (0x80002cc0#64) := by
    have := obs_alu_pc hobs20; rwa [show BitVec.addInt (0x80002cbc#64) 4 = (0x80002cc0#64:BitVec 64) from by decide] at this
  have hsp_20 : σ20.regs.get? Register.x2 = some (sp + 64#64) := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sp + sign_extend (m := 64) (0x040#12) : BitVec 64) = sp + 64#64 from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add,
        show (sign_extend (m := 64) (0x040#12) : BitVec 64).toNat = 64 from by decide,
        show (64#64 : BitVec 64).toNat = 64 from by decide]] at this
  have ha0_20 : σ20.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_alu_other' hobs20 Register.x10 (by decide) ha0_19
  have hx1_20 : σ20.regs.get? Register.x1 = some r :=
    obs_alu_other' hobs20 Register.x1 (by decide) hx1_19
  have hx8_20 : σ20.regs.get? Register.x8 = some r8 :=
    obs_alu_other' hobs20 Register.x8 (by decide) hx8_19
  have hx9_20 : σ20.regs.get? Register.x9 = some r9 :=
    obs_alu_other' hobs20 Register.x9 (by decide) hx9_19
  have hx18_20 : σ20.regs.get? Register.x18 = some r18 :=
    obs_alu_other' hobs20 Register.x18 (by decide) hx18_19
  have hx19_20 : σ20.regs.get? Register.x19 = some r19 :=
    obs_alu_other' hobs20 Register.x19 (by decide) hx19_19
  have hx20_20 : σ20.regs.get? Register.x20 = some r20 :=
    obs_alu_other' hobs20 Register.x20 (by decide) hx20_19
  have hx21_20 : σ20.regs.get? Register.x21 = some r21 :=
    obs_alu_other' hobs20 Register.x21 (by decide) hx21_19
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hcode20 : Env_getLoaded σ20.mem := by rw [hm20e]; exact hcode12
  -- ============ cc0: ret → PC := r ============
  have hretr : (Sail.BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) = r :=
    ret_tgt r hSt.rAlign
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [hretr]; exact hSt.rAlign
  obtain ⟨σ21, i21, hstep21', hi21, hG21, hmem21, hobs21⟩ :=
    site_80002cc0_eg2 σ20 i20 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002cc0#64) vmi20 r
      hG20 hpc20 hmi20 hx1_20 hcode20 rfl hrettgt hi20
  have hstep21 : Step ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hstep21'
  have hm21e : σ21.mem = σ12.mem := by rw [hmem21]; exact hm20e
  have hpc21 : σ21.regs.get? Register.PC = some r := by
    have := obs_jr_pc hobs21; rwa [hretr] at this
  have ha0_21 : σ21.regs.get? Register.x10 = some (1#64:BitVec 64) :=
    obs_jr_other' hobs21 Register.x10 (by decide) ha0_20
  have hx1_21 : σ21.regs.get? Register.x1 = some r :=
    obs_jr_other' hobs21 Register.x1 (by decide) hx1_20
  have hsp_21 : σ21.regs.get? Register.x2 = some (sp + 64#64) :=
    obs_jr_other' hobs21 Register.x2 (by decide) hsp_20
  have hx8_21 : σ21.regs.get? Register.x8 = some r8 :=
    obs_jr_other' hobs21 Register.x8 (by decide) hx8_20
  have hx9_21 : σ21.regs.get? Register.x9 = some r9 :=
    obs_jr_other' hobs21 Register.x9 (by decide) hx9_20
  have hx18_21 : σ21.regs.get? Register.x18 = some r18 :=
    obs_jr_other' hobs21 Register.x18 (by decide) hx18_20
  have hx19_21 : σ21.regs.get? Register.x19 = some r19 :=
    obs_jr_other' hobs21 Register.x19 (by decide) hx19_20
  have hx20_21 : σ21.regs.get? Register.x20 = some r20 :=
    obs_jr_other' hobs21 Register.x20 (by decide) hx20_20
  have hx21_21 : σ21.regs.get? Register.x21 = some r21 :=
    obs_jr_other' hobs21 Register.x21 (by decide) hx21_20
  -- assemble the Steps chain, the ValueRepr copy, and the outside-window agreement
  have hSteps : Steps c ⟨σ21, i21, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ :=
    ((((((((((((((((((((Steps.single hstep1).trans (Steps.single hstep2)).trans
      (Steps.single hstep3)).trans (Steps.single hstep4)).trans (Steps.single hstep5)).trans
      (Steps.single hstep6)).trans (Steps.single hstep7)).trans (Steps.single hstep8)).trans
      (Steps.single hstep9)).trans (Steps.single hstep10)).trans (Steps.single hstep11)).trans
      (Steps.single hstep12)).trans (Steps.single hstep13)).trans (Steps.single hstep14)).trans
      (Steps.single hstep15)).trans (Steps.single hstep16)).trans (Steps.single hstep17)).trans
      (Steps.single hstep18)).trans (Steps.single hstep19)).trans (Steps.single hstep20)).trans
      (Steps.single hstep21)
  -- sailOutput preserved through all 21 steps
  have hout21 : σ21.sailOutput = c.σ.sailOutput := by
    rw [hobs21.out, sailOutput_sigmaPost_jump_x0,
        hobs20.out, sailOutput_sigmaPost_alu, hobs19.out, sailOutput_sigmaPost_alu,
        hobs18.out, sailOutput_sigmaPost_alu, hobs17.out, sailOutput_sigmaPost_alu,
        hobs16.out, sailOutput_sigmaPost_alu, hobs15.out, sailOutput_sigmaPost_alu,
        hobs14.out, sailOutput_sigmaPost_alu, hobs13.out, sailOutput_sigmaPost_alu,
        hobs12.out, sailOutput_sigmaPost_store, hobs11.out, sailOutput_sigmaPost_alu,
        hobs10.out, sailOutput_sigmaPost_store, hobs9.out, sailOutput_sigmaPost_alu,
        hobs8.out, sailOutput_sigmaPost_store, hobs7.out, sailOutput_sigmaPost_alu,
        hobs6.out, sailOutput_sigmaPost_alu, hobs5.out, sailOutput_sigmaPost_alu,
        hobs4.out, sailOutput_sigmaPost_alu, hobs3.out, sailOutput_sigmaPost_alu,
        hobs2.out, sailOutput_sigmaPost_alu, hobs1.out, sailOutput_sigmaPost_alu]
  -- the three destination words read back exactly w0/w1/w2 in σ12.mem
  have hout_w0 : read64 σ12.mem out.toNat = some w0 := by
    rw [hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := read64_lt_eg4 m0 (pv + 24 * i) w0 hSt.srcW0; exact this)]
  have hout_w1 : read64 σ12.mem (out.toNat + 8) = some w1 := by
    rw [hm12full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
        read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := read64_lt_eg4 m0 (pv + 24 * i + 8) w1 hSt.srcW1; exact this)]
  have hout_w2 : read64 σ12.mem (out.toNat + 16) = some w2 := by
    rw [hm12full, read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := read64_lt_eg4 m0 (pv + 24 * i + 16) w2 hSt.srcW2; exact this)]
  -- outside [out, out+24) agreement (both for ValueRepr and the exit predicate)
  have houtside : ∀ a : Nat, a < out.toNat ∨ out.toNat + 24 ≤ a → σ12.mem[a]? = m0[a]? := by
    intro a ha
    rw [hm12full,
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega)]
  -- byte-level copy: the 24 destination bytes equal the 24 source bytes.  Each 8-byte
  -- word matches because both `read64`s equal the same `wk`, and `read64_bytes_eg4`
  -- determines the bytes uniquely from the word.
  have hcopy8 : ∀ (dst src w : Nat), read64 σ12.mem dst = some w → read64 m0 src = some w →
      ∀ j, j < 8 → σ12.mem[dst + j]? = m0[src + j]? := by
    intro dst src w hd hs j hj
    obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7, hd0,hd1,hd2,hd3,hd4,hd5,hd6,hd7, hdq⟩ := read64_bytes_eg4 σ12.mem dst w hd
    obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7, he0,he1,he2,he3,he4,he5,he6,he7, heq⟩ := read64_bytes_eg4 m0 src w hs
    -- both byte-octets reconstruct `w`; equal byte-by-byte via toNat bounds + omega
    have b0 := d0.isLt; have b1 := d1.isLt; have b2 := d2.isLt; have b3 := d3.isLt
    have b4 := d4.isLt; have b5 := d5.isLt; have b6 := d6.isLt; have b7 := d7.isLt
    have c0 := e0.isLt; have c1 := e1.isLt; have c2 := e2.isLt; have c3 := e3.isLt
    have c4 := e4.isLt; have c5 := e5.isLt; have c6 := e6.isLt; have c7 := e7.isLt
    have hq0 : d0 = e0 := by apply BitVec.eq_of_toNat_eq; omega
    have hq1 : d1 = e1 := by apply BitVec.eq_of_toNat_eq; omega
    have hq2 : d2 = e2 := by apply BitVec.eq_of_toNat_eq; omega
    have hq3 : d3 = e3 := by apply BitVec.eq_of_toNat_eq; omega
    have hq4 : d4 = e4 := by apply BitVec.eq_of_toNat_eq; omega
    have hq5 : d5 = e5 := by apply BitVec.eq_of_toNat_eq; omega
    have hq6 : d6 = e6 := by apply BitVec.eq_of_toNat_eq; omega
    have hq7 : d7 = e7 := by apply BitVec.eq_of_toNat_eq; omega
    match j, hj with
    | 0, _ => rw [Nat.add_zero, Nat.add_zero, hd0, he0, hq0]
    | 1, _ => rw [hd1, he1, hq1]
    | 2, _ => rw [hd2, he2, hq2]
    | 3, _ => rw [hd3, he3, hq3]
    | 4, _ => rw [hd4, he4, hq4]
    | 5, _ => rw [hd5, he5, hq5]
    | 6, _ => rw [hd6, he6, hq6]
    | 7, _ => rw [hd7, he7, hq7]
  have hcopy : ∀ j, j < 24 → σ12.mem[out.toNat + j]? = m0[(pv + 24 * i) + j]? := by
    intro j hj
    rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ 16 ≤ j) with h | ⟨h1, h2⟩ | h
    · exact hcopy8 out.toNat (pv + 24 * i) w0 hout_w0 hSt.srcW0 j h
    · have := hcopy8 (out.toNat + 8) (pv + 24 * i + 8) w1 hout_w1 hSt.srcW1 (j - 8) (by omega)
      rw [show out.toNat + 8 + (j - 8) = out.toNat + j by omega,
          show pv + 24 * i + 8 + (j - 8) = pv + 24 * i + j by omega] at this
      exact this
    · have := hcopy8 (out.toNat + 16) (pv + 24 * i + 16) w2 hout_w2 hSt.srcW2 (j - 16) (by omega)
      rw [show out.toNat + 16 + (j - 16) = out.toNat + j by omega,
          show pv + 24 * i + 16 + (j - 16) = pv + 24 * i + j by omega] at this
      exact this
  refine ⟨⟨σ21, i21, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩, σ12.mem, hSteps, hG21, hi21, hpc21, ha0_21, hx1_21, hsp_21, hx8_21, hx9_21, hx18_21, hx19_21, hx20_21, hx21_21, hm21e, hm21e ▸ hcode12, ?_, ?_, ?_⟩
  · -- ValueRepr m' N φc out.toNat (f.vars[i]'hi).2
    refine valueRepr_copy_of_writeWindow (m := m0) (m' := σ12.mem) (srcAddr := pv + 24 * i) (dstAddr := out.toNat) hcopy ?_ ?_ hvr
    · intro a ha; exact houtside a ha
    · -- the value's string payload target is disjoint from [out, out+24)
      intro p s hp k hk
      -- the payload string lives in the arena / rodata, disjoint from the out buffer;
      -- carried by `HitTailSt.payDisj` (the pointed-to string is a separate region).
      exact hSt.payDisj p s hp k hk
  · -- outside-window agreement for the exit predicate
    intro a ha
    refine houtside a ?_
    rcases Nat.lt_or_ge a out.toNat with h | h
    · left; exact h
    · right
      rcases Nat.lt_or_ge a (out.toNat + 24) with h2 | h2
      · exact absurd ⟨h, h2⟩ ha
      · exact h2
  · -- sailOutput preserved through all 21 steps
    exact hout21

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
theorem env_get_found_spec
    (g : (R : Register) → Option (RegisterType R))
    (env out sp r : BitVec 64) (rr r8 r9 r18 r19 r20 r21 : BitVec 64) (i : Nat) (pv : Nat)
    (w0 w1 w2 : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) (hi : i < f.vars.length)
    -- The prologue + scan-to-HIT residual: from the env_get entry the machine reaches a
    -- HIT-tail entry config (`HitTailSt` at 0x80002c70, first-match at index `i`).
    (hreach : ∃ c1, Steps c c1 ∧
      HitTailSt g env out sp r rr r8 r9 r18 r19 r20 r21 i pv w0 w1 w2 f N φf φc m0 c1) :
    ∃ (c' : Config) (m' : Mem),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some r ∧
      c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.regs.get? Register.x2 = some (sp + 64#64) ∧
      c'.σ.regs.get? Register.x8 = some r8 ∧
      c'.σ.regs.get? Register.x9 = some r9 ∧
      c'.σ.regs.get? Register.x18 = some r18 ∧
      c'.σ.regs.get? Register.x19 = some r19 ∧
      c'.σ.regs.get? Register.x20 = some r20 ∧
      c'.σ.regs.get? Register.x21 = some r21 ∧
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      ValueRepr m' N φc out.toNat (f.vars[i]'hi).2 ∧
      (∀ a : Nat, ¬ (out.toNat ≤ a ∧ a < out.toNat + 24) → m'[a]? = m0[a]?) := by
  obtain ⟨c1, hs1, hSt⟩ := hreach
  obtain ⟨c', m', hs2, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', hvr, houtside, _hout'⟩ :=
    env_get_hit_tail g env out sp r rr r8 r9 r18 r19 r20 r21 i pv w0 w1 w2 f N φf φc m0 c1 hi hSt
  exact ⟨c', m', hs1.trans hs2, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', hvr, houtside⟩

end Vsa.Sim

#print axioms Vsa.Sim.env_get_hit_tail
#print axioms Vsa.Sim.env_get_found_spec
