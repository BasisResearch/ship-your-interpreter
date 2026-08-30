import Vsa.Sim.EnvGetSpec6
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `env_get` PROLOGUE `Steps` chain (`0x80002c10 → 0x80002c60`)

This file lands the last genuinely-missing STRAIGHT-LINE machine piece of the
immediate-frame FOUND case: the 17-instruction prologue

```
c10 blez a0,cd4      -- null-check env (NOT taken: env ≠ 0)
c14 addi sp,sp,-64   -- sp := sp0 - 64
c18 sd s3,24(sp)     -- spill x19 → sp+24
c1c sd s4,16(sp)     -- spill x20 → sp+16
c20 sd s5,8(sp)      -- spill x21 → sp+8
c24 sd ra,56(sp)     -- spill x1  → sp+56
c28 sd s0,48(sp)     -- spill x8  → sp+48
c2c sd s1,40(sp)     -- spill x9  → sp+40
c30 sd s2,32(sp)     -- spill x18 → sp+32
c34 mv s4,a0         -- x20 := env
c38 mv s3,a1         -- x19 := name
c3c mv s5,a2         -- x21 := out
c40 lw s2,0(s4)      -- x18 := env->count = ofNat len (sext32)
c44 blez s2,cc4      -- NOT taken (count > 0)
c48 ld s1,8(s4)      -- x9  := env->names = ofNat pn
c4c li s0,0          -- x8  := 0
c50 j 0x80002c60     -- jump to the do-while body entry (c50 + 0x10 = c60)
```

Note the prologue is a **do-while**: after `li s0,0` it jumps straight to the
loop BODY at `0x80002c60` (`ld a0,0(s1)`), NOT to the test `0x80002c5c` — the
`count > 0` check at `c44` guarantees `i = 0 < count`, so the first `beq` test is
skipped.  Hence `env_get_prologue` lands at `0x80002c60` with the scan live
registers established (`s4=env`, `s3=name`, `s5=out`, `s2=count`, `s1=names`,
`s0=0`) and the seven callee-saved spill slots written.

The seven spill words are written into the fresh 64-byte frame `[sp, sp+64)` with
`sp = sp0 - 64`; the destination slots are disjoint from the `env_get` code text
and (by the entry predicate's `spillArenaDisj` field) from the `env` frame's
arena region, so `Env_getLoaded` and the header reads `read64 (env+16)=pv` /
`read32 (env)=len` survive every store.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  Uses only the `EnvGetSites`/
`EnvGetSites2` sites + the `writeMap8` disjointness bridges from `EnvGetSpec6`.
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

/-! ## Local `jump_x0` read-back consumers (the `c50` `j` step)

`EnvGetSpec`'s import closure has `frame_jump_x0_eg`/`obs_jump_x0_pc_eg` (PC) and
`get?_sigmaPost_jump_x0`; the `other`/`minstret` read-backs are re-derived here
following the `obs_store_*` idiom (`MemcpySpec`). -/

theorem obs_jx0_other_eg7 {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_jump_x0 σ pc vm tgt R h1 h2 h4 h5).trans hσ)

theorem obs_jx0_minstret_eg7 {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## Small offset helper (positive immediate loads/stores)

`off_pos_eg6` (EnvGetSpec6) computes `(base + sext off).toNat = base.toNat + k`.
The prologue's spill offsets are all `< 0x800`, positive. -/

/-- `sext (small 12-bit) = its value` (for `k < 0x800`). -/
theorem sext_small_eg7 (off : BitVec 12) (k : Nat)
    (h : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 k) (hk : k < 2^64) :
    (sign_extend (m := 64) off : BitVec 64).toNat = k := by
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-! ## The prologue standing-entry predicate (`PrologueSt`)

`PrologueSt`: at `0x80002c10` (the `env_get` entry) with the C ABI arguments
`a0=env`, `a1=name`, `a2=out`, `ra=r`, `sp=sp0`, `GoodState`, `Env_getLoaded`,
memory `m0`; the frame `f` is represented at `env` (`FrameRepr`) with at least one
binding (`0 < f.vars.length`, so the `blez` at `c44` is NOT taken); the header
reads `read32 (env)=len` and `read64 (env+8)=pn` come from `FrameRepr`.  The fresh
64-byte frame `[sp0-64, sp0)` is in RAM, above HTIF, 8-aligned, disjoint from the
code text and from the `env` frame region (`spillEnvDisj`) so all seven spills and
the two header loads commute. -/
structure PrologueSt
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Env_getLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002c10#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some env
  a1 : c.σ.regs.get? Register.x11 = some name
  a2 : c.σ.regs.get? Register.x12 = some out
  ra : c.σ.regs.get? Register.x1 = some r0     -- incoming ra (spilled → sp+56, restored as r)
  sp : c.σ.regs.get? Register.x2 = some sp0
  -- incoming callee-saved values (spilled by the prologue, restored by the tail)
  cs8  : c.σ.regs.get? Register.x8  = some r8
  cs9  : c.σ.regs.get? Register.x9  = some r9
  cs18 : c.σ.regs.get? Register.x18 = some r18
  cs19 : c.σ.regs.get? Register.x19 = some r19
  cs20 : c.σ.regs.get? Register.x20 = some r20
  cs21 : c.σ.regs.get? Register.x21 = some r21
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  -- env ≠ 0 (the c10 blez a0 null-check is NOT taken)
  envNe : (env == (0#64 : BitVec 64)) = false
  -- representation & header reads
  frame : FrameRepr m0 N φf φc env.toNat f
  len_eq : len = f.vars.length
  lenPos : 0 < len
  lenSmall : len < 2^31
  read_len : read32 m0 env.toNat = some len          -- env->count
  read_pn  : read64 m0 (env.toNat + 8) = some pn      -- env->names
  -- env header geometry (the c40 lw / c48 ld load addresses)
  envLo : 0x80000000 ≤ env.toNat
  envHi : env.toNat + 24 ≤ 0x100000000
  envWin : tohostAddr + 8 ≤ env.toNat
  envAlign : env.toNat % 8 = 0
  -- fresh 64-byte stack frame `[sp0-64, sp0)` geometry
  spDrop : 0x40 ≤ sp0.toNat                           -- sp0 - 64 does not underflow
  spLo : 0x80000000 ≤ sp0.toNat - 64
  spHi : sp0.toNat ≤ 0x100000000
  spWin : tohostAddr + 64 ≤ sp0.toNat - 64
  spAlign : sp0.toNat % 8 = 0
  spCode : sp0.toNat ≤ 0x80002c10 ∨ 0x80002cdc ≤ sp0.toNat - 64
  -- the env frame header `[env, env+24)` is disjoint from the fresh stack frame
  -- `[sp0-64, sp0)` (the stack is below the arena; a real, honest side condition)
  envStackDisj : env.toNat + 24 ≤ sp0.toNat - 64 ∨ sp0.toNat ≤ env.toNat

/-! ## `lw`/`ld` header-value bridges (32-bit signed count, 64-bit names pointer) -/

/-- The 4-byte LE reconstruction as a `toNat` sum (local, no external deps). -/
theorem word4_recon_eg7 (b0 b1 b2 b3 : BitVec 8) :
    ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- `read32 m a = some k` reconstructs the four LE bytes and their `Nat` value
(local copy from `readLE`; `EvalIntSim2`'s `read32_bytes` is out of closure). -/
theorem read32_bytes_eg7 (m : Mem) (a k : Nat) (hk : read32 m a = some k) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k := by
  simp only [read32, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hk
  obtain ⟨b0, hb0, r1, ⟨b1, hb1, r2, ⟨b2, hb2, r3, ⟨b3, hb3, r4, hr4, hq3⟩, hq2⟩, hq1⟩, hq0⟩ := hk
  refine ⟨b0, b1, b2, b3, hb0, ?_, ?_, ?_, ?_⟩
  · simpa using hb1
  · simpa using hb2
  · simpa using hb3
  · subst hr4; simp only [Nat.add_zero, Nat.mul_zero] at *; omega

/-- Signed extension of a NONNEG 32-bit LE word folds to `ofNat k` (`k < 2^31`).
The `lw s2,0(s4)` count load delivers `sign_extend (b3++b2++b1++b0 : BitVec (8*4))`;
for a nonneg count `k < 2^31` this equals `ofNat 64 k`. -/
theorem sext_count_eg7 (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 2^31)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hlt : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    rw [word4_recon_eg7]; exact hrec
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 by omega)]
  simp only [sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.toNat_signExtend]
  have hmsb : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by decide),
      BitVec.getElem_eq_testBit_toNat, hlt]
    exact Nat.testBit_lt_two_pow (by omega)
  simp only [hmsb, Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth, hlt]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## `read64`/`read32` survival across a disjoint `writeMap8`

The header reads `read32 (env)=len`, `read64 (env+8)=pn` and the running spill
reads survive each spill store (disjoint 8-byte windows).  We reuse
`read64_writeMap8_disjoint_eg6` (EnvGetSpec6) for the 8-byte reads, and derive the
4-byte survival locally. -/

theorem read32_writeMap8_disjoint_eg7 (mem : Mem) (a a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a + 4 ≤ a8 ∨ a8 + 8 ≤ a) :
    read32 (writeMap8 mem a8 d) a = read32 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  simp only [read32, readLE, g0, g1, g2, g3]

/-! ## The `env_get` PROLOGUE machine `Steps` chain (verified)

**`env_get_prologue`.** From `PrologueSt` at `0x80002c10`, the 17-instruction
prologue runs to the do-while body entry `0x80002c60` with the scan live registers
established and the seven callee-saved spill slots written into the fresh frame
`[sp0-64, sp0)`.  Fully verified. -/
theorem env_get_prologue
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hSt : PrologueSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c) :
    ∃ (c' : Config) (m' : Mem),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x20 = some env ∧               -- s4 = env
      c'.σ.regs.get? Register.x19 = some name ∧              -- s3 = name
      c'.σ.regs.get? Register.x21 = some out ∧               -- s5 = out
      c'.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 len) ∧  -- s2 = count
      c'.σ.regs.get? Register.x9  = some (BitVec.ofNat 64 pn) ∧   -- s1 = names
      c'.σ.regs.get? Register.x8  = some (0#64 : BitVec 64) ∧     -- s0 = 0
      c'.σ.regs.get? Register.x1  = some r0 ∧                -- ra unchanged (in reg)
      c'.σ.regs.get? Register.x2  = some (sp0 - 64#64) ∧     -- sp popped by 64
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      -- the seven callee-saved spill slots hold their incoming values
      read64 m' ((sp0 - 64#64).toNat + 56) = some r0.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 48) = some r8.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 40) = some r9.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 32) = some r18.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 24) = some r19.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 16) = some r20.toNat ∧
      read64 m' ((sp0 - 64#64).toNat + 8) = some r21.toNat ∧
      -- memory outside the stack frame is unchanged (⇒ every disjoint header read,
      -- and hence `FrameRepr`/`Env_getLoaded`, survives at the composition site)
      (∀ a : Nat, ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64) → m'[a]? = m0[a]?) ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  obtain ⟨vmi, hmi⟩ := hSt.minstret
  have hmem := hSt.mem
  have hloaded0 : Env_getLoaded m0 := hmem ▸ hSt.loadedG
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- the post-c14 stack pointer `sp = sp0 - 64`, its `.toNat`, and geometry.
  have hspNat : (sp0 + sign_extend (m := 64) (0xfc0#12)).toNat = sp0.toNat - 64 := by
    have hsext : (sign_extend (m := 64) (0xfc0#12) : BitVec 64) = BitVec.ofNat 64 (2^64 - 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hsext]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (2^64 - 64) < 2^64)]
    have hd := hSt.spDrop; have hlt := sp0.isLt
    -- sp0.toNat + (2^64 - 64) = (sp0.toNat - 64) + 2^64, and (x + 2^64) % 2^64 = x for x < 2^64
    rw [show sp0.toNat + (2^64 - 64) = (sp0.toNat - 64) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hspEq : (sp0 + sign_extend (m := 64) (0xfc0#12)) = sp0 - 64#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hspNat, BitVec.toNat_sub]
    have hd := hSt.spDrop; have hlt := sp0.isLt
    have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
    rw [h64, show 2^64 - 64 + sp0.toNat = (sp0.toNat - 64) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- spill-slot addresses (all within [sp, sp+64), sp = sp0-64)
  have hspBase : (sp0 - 64#64).toNat = sp0.toNat - 64 := by rw [← hspEq, hspNat]
  -- ============ c10: beqz a0 NOT taken (env ≠ 0) → c14 ============
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002c10_nottaken_eg c.σ c.tick c.steps (0x80002c10#64) vmi env
      hSt.good hSt.pc hmi hSt.a0 hSt.loadedG rfl hSt.envNe hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hmem1e : σ1.mem = m0 := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002c14#64) := by
    have := obs_bnottaken_pc hobs1
    rwa [show BitVec.addInt (0x80002c10#64) 4 = (0x80002c14#64:BitVec 64) from by decide] at this
  have bcarry1 : ∀ (R : Register) (w : RegisterType R),
      (Register.minstret == R) = false → (Register.PC == R) = false →
      (Register.nextPC == R) = false → (Register.minstret_increment == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → c.σ.regs.get? R = some w → σ1.regs.get? R = some w := by
    intro R w h1 h2 h4 h5 hmc hmt hmi hσ; exact obs_bnottaken_other hobs1 R hmc hmt hmi h1 h2 h4 h5 hσ
  have hsp1 := bcarry1 Register.x2 sp0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.sp
  have ha0_1 := bcarry1 Register.x10 env (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0
  have ha1_1 := bcarry1 Register.x11 name (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1
  have ha2_1 := bcarry1 Register.x12 out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2
  have hra1 := bcarry1 Register.x1 r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra
  have h8_1 := bcarry1 Register.x8 r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs8
  have h9_1 := bcarry1 Register.x9 r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs9
  have h18_1 := bcarry1 Register.x18 r18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs18
  have h19_1 := bcarry1 Register.x19 r19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs19
  have h20_1 := bcarry1 Register.x20 r20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs20
  have h21_1 := bcarry1 Register.x21 r21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cs21
  obtain ⟨vmi1, hmi1⟩ := obs_bnottaken_minstret hobs1
  have hcode1 : Env_getLoaded σ1.mem := by rw [hmem1e]; exact hloaded0
  -- ============ c14: addi sp,sp,-64 → x2 := sp0 - 64 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002c14_eg σ1 i1 (c.steps+1) (0x80002c14#64) vmi1 sp0 hG1 hpc1 hmi1 hsp1 hcode1 rfl hi1
  have hstep2 : Step (⟨σ1,i1,c.steps+1⟩ : Config) ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hmem2e : σ2.mem = m0 := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002c18#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80002c14#64) 4 = (0x80002c18#64:BitVec 64) from by decide] at this
  have hsp2 : σ2.regs.get? Register.x2 = some (sp0 - 64#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hspEq] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have hra2 := obs_alu_other' hobs2 Register.x1 (by decide) hra1
  have h8_2 := obs_alu_other' hobs2 Register.x8 (by decide) h8_1
  have h9_2 := obs_alu_other' hobs2 Register.x9 (by decide) h9_1
  have h18_2 := obs_alu_other' hobs2 Register.x18 (by decide) h18_1
  have h19_2 := obs_alu_other' hobs2 Register.x19 (by decide) h19_1
  have h20_2 := obs_alu_other' hobs2 Register.x20 (by decide) h20_1
  have h21_2 := obs_alu_other' hobs2 Register.x21 (by decide) h21_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Env_getLoaded σ2.mem := by rw [hmem2e]; exact hloaded0
  -- store-address helpers: (sp0-64 + sext off).toNat = (sp0.toNat - 64) + off
  have hoff : ∀ (off : BitVec 12) (k : Nat), (sign_extend (m := 64) off : BitVec 64).toNat = k →
      k < 0x40 → ((sp0 - 64#64) + sign_extend (m := 64) off).toNat = (sp0.toNat - 64) + k := by
    intro off k hk hlt
    rw [BitVec.toNat_add, hspBase, hk]
    have := hSt.spHi; have := hSt.spDrop
    rw [Nat.mod_eq_of_lt (by omega)]
  -- concrete offset values
  have ho8  : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  have ho16 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
  have ho24 : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
  have ho32 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
  have ho40 : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
  have ho48 : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
  have ho56 : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide
  have hspb := hSt.spWin; have hspHi := hSt.spHi; have hspLo := hSt.spLo
  have hspAl := hSt.spAlign; have hspDr := hSt.spDrop
  have hspalign : (sp0.toNat - 64) % 8 = 0 := by omega
  -- the running memory after K spills; each `mkDisj` is `read64` at a spill slot
  -- against the writeMap8 window, disjoint (distinct 8-aligned slots).
  -- Spill store-address side conditions helper (RAM, above-HTIF, aligned)
  rw [htoh] at hspb
  have sc : ∀ (k : Nat), k < 0x40 → k % 8 = 0 →
      (0x80000000 ≤ (sp0.toNat - 64) + k) ∧ ((sp0.toNat - 64) + k + 8 ≤ 0x100000000) ∧
      (tohostAddr + 16 ≤ (sp0.toNat - 64) + k) ∧ (((sp0.toNat - 64) + k) % 8 = 0) := by
    intro k hk hkm
    refine ⟨by omega, by omega, by rw [htoh]; omega, by omega⟩
  -- ============ c18: sd s3(x19),24(sp) → *(sp+24) := r19 ============
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002c18_eg2 σ2 i2 (c.steps+1+1) (0x80002c18#64) vmi2 (sp0 - 64#64) r19
      hG2 hpc2 hmi2 hsp2 h19_2 hcode2 rfl
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 24 ho24 (by decide)]; exact (sc 24 (by decide) (by decide)).2.2.2) hi2
  have hstep3 : Step (⟨σ2,i2,c.steps+1+1⟩ : Config) ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hm3 : σ3.mem = writeMap8 m0 ((sp0.toNat - 64) + 24) (sdData_val r19) := by
    rw [hmem3, mem_afterNextPC, mem_afterPrelude, hmem2e, hoff _ 24 ho24 (by decide)]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002c1c#64) := by
    have := obs_store_pc hobs3; rwa [show BitVec.addInt (0x80002c18#64) 4 = (0x80002c1c#64:BitVec 64) from by decide] at this
  have hsp3 := obs_store_other' hobs3 Register.x2 (by decide) hsp2
  have h20_3 := obs_store_other' hobs3 Register.x20 (by decide) h20_2
  have h21_3 := obs_store_other' hobs3 Register.x21 (by decide) h21_2
  have hra3 := obs_store_other' hobs3 Register.x1 (by decide) hra2
  have h8_3 := obs_store_other' hobs3 Register.x8 (by decide) h8_2
  have h9_3 := obs_store_other' hobs3 Register.x9 (by decide) h9_2
  have h18_3 := obs_store_other' hobs3 Register.x18 (by decide) h18_2
  have h19_3 := obs_store_other' hobs3 Register.x19 (by decide) h19_2
  have ha0_3 := obs_store_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_store_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_store_other' hobs3 Register.x12 (by decide) ha2_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hspCode := hSt.spCode
  have hcodeDisj : ∀ k, k < 0x40 → ((sp0.toNat - 64) + k + 8 ≤ 0x80002c10 ∨ 0x80002cdc ≤ (sp0.toNat - 64) + k) := by
    intro k hk
    rcases hspCode with h | h
    · left; omega
    · right; omega
  have hcode3 : Env_getLoaded σ3.mem := by
    rw [hm3]; exact loaded_env_get_writeMap8_eg6 m0 _ _ (hcodeDisj 24 (by decide)) hloaded0
  -- ============ c1c: sd s4(x20),16(sp) → *(sp+16) := r20 ============
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002c1c_eg2 σ3 i3 (c.steps+1+1+1) (0x80002c1c#64) vmi3 (sp0 - 64#64) r20
      hG3 hpc3 hmi3 hsp3 h20_3 hcode3 rfl
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 16 ho16 (by decide)]; exact (sc 16 (by decide) (by decide)).2.2.2) hi3
  have hstep4 : Step (⟨σ3,i3,c.steps+1+1+1⟩ : Config) ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hm4 : σ4.mem = writeMap8 σ3.mem ((sp0.toNat - 64) + 16) (sdData_val r20) := by
    rw [hmem4, mem_afterNextPC, mem_afterPrelude, hoff _ 16 ho16 (by decide)]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002c20#64) := by
    have := obs_store_pc hobs4; rwa [show BitVec.addInt (0x80002c1c#64) 4 = (0x80002c20#64:BitVec 64) from by decide] at this
  have hsp4 := obs_store_other' hobs4 Register.x2 (by decide) hsp3
  have h21_4 := obs_store_other' hobs4 Register.x21 (by decide) h21_3
  have hra4 := obs_store_other' hobs4 Register.x1 (by decide) hra3
  have h8_4 := obs_store_other' hobs4 Register.x8 (by decide) h8_3
  have h9_4 := obs_store_other' hobs4 Register.x9 (by decide) h9_3
  have h18_4 := obs_store_other' hobs4 Register.x18 (by decide) h18_3
  have h19_4 := obs_store_other' hobs4 Register.x19 (by decide) h19_3
  have h20_4 := obs_store_other' hobs4 Register.x20 (by decide) h20_3
  have ha0_4 := obs_store_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_store_other' hobs4 Register.x12 (by decide) ha2_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hcode4 : Env_getLoaded σ4.mem := by
    rw [hm4]; exact loaded_env_get_writeMap8_eg6 σ3.mem _ _ (hcodeDisj 16 (by decide)) hcode3
  -- ============ c20: sd s5(x21),8(sp) → *(sp+8) := r21 ============
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002c20_eg2 σ4 i4 (c.steps+1+1+1+1) (0x80002c20#64) vmi4 (sp0 - 64#64) r21
      hG4 hpc4 hmi4 hsp4 h21_4 hcode4 rfl
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 8 ho8 (by decide)]; exact (sc 8 (by decide) (by decide)).2.2.2) hi4
  have hstep5 : Step (⟨σ4,i4,c.steps+1+1+1+1⟩ : Config) ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hm5 : σ5.mem = writeMap8 σ4.mem ((sp0.toNat - 64) + 8) (sdData_val r21) := by
    rw [hmem5, mem_afterNextPC, mem_afterPrelude, hoff _ 8 ho8 (by decide)]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002c24#64) := by
    have := obs_store_pc hobs5; rwa [show BitVec.addInt (0x80002c20#64) 4 = (0x80002c24#64:BitVec 64) from by decide] at this
  have hsp5 := obs_store_other' hobs5 Register.x2 (by decide) hsp4
  have hra5 := obs_store_other' hobs5 Register.x1 (by decide) hra4
  have h8_5 := obs_store_other' hobs5 Register.x8 (by decide) h8_4
  have h9_5 := obs_store_other' hobs5 Register.x9 (by decide) h9_4
  have h18_5 := obs_store_other' hobs5 Register.x18 (by decide) h18_4
  have h19_5 := obs_store_other' hobs5 Register.x19 (by decide) h19_4
  have h20_5 := obs_store_other' hobs5 Register.x20 (by decide) h20_4
  have h21_5 := obs_store_other' hobs5 Register.x21 (by decide) h21_4
  have ha0_5 := obs_store_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_store_other' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 := obs_store_other' hobs5 Register.x12 (by decide) ha2_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hcode5 : Env_getLoaded σ5.mem := by
    rw [hm5]; exact loaded_env_get_writeMap8_eg6 σ4.mem _ _ (hcodeDisj 8 (by decide)) hcode4
  -- ============ c24: sd ra(x1),56(sp) → *(sp+56) := r0 ============
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002c24_eg2 σ5 i5 (c.steps+1+1+1+1+1) (0x80002c24#64) vmi5 (sp0 - 64#64) r0
      hG5 hpc5 hmi5 hsp5 hra5 hcode5 rfl
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 56 ho56 (by decide)]; exact (sc 56 (by decide) (by decide)).2.2.2) hi5
  have hstep6 : Step (⟨σ5,i5,c.steps+1+1+1+1+1⟩ : Config) ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hm6 : σ6.mem = writeMap8 σ5.mem ((sp0.toNat - 64) + 56) (sdData_val r0) := by
    rw [hmem6, mem_afterNextPC, mem_afterPrelude, hoff _ 56 ho56 (by decide)]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002c28#64) := by
    have := obs_store_pc hobs6; rwa [show BitVec.addInt (0x80002c24#64) 4 = (0x80002c28#64:BitVec 64) from by decide] at this
  have hsp6 := obs_store_other' hobs6 Register.x2 (by decide) hsp5
  have h8_6 := obs_store_other' hobs6 Register.x8 (by decide) h8_5
  have h9_6 := obs_store_other' hobs6 Register.x9 (by decide) h9_5
  have h18_6 := obs_store_other' hobs6 Register.x18 (by decide) h18_5
  have h19_6 := obs_store_other' hobs6 Register.x19 (by decide) h19_5
  have h20_6 := obs_store_other' hobs6 Register.x20 (by decide) h20_5
  have h21_6 := obs_store_other' hobs6 Register.x21 (by decide) h21_5
  have ha0_6 := obs_store_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_store_other' hobs6 Register.x11 (by decide) ha1_5
  have ha2_6 := obs_store_other' hobs6 Register.x12 (by decide) ha2_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hcode6 : Env_getLoaded σ6.mem := by
    rw [hm6]; exact loaded_env_get_writeMap8_eg6 σ5.mem _ _ (hcodeDisj 56 (by decide)) hcode5
  -- ============ c28: sd s0(x8),48(sp) → *(sp+48) := r8 ============
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80002c28_eg2 σ6 i6 (c.steps+1+1+1+1+1+1) (0x80002c28#64) vmi6 (sp0 - 64#64) r8
      hG6 hpc6 hmi6 hsp6 h8_6 hcode6 rfl
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 48 ho48 (by decide)]; exact (sc 48 (by decide) (by decide)).2.2.2) hi6
  have hstep7 : Step (⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ : Config) ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hm7 : σ7.mem = writeMap8 σ6.mem ((sp0.toNat - 64) + 48) (sdData_val r8) := by
    rw [hmem7, mem_afterNextPC, mem_afterPrelude, hoff _ 48 ho48 (by decide)]
  have hpc7 : σ7.regs.get? Register.PC = some (0x80002c2c#64) := by
    have := obs_store_pc hobs7; rwa [show BitVec.addInt (0x80002c28#64) 4 = (0x80002c2c#64:BitVec 64) from by decide] at this
  have hsp7 := obs_store_other' hobs7 Register.x2 (by decide) hsp6
  have h9_7 := obs_store_other' hobs7 Register.x9 (by decide) h9_6
  have h18_7 := obs_store_other' hobs7 Register.x18 (by decide) h18_6
  have h19_7 := obs_store_other' hobs7 Register.x19 (by decide) h19_6
  have h20_7 := obs_store_other' hobs7 Register.x20 (by decide) h20_6
  have h21_7 := obs_store_other' hobs7 Register.x21 (by decide) h21_6
  have ha0_7 := obs_store_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 := obs_store_other' hobs7 Register.x11 (by decide) ha1_6
  have ha2_7 := obs_store_other' hobs7 Register.x12 (by decide) ha2_6
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hcode7 : Env_getLoaded σ7.mem := by
    rw [hm7]; exact loaded_env_get_writeMap8_eg6 σ6.mem _ _ (hcodeDisj 48 (by decide)) hcode6
  -- ============ c2c: sd s1(x9),40(sp) → *(sp+40) := r9 ============
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80002c2c_eg2 σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80002c2c#64) vmi7 (sp0 - 64#64) r9
      hG7 hpc7 hmi7 hsp7 h9_7 hcode7 rfl
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 40 ho40 (by decide)]; exact (sc 40 (by decide) (by decide)).2.2.2) hi7
  have hstep8 : Step (⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ : Config) ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hm8 : σ8.mem = writeMap8 σ7.mem ((sp0.toNat - 64) + 40) (sdData_val r9) := by
    rw [hmem8, mem_afterNextPC, mem_afterPrelude, hoff _ 40 ho40 (by decide)]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80002c30#64) := by
    have := obs_store_pc hobs8; rwa [show BitVec.addInt (0x80002c2c#64) 4 = (0x80002c30#64:BitVec 64) from by decide] at this
  have hsp8 := obs_store_other' hobs8 Register.x2 (by decide) hsp7
  have h18_8 := obs_store_other' hobs8 Register.x18 (by decide) h18_7
  have h19_8 := obs_store_other' hobs8 Register.x19 (by decide) h19_7
  have h20_8 := obs_store_other' hobs8 Register.x20 (by decide) h20_7
  have h21_8 := obs_store_other' hobs8 Register.x21 (by decide) h21_7
  have ha0_8 := obs_store_other' hobs8 Register.x10 (by decide) ha0_7
  have ha1_8 := obs_store_other' hobs8 Register.x11 (by decide) ha1_7
  have ha2_8 := obs_store_other' hobs8 Register.x12 (by decide) ha2_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hcode8 : Env_getLoaded σ8.mem := by
    rw [hm8]; exact loaded_env_get_writeMap8_eg6 σ7.mem _ _ (hcodeDisj 40 (by decide)) hcode7
  -- ============ c30: sd s2(x18),32(sp) → *(sp+32) := r18 ============
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80002c30_eg2 σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80002c30#64) vmi8 (sp0 - 64#64) r18
      hG8 hpc8 hmi8 hsp8 h18_8 hcode8 rfl
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.2.1)
      (by rw [hoff _ 32 ho32 (by decide)]; exact (sc 32 (by decide) (by decide)).2.2.2) hi8
  have hstep9 : Step (⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ : Config) ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hm9 : σ9.mem = writeMap8 σ8.mem ((sp0.toNat - 64) + 32) (sdData_val r18) := by
    rw [hmem9, mem_afterNextPC, mem_afterPrelude, hoff _ 32 ho32 (by decide)]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80002c34#64) := by
    have := obs_store_pc hobs9; rwa [show BitVec.addInt (0x80002c30#64) 4 = (0x80002c34#64:BitVec 64) from by decide] at this
  have hsp9 := obs_store_other' hobs9 Register.x2 (by decide) hsp8
  have ha0_9 := obs_store_other' hobs9 Register.x10 (by decide) ha0_8
  have ha1_9 := obs_store_other' hobs9 Register.x11 (by decide) ha1_8
  have ha2_9 := obs_store_other' hobs9 Register.x12 (by decide) ha2_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
  have hcode9 : Env_getLoaded σ9.mem := by
    rw [hm9]; exact loaded_env_get_writeMap8_eg6 σ8.mem _ _ (hcodeDisj 32 (by decide)) hcode8
  -- σ9.mem as the 7-fold writeMap8 of m0
  have hm9full : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
      (writeMap8 (writeMap8 m0 ((sp0.toNat-64)+24) (sdData_val r19))
        ((sp0.toNat-64)+16) (sdData_val r20)) ((sp0.toNat-64)+8) (sdData_val r21))
        ((sp0.toNat-64)+56) (sdData_val r0)) ((sp0.toNat-64)+48) (sdData_val r8))
        ((sp0.toNat-64)+40) (sdData_val r9)) ((sp0.toNat-64)+32) (sdData_val r18) := by
    rw [hm9, hm8, hm7, hm6, hm5, hm4, hm3]
  -- env-header window disjointness against every spill slot (used to survive reads)
  have hdisjSlot8 : ∀ (a slotoff : Nat), env.toNat ≤ a → a + 8 ≤ env.toNat + 24 →
      slotoff ≤ 56 → (a + 8 ≤ (sp0.toNat-64)+slotoff ∨ (sp0.toNat-64)+slotoff + 8 ≤ a) := by
    intro a slotoff ha1 ha2 hs
    have hd := hSt.spDrop
    rcases hSt.envStackDisj with h | h
    · left; omega
    · right; omega
  have hdisjSlot4 : ∀ (a slotoff : Nat), env.toNat ≤ a → a + 4 ≤ env.toNat + 24 →
      slotoff ≤ 56 → (a + 4 ≤ (sp0.toNat-64)+slotoff ∨ (sp0.toNat-64)+slotoff + 8 ≤ a) := by
    intro a slotoff ha1 ha2 hs
    have hd := hSt.spDrop
    rcases hSt.envStackDisj with h | h
    · left; omega
    · right; omega
  have henvHi := hSt.envHi
  -- read64 at env+16 survives all 7 writes
  have hread_pv_env : read64 σ9.mem (env.toNat + 16) = read64 m0 (env.toNat + 16) := by
    rw [hm9full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 32 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 40 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 48 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 56 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 8 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 16 (by omega) (by omega) (by decide)),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+16) 24 (by omega) (by omega) (by decide))]
  -- read32 at env survives all 7 writes (env count)
  have hread_len : read32 σ9.mem env.toNat = some len := by
    have hsurv : read32 σ9.mem env.toNat = read32 m0 env.toNat := by
      rw [hm9full,
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 32 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 40 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 48 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 56 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 8 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 16 (by omega) (by omega) (by decide)),
        read32_writeMap8_disjoint_eg7 _ _ _ _ (hdisjSlot4 env.toNat 24 (by omega) (by omega) (by decide))]
    rw [hsurv]; exact hSt.read_len
  -- read64 at env+8 survives all 7 writes (env names)
  have hread_pn : read64 σ9.mem (env.toNat + 8) = some pn := by
    have hsurv : read64 σ9.mem (env.toNat + 8) = read64 m0 (env.toNat + 8) := by
      rw [hm9full,
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 32 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 40 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 48 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 56 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 8 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 16 (by omega) (by omega) (by decide)),
        read64_writeMap8_disjoint_eg6 _ _ _ _ (hdisjSlot8 (env.toNat+8) 24 (by omega) (by omega) (by decide))]
    rw [hsurv]; exact hSt.read_pn
  -- ============ c34: mv s4,a0 → x20 := env ============
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80002c34_eg2 σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80002c34#64) vmi9 env
      hG9 hpc9 hmi9 ha0_9 hcode9 rfl hi9
  have hmem10e : σ10.mem = σ9.mem := hmem10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80002c38#64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x80002c34#64) 4 = (0x80002c38#64:BitVec 64) from by decide] at this
  have h20_10 : σ10.regs.get? Register.x20 = some env := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (env + sign_extend (m := 64) (0x000#12) : BitVec 64) = env from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have ha1_10 := obs_alu_other' hobs10 Register.x11 (by decide) ha1_9
  have ha2_10 := obs_alu_other' hobs10 Register.x12 (by decide) ha2_9
  have hsp10 := obs_alu_other' hobs10 Register.x2 (by decide) hsp9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hcode10 : Env_getLoaded σ10.mem := by rw [hmem10e]; exact hcode9
  -- ============ c38: mv s3,a1 → x19 := name ============
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80002c38_eg2 σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80002c38#64) vmi10 name hG10 hpc10 hmi10 ha1_10 hcode10 rfl hi10
  have hmem11e : σ11.mem = σ9.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80002c3c#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80002c38#64) 4 = (0x80002c3c#64:BitVec 64) from by decide] at this
  have h19_11 : σ11.regs.get? Register.x19 = some name := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (name + sign_extend (m := 64) (0x000#12) : BitVec 64) = name from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have h20_11 := obs_alu_other' hobs11 Register.x20 (by decide) h20_10
  have ha2_11 := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
  have hsp11 := obs_alu_other' hobs11 Register.x2 (by decide) hsp10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hcode11 : Env_getLoaded σ11.mem := by rw [hmem11e]; exact hcode9
  -- ============ c3c: mv s5,a2 → x21 := out ============
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80002c3c_eg2 σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80002c3c#64) vmi11 out hG11 hpc11 hmi11 ha2_11 hcode11 rfl hi11
  have hmem12e : σ12.mem = σ9.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x80002c40#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80002c3c#64) 4 = (0x80002c40#64:BitVec 64) from by decide] at this
  have h21_12 : σ12.regs.get? Register.x21 = some out := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (out + sign_extend (m := 64) (0x000#12) : BitVec 64) = out from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have h20_12 := obs_alu_other' hobs12 Register.x20 (by decide) h20_11
  have h19_12 := obs_alu_other' hobs12 Register.x19 (by decide) h19_11
  have hsp12 := obs_alu_other' hobs12 Register.x2 (by decide) hsp11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hcode12 : Env_getLoaded σ12.mem := by rw [hmem12e]; exact hcode9
  -- ============ c40: lw s2,0(s4) → x18 := sext32 (env->count) = ofNat len ============
  have hread_len12 : read32 σ12.mem env.toNat = some len := by rw [hmem12e]; exact hread_len
  obtain ⟨cb0,cb1,cb2,cb3, hcb0,hcb1,hcb2,hcb3, hcrec⟩ := read32_bytes_eg7 σ12.mem env.toNat len hread_len12
  have hc40addr : (env + sign_extend (m := 64) (0x000#12)).toNat = env.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]
  have henvW : tohostAddr + 8 ≤ env.toNat := hSt.envWin
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80002c40_eg2 σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002c40#64) vmi12 env
      cb0 cb1 cb2 cb3 hG12 hpc12 hmi12 h20_12 hcode12 rfl
      (by rw [hc40addr]; exact hSt.envLo) (by rw [hc40addr]; have := hSt.envHi; omega)
      (by rw [hc40addr]; right; rw [show tohostAddr = 0x8001ad00 from rfl] at henvW ⊢; omega)
      (by rw [hc40addr]; have := hSt.envAlign; omega)
      (by rw [hc40addr]; exact hcb0) (by rw [hc40addr]; exact hcb1)
      (by rw [hc40addr]; exact hcb2) (by rw [hc40addr]; exact hcb3) hi12
  have hmem13e : σ13.mem = σ9.mem := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80002c44#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80002c40#64) 4 = (0x80002c44#64:BitVec 64) from by decide] at this
  have h18_13 : σ13.regs.get? Register.x18 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_count_eg7 cb0 cb1 cb2 cb3 len hSt.lenSmall hcrec] at this
  have h20_13 := obs_alu_other' hobs13 Register.x20 (by decide) h20_12
  have h19_13 := obs_alu_other' hobs13 Register.x19 (by decide) h19_12
  have h21_13 := obs_alu_other' hobs13 Register.x21 (by decide) h21_12
  have hsp13 := obs_alu_other' hobs13 Register.x2 (by decide) hsp12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hcode13 : Env_getLoaded σ13.mem := by rw [hmem13e]; exact hcode9
  -- ============ c44: blez s2 NOT taken (count = len > 0) → c48 ============
  have hblez : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 len) = false := by
    -- bge x0, s2  is  0 ≥s len  which is FALSE for 0 < len < 2^31 (positive)
    have hlp := hSt.lenPos; have hls := hSt.lenSmall
    have hpos : 0 < (BitVec.ofNat 64 len).toInt := by
      rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact_mod_cast hlp
    unfold zopz0zKzJ_s
    rw [decide_eq_false_iff_not]
    simp only [BitVec.toInt_zero, ge_iff_le, Int.not_le]
    exact hpos
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80002c44_nottaken_eg2 σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002c44#64) vmi13
      (BitVec.ofNat 64 len) hG13 hpc13 hmi13 h18_13 hcode13 rfl hblez hi13
  have hmem14e : σ14.mem = σ9.mem := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80002c48#64) := by
    have := obs_bnottaken_pc hobs14; rwa [show BitVec.addInt (0x80002c44#64) 4 = (0x80002c48#64:BitVec 64) from by decide] at this
  have bcarry14 : ∀ (R : Register) (w : RegisterType R),
      (Register.minstret == R) = false → (Register.PC == R) = false →
      (Register.nextPC == R) = false → (Register.minstret_increment == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → σ13.regs.get? R = some w → σ14.regs.get? R = some w := by
    intro R w h1 h2 h4 h5 hmc hmt hmi hσ; exact obs_bnottaken_other hobs14 R hmc hmt hmi h1 h2 h4 h5 hσ
  have h18_14 := bcarry14 Register.x18 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h18_13
  have h20_14 := bcarry14 Register.x20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h20_13
  have h19_14 := bcarry14 Register.x19 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h19_13
  have h21_14 := bcarry14 Register.x21 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h21_13
  have hsp14 := bcarry14 Register.x2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp13
  obtain ⟨vmi14, hmi14⟩ := obs_bnottaken_minstret hobs14
  have hcode14 : Env_getLoaded σ14.mem := by rw [hmem14e]; exact hcode9
  -- ============ c48: ld s1,8(s4) → x9 := env->names = ofNat pn ============
  have hread_pn14 : read64 σ14.mem (env.toNat + 8) = some pn := by rw [hmem14e]; exact hread_pn
  obtain ⟨nb0,nb1,nb2,nb3,nb4,nb5,nb6,nb7, hnb0,hnb1,hnb2,hnb3,hnb4,hnb5,hnb6,hnb7⟩ :=
    ld64_bytes σ14.mem (env.toNat + 8) pn hread_pn14
  have hc48addr : (env + sign_extend (m := 64) (0x008#12)).toNat = env.toNat + 8 :=
    off_pos_eg6 env (0x008#12) 8 (by decide) (by have := hSt.envHi; omega)
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80002c48_eg2 σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002c48#64) vmi14 env
      nb0 nb1 nb2 nb3 nb4 nb5 nb6 nb7 hG14 hpc14 hmi14 h20_14 hcode14 rfl
      (by rw [hc48addr]; have := hSt.envLo; omega) (by rw [hc48addr]; have := hSt.envHi; omega)
      (by rw [hc48addr]; right; rw [show tohostAddr = 0x8001ad00 from rfl] at henvW ⊢; omega)
      (by rw [hc48addr]; have := hSt.envAlign; omega)
      (by rw [hc48addr]; exact hnb0) (by rw [hc48addr]; exact hnb1)
      (by rw [hc48addr]; exact hnb2) (by rw [hc48addr]; exact hnb3)
      (by rw [hc48addr]; exact hnb4) (by rw [hc48addr]; exact hnb5)
      (by rw [hc48addr]; exact hnb6) (by rw [hc48addr]; exact hnb7) hi14
  have hmem15e : σ15.mem = σ9.mem := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x80002c4c#64) := by
    have := obs_alu_pc hobs15; rwa [show BitVec.addInt (0x80002c48#64) 4 = (0x80002c4c#64:BitVec 64) from by decide] at this
  have h9_15 : σ15.regs.get? Register.x9 = some (BitVec.ofNat 64 pn) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ld_value_eq_read64 σ14.mem (env.toNat + 8) pn nb0 nb1 nb2 nb3 nb4 nb5 nb6 nb7 hread_pn14
      hnb0 hnb1 hnb2 hnb3 hnb4 hnb5 hnb6 hnb7] at this
  have h18_15 := obs_alu_other' hobs15 Register.x18 (by decide) h18_14
  have h20_15 := obs_alu_other' hobs15 Register.x20 (by decide) h20_14
  have h19_15 := obs_alu_other' hobs15 Register.x19 (by decide) h19_14
  have h21_15 := obs_alu_other' hobs15 Register.x21 (by decide) h21_14
  have hsp15 := obs_alu_other' hobs15 Register.x2 (by decide) hsp14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hcode15 : Env_getLoaded σ15.mem := by rw [hmem15e]; exact hcode9
  -- ============ c4c: li s0,0 → x8 := 0 ============
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80002c4c_eg2 σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002c4c#64) vmi15 hG15 hpc15 hmi15 hcode15 rfl hi15
  have hmem16e : σ16.mem = σ9.mem := by rw [hmem16]; exact hmem15e
  have hpc16 : σ16.regs.get? Register.PC = some (0x80002c50#64) := by
    have := obs_alu_pc hobs16; rwa [show BitVec.addInt (0x80002c4c#64) 4 = (0x80002c50#64:BitVec 64) from by decide] at this
  have h8_16 : σ16.regs.get? Register.x8 = some (0#64 : BitVec 64) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have h18_16 := obs_alu_other' hobs16 Register.x18 (by decide) h18_15
  have h20_16 := obs_alu_other' hobs16 Register.x20 (by decide) h20_15
  have h19_16 := obs_alu_other' hobs16 Register.x19 (by decide) h19_15
  have h21_16 := obs_alu_other' hobs16 Register.x21 (by decide) h21_15
  have h9_16 := obs_alu_other' hobs16 Register.x9 (by decide) h9_15
  have hsp16 := obs_alu_other' hobs16 Register.x2 (by decide) hsp15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hcode16 : Env_getLoaded σ16.mem := by rw [hmem16e]; exact hcode9
  -- ============ c50: j 0x80002c60 (jump_x0) → PC := c60 ============
  have hc50tgt : ((0x80002c50#64 : BitVec 64) + sign_extend (m := 64) (0x000010#21)).toNat % 4 = 0 := by decide
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80002c50_eg2 σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80002c50#64) vmi16 hG16 hpc16 hmi16 hcode16 rfl hc50tgt hi16
  have hmem17e : σ17.mem = σ9.mem := by rw [hmem17]; exact hmem16e
  have hpc17 : σ17.regs.get? Register.PC = some (0x80002c60#64) := by
    have := obs_jump_x0_pc_eg hobs17
    rwa [show (0x80002c50#64 : BitVec 64) + sign_extend (m := 64) (0x000010#21) = (0x80002c60#64:BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have h8_17 := obs_jx0_other_eg7 hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h8_16
  have h9_17 := obs_jx0_other_eg7 hobs17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h9_16
  have h18_17 := obs_jx0_other_eg7 hobs17 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h18_16
  have h19_17 := obs_jx0_other_eg7 hobs17 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h19_16
  have h20_17 := obs_jx0_other_eg7 hobs17 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h20_16
  have h21_17 := obs_jx0_other_eg7 hobs17 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h21_16
  have hsp17 := obs_jx0_other_eg7 hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp16
  have hra17 : σ17.regs.get? Register.x1 = some r0 := by
    -- ra (x1) was preserved after c24 spilled it; it is untouched by c24..c50
    have hra12 : σ12.regs.get? Register.x1 = some r0 := by
      have h0 := obs_store_other' hobs6 Register.x1 (by decide) hra5
      have h1 := obs_store_other' hobs7 Register.x1 (by decide) h0
      have h2 := obs_store_other' hobs8 Register.x1 (by decide) h1
      have h3 := obs_store_other' hobs9 Register.x1 (by decide) h2
      have h4 := obs_alu_other' hobs10 Register.x1 (by decide) h3
      have h5 := obs_alu_other' hobs11 Register.x1 (by decide) h4
      exact obs_alu_other' hobs12 Register.x1 (by decide) h5
    have h13 := obs_alu_other' hobs13 Register.x1 (by decide) hra12
    have h14 := obs_bnottaken_other' hobs14 Register.x1 (by decide) h13
    have h15 := obs_alu_other' hobs15 Register.x1 (by decide) h14
    have h16 := obs_alu_other' hobs16 Register.x1 (by decide) h15
    exact obs_jx0_other_eg7 hobs17 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h16
  have hcode17 : Env_getLoaded σ17.mem := by rw [hmem17e]; exact hcode9
  -- ==================== assemble the Steps chain and the post ====================
  have hchain : Steps c ⟨σ17, i17, _⟩ :=
    (Steps.single hstep1).trans (Steps.single hstep2) |>.trans (Steps.single hstep3)
      |>.trans (Steps.single hstep4) |>.trans (Steps.single hstep5) |>.trans (Steps.single hstep6)
      |>.trans (Steps.single hstep7) |>.trans (Steps.single hstep8) |>.trans (Steps.single hstep9)
      |>.trans (Steps.single hs10) |>.trans (Steps.single hs11) |>.trans (Steps.single hs12)
      |>.trans (Steps.single hs13) |>.trans (Steps.single hs14) |>.trans (Steps.single hs15)
      |>.trans (Steps.single hs16) |>.trans (Steps.single hs17)
  -- σ17.mem = σ9.mem = the 7-fold writeMap8; reduce each spill read to its data.
  have hm17full : σ17.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
      (writeMap8 (writeMap8 m0 ((sp0.toNat-64)+24) (sdData_val r19))
        ((sp0.toNat-64)+16) (sdData_val r20)) ((sp0.toNat-64)+8) (sdData_val r21))
        ((sp0.toNat-64)+56) (sdData_val r0)) ((sp0.toNat-64)+48) (sdData_val r8))
        ((sp0.toNat-64)+40) (sdData_val r9)) ((sp0.toNat-64)+32) (sdData_val r18) := by
    rw [hmem17e]; exact hm9full
  -- slot address `(sp0-64#64).toNat + off = (sp0.toNat-64) + off`
  have hbn : ∀ off, ((sp0 - 64#64).toNat + off) = (sp0.toNat - 64) + off := by
    intro off; rw [hspBase]
  refine ⟨⟨σ17, i17, _⟩, σ17.mem, hchain, hG17, hi17, hpc17, h20_17, h19_17, h21_17, h18_17, h9_17, h8_17,
    hra17, hsp17, rfl, hcode17, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- peel order (outer→inner): +32, +40, +48, +56, +8, +16, +24 (self stops the peel)
  -- slot +56 = r0  (writes below it: +32,+40,+48 ⇒ right)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +48 = r8  (below: +32,+40 ⇒ right)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +40 = r9  (below: +32 ⇒ right)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +32 = r18 (outermost)
  · rw [hbn, hm17full, read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +24 = r19 (innermost; above: +32,+40,+48,+56 ⇒ left, below: +8,+16 ⇒ right)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +16 = r20 (above: +32,+40,+48,+56 ⇒ left, below: +8 ⇒ right)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by right; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- slot +8 = r21 (above: +32,+40,+48,+56 ⇒ left; self)
  · rw [hbn, hm17full,
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8_disjoint_eg6 _ _ _ _ (by left; omega),
      read64_writeMap8 _ _ _, sdData_toNat]
  -- outside-the-frame bytes unchanged
  · intro a hnot
    rw [hm17full]
    have hd := hSt.spDrop
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
  -- sailOutput preserved through all 17 steps
  · rw [hobs17.out, sailOutput_sigmaPost_jump_x0, hobs16.out, sailOutput_sigmaPost_alu,
      hobs15.out, sailOutput_sigmaPost_alu, hobs14.out, sailOutput_sigmaPost_branch_nottaken,
      hobs13.out, sailOutput_sigmaPost_alu, hobs12.out, sailOutput_sigmaPost_alu,
      hobs11.out, sailOutput_sigmaPost_alu, hobs10.out, sailOutput_sigmaPost_alu,
      hobs9.out, sailOutput_sigmaPost_store, hobs8.out, sailOutput_sigmaPost_store,
      hobs7.out, sailOutput_sigmaPost_store, hobs6.out, sailOutput_sigmaPost_store,
      hobs5.out, sailOutput_sigmaPost_store, hobs4.out, sailOutput_sigmaPost_store,
      hobs3.out, sailOutput_sigmaPost_store, hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_branch_nottaken]

/-! ## FOUND-case composition with the verified prologue (`env_get_found_uncond`)

The immediate-frame FOUND case is now:

  **`env_get_prologue`** (this file, verified: `0x80002c10 → 0x80002c60`, spills the 7
  callee-saveds, loads `s4=env`/`s2=count`/`s1=names`, `s0=0`) ≫
  [`0x80002c60 → 0x80002c70`: the do-while first body + `env_get_scan_spec'` HIT
  branch + `AtHit → HitTailSt` repackaging] ≫
  **`env_get_hit_tail`** (EnvGetSpec6, verified: `0x80002c70 → ret`).

The prologue and the HIT tail are BOTH fully discharged.  The one remaining machine
residual — bundled as `hbody`, a single `Steps`-shaped hypothesis from the
post-prologue body-entry config at `0x80002c60` to a `HitTailSt` at `0x80002c70`
— is strictly SMALLER than `env_get_found_spec`'s `hreach` (which also had to cover
the whole prologue): it now covers ONLY (1) the do-while first scan iteration from
`0x80002c60` (the prologue jumps to the body, skipping the `beq` test) followed by
`env_get_scan_spec'`'s HIT branch, and (2) the `AtHit → HitTailSt` repackaging
(deriving `pv = read64 (env+16)`, the three source words, and the out/spill/src
geometry from `FrameRepr` + the prologue's spill facts).  Both pieces are DESIGNED
(the from-`c60` first body reuses `scan_iter`'s sites shifted to start at the load;
the geometry comes from `FrameRepr`/`frame_slot_valueRepr` + the prologue's seven
`read64` spill facts) but not yet threaded within this session's budget.

`env_get_found_uncond` composes the verified prologue with that residual and the
verified HIT tail into the immediate-frame FOUND post: `PC = r`, `a0 = 1`,
`*out = ValueRepr v`, callee-saved restored, `sp` popped. -/
theorem env_get_found_uncond
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (i : Nat) (pv : Nat) (w0 w1 w2 : Nat) (len pn : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) (hi : i < f.vars.length)
    (hSt : PrologueSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c)
    -- residual: from the do-while body entry (0x80002c60, post-prologue) the machine
    -- reaches the HIT-tail entry config (`HitTailSt` at 0x80002c70), first-match at `i`,
    -- return-link `r` (the incoming ra spilled at sp+56, `HitTailSt.rr_eq : rr = r`).
    (hbody : ∀ (c60 : Config) (m9 : Mem),
      c60.σ.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64) →
      c60.σ.regs.get? Register.x20 = some env → c60.σ.regs.get? Register.x19 = some name →
      c60.σ.regs.get? Register.x21 = some out → c60.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 len) →
      c60.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 pn) → c60.σ.regs.get? Register.x8 = some (0#64 : BitVec 64) →
      c60.σ.regs.get? Register.x1 = some r0 → c60.σ.regs.get? Register.x2 = some (sp0 - 64#64) →
      c60.σ.mem = m9 → GoodState c60.σ → c60.tick < 2 → Env_getLoaded m9 →
      read64 m9 ((sp0 - 64#64).toNat + 56) = some r0.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 48) = some r8.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 40) = some r9.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 32) = some r18.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 24) = some r19.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 16) = some r20.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 8) = some r21.toNat →
      ∃ (g : (R : Register) → Option (RegisterType R)) (c70 : Config),
        Steps c60 c70 ∧
        HitTailSt g env out (sp0 - 64#64) r r0 r8 r9 r18 r19 r20 r21 i pv w0 w1 w2 f N φf φc m9 c70) :
    ∃ (c' : Config) (m' : Mem),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some r ∧
      c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.regs.get? Register.x2 = some ((sp0 - 64#64) + 64#64) ∧
      c'.σ.regs.get? Register.x8 = some r8 ∧
      c'.σ.regs.get? Register.x9 = some r9 ∧
      c'.σ.regs.get? Register.x18 = some r18 ∧
      c'.σ.regs.get? Register.x19 = some r19 ∧
      c'.σ.regs.get? Register.x20 = some r20 ∧
      c'.σ.regs.get? Register.x21 = some r21 ∧
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      ValueRepr m' N φc out.toNat (f.vars[i]'hi).2 := by
  -- run the verified prologue to the body entry `c60` at 0x80002c60
  obtain ⟨c60, m9, hsP, hGP, htickP, hpcP, h20P, h19P, h21P, h18P, h9P, h8P, hraP, hspP,
    hmemP, hcodeP, s56, s48, s40, s32, s24, s16, s8, _hout, _hsout⟩ :=
    env_get_prologue env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c hSt
  -- discharge the residual body: reach the HIT-tail entry config at 0x80002c70
  obtain ⟨g, c70, hs60, hSt70⟩ :=
    hbody c60 m9 hpcP h20P h19P h21P h18P h9P h8P hraP hspP hmemP hGP htickP hcodeP
      s56 s48 s40 s32 s24 s16 s8
  -- run the verified HIT tail 0x80002c70 → ret
  obtain ⟨c', m', hsT, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', hvr, _, _⟩ :=
    env_get_hit_tail g env out (sp0 - 64#64) r r0 r8 r9 r18 r19 r20 r21 i pv w0 w1 w2 f N φf φc m9 c70 hi hSt70
  exact ⟨c', m', (hsP.trans hs60).trans hsT, hG, htick, hpc, ha0, hra, hsp',
    hx8, hx9, hx18, hx19, hx20, hx21, hmem', hcode', hvr⟩

end Vsa.Sim
