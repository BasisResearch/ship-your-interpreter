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

/-! ## Small offset helper (positive immediate loads/stores)

`off_pos_eg6` (EnvGetSpec6) computes `(base + sext off).toNat = base.toNat + k`.
The prologue's spill offsets are all `< 0x800`, positive. -/

/-! ## The prologue standing-entry predicate (`PrologueSt`)

`PrologueSt`: at `0x80002c10` (the `env_get` entry) with the C ABI arguments
`a0=env`, `a1=name`, `a2=out`, `ra=r`, `sp=sp0`, `GoodState`, `Env_getLoaded`,
memory `m0`; the frame `f` is represented at `env` (`FrameRepr`) with at least one
binding (`0 < f.vars.length`, so the `blez` at `c44` is NOT taken); the header
reads `read32 (env)=len` and `read64 (env+8)=pn` come from `FrameRepr`.  The fresh
64-byte frame `[sp0-64, sp0)` is in RAM, above HTIF, 8-aligned, disjoint from the
code text and from the `env` frame region (`spillEnvDisj`) so all seven spills and
the two header loads commute. -/

/-! ## `lw`/`ld` header-value bridges (32-bit signed count, 64-bit names pointer) -/

/-! ## `read64`/`read32` survival across a disjoint `writeMap8`

The header reads `read32 (env)=len`, `read64 (env+8)=pn` and the running spill
reads survive each spill store (disjoint 8-byte windows).  We reuse
`read64_writeMap8_disjoint_eg6` (EnvGetSpec6) for the 8-byte reads, and derive the
4-byte survival locally. -/

/-! ## The `env_get` PROLOGUE machine `Steps` chain (verified)

**`env_get_prologue`.** From `PrologueSt` at `0x80002c10`, the 17-instruction
prologue runs to the do-while body entry `0x80002c60` with the scan live registers
established and the seven callee-saved spill slots written into the fresh frame
`[sp0-64, sp0)`.  Fully verified. -/

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

end Vsa.Sim
