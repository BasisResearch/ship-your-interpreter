import Vsa.Sim.NativeWrapperSites
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.EvalCallNative2
import Vsa.Sim.DecodeTable.Batch02Part01

/-!
# Layer 4 — M4: the native dispatch / `jalr` wrapper (shared assert/print/println)

`EvalCallNative2.lean` lands `nativeAssertInternal` — the `native_assert`
INTERNAL run (`0x80002df4 … ret`) in its own 80-byte frame, from `naEntry` (the
ABI *after* the arm's marshal) to `naExit` (`.null` in the CALL sret). This file
lands the surrounding WRAPPER — the fv-kind dispatch (`0x80003254`), the native
arm's register marshal (`0x800039e0`), and the **indirect `jalr a6`**
(`0x800039f4`) — as a reusable per-site battery + the hand `jalr` site, so that

    NativeAssertOkSpec  =  dispatch  ≫  arm-marshal  ≫  jalr  ≫
                           nativeAssertInternal  ≫  (ld s7 ; j callJoinPC)

can be assembled (see the compose note at the bottom). The wrapper is SHARED by
`Call.print`/`println`/`assertOk`: the ONLY difference is the value of `a6` at
the `jalr` (`= N.addr .print` / `.println` / `.assert`), pinned from
`ValueRepr (.native f)` (`read64 m (fvAddr+16) = some (N.addr f)`,
`RuntimeRepr.lean:86`), and which native's internal run is composed after.

## The decoded wrapper (from `CallEntry.lean` / the memory note)

### fv-kind dispatch `0x80003254 … 0x8000327c` (`NativeWrapperSites`, `_nw`)
```
80003254  ld   a4,96(sp)     -- a4 = *(sp+96)  = fv word0 (kind in low 32)
80003258  ld   a3,104(sp)    -- a3 = fv word1
8000325c  ld   a6,112(sp)    -- a6 = *(sp+112) = fv word2 = N.addr f  (fn ptr)
80003260  lw   a1,4(s0)      -- a1 = e->line  (noise)
80003264  sd   a4,120(sp)    -- restage fv word0
80003268  lw   a4,96(sp)     -- a4 = fv->kind (low word) = 5
8000326c  sd   a3,128(sp)    -- restage fv word1
80003270  sd   a6,136(sp)    -- restage fv word2 (fn ptr)
80003274  li   a2,5          -- VAL_NATIVE
80003278  mv   s7,a1
8000327c  beq  a4,a2,0x800039e0  -- kind==5 ⇒ native arm (TAKEN; Call.native ⇒ kind 5)
```
The four `sd`s land in the caller's frame at `sp+120/128/136` — disjoint from
`eval_expr`'s code region `[0x80003164,0x80003fe0)`, so `Eval_exprLoaded`
survives them (`loaded_eval_expr_writeMap8_ee`, `EvalIntSim2.lean`).

### native arm marshal `0x800039e0 … 0x800039f4` (`_nw` + the hand `jalr` here)
```
800039e0  mv   a4,a1         -- a4 := a1(old) = scratch (e->line; native reads a4 as scratch)
800039e4  mv   a2,a5         -- a2 := a5(old) = argc    (a5 preserved through dispatch)
800039e8  mv   a1,s2         -- a1 := s2      = interp
800039ec  addi a3,sp,240     -- a3 := sp+240  = arg Value-array base  (NOT scratch!)
800039f0  mv   a0,s1         -- a0 := s1      = CALL sret
800039f4  jalr a6            -- a6 = N.addr f  (indirect native dispatch)  ← HERE
```
**ABI CORRECTION** (the `CallEntry.lean` prose comment is loose; this is the real
register map, cross-checked against `native_assert`'s entry decode
`addiw a6,a2,-1 ; ld a1,0(a3)`): after the arm, `a0=sret`, `a1=interp`,
`a2=argc`, `a3 = sp+240 = argsBase`, `a4=scratch`, `a6=N.addr f`, `ra=0x800039f8`.
This matches `native_assert`'s `naEntry` (x10=sret, x11=interp, x12=argc,
x13=argsBase, x14=scratch) with `fsp = sp` (native_assert's prologue subtracts
80). So the compose sets `argc := a5@arm-entry` (= x15, untouched by the dispatch,
which writes only x14/x13/x16/x11/x23), `argsBase := sp+240`, `scratch := a1@arm-
entry` (= e->line after `lw a1,4(s0)`), `interp := s2`, `sret := s1`. The
`native_assert` `naEntry.hargsFrame` (`argsBase` disjoint from `[fsp-80,fsp+40)`)
holds since `argsBase = sp+240 > sp+40`.

### return join `0x800039f8 … 0x800039fc` (`_nw`)
```
800039f8  ld   s7,1016(sp)   -- restore s7
800039fc  j    0x800033ec    -- join the eval_expr epilogue (callJoinPC)
```

## What lands here
* `site_800039f4_nw` — the hand `jalr a6` site (`stepObs_jalr`,
  `SnprintfSitesRet5.lean`), completing the decode battery. The link is
  `ra := 0x800039f8`; the target is the bit-0-cleared `a6 = N.addr f`
  (`ValueRepr (.native f)` pins `a6`), so the indirect call resolves to the
  native's entry unconditionally.

The 18 straight-line + branch sites of `NativeWrapperSites.lean` plus this
`jalr` site are the complete instruction-level decode of the shared wrapper.
Assembling them into `NativeAssertOkSpec` (discharging `callAssertOk`
unconditionally) additionally needs the `SegEntry`→concrete-ABI bridge — see the
compose note below. NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The indirect native dispatch `jalr a6` (`0x800039f4`).** Links
`ra := 0x800039f8` and jumps to the bit-0-cleared `a6` — which, for a
`ValueRepr (.native f)`-staged `fv`, is `N.addr f` (the native entry). Hand
site over `stepObs_jalr` (`SnprintfSitesRet5.lean`), mirroring the locale
`mbtowc` indirect call (`site_80007740_rt5`). Reusable by assert/print/println
(they differ only in `a6`'s value). -/
theorem site_800039f4_nw (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800039f4#64 : BitVec 64))
    (htgt : (BitVec.update (v16 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jalr σ pc vminstret
        (BitVec.update (v16 + sign_extend (m := 64) (0x000#12)) 0 0#1)
        Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800039f4 hmem
  refine stepObs_jalr σ i u (0x800039f4#64) vminstret v16 (0x000800e7#32) (0x000#12)
    (regidx.Regidx 0x10#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800039f4#64) 4)
    (0xe7#8) (0x00#8) (0x08#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_000800e7 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x16 _ v16
      (by rw [get?_afterNextPC σ (0x800039f4#64) _ (by decide) (by decide)]; exact hx16))
    htgt
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800039f4#64) 4)

/-! ## `jalr` target = `N.addr f` (from `ValueRepr (.native f)`)

The `jalr a6` target is the bit-0-cleared `a6`. `a6` is loaded at `0x8000325c`
from the staged `fv` word2 (`*(sp+112)`). `ValueRepr (.native f)` pins
`read64 m (fvAddr+16) = some (N.addr f)` (`RuntimeRepr.lean:86`), so once the
staged `fv` word2 equals the arg-vector's `fv`, `a6 = N.addr f` and the target
is `N.addr f` (already 4-aligned for a code entry). This resolves the indirect
call to `native_assert`'s entry (`= N.addr .assert = 0x80002df4`) for the
`assert` case; `.print`/`.println` land at their own entries. -/

/-- The staged native fn ptr `a6` gives the `jalr` its target: the bit-0-cleared
`a6` is `a6` itself when `a6` is 4-aligned (a native code entry always is — every
RISC-V instruction address is 4-aligned). Packaged so the wrapper compose can
rewrite the `jalr` target to the native entry `a6 = N.addr f`. Reuses `ret_tgt`
(`Muldi3Spec`), the same bit-0-clear-is-no-op fact the `ret`/`jr` sites use. -/
theorem jalr_native_target (a6 : BitVec 64) (halign : a6.toNat % 4 = 0) :
    BitVec.update (a6 + sign_extend (m := 64) (0x000#12)) 0 0#1 = a6 :=
  ret_tgt a6 halign

/-! ## Compose note — assembling `NativeAssertOkSpec` (`callAssertOk`
UNCONDITIONAL)

With the full decode battery in hand (18 `_nw` sites + `site_800039f4_nw` +
`nativeAssertInternal`), the remaining work to discharge `NativeAssertOkSpec`
(and make `callAssertOk` unconditional) is the `SegEntry`→concrete-ABI BRIDGE:

`CallEntryP` (= `SegEntry` at `callDispatchPC`) exposes only `StoreRepr`,
`OutRepr`, the ghost frame on `AbiPreservedNoise` regs, budgets, and `mem = m0`.
It does NOT name the concrete native-call geometry the dispatch decode reads —
`sp`, `x9=s1=sret`, `x18=s2=interp`, `x15=a5=argc`, the staged `fv` words at
`sp+96/112`, the arg Value-array at `sp+240` with `ValueRepr m N φc (sp+240) v`,
and the region facts (the caller frame `sp+96…` window vs `native_assert`'s
`[sp-80,sp+40)` frame vs the arg Value-array at `sp+240`). Those are established
by the CALLER (`evalCallSim`'s `CallArmSpec`) and abstracted away by the
`SegEntry` skeleton.

So `NativeAssertOkSpec` is dischargeable only once that geometry is threaded —
either by ENRICHING the `SegEntry` skeleton with the native-call ABI fields
(a cross-cutting scaffold change touching every `SegEntry` consumer) or by
carrying it as an explicit MINIMAL-GEOMETRY hypothesis bundle on `callAssertOk`
(a `CallNativeGeom` predicate: the register + staged-`fv` + `ValueRepr` + region
facts), and then running:

    dispatch (`site_80003254_nw … site_8000327c_taken_nw`, `beq` TAKEN via
      `kind = 5` from `ValueRepr (.native)`)
  ≫ arm marshal (`site_800039e0_nw … site_800039f0_nw`)
  ≫ `site_800039f4_nw` (`jalr`, target `= N.addr .assert` via
      `jalr_native_target` + the `a6 = N.addr .assert` fact)
  ≫ `nativeAssertInternal` (`fsp := sp`, `naEntry` ABI matched)
  ≫ `site_800039f8_nw` (`ld s7`) ≫ `site_800039fc_nw` (`j callJoinPC`)

then rebuild `CallExitP` (= `SegExit` at `callJoinPC`): the store is UNCHANGED
(`Call.assertOk` returns `st`), so reuse `φf`/`φc` (`PhiExtends.refl`); the
output is unchanged (`OutRepr`); `memFrame` holds because the whole run only
scribbles the caller stack window + the `sret`/scratch buffers, all outside the
arena (and the stack carve-out `SL.lo…SL.hi`). The `.null` `ValueRepr` at `sret`
from `nativeAssertInternal`'s `naExit` re-expresses the CALL result.
-/

end Vsa.Sim
