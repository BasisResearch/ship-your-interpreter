import Vsa.Sim.EnvGetSpec10

/-!
# Layer 3 — marshalling whole-store `StoreRepr` into the `env_get` FOUND contract
(`foundSt_of_storeRepr`).

`env_get_found_uncond''`/`env_get_found_framed` (EnvGetSpec9/10) consume the native
`env_get` FOUND contract `FoundSt` + `FrameStackDisj`.  The M4 caller
(`ArmEntryK`/the eval-var arm, `rows/EvalVarBridge.lean`) carries instead the WHOLE
store representation `StoreRepr m N A φf φc st.store` plus a spec-side successful
lookup `st.store.get? env x = some v`.

This file marshals the two: `foundSt_of_storeRepr` builds `FoundSt` for the
IMMEDIATE frame the lookup resolves in, out of

* the store representation at the looked-up frame `φf env` — `StoreRepr.frames env`
  is exactly `FrameRepr m N φf φc (φf env) (st.store.frames[env])`, which supplies
  `FoundSt.base.frame`, the header reads (`read_len`, `read_pn`), `len_eq`, and the
  per-slot name-CString / value-`ValueRepr` conjuncts;
* the first-match witness for the immediate hit (index `iw`, `iwHit`, `firstMatch`)
  — this is what `Store.get?`'s immediate resolution provides (`get?_immediate_hit`
  is the exact converse), giving `FoundSt.iwLt`/`iwHit`, `lenPos`, and the found
  value `v = st.store.frames[env].vars[iw].2`;
* the machine-side residue `StoreRepr` genuinely CANNOT provide — the callee's
  register-entry state (`a0..a2`, `ra`, `sp`, the six callee-saveds), all the
  RAM/HTIF/alignment geometry (`envLo`, `outLo`, `spill*`, `pvVals` bounds), the
  `ScanNames` strcmp-region carrier, `StrcmpLoaded`, `MaskPinned` — packaged as ONE
  named typed premise `EnvGetCallerGeom` (documented field-by-field).  Every field
  is a machine/layout fact the M4 caller's layout witness supplies ABOVE the store
  representation; `StoreRepr` (a pure heap-representation predicate) carries none of
  them (see the per-field notes).

`FrameStackDisj` is likewise pure heap-vs-stack disjointness geometry — the frame's
footprint (header, names/values arrays, payload strings) and the strcmp rodata/text
vs the callee's fresh stack window `[sp0-64, sp0)`.  `StoreRepr` gives the arena
bounds of `φf env` but NOT its relation to the caller-chosen `sp0`; so
`FrameStackDisj` is also taken as a caller premise (it is exactly the honest
heap-vs-stack side condition captured in EnvGetSpec9).

## What marshals cleanly vs. needs a named premise

| `FoundSt` field(s)                        | source                              |
| ----------------------------------------- | ----------------------------------- |
| `base.frame`, `read_len`, `read_pn`,      | `StoreRepr.frames env` (= FrameRepr)|
|   `len_eq`, per-slot names/values         |                                     |
| `iwLt`, `iwHit`, `lenPos`, value `v`      | the immediate-hit first-match       |
| `base` registers/geometry, `ScanNames`,   | `EnvGetCallerGeom` (caller layout)  |
|   `StrcmpLoaded`, `MaskPinned`, `pvVals`, |   — NOT in `StoreRepr`              |
|   spill/out/env geometry                  |                                     |
| `FrameStackDisj`                          | caller premise (heap-vs-stack disj) |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 800000

namespace Vsa.Sim

/-! ## The machine-side residue `StoreRepr` cannot provide (`EnvGetCallerGeom`)

Every field here is a fact about the CALLEE's entry configuration `c` (registers,
tick, GoodState) or the machine LAYOUT (RAM/HTIF/alignment bounds, the strcmp code
image, the per-binding strcmp regions) — none of which lives in a heap-representation
predicate.  The M4 caller's layout witness supplies them.  The structure mirrors
`PrologueSt`'s non-representation fields plus `FoundSt`'s scan/geometry residue, so
the assembly below is a field-by-field copy. -/
structure EnvGetCallerGeom
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String) (f : Vsa.While.Frame) (m0 : Mem) (c : Config) : Prop where
  -- callee entry register/machine state (the C ABI call frame `env_get` sees)
  good : GoodState c.σ
  loadedG : Env_getLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002c10#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some env
  a1 : c.σ.regs.get? Register.x11 = some name
  a2 : c.σ.regs.get? Register.x12 = some out
  ra : c.σ.regs.get? Register.x1 = some r0
  sp : c.σ.regs.get? Register.x2 = some sp0
  cs8  : c.σ.regs.get? Register.x8  = some r8
  cs9  : c.σ.regs.get? Register.x9  = some r9
  cs18 : c.σ.regs.get? Register.x18 = some r18
  cs19 : c.σ.regs.get? Register.x19 = some r19
  cs20 : c.σ.regs.get? Register.x20 = some r20
  cs21 : c.σ.regs.get? Register.x21 = some r21
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  tick : c.tick < 2
  envNe : (env == (0#64 : BitVec 64)) = false
  -- the scan/strcmp code image + per-binding regions (strcmp-specific, not in StoreRepr)
  loadedS : StrcmpLoaded m0
  namesC : ScanNames m0 pn name nameStr f
  pnSmall : pn < 2^64
  -- the concrete names-pointer header read pinning `pn` (FrameRepr gives it only
  -- existentially; `ScanNames`'s slots are keyed to THIS `pn`, so the caller pins it).
  read_pn : read64 m0 (env.toNat + 8) = some pn
  rLinkEq : r0 = r
  -- the caller link's 4-alignment
  rAlign : r.toNat % 4 = 0
  lenSmall : len < 2^31
  -- machine header/frame geometry (all RAM/HTIF/alignment bounds)
  envLo : 0x80000000 ≤ env.toNat
  envHi : env.toNat + 24 ≤ 0x100000000
  envWin : tohostAddr + 8 ≤ env.toNat
  envAlign : env.toNat % 8 = 0
  spDrop : 0x40 ≤ sp0.toNat
  spLo : 0x80000000 ≤ sp0.toNat - 64
  spHi : sp0.toNat ≤ 0x100000000
  spWin : tohostAddr + 64 ≤ sp0.toNat - 64
  spAlign : sp0.toNat % 8 = 0
  spCode : sp0.toNat ≤ 0x80002c10 ∨ 0x80002cdc ≤ sp0.toNat - 64
  envStackDisj : env.toNat + 24 ≤ sp0.toNat - 64 ∨ sp0.toNat ≤ env.toNat
  -- the FoundSt scan/hit-tail geometry residue (verbatim from FoundSt)
  ismall : ∀ i, i < f.vars.length → i < 2^32
  envValsLo : 0x80000000 ≤ env.toNat + 16
  envValsWin : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  envValsAlign : (env.toNat + 16) % 8 = 0
  envNoWrap : env.toNat + 24 < 2^64
  envValsHi : env.toNat + 24 ≤ 0x100000000
  outLo : 0x80000000 ≤ out.toNat
  outHi : out.toNat + 24 ≤ 0x100000000
  outWin : tohostAddr + 16 ≤ out.toNat
  outAlign : out.toNat % 8 = 0
  outCode : out.toNat + 24 ≤ 0x80002c10 ∨ 0x80002cdc ≤ out.toNat
  spillLo : 0x80000000 ≤ (sp0 - 64#64).toNat + 8
  spillHi : (sp0 - 64#64).toNat + 64 ≤ 0x100000000
  spillWin : tohostAddr + 16 ≤ (sp0 - 64#64).toNat + 8
  spillAlign : (sp0 - 64#64).toNat % 8 = 0
  spillNoWrap : (sp0 - 64#64).toNat + 64 < 2^64
  pvVals : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
    ∀ i, i < f.vars.length →
      (∃ w0 w1 w2, read64 m0 (pv + 24 * i) = some w0 ∧ read64 m0 (pv + 24 * i + 8) = some w1 ∧
        read64 m0 (pv + 24 * i + 16) = some w2) ∧
      0x80000000 ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ pv + 24 * i ∧ (pv + 24 * i) % 8 = 0 ∧ pv + 24 * i + 24 < 2^64 ∧
      pv + 24 * i < 2^64 ∧
      (pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i) ∧
      (∀ (p : Nat) (s : String), read64 m0 (pv + 24 * i + 8) = some p →
        ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k))
  outSpillDisj : out.toNat + 24 ≤ (sp0 - 64#64).toNat + 8 ∨ (sp0 - 64#64).toNat + 64 ≤ out.toNat

/-! ## `PrologueSt` from `FrameRepr` + `EnvGetCallerGeom`

The header reads `read_len`/`read_pn` come off `FrameRepr` (the immediate frame's
representation); everything else is register/geometry from `EnvGetCallerGeom`. -/
theorem prologueSt_of_frameRepr
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String) (f : Vsa.While.Frame)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hFR : FrameRepr m0 N φf φc env.toNat f)
    (hlen : len = f.vars.length) (hlenPos : 0 < f.vars.length)
    (hG : EnvGetCallerGeom env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr f m0 c) :
    PrologueSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c := by
  obtain ⟨hcnt, _hcap, _hslots, _hpar⟩ := id hFR
  exact
    { good := hG.good, loadedG := hG.loadedG, mem := hG.mem, pc := hG.pc,
      a0 := hG.a0, a1 := hG.a1, a2 := hG.a2, ra := hG.ra, sp := hG.sp,
      cs8 := hG.cs8, cs9 := hG.cs9, cs18 := hG.cs18, cs19 := hG.cs19,
      cs20 := hG.cs20, cs21 := hG.cs21, minstret := hG.minstret, tick := hG.tick,
      envNe := hG.envNe, frame := hFR, len_eq := hlen, lenPos := by rw [hlen]; exact hlenPos,
      lenSmall := hG.lenSmall,
      read_len := by rw [hlen]; exact hcnt,
      read_pn := hG.read_pn,
      envLo := hG.envLo, envHi := hG.envHi, envWin := hG.envWin, envAlign := hG.envAlign,
      spDrop := hG.spDrop, spLo := hG.spLo, spHi := hG.spHi, spWin := hG.spWin,
      spAlign := hG.spAlign, spCode := hG.spCode, envStackDisj := hG.envStackDisj }

/-! ## `FoundSt` from `StoreRepr` + the immediate hit + `EnvGetCallerGeom`

The immediate-frame first-match witness supplies `iw`/`iwHit`/`firstMatch` and the
found value; `StoreRepr.frames env` supplies the frame representation; the rest is
`EnvGetCallerGeom`. -/
set_option linter.unusedVariables false in
theorem foundSt_of_storeRepr
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (s : Store) (fa : Vsa.While.Addr) (iw : Nat) (m0 : Mem) (c : Config)
    (hSR : StoreRepr m0 N A φf φc s)
    (hfa : fa < s.frames.size)
    (henvAddr : env.toNat = φf fa)
    -- the immediate first-match (what `Store.get? s fa nameStr = some v` provides).
    -- `hbelow` is not needed for `FoundSt` (it has no first-match field, only a
    -- hit witness `iwHit`), but it IS needed for the spec verdict in the combined
    -- `envGetContract_of_storeRepr`; kept here for a uniform witness shape.
    (hiw : iw < s.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < iw) →
      ¬ (s.frames[fa].vars[j]'(Nat.lt_trans hj hiw)).1 = nameStr)
    (hhit : (s.frames[fa].vars[iw]).1 = nameStr)
    (hlen : len = s.frames[fa].vars.length)
    (hG : EnvGetCallerGeom env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr
      s.frames[fa] m0 c) :
    FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
      s.frames[fa] N φf φc m0 c := by
  have hFR : FrameRepr m0 N φf φc env.toNat s.frames[fa] := by
    rw [henvAddr]; exact hSR.frames fa hfa
  have hlenPos : 0 < s.frames[fa].vars.length := Nat.lt_of_le_of_lt (Nat.zero_le iw) hiw
  exact
    { base := prologueSt_of_frameRepr env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr
        s.frames[fa] N φf φc m0 c hFR hlen hlenPos hG,
      loadedS := hG.loadedS, namesC := hG.namesC, pnSmall := hG.pnSmall,
      rLinkEq := hG.rLinkEq, iwLt := hiw, iwHit := hhit,
      ismall := hG.ismall,
      envValsLo := hG.envValsLo, envValsWin := hG.envValsWin, envValsAlign := hG.envValsAlign,
      envNoWrap := hG.envNoWrap, envValsHi := hG.envValsHi,
      outLo := hG.outLo, outHi := hG.outHi, outWin := hG.outWin, outAlign := hG.outAlign,
      outCode := hG.outCode,
      spillLo := hG.spillLo, spillHi := hG.spillHi, spillWin := hG.spillWin,
      spillAlign := hG.spillAlign, spillNoWrap := hG.spillNoWrap,
      pvVals := hG.pvVals, outSpillDisj := hG.outSpillDisj, rAlign := hG.rAlign }

/-! ## The combined marshalling: `FoundSt` + `FrameStackDisj` from `StoreRepr`

The caller supplies the whole store `StoreRepr`, the immediate first-match, the
machine residue `EnvGetCallerGeom`, and the heap-vs-stack disjointness
`FrameStackDisj` (all four are what the M4 caller's layout witness carries).  The
found value is `s.frames[fa].vars[iw].2`, and `Store.get? s fa nameStr = some v`
holds (via `get?_immediate_hit`), so the caller's spec lookup is discharged too. -/
theorem envGetContract_of_storeRepr
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (len pn : Nat) (nameStr : String)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (s : Store) (fa : Vsa.While.Addr) (iw : Nat) (m0 : Mem) (c : Config)
    (hSR : StoreRepr m0 N A φf φc s)
    (hfa : fa < s.frames.size)
    (henvAddr : env.toNat = φf fa)
    (hiw : iw < s.frames[fa].vars.length)
    (hbelow : ∀ j, (hj : j < iw) →
      ¬ (s.frames[fa].vars[j]'(Nat.lt_trans hj hiw)).1 = nameStr)
    (hhit : (s.frames[fa].vars[iw]).1 = nameStr)
    (hlen : len = s.frames[fa].vars.length)
    (hG : EnvGetCallerGeom env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr
      s.frames[fa] m0 c)
    (hD : FrameStackDisj env name sp0 pn nameStr s.frames[fa] m0) :
    (FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw
        s.frames[fa] N φf φc m0 c ∧
      FrameStackDisj env name sp0 pn nameStr s.frames[fa] m0) ∧
    s.get? fa nameStr = some (s.frames[fa].vars[iw].2) :=
  ⟨⟨foundSt_of_storeRepr env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr
      N A φf φc s fa iw m0 c hSR hfa henvAddr hiw hbelow hhit hlen hG, hD⟩,
   get?_immediate_hit s fa nameStr iw hfa hiw hbelow hhit⟩

#print axioms prologueSt_of_frameRepr
#print axioms foundSt_of_storeRepr
#print axioms envGetContract_of_storeRepr

end Vsa.Sim
