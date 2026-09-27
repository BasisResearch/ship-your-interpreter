import Vsa.Sim.BridgeSeg

/-!
# `BridgeSegFramed` — the avoid-set-generic frame core

`FrameMeta.abiFrame_of_wrChain` (and its consumer `BridgeSeg.bridgeOfSeg`) collapse
a reflected span's raw register-frame clause

    ∀ R, (∀ rr ∈ noiseRegs, (rr == R) = false) →
         (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R

to the callee-contract shape `∀ R, AbiPreserved R = true → get? R = get? R`, under
the ONE `decide` datum `WrChainAvoidAbi bs` (no register the span writes is
callee-saved). The closure-arm dispatch head genuinely writes callee-saved
registers, so `WrChainAvoidAbi` legitimately fails:

* The closure-arm dispatch head `0x80003254..0x800032b8` (`mv s7,a1` at
  `0x80003278`, `mv s5,a4` at `0x80003290` — deliberate callee-saved *reseats*
  before the `jal env_new @0x800032bc`).  `wrChain` here contains `{x21, x23}`,
  both `AbiPreserved`.

## Design verdict

The frame machinery's *kernel* (`FrameMeta.abiPreserved_ne`) is already avoid-set
generic — it proves `(X == R) = false` from `R`, `X` on opposite sides of the SAME
predicate.  Only the *packaging* (`WrChainAvoidAbi`, `noise_ne_abi`,
`abiFrame_of_wrChain`) is hardcoded to `AbiPreserved`.  This file factors the
hardcoding out: ONE generic `wrChain_avoids_frame (P : Register → Bool)` core, with
`AbiPreserved` re-expressed as a THIN instance (the landed path, consumers
untouched).

The closure head genuinely needs spill/delta EXPOSURE, not an avoid-set swap.
`s5` and `s7` are both written and callee-saved, so no non-trivial predicate
collapse recovers their frame — the frame simply does not hold for them. The seg
already computes the reseated values in `out.regs` (`GHolds σ' out.regs`);
`bridgeOfSegFramed` exposes that directly, and asserts the ABI frame only for the
callee-saved registers the span does not write.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. The avoid-set-generic frame core

The whole `FrameMeta` (c) layer, parameterised by an arbitrary decidable bool
predicate `P : Register → Bool`.  `AbiPreserved` is one `P`; the error-branch
`NotWrittenJmp`-shaped set is another. -/

/-! ### Instance 1 — `AbiPreserved` (re-expressing the landed path)

`WrChainAvoids AbiPreserved` and `frame_of_wrChain_avoids (P := AbiPreserved)` ARE
`FrameMeta.WrChainAvoidAbi` / `FrameMeta.abiFrame_of_wrChain` — verified equal
below.  The landed `bridgeOfSeg` path is unchanged; this just exhibits it as the
`P := AbiPreserved` specialisation of the generic core. -/

/-! ## §2. `bridgeOfSegFramed` — the ABI-mutating jal-terminated bridge

`BridgeSeg.bridgeOfSeg` requires `WrChainAvoidAbi bs`, so it produces an ABI frame
`∀ R, AbiPreserved R → get? R = get? R` over the WHOLE callee-saved set.  A span
that reseats callee-saveds (consumer (a): `mv s7`, `mv s5`) cannot satisfy that.

`bridgeOfSegFramed` keeps everything `bridgeOfSeg` gives — the seg run, the jal
seam, the marshalled args' survival, the memory `writeLog m0 out.log`, the minstret
witness — but replaces the ABI-frame conclusion with the generic `P`-frame
(`frame_of_wrChain_avoids`).  A consumer instantiates `P` at the callee-saveds the
span does NOT write; the reseated ones (`s5`/`s7`) are read off the *exposed*
`GHolds σ2 out.regs` post — the deltas, already computed by the seg, are the "spill
tracking" the observation `callclosure-entrybase-abi` asked for, and they come FREE.

The genuinely per-callee jal seam is still the `JalStep` datum; only the frame
predicate is swapped from `AbiPreserved` (hardcoded) to caller-supplied `P`. -/

/-! ## §4. Demo (a) — the closure entryBase callee-saved reseat, via `bridgeOfSegFramed`

The closure-arm dispatch head `0x80003254..0x800032b8` reseats TWO callee-saved
registers before its `jal env_new @0x800032bc`: `mv s7,a1` (`x23 := x11`) at
`0x80003278` and `mv s5,a4` (`x21 := x14`) at `0x80003290`.  So `wrChain` contains
`{x21, x23}`, both `AbiPreserved` — `WrChainAvoidAbi` FAILS and `bridgeOfSeg` is
inapplicable (observation `callclosure-entrybase-abi`).

Here we demonstrate `bridgeOfSegFramed` on the load-bearing idiom — the real
`mv s7,a1` reseat (`0x80003278`, word `0x00058b93`).  The frame predicate is
`AbiPreserved` RESTRICTED to drop the written `x23` (`P := fun R => AbiPreserved R
&& !(R == x23)`); the reseated `s7 = a1` value is read off the EXPOSED post register
bundle `GHolds σ2 out.regs` — the "spill tracking" the observation asked for, FREE
from the seg.  The full 5-block entryBase (with its 4 guard branches) composes the
same way; the interior branches are a separate `#derive_case chain` `ChainOK`
concern, orthogonal to the frame issue this file resolves. -/

/-! The `mv s7,a1` reseat block (`0x80003278: addi x23,x11,0`), the callee-saved
write that defeats `WrChainAvoidAbi`. -/
   -- addi x23,x11,0  (= mv s7,a1)

end Vsa.Sim
