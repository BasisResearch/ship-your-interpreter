import Vsa.Sim.rows.ConcatStringifyLArg
import Vsa.Sim.BridgeSegFramed

/-!
# `concatStringifyRArg` — the concat arm's stringify(R) arg-staging span (0x80003a44)

Task Wave-35, Residual 2.  The R staging span `0x80003a44 → 0x80003a68`
(jal-terminated into `stringify@0x80002fc0`) is the twin of the L span
(`ConcatStringifyLArg`), with one crucial difference: it contains the two
callee-saved *reseats* `mv s2,a0` (`x18 := a0`) and `mv s3,a0` (`x19 := a0`) that
park the just-returned stringify(L) pointer.  Because `s2 = x18` and `s3 = x19` are
`AbiPreserved`, `WrChainAvoidAbi` is FALSE — the plain `bridgeOfSeg` ABI no-op fails
(exactly the failure genseg emitted silently as a false `decide → sorryAx`; see the
genseg audit in `experiments/logs/wave35-concat-resid.md`).

The RIGHT tool is `BridgeSegFramed.bridgeOfSegFramed` with the avoid-set
`AbiExceptS2S3` (callee-saved EXCEPT the reseated `s2`/`s3`), exactly the way the
strdup/closure-entry reseats use `AbiExceptS7` (`BridgeSegFramed.entryBaseReseat_framed`).
The combinator produces: parked at the callee entry, `x1 = link`, the whole EXPOSED
reseated register bundle (`GHolds σ2 out.regs`, carrying the new `s2 = s3 = a0`), and
the ABI frame for every callee-saved EXCEPT `s2`/`s3`.

```
80003a44  ld a3,144(sp)   0x09013683
80003a48  ld a4,152(sp)   0x09813703
80003a4c  ld a5,160(sp)   0x0a013783
80003a50  mv s2,a0        0x00050913   (addi x18,x10,0) — reseat callee-saved s2
80003a54  mv s3,a0        0x00050993   (addi x19,x10,0) — reseat callee-saved s3
80003a58  addi a0,sp,64   0x04010513
80003a5c  sd a3,64(sp)    0x04d13023
80003a60  sd a4,72(sp)    0x04e13423
80003a64  sd a5,80(sp)    0x04f13823   ▷ jal stringify@0x80002fc0
```

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- The `concatStringifyRArg` span body `0x80003a44 → 0x80003a68` (jal-terminated,
1 block), decoded from `experiments/disasm.txt`. -/
#derive_case concatStringifyRArgSeg chain
  [(0x80003a44#64, 0x09013683#32),  -- ld a3,144(sp)
   (0x80003a48#64, 0x09813703#32),  -- ld a4,152(sp)
   (0x80003a4c#64, 0x0a013783#32),  -- ld a5,160(sp)
   (0x80003a50#64, 0x00050913#32),  -- mv s2,a0  (addi x18,x10,0)
   (0x80003a54#64, 0x00050993#32),  -- mv s3,a0  (addi x19,x10,0)
   (0x80003a58#64, 0x04010513#32),  -- addi a0,sp,64
   (0x80003a5c#64, 0x04d13023#32),  -- sd a3,64(sp)
   (0x80003a60#64, 0x04e13423#32),  -- sd a4,72(sp)
   (0x80003a64#64, 0x04f13823#32)]  -- sd a5,80(sp)

#print axioms concatStringifyRArgSeg_seg

/-- The `concatStringifyRArg` entry pin list — the registers the body reads: `x2`
(sp, for the loads/stores) and `x10` (a0 = the stringify(L) result being parked into
`s2`/`s3`). -/
def concatStringifyRArgL (sp a0v : BitVec 64) : GRegs := [(2, sp), (10, a0v)]

/-- The restricted ABI frame predicate: callee-saved EXCEPT the reseated `s2 = x18`
and `s3 = x19`.  `bridgeOfSegFramed`'s frame conclusion holds for exactly these; the
new `s2`/`s3` values are read off the exposed post bundle instead. -/
def AbiExceptS2S3 (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x18) && !(R == Register.x19)

/-- **`concatStringifyRArgBridge`** — the R staging body ≫ `jal stringify` bridge, via
`bridgeOfSegFramed` at `AbiExceptS2S3`.  The seg run + the restricted ABI frame are
FREE; the reseated `s2 = s3 = a0v` are read off the EXPOSED post bundle.  `hfacts`
(memory chain-facts) and `hjalSeam` (the call-seam `JalStep`) are the only
region-specific residuals.  Conclusion: parked at the callee entry `0x80002fc0` with
link `0x80003a6c`, memory = the seg write-log, `s2 = s3 = a0v` exposed, and the ABI
frame for every callee-saved EXCEPT `s2`/`s3`. -/
theorem concatStringifyRArgBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64) (sp a0v : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003a44#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (concatStringifyRArgL sp a0v))
    (hfacts : ChainFacts σ.mem σ.mem (concatStringifyRArgL sp a0v) [] concatStringifyRArgSeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks concatStringifyRArgSeg
      (SegEvalState.init (concatStringifyRArgL sp a0v) [])).regs))
    (hRaOut : KeysAvoidRa (evalBlocks concatStringifyRArgSeg
      (SegEvalState.init (concatStringifyRArgL sp a0v) [])).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003a44#64 (SegEvalState.init (concatStringifyRArgL sp a0v) [])
          concatStringifyRArgSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks concatStringifyRArgSeg
        (SegEvalState.init (concatStringifyRArgL sp a0v) [])).log →
      GHolds σ' (evalBlocks concatStringifyRArgSeg
        (SegEvalState.init (concatStringifyRArgL sp a0v) [])).regs →
      JalStep 0x80002fc0#64 0x80003a6c#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel concatStringifyRArgSeg + 1⟩ ∧ i2 < 2 ∧
      GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80002fc0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003a6c#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      -- the whole reseated register bundle, EXPOSED (carries the new `s2 = s3 = a0v`
      -- as deltas the seg computed — read off via `gholds_lookup` by any consumer):
      GHolds σ2 (evalBlocks concatStringifyRArgSeg
        (SegEvalState.init (concatStringifyRArgL sp a0v) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks concatStringifyRArgSeg
        (SegEvalState.init (concatStringifyRArgL sp a0v) [])).log ∧
      -- the ABI frame for every callee-saved EXCEPT the reseated `s2`/`s3`:
      (∀ R, AbiExceptS2S3 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  have hkeys : KeysOK (keysG (concatStringifyRArgL sp a0v)) := by
    show KeysOK [2, 10]; decide
  have hwf : ChainOK 0x80003a44#64 (keysG (concatStringifyRArgL sp a0v)) concatStringifyRArgSeg := by
    show ChainOK 0x80003a44#64 [2, 10] concatStringifyRArgSeg; decide
  have hnoiseP : ∀ rr ∈ noiseRegs, AbiExceptS2S3 rr = false := by decide
  have hAvoidP : WrChainAvoids AbiExceptS2S3 concatStringifyRArgSeg := by decide
  -- `AbiExceptS2S3 R → AbiPreserved R`: the restricted predicate is a subset (Bool `&&`).
  have hPabi : ∀ R, AbiExceptS2S3 R = true → AbiPreserved R = true := by
    intro R hR
    unfold AbiExceptS2S3 at hR
    exact (Bool.and_eq_true .. |>.mp ((Bool.and_eq_true .. |>.mp hR).1)).1
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    bridgeOfSegFramed AbiExceptS2S3 concatStringifyRArgSeg (concatStringifyRArgL sp a0v) []
      σ i u 0x80003a44#64 0x80002fc0#64 0x80003a6c#64 vminstret m0
      hG hpc hminstret hmem hL hkeys hfacts hi hwf
      hnoiseP hAvoidP hKeysOut hRaOut hPabi hjalSeam
  exact ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩

#print axioms concatStringifyRArgBridge

/-! ## The reseated `s2`/`s3` are carried in the exposed bundle

The `mv s2,a0`/`mv s3,a0` reseats wrote `x18 := x19 := a0v` (the parked stringify(L)
pointer).  These are NOT dropped by the restricted frame — they live in the EXPOSED
`GHolds σ2 out.regs` post the bridge conclusion carries.  Because the seg body
contains LOADS before the reseats, a consumer reads them back through the
`SegReadback` peel bricks (`gholds_lookup_ld` + `lookupG_runGM_snoc` +
`srcVal_runGM_ne`), NOT a plain `rfl` (which native-stack-overflows on the
load-bearing fold — the documented `loadbearing-seg-register-readback` idiom).  The
concat-heap-core consumer performs that read at its use site; here we deliver the
bundle. -/

end Vsa.Sim
