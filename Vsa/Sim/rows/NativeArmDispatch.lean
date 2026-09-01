import Vsa.Sim.rows.NativeAddrResolve
import Vsa.Sim.BridgeSegFramed

/-!
# `nativeDispatchStage` — the native-route dispatch/marshal span (wave 41)

The machine body of the `nativeArmSplice` dispatch leg: the fv-kind dispatch
`0x80003254 → 0x8000327c` (`beq a4,a2` **TAKEN** — `kind = 5`, the native
route) chained with the native arm's register marshal `0x800039e0 →
0x800039f0`, parked at the **`jalr a6`** (`0x800039f4`).  The seam is the
indirect-call `JalStep a6v 0x800039f8` (`nativeJalrStep`,
`rows/NativeAddrResolve.lean`) — `a6v = N.addr f` once the caller ties the
`sp+112` staged-`fv` load (`lds`) to `nativeAddr_of_valueRepr`.

The TWIN of `rows/CallClosureDispatchStage.lean` (same entry block, branch
polarity flipped): `genseg.py` HARD-ERRORS on this span too (`mv s7,a1` at
`0x80003278` reseats the callee-saved `s7 = x23`, so `WrChainAvoidAbi` is
FALSE); the right tool is `BridgeSegFramed.bridgeOfSegFramed` at the
restricted avoid-set `AbiExceptS7`.  Unlike the closure route this span spills
NO further callee-saveds (`s5`/`s3` are the closure head's), so only `s7` is
excluded.

```
80003254  ld a4,96(sp)      -- fv word0 (kind)
80003258  ld a3,104(sp)     -- fv word1
8000325c  ld a6,112(sp)     -- fv word2 = the native fn ptr  (→ the jalr target)
80003260  lw a1,4(s0)       -- e->line (noise)
80003264  sd a4,120(sp)     -- 24-byte fv restage …
80003268  lw a4,96(sp)      -- kind reload (word)
8000326c  sd a3,128(sp)
80003270  sd a6,136(sp)
80003274  li a2,5
80003278  mv s7,a1          -- RESEAT s7 (callee-saved!)
8000327c  ▷ beq a4,a2 → 0x800039e0   (TAKEN: kind = 5 = VAL_NATIVE)
800039e0  mv a4,a1          -- a4 := scratch (e->line)
800039e4  mv a2,a5          -- a2 := argc
800039e8  mv a1,s2          -- a1 := interp
800039ec  addi a3,sp,240    -- a3 := argsBase (sp+240)
800039f0  mv a0,s1          -- a0 := CALL sret
          ▷ jalr a6 @0x800039f4  (the indirect seam, link 0x800039f8)
```

The TAKEN-`beq` guard obligation (`kind word = 5`) lives in the caller's
`ChainFacts` (dischargeable from `nativeKind_of_valueRepr`); `lds` is threaded
PARAMETRICALLY (observation `genseg-jal-rows-zero-pin-loads`).

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

/- The `nativeDispatchStage` span body `0x80003254 → 0x800039f0` (2 blocks,
TAKEN beq mid-chain, parked at the `jalr` seam), decoded from
`experiments/disasm.txt`. -/
#derive_case nativeDispatchStageSeg chain
  [(0x80003254#64, 0x06013703#32),  -- ld a4,96(sp)
   (0x80003258#64, 0x06813683#32),  -- ld a3,104(sp)
   (0x8000325c#64, 0x07013803#32),  -- ld a6,112(sp)
   (0x80003260#64, 0x00442583#32),  -- lw a1,4(s0)
   (0x80003264#64, 0x06e13c23#32),  -- sd a4,120(sp)
   (0x80003268#64, 0x06012703#32),  -- lw a4,96(sp)
   (0x8000326c#64, 0x08d13023#32),  -- sd a3,128(sp)
   (0x80003270#64, 0x09013423#32),  -- sd a6,136(sp)
   (0x80003274#64, 0x00500613#32),  -- li a2,5
   (0x80003278#64, 0x00058b93#32)]  -- mv s7,a1  (addi x23,x11,0)
    terminator ⟨0x8000327c#64, 0x76c70263#32, 0x63#8, 0x02#8, 0xc7#8, 0x76#8,
      .br bop.BEQ true, 14, 12, 0x0764#13, 0#21, 0#12⟩ ;;
  [(0x800039e0#64, 0x00058713#32),  -- mv a4,a1  (addi x14,x11,0)
   (0x800039e4#64, 0x00078613#32),  -- mv a2,a5  (addi x12,x15,0)
   (0x800039e8#64, 0x00090593#32),  -- mv a1,s2  (addi x11,x18,0)
   (0x800039ec#64, 0x0f010693#32),  -- addi a3,sp,240
   (0x800039f0#64, 0x00048513#32)]  -- mv a0,s1  (addi x10,x9,0)

#print axioms nativeDispatchStageSeg_seg

/-- The `nativeDispatchStage` entry pin list — the registers the body reads:
`x2` (sp — the fv staging loads + `addi a3,sp,240`), `x8` (s0 = the EX_CALL
node, `lw a1,4(s0)`), `x15` (a5 = argc, marshalled to `a2`), `x18` (s2 =
interp, marshalled to `a1`), `x9` (s1 = the CALL sret, marshalled to `a0`). -/
def nativeDispatchStageL (sp s0v a5v s2v s1v : BitVec 64) : GRegs :=
  [(2, sp), (8, s0v), (15, a5v), (18, s2v), (9, s1v)]

/- The restricted ABI frame predicate `AbiExceptS7` (callee-saved EXCEPT the
reseated `s7 = x23` — the ONLY callee-saved this span writes) is REUSED from
`BridgeSegFramed.lean:398`. -/

/-- **`nativeDispatchStageBridge`** — the dispatch/marshal body ≫ `jalr a6`
bridge, via `bridgeOfSegFramed` at `AbiExceptS7`.  The seg run + the
restricted ABI frame are FREE; `hfacts` (memory chain-facts, incl. the TAKEN
`beq` guard `kind = 5`) and `hjalSeam` (the indirect `JalStep a6v 0x800039f8`
— dischargeable by `nativeDispatchJalSeam_of` below) are the region-specific
residuals.  Conclusion: parked at the native entry `a6v` with link
`0x800039f8`, memory = the seg write-log (the fv restage at `120..136(sp)`),
the reseated `s7` exposed in the post bundle, and the ABI frame for every
callee-saved except `s7`. -/
theorem nativeDispatchStageBridge
    (σ : MState) (i u : Nat) (vminstret a6v : BitVec 64)
    (sp s0v a5v s2v s1v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003254#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (nativeDispatchStageL sp s0v a5v s2v s1v))
    (hfacts : ChainFacts σ.mem σ.mem (nativeDispatchStageL sp s0v a5v s2v s1v)
      lds nativeDispatchStageSeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks nativeDispatchStageSeg
      (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks nativeDispatchStageSeg
      (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003254#64
          (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)
          nativeDispatchStageSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).log →
      GHolds σ' (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs →
      JalStep a6v 0x800039f8#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel nativeDispatchStageSeg + 1⟩ ∧
      i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some a6v ∧
      σ2.regs.get? Register.x1 = some (0x800039f8#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      -- the whole marshalled register bundle, EXPOSED (a0..a4 + the reseated s7):
      GHolds σ2 (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).log ∧
      -- the ABI frame for every callee-saved EXCEPT the reseated s7:
      (∀ R, AbiExceptS7 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  have hkeys : KeysOK (keysG (nativeDispatchStageL sp s0v a5v s2v s1v)) := by
    show KeysOK [2, 8, 15, 18, 9]; decide
  have hwf : ChainOK 0x80003254#64 (keysG (nativeDispatchStageL sp s0v a5v s2v s1v))
      nativeDispatchStageSeg := by
    show ChainOK 0x80003254#64 [2, 8, 15, 18, 9] nativeDispatchStageSeg; decide
  have hnoiseP : ∀ rr ∈ noiseRegs, AbiExceptS7 rr = false := by decide
  have hAvoidP : WrChainAvoids AbiExceptS7 nativeDispatchStageSeg := by decide
  have hPabi : ∀ R, AbiExceptS7 R = true → AbiPreserved R = true := by
    intro R hR
    unfold AbiExceptS7 at hR
    exact (Bool.and_eq_true .. |>.mp hR).1
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    bridgeOfSegFramed AbiExceptS7 nativeDispatchStageSeg
      (nativeDispatchStageL sp s0v a5v s2v s1v) lds
      σ i u 0x80003254#64 a6v 0x800039f8#64 vminstret m0
      hG hpc hminstret hmem hL hkeys hfacts hi hwf
      hnoiseP hAvoidP hKeysOut hRaOut hPabi hjalSeam
  exact ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩

#print axioms nativeDispatchStageBridge

/-! ## The `jalr` seam residual, discharged

Unlike a `jal` bridge (whose seam is a per-callee `site_*` obs), the native
seam is ONE reusable lemma: `nativeJalrStep` fires at the parked config
provided the caller supplies (a) the parked PC computes to `0x800039f4`
(`hpcEq` — a seg-static fact, closed at concrete `lds`), (b) the computed
out-regs pin `x16 = a6v` (the `sp+112` load's `lds` slot — `gholds_lookup` at
concrete `lds`), (c) `eval_expr`'s code survives the seg's stack writes
(`hloadOut` — geometry: the fv restage window is off the code region), and
(d) the 4-alignment of the native entry. -/
theorem nativeDispatchJalSeam_of
    (a6v : BitVec 64) (sp s0v a5v s2v s1v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hpcEq : evalBlocksPC 0x80003254#64
      (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)
      nativeDispatchStageSeg = (0x800039f4#64 : BitVec 64))
    (hx16pin : ∀ σ' : MState,
      GHolds σ' (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs →
      σ'.regs.get? Register.x16 = some a6v)
    (hloadOut : Vsa.Sim.Code.Eval_exprLoaded (writeLog m0
      (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).log))
    (halign : a6v.toNat % 4 = 0) :
    ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003254#64
          (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)
          nativeDispatchStageSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).log →
      GHolds σ' (evalBlocks nativeDispatchStageSeg
        (SegEvalState.init (nativeDispatchStageL sp s0v a5v s2v s1v) lds)).regs →
      JalStep a6v 0x800039f8#64 σ' i' u' := by
  intro σ' i' u' hG' hi' hpc' hmi' hmem' hregs'
  obtain ⟨vm, hvm⟩ := hmi'
  rw [hpcEq] at hpc'
  exact nativeJalrStep σ' i' u' vm a6v hG' hpc' hvm (hx16pin σ' hregs')
    (by rw [hmem']; exact hloadOut) halign hi'

#print axioms nativeDispatchJalSeam_of

end Vsa.Sim
