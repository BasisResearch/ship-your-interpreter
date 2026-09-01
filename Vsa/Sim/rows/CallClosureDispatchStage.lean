import Vsa.Sim.rows.CallClosureEnvNewCallGen
import Vsa.Sim.BridgeSegFramed

/-!
# `callClosureDispatchStage` — the frame-tracking dispatch/head span (wave 38)

Task Wave-38, residual span (a): the closure-arm dispatch + head
`0x80003254 → 0x800032b8 ▷ jal env_new @0x800032bc` — the machine body of the
`hDispatchStage` premise of `callClosureEntrySplice`
(`rows/CallClosureSplice.lean`).  `genseg.py` HARD-ERRORS on this span (it
reseats the callee-saved `s7 = x23` at `0x80003278` and `s5 = x21` at
`0x80003290`, so `WrChainAvoidAbi` is FALSE); the right tool is
`BridgeSegFramed.bridgeOfSegFramed` at the restricted avoid-set
`AbiExceptS7S5`, exactly the `rows/ConcatStringifyRArg.lean` model (its
`AbiExceptS2S3`) and the `entryBaseReseat_framed` demo this span was the
motivating consumer for.

```
80003254  ld a4,96(sp)      0x06013703   -- fval kind (spill source)
80003258  ld a3,104(sp)     0x06813683   -- fval payload (ClosureData ptr)
8000325c  ld a6,112(sp)     0x07013803   -- fval payload2
80003260  lw a1,4(s0)       0x00442583   -- argc from the call node
80003264  sd a4,120(sp)     0x06e13c23   -- 24-byte fval spill …
80003268  lw a4,96(sp)      0x06012703   -- kind reload (word)
8000326c  sd a3,128(sp)     0x08d13023
80003270  sd a6,136(sp)     0x09013423
80003274  li a2,5           0x00500613
80003278  mv s7,a1          0x00058b93   -- RESEAT s7 := argc  (callee-saved!)
8000327c  ▷ beq a4,a2 → native (NOT taken: kind = 4 ≠ 5)
80003280  li a2,4           0x00400613
80003284  ▷ bne a4,a2 → error  (NOT taken: kind = 4)
80003288  ld a4,0(a3)       0x0006b703   -- closure record ptr
8000328c  sd s5,1032(sp)    0x41513423   -- SPILL caller s5
80003290  mv s5,a4          0x00070a93   -- RESEAT s5 := closure rec  (callee-saved!)
80003294  lw a4,24(a4)      0x01872703   -- arity
80003298  ▷ bne a5,a4 → error  (NOT taken: a_2, argc = arity)
8000329c  lw a4,8(s2)       0x00892703   -- call_depth
800032a0  li a2,1000        0x3e800613
800032a4  addiw a4,a4,1     0x0017071b
800032a8  sw a4,8(s2)       0x00e92423   -- ++call_depth
800032ac  sd s3,1048(sp)    0x41313c23   -- SPILL caller s3
800032b0  ▷ blt a2,a4 → error  (NOT taken: a_3, depth+1 ≤ 1000)
800032b4  ld a0,8(a3)       0x0086b503   -- a0 := cd->env  (the env_new arg)
800032b8  sd a5,0(sp)       0x00f13023   -- spill argc across the call
          ▷ jal env_new @0x800032bc  (callee 0x800029fc, link 0x800032c0)
```

The four guard branches are declared NOT-taken in-model; their `guardB`
obligations live in the caller's `ChainFacts` (dischargeable from the kind
load pin `= 4`, `a_2` for the arity `bne`, `a_3` for the depth `blt`).  `lds`
is threaded PARAMETRICALLY (observation `genseg-jal-rows-zero-pin-loads`: a
hardcoded `[]` would zero-pin the loads).  The reseated `s7`/`s5` are read off
the EXPOSED post bundle; the restricted frame covers every other callee-saved.

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

/- The `callClosureDispatchStage` span body `0x80003254 → 0x800032b8`
(jal-terminated, 5 blocks, 4 NOT-taken guard branches), decoded from
`experiments/disasm.txt`. -/
#derive_case callClosureDispatchStageSeg chain
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
      .br bop.BEQ false, 14, 12, 0x0764#13, 0#21, 0#12⟩ ;;
  [(0x80003280#64, 0x00400613#32)]  -- li a2,4
    terminator ⟨0x80003284#64, 0x32c710e3#32, 0xe3#8, 0x10#8, 0xc7#8, 0x32#8,
      .br bop.BNE false, 14, 12, 0x0B20#13, 0#21, 0#12⟩ ;;
  [(0x80003288#64, 0x0006b703#32),  -- ld a4,0(a3)
   (0x8000328c#64, 0x41513423#32),  -- sd s5,1032(sp)
   (0x80003290#64, 0x00070a93#32),  -- mv s5,a4  (addi x21,x14,0)
   (0x80003294#64, 0x01872703#32)]  -- lw a4,24(a4)
    terminator ⟨0x80003298#64, 0x2ce794e3#32, 0xe3#8, 0x94#8, 0xe7#8, 0x2c#8,
      .br bop.BNE false, 15, 14, 0x0AC8#13, 0#21, 0#12⟩ ;;
  [(0x8000329c#64, 0x00892703#32),  -- lw a4,8(s2)
   (0x800032a0#64, 0x3e800613#32),  -- li a2,1000
   (0x800032a4#64, 0x0017071b#32),  -- addiw a4,a4,1
   (0x800032a8#64, 0x00e92423#32),  -- sw a4,8(s2)
   (0x800032ac#64, 0x41313c23#32)]  -- sd s3,1048(sp)
    terminator ⟨0x800032b0#64, 0x1ee64ae3#32, 0xe3#8, 0x4a#8, 0xe6#8, 0x1e#8,
      .br bop.BLT false, 12, 14, 0x09F4#13, 0#21, 0#12⟩ ;;
  [(0x800032b4#64, 0x0086b503#32),  -- ld a0,8(a3)
   (0x800032b8#64, 0x00f13023#32)]  -- sd a5,0(sp)

#print axioms callClosureDispatchStageSeg_seg

/-- The `callClosureDispatchStage` entry pin list — the registers the body
reads: `x2` (sp), `x8` (s0 = the EX_CALL node), `x13` (a3 — dead-on-entry but
reloaded at `0x80003258`; pinned for the toml parity), `x15` (a5 = argc, the
arity `bne` source and the `0(sp)` spill), `x18` (s2 = interp, `call_depth`),
and the two CALLER values this span spills — `x21` (s5, `sd s5,1032(sp)`) and
`x19` (s3, `sd s3,1048(sp)`); their pins are exactly the bytes
`CallerSpillSlots` (`rows/CallClosureRow.lean`) carries to the ret routes. -/
def callClosureDispatchStageL (sp s0v a3v a5v s2v s5v s3v : BitVec 64) : GRegs :=
  [(2, sp), (8, s0v), (13, a3v), (15, a5v), (18, s2v), (21, s5v), (19, s3v)]

/-- The restricted ABI frame predicate: callee-saved EXCEPT the reseated
`s7 = x23` and `s5 = x21`.  `bridgeOfSegFramed`'s frame conclusion holds for
exactly these; the new `s7`/`s5` values are read off the exposed post bundle. -/
def AbiExceptS7S5 (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x23) && !(R == Register.x21)

/-- **`callClosureDispatchStageBridge`** — the dispatch/head body ≫
`jal env_new` bridge, via `bridgeOfSegFramed` at `AbiExceptS7S5`.  The seg run
+ the restricted ABI frame are FREE; `hfacts` (memory chain-facts, incl. the
four guard obligations) and `hjalSeam` (the `env_new` call-seam `JalStep`) are
the region-specific residuals.  Conclusion: parked at `env_new @0x800029fc`
with link `0x800032c0`, memory = the seg write-log (the fval spill at
`120..136(sp)`, the `s5/s3` spills at `1032/1048(sp)`, `++call_depth` at
`8(s2)`, the argc spill at `0(sp)`), the reseated `s7`/`s5` exposed in the
post bundle, and the ABI frame for every callee-saved EXCEPT `s7`/`s5`. -/
theorem callClosureDispatchStageBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0v a3v a5v s2v s5v s3v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003254#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v))
    (hfacts : ChainFacts σ.mem σ.mem (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v)
      lds callClosureDispatchStageSeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks callClosureDispatchStageSeg
      (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks callClosureDispatchStageSeg
      (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003254#64
          (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)
          callClosureDispatchStageSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).log →
      GHolds σ' (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs →
      JalStep 0x800029fc#64 0x800032c0#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel callClosureDispatchStageSeg + 1⟩ ∧
      i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x800029fc#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x800032c0#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      -- the whole reseated register bundle, EXPOSED (carries the new
      -- `s7 = argc` / `s5 = closure rec` as the seg's computed deltas):
      GHolds σ2 (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks callClosureDispatchStageSeg
        (SegEvalState.init (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds)).log ∧
      -- the ABI frame for every callee-saved EXCEPT the reseated `s7`/`s5`:
      (∀ R, AbiExceptS7S5 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  have hkeys : KeysOK (keysG (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v)) := by
    show KeysOK [2, 8, 13, 15, 18, 21, 19]; decide
  have hwf : ChainOK 0x80003254#64 (keysG (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v))
      callClosureDispatchStageSeg := by
    show ChainOK 0x80003254#64 [2, 8, 13, 15, 18, 21, 19] callClosureDispatchStageSeg; decide
  have hnoiseP : ∀ rr ∈ noiseRegs, AbiExceptS7S5 rr = false := by decide
  have hAvoidP : WrChainAvoids AbiExceptS7S5 callClosureDispatchStageSeg := by decide
  -- `AbiExceptS7S5 R → AbiPreserved R`: the restricted predicate is a subset.
  have hPabi : ∀ R, AbiExceptS7S5 R = true → AbiPreserved R = true := by
    intro R hR
    unfold AbiExceptS7S5 at hR
    exact (Bool.and_eq_true .. |>.mp ((Bool.and_eq_true .. |>.mp hR).1)).1
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    bridgeOfSegFramed AbiExceptS7S5 callClosureDispatchStageSeg
      (callClosureDispatchStageL sp s0v a3v a5v s2v s5v s3v) lds
      σ i u 0x80003254#64 0x800029fc#64 0x800032c0#64 vminstret m0
      hG hpc hminstret hmem hL hkeys hfacts hi hwf
      hnoiseP hAvoidP hKeysOut hRaOut hPabi hjalSeam
  exact ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩

#print axioms callClosureDispatchStageBridge

end Vsa.Sim
