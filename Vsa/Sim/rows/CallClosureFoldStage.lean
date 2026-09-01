import Vsa.Sim.rows.CallClosureEnvDefineCallGen
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.rows.StrdupTailJalSeams

/-!
# `callClosureFoldStage` — the per-param fold staging span (wave 38)

Task Wave-38, residual span (c): ONE per-param staging body of the
`env_define` fold, `0x800032dc → 0x8000330c ▷ jal env_define @0x80003310` —
the machine body of the `hFoldSeam` staging hop (`callParamFoldSeam_of`'s
`hStage`, `rows/CallClosureSplice.lean`).

VERDICT on the gen_stagepre question: this is NOT the 3-step-uniform
`ld+addi+sd → jal eval_expr` class (`assign-call-logical-stagepre-uniform`) —
it is a 13-instruction 24-byte value copy + names-array indexing + cursor
bump, and it WRITES the callee-saved cursor `s0 = x8` (`addi s0,s0,24` at
`0x80003304`), so like the dispatch head it needs `bridgeOfSegFramed` at a
restricted avoid-set (`AbiExceptS0`), not `bridgeOfSeg` and not a stagepre
clone.  It occurs ONCE per param but the SAME span serves every `k` (the
loop-carried state is all in pins: `s0` cursor, `a5 = 8k` index) — so this ONE
bridge is the whole family's machine body; the back-edge
(`0x80003314..0x8000331c`, `bne s6,a5` — taken for `k+1 < n`, not-taken exit)
stays a named residual of the seam family.

```
800032dc  ld a3,0(s0)       0x00043683   -- arg value word 0 (cursor)
800032e0  ld a4,16(s5)      0x010ab703   -- params names array base
800032e4  addi a2,sp,64     0x04010613   -- a2 := the 24-byte value buffer
800032e8  sd a3,64(sp)      0x04d13023
800032ec  ld a3,8(s0)       0x00843683   -- word 1
800032f0  add a4,a4,a5      0x00f70733   -- names + 8k
800032f4  mv a0,s3          0x00098513   -- a0 := the fresh frame ptr
800032f8  sd a3,72(sp)      0x04d13423
800032fc  ld a3,16(s0)      0x01043683   -- word 2
80003300  sd a5,0(sp)       0x00f13023   -- spill the byte index across the call
80003304  addi s0,s0,24     0x01840413   -- CURSOR BUMP (callee-saved write!)
80003308  sd a3,80(sp)      0x04d13823
8000330c  ld a1,0(a4)       0x00073583   -- a1 := names[k]
          ▷ jal env_define @0x80003310  (callee 0x80002a5c, link 0x80003314)
```

`lds` is parametric (observation `genseg-jal-rows-zero-pin-loads`).

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

/- The `callClosureFoldStage` span body `0x800032dc → 0x8000330c`
(jal-terminated, 1 block), decoded from `experiments/disasm.txt`. -/
#derive_case callClosureFoldStageSeg chain
  [(0x800032dc#64, 0x00043683#32),  -- ld a3,0(s0)
   (0x800032e0#64, 0x010ab703#32),  -- ld a4,16(s5)
   (0x800032e4#64, 0x04010613#32),  -- addi a2,sp,64
   (0x800032e8#64, 0x04d13023#32),  -- sd a3,64(sp)
   (0x800032ec#64, 0x00843683#32),  -- ld a3,8(s0)
   (0x800032f0#64, 0x00f70733#32),  -- add a4,a4,a5
   (0x800032f4#64, 0x00098513#32),  -- mv a0,s3
   (0x800032f8#64, 0x04d13423#32),  -- sd a3,72(sp)
   (0x800032fc#64, 0x01043683#32),  -- ld a3,16(s0)
   (0x80003300#64, 0x00f13023#32),  -- sd a5,0(sp)
   (0x80003304#64, 0x01840413#32),  -- addi s0,s0,24
   (0x80003308#64, 0x04d13823#32),  -- sd a3,80(sp)
   (0x8000330c#64, 0x00073583#32)]  -- ld a1,0(a4)

#print axioms callClosureFoldStageSeg_seg

/-- The `callClosureFoldStage` entry pin list: `x2` (sp), `x8` (s0 = the arg
cursor `sp+240+24k`), `x15` (a5 = the byte index `8k`), `x19` (s3 = the fresh
frame ptr), `x21` (s5 = the closure record; names at `16(s5)`) — exactly the
`CallParamFoldInv` register pins. -/
def callClosureFoldStageL (sp s0v a5v s3v s5v : BitVec 64) : GRegs :=
  [(2, sp), (8, s0v), (15, a5v), (19, s3v), (21, s5v)]

/- The restricted ABI frame predicate `AbiExceptS0` (callee-saved EXCEPT the
bumped cursor `s0 = x8`; the new cursor value `s0v + 24` is read off the
exposed post bundle) is REUSED from `rows/StrdupTailJalSeams` — the local
duplicate clashed at Vsa.lean wiring time. -/

/-- **`callClosureFoldStageBridge`** — the per-param staging body ≫
`jal env_define` bridge, via `bridgeOfSegFramed` at `AbiExceptS0`.  Conclusion:
parked at `env_define @0x80002a5c` with link `0x80003314`, memory = the seg
write-log (the 24-byte value copy at `64..80(sp)`, the index spill at `0(sp)`),
the bumped cursor exposed in the post bundle, and the ABI frame for every
callee-saved EXCEPT `s0`. -/
theorem callClosureFoldStageBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0v a5v s3v s5v : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800032dc#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (callClosureFoldStageL sp s0v a5v s3v s5v))
    (hfacts : ChainFacts σ.mem σ.mem (callClosureFoldStageL sp s0v a5v s3v s5v)
      lds callClosureFoldStageSeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks callClosureFoldStageSeg
      (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks callClosureFoldStageSeg
      (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x800032dc#64
          (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)
          callClosureFoldStageSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks callClosureFoldStageSeg
        (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).log →
      GHolds σ' (evalBlocks callClosureFoldStageSeg
        (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).regs →
      JalStep 0x80002a5c#64 0x80003314#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel callClosureFoldStageSeg + 1⟩ ∧
      i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80002a5c#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003314#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks callClosureFoldStageSeg
        (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks callClosureFoldStageSeg
        (SegEvalState.init (callClosureFoldStageL sp s0v a5v s3v s5v) lds)).log ∧
      (∀ R, AbiExceptS0 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  have hkeys : KeysOK (keysG (callClosureFoldStageL sp s0v a5v s3v s5v)) := by
    show KeysOK [2, 8, 15, 19, 21]; decide
  have hwf : ChainOK 0x800032dc#64 (keysG (callClosureFoldStageL sp s0v a5v s3v s5v))
      callClosureFoldStageSeg := by
    show ChainOK 0x800032dc#64 [2, 8, 15, 19, 21] callClosureFoldStageSeg; decide
  have hnoiseP : ∀ rr ∈ noiseRegs, AbiExceptS0 rr = false := by decide
  have hAvoidP : WrChainAvoids AbiExceptS0 callClosureFoldStageSeg := by decide
  have hPabi : ∀ R, AbiExceptS0 R = true → AbiPreserved R = true := by
    intro R hR
    unfold AbiExceptS0 at hR
    exact (Bool.and_eq_true .. |>.mp hR).1
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    bridgeOfSegFramed AbiExceptS0 callClosureFoldStageSeg
      (callClosureFoldStageL sp s0v a5v s3v s5v) lds
      σ i u 0x800032dc#64 0x80002a5c#64 0x80003314#64 vminstret m0
      hG hpc hminstret hmem hL hkeys hfacts hi hwf
      hnoiseP hAvoidP hKeysOut hRaOut hPabi hjalSeam
  exact ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩

#print axioms callClosureFoldStageBridge

end Vsa.Sim
