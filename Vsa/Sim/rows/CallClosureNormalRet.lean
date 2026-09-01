import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BridgeSeg

/-!
# `callClosureNormalRet` — the `.normal` return path `0x80003954..74` (wave 40)

Wave-40 residual span: the `.normal` status route — reached from the body
loop's exit `bge @0x80003350`, the empty-body `j @0x8000333c`, or the dead
`bne @0x80003398` target — down to the epilogue join `callJoinPC = 0x800033ec`.
TWO pieces around the `jal value_null` call seam (Shape D):

```
80003954  lw a5,8(s2)       0x00892783   -- call_depth
80003958  addiw a5,a5,-1    0xfff7879b   -- --call_depth
8000395c  sw a5,8(s2)       0x00f92423   -- (the ONLY store: 4 bytes at 8(s2))
80003960  mv a0,s1          0x00048513   -- a0 := the CALL's sret buffer
80003964  ▷ jal value_null @0x800027ec  (link 0x80003968)  [bridge seam]
-- value_null writes the null Value into the sret buffer, returns:
80003968  ld s3,1048(sp)    0x41813983   -- RESTORE s3  (in-span spill @0x800032ac)
8000396c  ld s5,1032(sp)    0x40813a83   -- RESTORE s5  (in-span spill @0x8000328c)
80003970  ld s7,1016(sp)    0x3f813b83   -- RESTORE s7  (PRE-span spill @0x800031cc —
                                            the `EntryImage`/`s7ImageAtBody` slot)
80003974  ▷ j 0x800033ec (callJoinPC)
```

The restore seg's `lds` readbacks are exactly what the wave-38/40 layer
supplies: `s3`/`s5` from `CallerSpillSlots.s3/.s5` (+`stackWin` survival via
`callerSlotsSurviveBody`), `s7` from `s7ImageAtBody`
(`EntryImage@callDispatchPC` + `.s7carry`) — so the join's ghost-frame clause
for the three clobbered callee-saveds closes from these rows' `GHolds`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/- Piece 1: the `--call_depth` + sret staging, jal-terminated (the value_null
call seam — outside `TKind`, a `bridgeOfSeg` row). -/
#derive_case callClosureNormalDepthSeg chain
  [(0x80003954#64, 0x00892783#32),  -- lw a5,8(s2)
   (0x80003958#64, 0xfff7879b#32),  -- addiw a5,a5,-1
   (0x8000395c#64, 0x00f92423#32),  -- sw a5,8(s2)
   (0x80003960#64, 0x00048513#32)]  -- mv a0,s1  (addi x10,x9,0)

#print axioms callClosureNormalDepthSeg_seg

/-- Piece-1 entry pin list: `x18` (s2 — `call_depth` at `8(s2)`) and `x9`
(s1 — the CALL's sret pointer, staged into `a0`). -/
def callClosureNormalDepthL (s2v s1v : BitVec 64) : GRegs := [(18, s2v), (9, s1v)]

/-- **`callClosureNormalDepthBridge`** — the `--call_depth`/staging body ≫
`jal value_null` bridge, via `bridgeOfSeg`.  The seg run + ABI frame are FREE;
`hfacts` and the call-seam `hjalSeam` (`JalStep` off the region's
`site_80003964_*` obs) are the only region-specific residuals.  `lds` is the
parametric load-readback list (the `lw 8(s2)` depth word).  Conclusion: parked
at the `value_null` entry `0x800027ec#64` with link `0x80003968#64`, memory =
the seg write-log (the depth word at `8(s2)`), ABI frame preserved. -/
theorem callClosureNormalDepthBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64) (s2v s1v : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x80003954#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (callClosureNormalDepthL s2v s1v))
    (hfacts : ChainFacts σ.mem σ.mem (callClosureNormalDepthL s2v s1v) lds callClosureNormalDepthSeg)
    (hi : i < 2)
    -- output-regs key hygiene: closed by ONE `decide` each at the caller
    -- (observations `keys-decides-per-seg`).
    (hKeysOut : KeysOK (keysG (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs)
    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some
        (evalBlocksPC 0x80003954#64 (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds) callClosureNormalDepthSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      σ'.mem = writeLog m0 (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log →
      GHolds σ' (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs →
      JalStep 0x800027ec#64 0x80003968#64 σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel callClosureNormalDepthSeg + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x800027ec#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003968#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks callClosureNormalDepthSeg (SegEvalState.init (callClosureNormalDepthL s2v s1v) lds)).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg callClosureNormalDepthSeg (callClosureNormalDepthL s2v s1v) lds
    σ i u (0x80003954#64) (0x800027ec#64) (0x80003968#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (callClosureNormalDepthL s2v s1v) = [18, 9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (callClosureNormalDepthL s2v s1v) = [18, 9] := rfl
        rw [h]; show ChainOK 0x80003954#64 [18, 9] callClosureNormalDepthSeg; decide)
    (by show WrChainAvoidAbi callClosureNormalDepthSeg; decide)
    hKeysOut hRaOut
  exact hjalSeam

#print axioms callClosureNormalDepthBridge

/- Piece 2: the post-value_null restore seg, `j`-terminated at the epilogue
join `callJoinPC = 0x800033ec`. -/
#derive_case callClosureNormalJoinSeg chain
  [(0x80003968#64, 0x41813983#32),  -- ld s3,1048(sp)
   (0x8000396c#64, 0x40813a83#32),  -- ld s5,1032(sp)
   (0x80003970#64, 0x3f813b83#32)]  -- ld s7,1016(sp)
    terminator ⟨0x80003974#64, 0xa79ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xa7#8,
      .j, 0, 0, 0#13, 0x1FFA78#21, 0#12⟩

#print axioms callClosureNormalJoinSeg_seg

/-- Piece-2 entry pin list: `x2` (sp — the three restore slots). -/
def callClosureNormalJoinL (sp : BitVec 64) : GRegs := [(2, sp)]

/-- The restore-seg post: parked at `callJoinPC = 0x800033ec`, memory
unchanged (this span stores nothing), the three restored callee-saveds
(`s3`/`s5`/`s7` = the `lds` readbacks) exposed via `GHolds`. -/
def CallClosureNormalJoinPost (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks callClosureNormalJoinSeg
    (SegEvalState.init (callClosureNormalJoinL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800033ec#64 ∧
  GHolds c.σ (evalBlocks callClosureNormalJoinSeg
    (SegEvalState.init (callClosureNormalJoinL sp) lds)).regs

/-- **`callClosureNormalJoinRow`** — the restore seg as a `Triple`
(`segToTriple`), landing at the epilogue join. -/
theorem callClosureNormalJoinRow (sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre callClosureNormalJoinSeg (callClosureNormalJoinL sp)
        lds 0x80003968#64 m0)
      (CallClosureNormalJoinPost sp lds m0) := by
  apply segToTriple callClosureNormalJoinSeg (callClosureNormalJoinL sp)
    lds 0x80003968#64 m0 (CallClosureNormalJoinPost sp lds m0)
    (by have h : keysG (callClosureNormalJoinL sp) = [2] := rfl
        rw [h]
        show ChainOK 0x80003968#64 [2] callClosureNormalJoinSeg
        decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, hregs⟩
  rw [hpc']
  show some (evalBlocksPC 0x80003968#64
      (SegEvalState.init (callClosureNormalJoinL sp) lds)
      callClosureNormalJoinSeg)
    = some 0x800033ec#64
  rfl

#print axioms callClosureNormalJoinRow

end Vsa.Sim
