import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac

/-!
# Argument-loop return/copy/backedge rows

The recursive `eval_expr` call returns at `0x80003224`.  This block reloads its
24-byte result from `sp+64`, reloads the saved destination/index/count/env,
copies the result into the indexed argument-vector slot, increments the index,
and branches either back to `0x800031dc` or forward to `0x80003254`.

Both branch polarities are reflected.  No control or memory effect is hidden in
an oracle.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

#derive_case argsReturnMoreSeg chain
  [(0x80003224#64, 0x04013603#32),  -- ld a2,64(sp): result word 0
   (0x80003228#64, 0x00013703#32),  -- ld a4,0(sp): destination+768
   (0x8000322c#64, 0x01013803#32),  -- ld a6,16(sp): old index
   (0x80003230#64, 0x01813783#32),  -- ld a5,24(sp): argc
   (0x80003234#64, 0xd0c73023#32),  -- sd a2,-768(a4)
   (0x80003238#64, 0x04813603#32),  -- ld a2,72(sp): result word 1
   (0x8000323c#64, 0x00180813#32),  -- addi a6,a6,1
   (0x80003240#64, 0x00813683#32),  -- ld a3,8(sp): env
   (0x80003244#64, 0xd0c73423#32),  -- sd a2,-760(a4)
   (0x80003248#64, 0x05013603#32),  -- ld a2,80(sp): result word 2
   (0x8000324c#64, 0xd0c73823#32)]  -- sd a2,-752(a4)
    terminator ⟨0x80003250#64, 0xf8f816e3#32,
      0xe3#8, 0x16#8, 0xf8#8, 0xf8#8,
      .br bop.BNE true, 16, 15, 0x1f8c#13, 0#21, 0#12⟩

#derive_case argsReturnDoneSeg chain
  [(0x80003224#64, 0x04013603#32),
   (0x80003228#64, 0x00013703#32),
   (0x8000322c#64, 0x01013803#32),
   (0x80003230#64, 0x01813783#32),
   (0x80003234#64, 0xd0c73023#32),
   (0x80003238#64, 0x04813603#32),
   (0x8000323c#64, 0x00180813#32),
   (0x80003240#64, 0x00813683#32),
   (0x80003244#64, 0xd0c73423#32),
   (0x80003248#64, 0x05013603#32),
   (0x8000324c#64, 0xd0c73823#32)]
    terminator ⟨0x80003250#64, 0xf8f816e3#32,
      0xe3#8, 0x16#8, 0xf8#8, 0xf8#8,
      .br bop.BNE false, 16, 15, 0x1f8c#13, 0#21, 0#12⟩

/-- Only `sp` is live on entry.  Every other live value is deliberately
recovered from the four caller spill slots and the three result words. -/
def argsReturnL (sp : BitVec 64) : GRegs := [(2, sp)]

/-- Reflected postcondition of either return block.  The full computed register
map and write log remain exposed for the indexed ABI marshaller. -/
def ArgsReturnPost (seg : List BBlock) (sp nextPC : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.regs.get? Register.PC = some nextPC ∧
  GHolds c.σ (evalBlocks seg (SegEvalState.init (argsReturnL sp) lds)).regs ∧
  c.σ.mem = writeLog m0
    (evalBlocks seg (SegEvalState.init (argsReturnL sp) lds)).log

theorem argsReturnMoreRow (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre argsReturnMoreSeg (argsReturnL sp) lds 0x80003224#64 m0)
      (ArgsReturnPost argsReturnMoreSeg sp 0x800031dc#64 lds m0) := by
  apply segToTriple argsReturnMoreSeg (argsReturnL sp) lds 0x80003224#64 m0
    (ArgsReturnPost argsReturnMoreSeg sp 0x800031dc#64 lds m0)
    (by show ChainOK 0x80003224#64 [2] argsReturnMoreSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, hregs, hmem'⟩
  rw [hpc']
  show some (chainEndPC 0x80003224#64 (argsReturnL sp) lds argsReturnMoreSeg) = some 0x800031dc#64
  rw [chainEndPC_eq_bt argsReturnMoreSeg 0x80003224#64 (argsReturnL sp) lds (by decide)]
  rfl

theorem argsReturnDoneRow (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre argsReturnDoneSeg (argsReturnL sp) lds 0x80003224#64 m0)
      (ArgsReturnPost argsReturnDoneSeg sp 0x80003254#64 lds m0) := by
  apply segToTriple argsReturnDoneSeg (argsReturnL sp) lds 0x80003224#64 m0
    (ArgsReturnPost argsReturnDoneSeg sp 0x80003254#64 lds m0)
    (by show ChainOK 0x80003224#64 [2] argsReturnDoneSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, hregs, hmem'⟩
  rw [hpc']
  show some (chainEndPC 0x80003224#64 (argsReturnL sp) lds argsReturnDoneSeg) = some 0x80003254#64
  rw [chainEndPC_eq_bt argsReturnDoneSeg 0x80003224#64 (argsReturnL sp) lds (by decide)]
  rfl

#print axioms argsReturnMoreRow
#print axioms argsReturnDoneRow

end Vsa.Sim
