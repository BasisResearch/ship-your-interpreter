import Vsa.Sim.rows.FnWriteR
import Vsa.Sim.SegToTripleFramed

/-! Probe: computed outcomes of the `_write_r` generated segs (P2 fold). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

variable (reent fd buf len ra0 sp0 s00 gp0 : BitVec 64)

-- entry pin list instantiation
-- write_rX04fcL (a1 sp s0 a2 a0 a3 ra gp)
#check (evalBlocks write_rX04fcSeg
  (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).log

-- 1. the write log
example :
    (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).log
    = [(((sp0 + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x000#12)).toNat, 8, s00),
       (((sp0 + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x008#12)).toNat, 8, ra0),
       ((gp0 + sign_extend (m := 64) (0x4f8#12)).toNat, 4, 0#64)] := rfl

-- 2. computed regs of the entry seg
example :
    lookupG 10 (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).regs
    = some ((fd + sign_extend (m := 64) (0x000#12)) + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 11 (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).regs
    = some (buf + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 12 (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).regs
    = some (len + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 2 (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).regs
    = some (sp0 + sign_extend (m := 64) (0xff0#12)) := rfl

example :
    lookupG 8 (evalBlocks write_rX04fcSeg
      (SegEvalState.init (write_rX04fcL fd sp0 s00 buf reent len ra0 gp0) [])).regs
    = some (reent + sign_extend (m := 64) (0x000#12)) := rfl

-- 3. epilogue seg: byte lists for the two lds
def raBytesP (v : BitVec 64) : List (BitVec 8) :=
  [(sdData_val v).extractLsb' 0 8, (sdData_val v).extractLsb' 8 8,
   (sdData_val v).extractLsb' 16 8, (sdData_val v).extractLsb' 24 8,
   (sdData_val v).extractLsb' 32 8, (sdData_val v).extractLsb' 40 8,
   (sdData_val v).extractLsb' 48 8, (sdData_val v).extractLsb' 56 8]

variable (spE : BitVec 64)

-- computed regs off the epilogue seg (ld ra; ld s0; addi sp,16 ▷ jr)
example :
    lookupG 1 (evalBlocks write_rX052cSeg
      (SegEvalState.init (write_rX052cL spE) [raBytesP ra0, raBytesP s00])).regs
    = some (bytesVal .ld (raBytesP ra0)) := rfl

example :
    lookupG 8 (evalBlocks write_rX052cSeg
      (SegEvalState.init (write_rX052cL spE) [raBytesP ra0, raBytesP s00])).regs
    = some (bytesVal .ld (raBytesP s00)) := rfl

example :
    lookupG 2 (evalBlocks write_rX052cSeg
      (SegEvalState.init (write_rX052cL spE) [raBytesP ra0, raBytesP s00])).regs
    = some (spE + sign_extend (m := 64) (0x010#12)) := rfl

-- epilogue end PC (jr): BitVec.update (ra + sext 0) 0 0
example :
    evalBlocksPC 0x8001052c#64
      (SegEvalState.init (write_rX052cL spE) [raBytesP ra0, raBytesP s00]) write_rX052cSeg
    = BitVec.update (bytesVal .ld (raBytesP ra0) + sign_extend (m := 64) (0x000#12)) 0 0#1 := rfl

-- epilogue log is empty
example :
    (evalBlocks write_rX052cSeg
      (SegEvalState.init (write_rX052cL spE) [raBytesP ra0, raBytesP s00])).log = [] := rfl

-- 4. the beq-fall seg log empty + computed a5
example :
    (evalBlocks write_rX0524FSeg (SegEvalState.init (write_rX0524FL len) [])).log = [] := rfl

example :
    lookupG 15 (evalBlocks write_rX0524FSeg (SegEvalState.init (write_rX0524FL len) [])).regs
    = some (0#64 + sign_extend (m := 64) (0xfff#12)) := rfl

end Vsa.Sim
