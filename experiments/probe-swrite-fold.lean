import Vsa.Sim.rows.FnSwrite
import Vsa.Sim.rows.FnWriteRFold
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.PtrArith
import Vsa.Sim.SegReadback
import Vsa.Sim.DecodeTable

/-! Probe: computed outcomes of the `__swrite` generated segs (P3 fold). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

variable (fp sp0 len ra0 buf cookie s00 : BitVec 64)
variable (fl0 fl1 fd0 fd1 : BitVec 8)

-- entry F pin list: swriteXefd4FL (a1 sp a3 ra a2 a0)
-- = [(11, fp), (2, sp0), (13, len), (1, ra0), (12, buf), (10, cookie)]

-- 1. entry write log: ONE sd (ra spill at (sp0-48)+40)
example :
    (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).log
    = [(((sp0 + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x028#12)).toNat,
        8, ra0)] := rfl

-- 2. entry computed regs
example :
    lookupG 15 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (bytesVal MKind.lh [fl0, fl1]) := rfl

example :
    lookupG 2 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (sp0 + sign_extend (m := 64) (0xfd0#12)) := rfl

example :
    lookupG 6 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (len + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 14 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (fp + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 17 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (buf + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 16 (evalBlocks swriteXefd4FSeg
      (SegEvalState.init (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]])).regs
    = some (cookie + sign_extend (m := 64) (0x000#12)) := rfl

-- 3. tail seg.  pin list swriteXeff8L (sp a5 a4 t1 a7 a6); loads in order:
--    ld ra,40(sp) then lh a1,18(a4)
def raBytesP3 (v : BitVec 64) : List (BitVec 8) :=
  [(sdData_val v).extractLsb' 0 8, (sdData_val v).extractLsb' 8 8,
   (sdData_val v).extractLsb' 16 8, (sdData_val v).extractLsb' 24 8,
   (sdData_val v).extractLsb' 32 8, (sdData_val v).extractLsb' 40 8,
   (sdData_val v).extractLsb' 48 8, (sdData_val v).extractLsb' 56 8]

def spEP : BitVec 64 := sp0 + sign_extend (m := 64) (0xfd0#12)
def flagsP : BitVec 64 := bytesVal MKind.lh [fl0, fl1]

-- 3a. the tail write log: ONE sh at fp+16, value = flags &&& (lui/addi mask)
example :
    (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).log
    = [((fp + sign_extend (m := 64) (0x010#12)).toNat, 2,
        (flagsP fl0 fl1) &&&
          (sign_extend (m := 64) ((0xfffff#20 : BitVec 20) +++ (0x000#12))
            + sign_extend (m := 64) (0xfff#12)))] := rfl

-- 3b. tail computed regs
example :
    lookupG 1 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some (bytesVal MKind.ld (raBytesP3 ra0)) := rfl

example :
    lookupG 11 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some (bytesVal MKind.lh [fd0, fd1]) := rfl

example :
    lookupG 13 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some (len + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 12 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some (buf + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 10 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some (cookie + sign_extend (m := 64) (0x000#12)) := rfl

example :
    lookupG 2 (evalBlocks swriteXeff8Seg
      (SegEvalState.init (swriteXeff8L (spEP sp0) (flagsP fl0 fl1) fp len buf cookie)
        [raBytesP3 ra0, [fd0, fd1]])).regs
    = some ((spEP sp0) + sign_extend (m := 64) (0x030#12)) := rfl

-- 3c. writeLog image shapes (for the getElem_lo `show`s)
example (m : Std.ExtHashMap Nat (BitVec 8)) (A : Nat) :
    writeLog m [(A, 8, ra0)] = writeMap8 m A (sdData_val ra0) := rfl

example (m : Std.ExtHashMap Nat (BitVec 8)) (B : Nat) (v : BitVec 64) :
    writeLog m [(B, 2, v)]
      = (m.insert B ((shData v).extractLsb' 0 8)).insert (B + 1) ((shData v).extractLsb' 8 8) := rfl

-- 4. the entry BNE-fall guard: probe what chain_facts leaves.  Trial facts
--    lemma; the guard bullet uses the P2 inlined simp-set idiom.
theorem swEntryF_facts_probe
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hcode : Vsa.Sim.Code.__swriteLoaded m0)
    (happ : (bytesVal MKind.lh [fl0, fl1] &&& sign_extend (m := 64) (0x100#12)) = 0#64)
    (hflo : 0x80000000 ≤ (fp + sign_extend (m := 64) (0x010#12)).toNat)
    (hfhi : (fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000)
    (hfhtif : tohostAddr + 8 ≤ (fp + sign_extend (m := 64) (0x010#12)).toNat)
    (hfal : (fp + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0)
    (hp0 : m0[(fp + sign_extend (m := 64) (0x010#12)).toNat]? = some fl0)
    (hp1 : m0[(fp + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some fl1)
    (hslo : 0x80000000 ≤ ((sp0 + sign_extend (m := 64) (0xfd0#12))
      + sign_extend (m := 64) (0x028#12)).toNat)
    (hshi : ((sp0 + sign_extend (m := 64) (0xfd0#12))
      + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hshtif : tohostAddr + 16 ≤ ((sp0 + sign_extend (m := 64) (0xfd0#12))
      + sign_extend (m := 64) (0x028#12)).toNat)
    (hsal : ((sp0 + sign_extend (m := 64) (0xfd0#12))
      + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) :
    ChainFacts m0 m0 (swriteXefd4FL fp sp0 len ra0 buf cookie) [[fl0, fl1]]
      swriteXefd4FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__swrite_at_"
  · -- lh a5,16(a1)
    exact ⟨⟨hflo, hfhi, Or.inr hfhtif, hfal⟩, hp0, hp1⟩
  · -- sd ra,40(sp)
    exact ⟨hslo, hshi, hshtif, hsal⟩
  · -- the BNE guard (append bit off)
    show (bytesVal MKind.lh [fl0, fl1] &&& sign_extend (m := 64) (0x100#12) != 0#64) = false
    rw [happ]
    decide

end Vsa.Sim
