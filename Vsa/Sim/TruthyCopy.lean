import Vsa.Sim.EvalChildArm
import Vsa.Sim.PinW
import Vsa.Sim.BridgeSegFramed

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

structure TruthyCopy where

  copySeg : List BBlock

  jalPC : BitVec 64

  jalImm : BitVec 21

namespace TruthyCopy

def lds (D : EvalChildArm) (m : Mem) (esp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (esp.toNat + D.sretOff),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 8),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 16)]

def out (D : EvalChildArm) (T : TruthyCopy) (esp s0 s1 s2 s3 : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks T.copySeg (SegEvalState.init (EvalChildArm.regs esp s0 s1 s2 s3) (lds D m esp))

end TruthyCopy
end Vsa.Sim
