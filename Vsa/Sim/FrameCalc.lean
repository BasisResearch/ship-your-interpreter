import Vsa.Sim.SegEvalSound

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

namespace Vsa.Sim

structure FrameCalc (ws : List W) (m0 m : Std.ExtHashMap Nat (BitVec 8)) where
  log : List WEntry
  mem_eq : m = writeLog m0 log
  writes_inside : LogInW ws log

namespace FrameCalc

end FrameCalc

end Vsa.Sim
