import Vsa.Sim.rows.EnvDefineUpdateExact
import Vsa.Sim.BridgeSegFramed

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

def EnvDefineTailKeep (R : Register) : Bool :=
  R == Register.x3 || R == Register.x4 || R == Register.x10 || R == Register.x23 ||
    R == Register.x24 || R == Register.x25 || R == Register.x26 || R == Register.x27

def EnvDefineTailKeepSp (R : Register) : Bool :=
  EnvDefineTailKeep R || R == Register.x2

theorem EnvDefineTailKeep.sp {R : Register} (h : EnvDefineTailKeep R = true) :
    EnvDefineTailKeepSp R = true := by
  simp [EnvDefineTailKeepSp, h]

end Vsa.Sim
