import Vsa.Sim.ObsAvoid
import Vsa.Sim.RamReadValue
import Vsa.Sim.StepObs
import Vsa.Sim.ExecuteAlu
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.ExecuteLoad
import Vsa.Sim.ExecuteStore
import Vsa.Sim.MemStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeNF
import Vsa.Sim.ValueSites
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.InterpEntry

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def MemExtends (m0 m : Mem) : Prop :=
  ∀ (a : Nat) (b : BitVec 8), m0[a]? = some b → ∃ b', m[a]? = some b'

end Vsa.Sim
