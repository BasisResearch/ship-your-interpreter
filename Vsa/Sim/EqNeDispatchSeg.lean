import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BlockTactics2
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.ExitFootprint
import Vsa.Sim.JmpSpec
import Vsa.Sim.SegFrameFacts
import Vsa.While.Cost

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (NativeFn)
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 4000000

def eqDispL (sp : BitVec 64) : GRegs := [(2, sp)]

end Vsa.Sim
