import Vsa.Sim.DecodeNF
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.EvalRecCommon

namespace Vsa.Sim.Scaffold

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.Scaffold
