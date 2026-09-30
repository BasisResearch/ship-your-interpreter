import Vsa.Sim.ErrorSim
import Vsa.Sim.TermSimAssembly

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config Halts)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr (NativeAddrs Arena)
open Vsa.Alloc (StackLayout)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
