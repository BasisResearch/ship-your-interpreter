import Vsa.Sim.TermSimClose

namespace Vsa.Sim.TermCaseBundle

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (MState Config Halts)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.TermCaseBundle
