import Vsa.Sim.StoreSeg
import Vsa.Sim.TermCaseBundle

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim

namespace Vsa.Sim.Rows

open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim.Rows
