import Vsa.Sim.InterpInit
import Vsa.Sim.TripleCat

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple Ent)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (initSt Store Frame Value NativeFn Addr St)

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

end Vsa.Sim
