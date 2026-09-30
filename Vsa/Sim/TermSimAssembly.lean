import Vsa.Sim.ExecSeqIndexed
import Vsa.Sim.CallEntry

namespace Vsa.Sim.TermSimAssembly

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

end Vsa.Sim.TermSimAssembly
