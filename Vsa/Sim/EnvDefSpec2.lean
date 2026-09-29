import Vsa.Sim.DecodeNF
import Vsa.Sim.StrcmpSpecW3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame Store)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def reallocEntry : Nat := 0x8000527c

theorem define_append_length (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) :
    (vars ++ [(x, v)]).length = vars.length + 1 := by
  rw [List.length_append, List.length_singleton]

theorem define_append_getElem_new (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) :
    (vars ++ [(x, v)])[vars.length]'(by rw [define_append_length]; omega) = (x, v) := by
  rw [List.getElem_append_right (by omega)]
  simp

theorem define_append_getElem_old (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) (j : Nat) (hj : j < vars.length) :
    (vars ++ [(x, v)])[j]'(by rw [define_append_length]; omega) = vars[j] := by
  rw [List.getElem_append_left hj]

end Vsa.Sim
