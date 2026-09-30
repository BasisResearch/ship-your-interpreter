import Vsa.Sim.SegFrameFactsAuto

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxRecDepth 4000

syntax "seg_guard_close" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| seg_guard_close $[[ $pins,* ]]?) => do
    let extra := match pins with
      | some ps => ps.getElems
      | none => #[]
    `(tactic|
      simp only [runGM, stepGM, wvalM, srcVal, lookupG, eraseG, guardB,
        $[$extra:term],*,
        Nat.reduceEqDiff, if_true, if_false, Option.getD_some] <;> decide)

end Vsa.Sim
