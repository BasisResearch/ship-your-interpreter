import Vsa.Sim.RegPins

/-!
# `KeepRegs` — value-free register-preservation transport

The post-widening companion to `RegPins`: a spec exports
`KeepRegs Rs c.σ c'.σ` for a *concrete* register list `Rs` disjoint from the
segment's write-set, and any caller holding `c.σ.regs.get? R = some w` for
`R ∈ Rs` transports it across the whole segment.  Unlike a `PinsHold` bundle
the list carries **no values**, so the statement needs no extra binders and the
side conditions close by `decide` (everything is concrete registers).

Threading cost inside a proof: one `keep_*` line per site (mirroring the
`pins_*` classes), or one `keep_of_frame` per callee/loop with a `NotWritten*`
register frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- Every register in `Rs` still reads in `σ'` whatever it read in `σ0`. -/
def KeepRegs (Rs : List Register) (σ0 σ' : MState) : Prop :=
  ∀ R ∈ Rs, ∀ w : RegisterType R, σ0.regs.get? R = some w → σ'.regs.get? R = some w

end Vsa.Sim
