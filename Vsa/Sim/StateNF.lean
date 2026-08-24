import Vsa.Elf
import Vsa.Sim.Attr

/-!
# Layer 0, item 2 — memory and register normal forms

Read-over-write simp interface for the Sail state containers
(`PLAN-InterpSim.md` §Layer 0 item 2). The containers are extensional
(quotient-backed) and not definitionally reducible (experiment E1g), so all
reads through pending writes are resolved propositionally by these lemmas:

- register file `σ.regs : Std.ExtDHashMap Register RegisterType` —
  `get?_insert`/`get?_insert_self`; the key disequalities are constructor
  disequalities on `Register`, which `simp` discharges.
- byte memory `σ.mem : Std.ExtHashMap Nat (BitVec 8)` —
  `getElem?_insert`/`getElem?_insert_self`; concrete-address and
  base-plus-offset disequalities close by `simp`/`omega`.

Canonical state form is an insert-chain over the initial state; these
lemmas are the only interface goals should use to consume it.
Validated in `experiments/M1_statenf_probe.lean`.
-/

namespace Vsa.Sim

attribute [seval_state]
  Std.ExtDHashMap.get?_insert
  Std.ExtDHashMap.get?_insert_self
  Std.ExtHashMap.getElem?_insert
  Std.ExtHashMap.getElem?_insert_self

end Vsa.Sim
