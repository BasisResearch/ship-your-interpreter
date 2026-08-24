import Lean

/-!
# Simp attributes for the Layer-0 symbolic-execution sets

`PLAN-InterpSim.md` §Layer 0: staged simp sets, never `rfl`, over the Sail
model's stateful computations. The attributes are registered here (an
attribute cannot be used in the file that registers it).

- `seval_state`: read-over-write normal forms for the two state containers
  (`Std.ExtDHashMap` register file, `Std.ExtHashMap` byte memory).
-/

register_simp_attr seval_state
