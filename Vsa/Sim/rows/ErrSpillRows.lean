import Vsa.Sim.rows.ErrSpillCore
import Vsa.Sim.rows.ErrorRouting

/-!
# Retired generated spill-route rows

The generated per-constructor wrappers in this module encoded the refuted
fixed-route table, so they have been removed. `ErrSpillCore` retains the
site-agnostic machine lemma. Live semantic composition uses the executable
leaf routes and `BinaryErrReach` in `ErrorRouting`.
-/
