import Vsa.Sim.rows.ErrSetupCore
import Vsa.Sim.rows.ErrorRouting

/-!
# Retired generated setup-route rows

The generated per-constructor wrappers in this module encoded the refuted
fixed-route table, so they have been removed. `ErrSetupCore` retains the
site-agnostic machine lemma. Live semantic composition uses the executable
leaf routes and `BinaryErrReach` in `ErrorRouting`.
-/
