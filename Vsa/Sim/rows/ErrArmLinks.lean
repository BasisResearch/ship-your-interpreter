import Vsa.Sim.rows.ErrorRouting

/-!
# Retired Family-A constructor collector

The former collector bundled fixed machine PCs for semantic constructors,
including propagation nodes. It is intentionally empty: the live residual
surface is `ErrLeafLinks`, with child errors propagated by induction and binary
leaf sites selected by `BinaryErrReach`.
-/
