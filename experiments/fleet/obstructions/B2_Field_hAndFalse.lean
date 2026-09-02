import Vsa.Sim.rows.Field_hNeg

/-!
# Field `hAndFalse` — MACHINE-CHECKED OBSTRUCTION (fleet B2-unary-logic)

`SkelHAndFalse L := ∀ el er vl, AndFalseResid el er vl` is refutable for the
same reason as `hNeg` (see `Field_hNeg.lean`): `AndFalseResid` ∀-closes all
ghosts — including an unconstrained `c : Config` — with only the left-operand
`read64`/`ExprRepr` hypotheses, but `AndFalseExtras` demands the entry-only
`sp_headroom : SL.lo + 3264 ≤ sp.toNat` (fails at `sp = 0#64`).  Consumes the
shared B2 witness (`b2WitMem`/`b2WitCfg`).
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.ScaffoldRows
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows.FieldB2

/-- **`SkelHAndFalse` is false** (for every `L`): witness as in
`field_hNeg_refuted` (plus `b2WitCfg` in the unconstrained `c` slot),
contradiction from `AndFalseExtras.sp_headroom` at `sp = 0#64`, `SL = ⟨0,0⟩`. -/
theorem field_hAndFalse_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHAndFalse L := by
  intro H
  have h := H .null .null .null ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (0#64) (0#64) (0#64) (0#64) (0#64) (40#64) b2WitMem b2WitCfg
    b2WitMem_payL b2WitMem_nullL
  exact absurd h.1.sp_headroom (by decide)

#print axioms field_hAndFalse_refuted

end Vsa.Sim.Rows.FieldB2
