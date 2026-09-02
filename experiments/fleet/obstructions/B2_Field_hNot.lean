import Vsa.Sim.rows.Field_hNeg

/-!
# Field `hNot` — MACHINE-CHECKED OBSTRUCTION (fleet B2-unary-logic)

`SkelHNot L := ∀ esub vsub, NotResid esub vsub` is refutable for the same
reason as `hNeg` (see `Field_hNeg.lean`): `NotResid` ∀-closes all ghosts with
only the operand `read64`/`ExprRepr` hypotheses, but `NotSimExtras` demands
the entry-only `sp_headroom : SL.lo + 3264 ≤ sp.toNat` (fails at `sp = 0#64`;
`op_lo`/`slot8`/`hMcallPop` fail independently).  Consumes the shared B2
witness (`b2WitMem`/`b2WitSt`).
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

/-- **`SkelHNot` is false** (for every `L`): witness as in `field_hNeg_refuted`,
contradiction from `NotSimExtras.sp_headroom` at `sp = 0#64`, `SL = ⟨0,0⟩`. -/
theorem field_hNot_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHNot L := by
  intro H
  have h := H .null .null ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (0#64) (0#64) (0#64) (0#64) (0#64) (40#64) b2WitMem
    b2WitMem_payL b2WitMem_nullL
  exact absurd h.1.sp_headroom (by decide)

#print axioms field_hNot_refuted

end Vsa.Sim.Rows.FieldB2
