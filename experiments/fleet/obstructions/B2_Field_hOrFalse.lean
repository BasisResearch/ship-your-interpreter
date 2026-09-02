import Vsa.Sim.rows.Field_hNeg

/-!
# Field `hOrFalse` — MACHINE-CHECKED OBSTRUCTION (fleet B2-unary-logic)

`SkelHOrFalse L := ∀ st' st'' el er vl vr, OrFalseResid st' st'' el er vl vr`
is refutable for the same reason as `hNeg` (see `Field_hNeg.lean`):
`OrFalseResid` ∀-closes all ghosts — including an unconstrained `c : Config` —
with only the two operand `read64`/`ExprRepr` hypothesis pairs (offsets
16/24), but `OrFalseExtras` demands the entry-only
`sp_headroom : SL.lo + 3264 ≤ sp.toNat` (fails at `sp = 0#64`).  Consumes the
shared B2 witness: both payload slots (`b2WitMem_payL`/`b2WitMem_payR`) and
both `.null` nodes (40/48).
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

/-- **`SkelHOrFalse` is false** (for every `L`): witness as in
`field_hNeg_refuted`, with the right operand at 48, contradiction from
`OrFalseExtras.sp_headroom` at `sp = 0#64`, `SL = ⟨0,0⟩`. -/
theorem field_hOrFalse_refuted (L : Layout) :
    ¬ Vsa.Sim.TermAssembly.Skel.SkelHOrFalse L := by
  intro H
  have h := H b2WitSt b2WitSt .null .null .null .null ⟨0, 0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩
    (0#64) (0#64) (0#64) (0#64) (0#64) (40#64) (48#64) b2WitMem b2WitCfg
    b2WitMem_payL b2WitMem_nullL b2WitMem_payR b2WitMem_nullR
  exact absurd h.1.sp_headroom (by decide)

#print axioms field_hOrFalse_refuted

end Vsa.Sim.Rows.FieldB2
