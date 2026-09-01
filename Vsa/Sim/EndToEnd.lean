import Vsa.Sim.TermAssembly
import Vsa.Sim.rows.ErrFamilyAssembly
import Vsa.Sim.rows.LayoutGround

/-!
# `EndToEnd` — THE single end-to-end theorem (the project's live progress meter)

`endToEnd : RemainingWork interpRunLayout → InterpSim interpRunLayout` — the
whole interpreter-correctness statement at the CONCRETE binary layout
(`Vsa.Sim.LayoutInstance.interpRunLayout`, machine-tied to the ELF symbol table
by the generated `rows/LayoutGround.lean`), conditional on exactly ONE
named-field record.  **The fields of `RemainingWork` ARE the remaining work**;
nothing else stands between the landed development and `InterpSim`.

## The hypothesis surface (`RemainingWork L`)

* **`toTermResidualsCore : TermResidualsCore L`** — the term/divergence-side
  residuals (`Vsa/Sim/TermAssembly.lean`): the per-row `*Resid` oracles
  (10 leaf/logical + var/assign + the 19 binary cells + call/fn/args + the exec
  rows), the `hCallClosure` crux, the 7 for-loop/ExecSeq GAP premises, the two
  entry residuals (`hInitStore`/`hEpilogueSpill`), and the divergence entry
  `hDivCorr` (`DivCorrFamily`).  Each field's doc comment names its supplier.
* **`errWork : ErrWork`** — the error side (`rows/ErrFamilyAssembly.lean`):
  `ErrSharedInputs` (the `SnprintfContract` + the 2 open exit-tail segments
  `MainErrorSeg`/`Crt0ExitSeg` + the 2 landed-segment geometry residuals +
  entry-output pinning), the two GENERATED arm-linkage collectors
  (`ErrArmLinks`/`ErrArmLinksB` — 42 `SpillArmPre`/`SetupArmPre` reachability
  fields), and the 2 non-`jal` passthroughs (`hBadClosure`/`hTopAbrupt`).

Everything else — `htri` (unconditional), the error routing + jal seams + exit
tail assembly, the divergence-family reduction, the entry-halt close, the 49
recursor rows, the concrete geometry (`GeomFacts`, all `decide`) — is landed and
composed inside `interpSim_of_residuals`/`errFamily_ofWork`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  Axioms ⊆
{propext, Classical.choice, Quot.sound}.
-/

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.TermAssembly (TermResidualsCore TermResiduals interpSim_of_residuals)
open Vsa.Sim.LayoutInstance (interpRunLayout)

namespace Vsa.Sim.EndToEnd

/-- **The project's remaining work, as ONE named-field record**: the
term/divergence residual core (parent fields) plus the error-side link work.
Discharging these fields — and nothing else — completes `InterpSim`. -/
structure RemainingWork (L : Layout) extends TermResidualsCore L where
  /-- The error-side remaining work (`rows/ErrFamilyAssembly.lean`):
  `ErrSharedInputs` + the two arm-linkage collectors + the 2 passthroughs. -/
  errWork : Vsa.Sim.ErrWork

/-- `InterpSim` from the one record, at any layout: the error family is built by
`errFamily_ofWork`, everything else by `interpSim_of_residuals`. -/
theorem interpSim_ofWork {L : Layout} (W : RemainingWork L) : InterpSim L :=
  interpSim_of_residuals
    { toTermResidualsCore := W.toTermResidualsCore
      hErrFam := Vsa.Sim.errFamily_ofWork L W.errWork }

/-- **THE END-TO-END THEOREM.**  Interpreter correctness for the fixed binary
(`c/while-riscv-htif.elf`, under the RISC-V ISA relation) at the concrete
layout, from the `RemainingWork` record alone. -/
theorem endToEnd (W : RemainingWork interpRunLayout) :
    InterpSim interpRunLayout :=
  interpSim_ofWork W

/-- The full behavioral correspondence at the concrete layout: for EVERY WHILE
program loaded in the interpreter's memory, clean machine halts are exactly the
big-step behaviors, and machine divergence entails the program has none. -/
theorem endToEnd_refinement (W : RemainingWork interpRunLayout) :
    ∀ p c, Loaded interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement (endToEnd W)

#print axioms interpSim_ofWork
#print axioms endToEnd
#print axioms endToEnd_refinement

end Vsa.Sim.EndToEnd
