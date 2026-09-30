import Vsa.Sim.RamReadPins
import Vsa.Sim.Exec_stmtSites2
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch08Part16
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch15Part24
import Vsa.Sim.DecodeTable.Batch13Part18
import Vsa.Sim.DecodeTable.Batch15Part15

/-!
# `ExecCondArmSites` — per-PC `_es` site batteries for the exec if/while/for cond arms

The `stmtIfCond` (`0x800041e8`), `stmtWhileCond` (`0x8000403c`) and `flCond`
(`0x8000426c`) arm heads reach `jal eval_expr` but their sites were not landed
before wave 41.  Each is a `ld/mv/addi/jal` (+ optional `beqz`) site — identical
class to the landed `Exec_stmtSites*` `_es` batteries, just at new PCs.  The byte
lemmas `exec_stmt_at_*` and the `decode_*` lemmas already exist.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps StepsN)

