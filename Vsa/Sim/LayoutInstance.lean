import Vsa.Sim.GeomFacts
import Vsa.Sim.ImageDischarge
import Vsa.Refinement

/-!
# L8/M6 — `LayoutInstance`: the concrete `Layout` + its `GeomFacts` / statics

This is the last *structural* file of the InterpSim proof: it instantiates the
abstract geometry the close (`interpSimClosed_of_families`/`termSimClosed`) leaves
open with the **actual constants of the fixed binary** `c/while-riscv-htif.elf`,
and discharges the whole geometry residual with a single `decide`/`omega` pass
over concrete `Nat` bounds.

## What M6 pins

The abstract refinement (`Vsa.Refine.Layout`, `Vsa/Refinement.lean`) quantifies
over an `atInterpRun` program-point predicate; the geometry residual the Layer-4
cases carry (`Vsa.Sim.GeomFacts`/`LayoutGeomPred`, `Vsa/Sim/GeomFacts.lean`) is
region-generic over the touched function's own `code` region, the caller's
`StackLayout`, and the entry `sp`.  M6's job is to supply the concrete values and
prove the numeric predicate ONCE:

| region              | symbol (`nm c/while-riscv-htif.elf`)        | concrete value            |
|---------------------|---------------------------------------------|---------------------------|
| `interp_run` code   | `interp_run … main`                         | `[0x800043ec, 0x80004588)`|
| C-stack window      | `__stack_top - __stack_size … __stack_top`  | `[0x87800000, 0x88000000)`|
| entry `sp`          | `__stack_top`                               | `0x88000000`              |
| HTIF `tohost`       | `tohost` (`Regions.tohostAddr`)             | `0x8001ad00` (+16 excl.)  |
| dispatch jump table | `.rodata` @ `eval_expr` binary dispatch     | `0x80019f58` (+44)        |
| `_exit`             | `_exit`                                     | `0x80000180`              |
| `runtime_error`     | `runtime_error`                             | `0x80002da8`              |
| `eval_expr` entry   | `eval_expr`                                 | `0x80003164`              |
| `exec_stmt` entry   | `exec_stmt`                                 | `0x80003fe0`              |

The stack sits *far above* the HTIF window (`0x8001ad10 ≤ 0x87800000`) and *far
below* nothing — the interp_run code (`… 0x80004588`) is entirely below the stack
(`0x80004588 ≤ 0x87800000`), so the three `LayoutGeomPred` atoms are one `decide`
over literals each.

## What is (and is not) discharged here

* `layoutGeomPredL : LayoutGeomPred interpRunCode stackSL spEntry` — GREEN by
  `decide`/`omega` on the concrete literals (the geometry residual of the close).
* `geomFactsL : GeomFacts interpRunCode stackSL spEntry` — via `geomFacts_of_layout`
  (this is the record every Layer-4 case projects its geometry residual off).
* `jumpTableDisjoint`, `interpRunCodeDisjoint` — the per-object geometry the
  dispatch / entry cases carry.  Both the dispatch jump table (`0x80019f58`) and
  the `interp_run` code (`0x800043ec`) sit BELOW the HTIF window, so each gets the
  D-atom `StackDisjoint` (disjointness from the C-stack scribble), not a full
  above-HTIF `ObjGeom`.
* `interpRunLayout : Vsa.Refine.Layout` — the concrete refinement `Layout` whose
  `atInterpRun` pins the entry PC `0x800043ec` with the AST-array `(a, n)` ABI
  arguments in `a0`/`a1`.
* the **statics** (`ImageStaticsLoaded`) are ALREADY fully discharged in
  `Vsa/Sim/ImageDischarge.lean`; `LayoutInstance` only re-exports the derivation
  handle (`layoutStaticsLoaded`) so a case can name ONE predicate.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  Every geometry proof
is `decide`/`omega` over small concrete `Nat`s (fast-elab).
-/

open Vsa Vsa.Alloc Vsa.Sim
open Vsa.Machine (Config)
open LeanRV64DExecutable

namespace Vsa.Sim.LayoutInstance

set_option maxHeartbeats 400000

/-! ## The concrete binary constants (all from `nm c/while-riscv-htif.elf`) -/

/-- `interp_run` entry PC (symbol `interp_run`). -/
def interpRunEntry : Nat := 0x800043ec
/-- `interp_run` code region `[0x800043ec, 0x80004588)` (up to `main`). -/
def interpRunCode : Region := (0x800043ec, 0x80004588 - 0x800043ec)

/-- `eval_expr` entry PC (symbol `eval_expr`). -/
def evalExprEntry : Nat := 0x80003164
/-- `exec_stmt` entry PC (symbol `exec_stmt`). -/
def execStmtEntry : Nat := 0x80003fe0
/-- `runtime_error` entry PC (symbol `runtime_error`). -/
def runtimeErrorEntry : Nat := 0x80002da8
/-- `_exit` entry PC (symbol `_exit`). -/
def exitEntry : Nat := 0x80000180

/-- The binary-`.op` dispatch jump table base (`.rodata`, 11 × 4-byte entries). -/
def jumpTableBase : Nat := 0x80019f58

/-- The C-stack region `[__stack_top - __stack_size, __stack_top)` =
`[0x87800000, 0x88000000)` (linker `__stack_top = 0x88000000`,
`__stack_size = 0x800000`). -/
def stackSL : StackLayout := { lo := 0x87800000, hi := 0x88000000 }

/-- The entry stack pointer `__stack_top = 0x88000000` (16-aligned, top of the
C-stack region). -/
def spEntry : Nat := 0x88000000

/-! ## The concrete geometry — `LayoutGeomPred` → `GeomFacts`

Each atom is a single `decide`/`omega` over concrete literals. -/

/-- **The M6 geometry predicate, proved for the real binary.**  All three atoms
(`stack_ram`, `stack_win`, `code_stack_disjoint`) are `decide`/`omega` over the
concrete `Nat` region bounds — the geometry residual the close leaves open. -/
theorem layoutGeomPredL : LayoutGeomPred interpRunCode stackSL spEntry where
  stack_ram := by decide
  stack_win := by
    show tohostAddr + 16 ≤ (0x87800000 : Nat)
    rw [tohostAddr_val]; decide
  code_stack_disjoint := by
    show spEntry ≤ interpRunCode.1 ∨ interpRunCode.1 + interpRunCode.2 ≤ stackSL.lo
    right; decide

/-- **The concrete `GeomFacts`.**  This discharges the geometry residual for the
final close: every Layer-4 case projects its geometry off this record via `geom`. -/
def geomFactsL : GeomFacts interpRunCode stackSL spEntry :=
  geomFacts_of_layout layoutGeomPredL

/-! ## Per-object geometry the dispatch / entry cases carry -/

/-- The dispatch **jump table** (`0x80019f58`, 44 bytes) sits BELOW the HTIF
window, so it is not a full `ObjGeom`; but it is disjoint from the C-stack
scribble `[stackSL.lo, spEntry)` — the only atom the slot-survival reasoning
consumes. -/
theorem jumpTableDisjoint : StackDisjoint jumpTableBase 44 stackSL spEntry where
  stack_disjoint := by
    show jumpTableBase + 44 ≤ stackSL.lo ∨ spEntry ≤ jumpTableBase
    left; decide

/-- The `interp_run` **code** region (`0x800043ec`, `0x19c` bytes) sits BELOW the
HTIF window (`0x80004588 < tohostAddr = 0x8001ad00`) and is only 4-aligned (entry
`0x…3ec`), so — like the jump table — it is NOT a full `ObjGeom`.  The only atom
the `code ↔ stack` reasoning consumes is its disjointness from the C-stack
scribble `[stackSL.lo, spEntry)`, which `StackDisjoint` packages. -/
theorem interpRunCodeDisjoint :
    StackDisjoint interpRunCode.1 interpRunCode.2 stackSL spEntry where
  stack_disjoint := by
    show interpRunCode.1 + interpRunCode.2 ≤ stackSL.lo ∨ spEntry ≤ interpRunCode.1
    left; decide

/-! ## The concrete refinement `Layout`

The abstract `Vsa.Refine.Layout` pins the interpreter phase's entry program point.
`interpRunLayout` instantiates it: `atInterpRun c a n` says the machine is parked
at `interp_run`'s entry PC `0x800043ec` with the AST-array base `a` in `a0` and
length `n` in `a1` (the C ABI arguments of `interp_run(prog, n)`).  The
region/geometry content lives in `geomFactsL` above; this record supplies only the
program-point predicate the refinement quantifies over. -/
def interpRunLayout : Vsa.Refine.Layout where
  atInterpRun c a n :=
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRunEntry) ∧
    c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 a) ∧
    c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 n)

/-! ## Statics — reuse `ImageStaticsLoaded`

The static-data hypotheses are ALREADY fully discharged from one predicate in
`Vsa/Sim/ImageDischarge.lean` (`imageStatics_*`).  `LayoutInstance` re-exports the
single derivation handle so a case can name ONE predicate for all statics: given
`Code.ImageStaticsLoaded c.σ.mem`, every static byte-pin / packaged predicate
(`LldFmtLoaded`, the digit tables, `_impure_ptr`, …) is an O(1) projection. -/
theorem layoutStaticsLoaded {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : Code.ImageStaticsLoaded m) :
    Code.LldFmtLoaded m ∧ m[(0x80019770 : Nat)]? = some (0x2e#8) :=
  ⟨imageStatics_lldFmt h, imageStatics_hdb0 h⟩

/-! ## `#print axioms` sanity — must be `{propext, Classical.choice, Quot.sound}`. -/

#print axioms layoutGeomPredL
#print axioms geomFactsL
#print axioms jumpTableDisjoint
#print axioms interpRunCodeDisjoint
#print axioms layoutStaticsLoaded

end Vsa.Sim.LayoutInstance
