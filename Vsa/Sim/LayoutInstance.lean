import Vsa.Sim.GeomFacts
import Vsa.Sim.ImageDischarge
import Vsa.Sim.ConsoleStream
import Vsa.Sim.GoodState
import Vsa.Sim.JmpSpec
import Vsa.Sim.Code.Interp_run
import Vsa.Sim.Code.Setjmp
import Vsa.Sim.EvalSimCommon
import Vsa.RuntimeRepr
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
  `atInterpRun` pins the post-startup runtime state and the actual four-argument
  ABI: `a0=in`, `a1=stmts`, `a2=count`, `a3=0`.
* the **statics** (`ImageStaticsLoaded`) are ALREADY fully discharged in
  `Vsa/Sim/ImageDischarge.lean`; `LayoutInstance` only re-exports the derivation
  handle (`layoutStaticsLoaded`) so a case can name ONE predicate.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  Every geometry proof
is `decide`/`omega` over small concrete `Nat`s (fast-elab).
-/

open Vsa Vsa.Alloc Vsa.Sim
open Vsa.RuntimeRepr
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

/-! ## The concrete refinement boundary -/

/-- The memory footprint written before `interp_run` reaches its loop head:
the caller stack plus the 112-byte `jmp_buf` at `interp->on_error`. -/
def interpRunWriteFootprint (inp : BitVec 64) (k : Nat) : Prop :=
  (stackSL.lo ≤ k ∧ k < stackSL.hi) ∨
  (inp.toNat + 16 ≤ k ∧ k < inp.toNat + 128)

/-- The proof-only fields of a valid post-`interp_init`, script-mode
`interp_run(in, stmts, count, repl_mode)` entry snapshot.  Data witnesses are
parameters so this remains a `Prop` structure with usable named projections. -/
structure InterpRunReadyFacts
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRunEntry)
  interp_arg : c.σ.regs.get? Register.x10 = some inp
  stmts_arg : c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 stmts)
  count_arg : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 count)
  /-- The refinement theorem is for file/script semantics, not REPL printing. -/
  repl_arg : c.σ.regs.get? Register.x13 = some (0#64 : BitVec 64)
  /-- `main`'s link after `jal interp_run`. -/
  ra : c.σ.regs.get? Register.x1 = some (0x800045ec#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (BitVec.ofNat 64 spEntry)
  gp : ∃ v, c.σ.regs.get? Register.x3 = some v
  s0 : ∃ v, c.σ.regs.get? Register.x8 = some v
  s1 : ∃ v, c.σ.regs.get? Register.x9 = some v
  s2 : ∃ v, c.σ.regs.get? Register.x18 = some v
  s3 : ∃ v, c.σ.regs.get? Register.x19 = some v
  s4 : ∃ v, c.σ.regs.get? Register.x20 = some v
  s5 : ∃ v, c.σ.regs.get? Register.x21 = some v
  s6 : ∃ v, c.σ.regs.get? Register.x22 = some v
  s7 : ∃ v, c.σ.regs.get? Register.x23 = some v
  s8 : ∃ v, c.σ.regs.get? Register.x24 = some v
  s9 : ∃ v, c.σ.regs.get? Register.x25 = some v
  s10 : ∃ v, c.σ.regs.get? Register.x26 = some v
  s11 : ∃ v, c.σ.regs.get? Register.x27 = some v
  run_code : Code.Interp_runLoaded c.σ.mem
  setjmp_code : Code.SetjmpLoaded c.σ.mem
  statics : Code.ImageStaticsLoaded c.σ.mem
  console : ConsoleStream c.σ.mem
  out : OutRepr c.σ Vsa.While.initSt
  /-- `Interp.globals` and `Interp.call_depth` after `interp_init`. -/
  globals : Vsa.MemRepr.read64 c.σ.mem inp.toNat = some (φf 0)
  call_depth : Vsa.MemRepr.read32 c.σ.mem (inp.toNat + 8) = some 0
  interp_geom : ObjGeom (inp.toNat, 384) stackSL spEntry
  setjmp_geom : WinRAM (inp + 16#64)
  stack_ok : StackOK stackSL (BitVec.ofNat 64 spEntry) (176 + 1088)
  /-- Sparse machine memory must nevertheless contain every concrete stack byte. -/
  stack_bytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b : BitVec 8, c.σ.mem[k]? = some b
  stmts_align : stmts % 8 = 0
  stmts_ram : 0x80000000 ≤ stmts ∧ stmts + 8 * count ≤ 0x100000000
  stmts_win : tohostAddr + 16 ≤ stmts
  stmts_stack : stmts + 8 * count ≤ stackSL.lo ∨ spEntry ≤ stmts
  store : StoreRepr c.σ.mem N A φf φc Vsa.While.initSt.store
  native_addrs : N.print = 0x80002ed4 ∧ N.println = 0x80002f7c ∧
    N.assert = 0x80002df4
  /-- The initial store survives the concrete prologue footprint: stack spills
  and `setjmp`'s 112-byte `jmp_buf` write at `inp + 16`. -/
  store_survives : ∀ m' : Vsa.MemRepr.Mem,
    (∀ k, ¬ interpRunWriteFootprint inp k → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc Vsa.While.initSt.store
  arena_budget : A.lo + aLeft ≤ A.hi

/-- Every concrete 24-byte result slot inside the declared stack has all three
words present.  This is the exact initialization fact recursive value copies use. -/
theorem InterpRunReadyFacts.valueWordsTotal
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft a : Nat}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hlo : stackSL.lo ≤ a) (hhi : a + 24 ≤ stackSL.hi) :
    ValueWordsTotal c.σ.mem a :=
  valueWordsTotal_of_interval F.stack_bytes hlo hhi

/-- The `interp_run` statement-result slot is `88` bytes above its post-spill
stack pointer.  Its complete 24-byte value image is present at entry. -/
theorem InterpRunReadyFacts.interpRetWords
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    ValueWordsTotal c.σ.mem (spEntry - 176 + 88) := by
  apply F.valueWordsTotal <;> decide

/-- The top-level interpreter starts in the distinguished allocated global
environment.  This is derived from `initSt`; it is not an extra runtime
assumption. -/
theorem InterpRunReadyFacts.envValid
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat}
    {aLeft : Nat}
    (_F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) :
    EnvValid Vsa.While.initSt 0 :=
  EnvValid.init

/-- A non-circular, post-startup refinement boundary.  It asserts the concrete
runtime snapshot from which the decoded `interp_run` prologue can be proved; it
does not assume a machine execution or `InterpInitStoreRepr`. -/
def InterpRunReady (c : Config) (stmts count : Nat) : Prop :=
  ∃ (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (aLeft : Nat),
    InterpRunReadyFacts c stmts count inp N A φf φc aLeft

/-- The concrete layout uses the actual four-argument RISC-V ABI:
`a0 = in`, `a1 = stmts`, `a2 = count`, and `a3 = 0` for script mode. -/
def interpRunLayout : Vsa.Refine.Layout where
  atInterpRun c a n := InterpRunReady c a n

/-- Expose the concrete ready witness from `Loaded`. -/
theorem loaded_interpRunReady {p : Vsa.While.Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) :
    ∃ a n, Vsa.MemRepr.ProgramRepr c.σ.mem a n p ∧ InterpRunReady c a n := by
  exact h

/-- A loaded configuration is a live Sail state, excluding the HTIF-latched
counterexample admitted by the former three-register boundary. -/
theorem loaded_goodState {p : Vsa.While.Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) : GoodState c.σ := by
  obtain ⟨_a, _n, _hp, _inp, _N, _A, _φf, _φc, _aLeft, F⟩ := h
  exact F.good

theorem loaded_tick {p : Vsa.While.Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) : c.tick < 2 := by
  obtain ⟨_a, _n, _hp, _inp, _N, _A, _φf, _φc, _aLeft, F⟩ := h
  exact F.tick

/-- The concrete refinement boundary is explicitly post-CRT. This projection
does not pretend that the zero-initialized ELF data already satisfies newlib's
runtime `FILE` state. -/
theorem loaded_consoleStream {p : Vsa.While.Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) : ConsoleStream c.σ.mem := by
  obtain ⟨_a, _n, _hp, _inp, _N, _A, _φf, _φc, _aLeft, F⟩ := h
  exact F.console

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
