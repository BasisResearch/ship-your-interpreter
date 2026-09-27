import Vsa.Sim.GeomFacts
import Vsa.Sim.LocaleData
import Vsa.Sim.StderrStream
import Vsa.Sim.JmpSpec
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.RuntimeOwnershipInitial
import Vsa.Refinement
import Vsa.Sim.SharedGeometry
import Vsa.Sim.BlockPilot
import Vsa.Sim.Code.ImageStatics
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part31
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch07Part18
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part31
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch10Part30
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch11Part31
import Vsa.Sim.DecodeTable.Batch12Part07
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch13Part04
import Vsa.Sim.DecodeTable.Batch13Part21
import Vsa.Sim.DecodeTable.Batch14Part05
import Vsa.Sim.DecodeTable.Batch14Part31
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part20
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.StrcmpSpecCond
import Vsa.Sim.ValueEqualSpec2

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
| entry `sp`          | `__stack_top - 768` (main frame)             | `0x87fffd00`              |
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

/-- The C-stack region `[__stack_top - __stack_size, __stack_top)` =
`[0x87800000, 0x88000000)` (linker `__stack_top = 0x88000000`,
`__stack_size = 0x800000`). -/
def stackSL : StackLayout := { lo := 0x87800000, hi := 0x88000000 }

/-- Main retains its 768-byte frame while calling `interp_run`. -/
def spEntry : Nat := 0x87fffd00

/-- CRT's fixed global pointer. -/
def gpEntry : Nat := 0x8001b510

/-- Main's local `Interp` object, at `sp + 272`. -/
def interpObject : Nat := 0x87fffe10

/-! ## The concrete geometry — `LayoutGeomPred` → `GeomFacts`

Each atom is a single `decide`/`omega` over concrete literals. -/

/-! ## Per-object geometry the dispatch / entry cases carry -/

/-! ## The concrete refinement boundary -/

/-- The memory footprint written before `interp_run` reaches its loop head:
the caller stack plus the 112-byte `jmp_buf` at `interp->on_error`. -/
def interpRunWriteFootprint (inp : BitVec 64) (k : Nat) : Prop :=
  (stackSL.lo ≤ k ∧ k < stackSL.hi) ∨
  (inp.toNat + 16 ≤ k ∧ k < inp.toNat + 128)

/-- The proof-only fields of a valid post-`interp_init`, script-mode
`interp_run(in, stmts, count, repl_mode)` entry snapshot.  Data witnesses are
parameters so this remains a `Prop` structure with usable named projections. -/
structure InterpRunPhysicalFacts
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRunEntry)
  interp_arg : c.σ.regs.get? Register.x10 = some inp
  interp_local : inp = BitVec.ofNat 64 interpObject
  stmts_arg : c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 stmts)
  count_arg : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 count)
  /-- The refinement theorem is for file/script semantics, not REPL printing. -/
  repl_arg : c.σ.regs.get? Register.x13 = some (0#64 : BitVec 64)
  /-- `main`'s link after `jal interp_run`. -/
  ra : c.σ.regs.get? Register.x1 = some (0x800045ec#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (BitVec.ofNat 64 spEntry)
  gp : c.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 gpEntry)
  main_ra : Vsa.MemRepr.read64 c.σ.mem 0x87fffff8 = some 0x80000038
  htif_payload : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
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
  text_image : Code.FixedTextLoaded c.σ.mem
  rodata_image : Code.FixedRodataLoaded c.σ.mem
  statics : Code.ImageStaticsLoaded c.σ.mem
  /-- `stdout` as `main`'s `setvbuf` leaves it: `_flags = 0x000a`, not yet
  oriented (the first console write sets `__SORD`: `ConsoleStreamAt.orient`). -/
  console : ConsoleBoot c.σ.mem
  exit_runtime : ExitRuntimeData c.σ.mem
  arena_protected : ∀ a, ProtectedInitialByte a → ¬ (A.lo ≤ a ∧ a < A.hi)
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

/-! ## Stack admissibility (INTERP_DESIGN.md Q1, §10.4)

The boundary's `stack_ok` is the constant `176 + 1088`, but each recursion
level consumes a real machine frame, and the heap ends where the stack begins
(`DlHeap.heapEnd = stackSL.lo`). A loaded program must fit the stack below
`interp_run`'s frame, beside the heap's `InitialAllocatorAt.capacity`. -/

/-- `interp_run`'s machine frame, bytes (`800043ec: addi sp,sp,-176`). -/
def interpRunFrame : Nat := 176

/-- Stack headroom below every `eval_expr` frame beyond ItemZero's
`evalFrame` (user decision Q7, 2026-09-25). A leaf arm at the deepest call
level owns `evalFrame` bytes below its frame, but `runtime_error` needs 1248
(its 224-byte frame plus `snprintf`'s 1024) and a native call's `fprintf`
chain 4224 below a call node's 2176: the larger shortfall, `4224 - 2176`. -/
def helperHeadroom : Nat := 2048

/-- A program fits the stack: every top-level statement's ItemZero need at
depth 0 (`ExecEntry.stackBudget`: `s.stackNeed + maxCallDepth * perCallBudget +
evalFrame`) lies between `stackSL.lo` and `interp_run`'s post-spill `sp`, and
every `.fn` body fits one call level. Decidable over the concrete AST
(`programStackFits`). -/
structure ProgramStackFits (p : Vsa.While.Program) : Prop where
  need : stackSL.lo + Vsa.While.Stmt.stackNeedList p +
    Vsa.While.maxCallDepth * Vsa.While.perCallBudget + Vsa.While.evalFrame + helperHeadroom +
    interpRunFrame ≤ spEntry
  bodies : Vsa.While.Stmt.bodiesBoundList Vsa.While.perCallBudget p = true

/-- The kernel-computable checker for `ProgramStackFits`. -/
def programStackFits (p : Vsa.While.Program) : Bool :=
  decide (stackSL.lo + Vsa.While.Stmt.stackNeedList p +
    Vsa.While.maxCallDepth * Vsa.While.perCallBudget + Vsa.While.evalFrame + helperHeadroom +
    interpRunFrame ≤ spEntry) &&
  Vsa.While.Stmt.bodiesBoundList Vsa.While.perCallBudget p

theorem ProgramStackFits.of_check {p : Vsa.While.Program}
    (h : programStackFits p = true) : ProgramStackFits p := by
  unfold programStackFits at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1, h.2⟩

/-- **Stack admissibility**, shaped like `DlHeap.InitialAllocatorAt.capacity`:
every program the memory represents fits the stack. -/
def StackAdmissible (m : Vsa.MemRepr.Mem) (stmts count : Nat) : Prop :=
  ∀ p : Vsa.While.Program, Vsa.MemRepr.ProgramRepr m stmts count p → ProgramStackFits p

/-! ## The boundary heap's frame chunks and allocator words (A0's `BootGap`)

`InitialOwned` places every live extent inside SOME in-use chunk, not alone in
it, and `DlHeap.HeapAt` leaves the break's alignment, the high bits of the
`binblocks` word, and the top chunk's minimum size open. `interp_init`
allocates the global frame's `Env` struct and its two arrays by three separate
`malloc`s; the loader leaves the break page-aligned; `binblocks` holds bits
`1 << (i / 4)` for `i < 128` only; and the ELF's `.data` sets
`_impure_data._stderr` to `&__sf[2]`. `BootHeap` states these facts about the
loaded configuration, with the ownership and allocator witnesses they are about
(user decision, 2026-09-24; INTERP_DESIGN.md "Decisions"). -/

/-- The global frame's heap geometry: the `Env` struct lies in `sblk`; while
`cap > 0` the names and values arrays start `nblk` and `vblk`. -/
structure BootFrame where
  cap : Nat
  pn : Nat
  pv : Nat
  sblk : Nat × Nat
  nblk : Nat × Nat
  vblk : Nat × Nat

/-- The heap blocks the global frame owns. -/
def BootFrame.blocks (F : BootFrame) : List (Nat × Nat) :=
  F.sblk :: (if F.cap = 0 then [] else [F.nblk, F.vblk])

/-- The global frame (`Env*` at `e`) owns three distinct whole in-use chunk
payloads (`malloc_usable_size = size - 8`) that hold no shared byte. -/
structure BootFrameChunks (m : Vsa.MemRepr.Mem) (chunks : List DlHeap.Chunk)
    (shared : Nat → Prop) (e : Nat) (F : BootFrame) : Prop where
  cap : Vsa.MemRepr.read32 m (e + 4) = some F.cap
  names : Vsa.MemRepr.read64 m (e + 8) = some F.pn
  vals : Vsa.MemRepr.read64 m (e + 16) = some F.pv
  sblk : F.sblk.1 ≤ e ∧ e + 32 ≤ F.sblk.1 + F.sblk.2
  arrays : 0 < F.cap → F.nblk.1 = F.pn ∧ 8 * F.cap ≤ F.nblk.2 ∧
    F.vblk.1 = F.pv ∧ 24 * F.cap ≤ F.vblk.2
  /-- Each block is a whole in-use chunk payload. -/
  live : ∀ b ∈ F.blocks, ∃ c ∈ chunks, c.inuse = true ∧ b = (c.addr + 16, c.size - 8)
  /-- Three different chunks. -/
  nodup : F.blocks.Nodup
  /-- No shared (immutable) byte lives in them. -/
  unshared : ∀ b ∈ F.blocks, ∀ k, b.1 ≤ k → k < b.1 + b.2 → ¬ shared k
  /-- The capacity `env_define`'s growth policy reaches for the three natives
  `interp_init` defines (`env.c`: `cap = cap ? 2*cap : 8`). User decision
  (2026-09-24, integration): the Iris frame invariant keeps capacities
  canonical (`FrameLayout.cap_canon`). -/
  cap_canon : F.cap = 8

/-- `_impure_data._stderr` (`reent + 24`), read by `main`'s error line. -/
def impureStderrAddr : Nat := consoleReent + 24

/-- The boundary heap facts `DlHeap.InitialAllocatorAt` does not state. -/
structure BootHeapFacts (m : Vsa.MemRepr.Mem) (shared : Nat → Prop) (e top brkv : Nat)
    (chunks : List DlHeap.Chunk) (F : BootFrame) : Prop where
  /-- dlmalloc keeps the top chunk at least `MINSIZE`. -/
  top_room : top + 16 ≤ brkv
  /-- The break is page-aligned (INTERP_DESIGN.md Q5). -/
  brk_page : brkv % 4096 = 0
  /-- `binblocks` fits in 32 bits (INTERP_DESIGN.md Q5b). -/
  binblocks : ∀ bb, Vsa.MemRepr.read64 m DlHeap.binblocksAddr = some bb → bb < 2 ^ 32
  /-- The global frame's blocks are whole, distinct, unshared chunk payloads. -/
  frame : BootFrameChunks m chunks shared e F
  /-- `_impure_data._stderr = &__sf[2]` (INTERP_DESIGN.md Q6). -/
  stderr : Vsa.MemRepr.read64 m impureStderrAddr = some exitStderr
  /-- The C locale's data (`LocaleData`): `_svfprintf_r`'s `mbtowc` hook,
  `__mb_cur_max`, the decimal point. Lane N2: the `snprintf`/`fprintf`
  proofs jump through the hook, so `StdioOK` carries it. -/
  locale : LocaleData m
  /-- `stderr`'s `_bf._base` (`NULL`) and `_write` (`__swrite`), which its
  first write reads (`StderrStream`). Lane N3: the `fwrite`/`fprintf`-to-`stderr`
  proofs, so `StdioOK` carries it. -/
  stderrStream : StderrStream m
  /-- Every shared byte is RAM with the word loop's slack, its read window
  off the HTIF words, and off the stack. User decisions: 2026-09-24
  (integration; the Iris route's string reads need it, `SharedWin`) and
  2026-09-25 (REVIEW.md P7: shared bytes may lie in `.rodata`, where the
  natives' value names are). -/
  shared_geom : SharedReadWin shared stackSL

/-- The initial ownership, one allocator walk of it, and the facts above, about
the same witnesses. -/
structure BootHeap (m : Vsa.MemRepr.Mem) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (stmts count : Nat) (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame) : Prop where
  owned : RuntimeOwnership.InitialOwned m A stackSL φf φc stmts count D
  alloc : DlHeap.InitialAllocatorAt m D.exts (RuntimeOwnership.ReallocExtent D.allocations)
    stmts count top brkv chunks bins
  facts : BootHeapFacts m D.shared (φf 0) top brkv chunks F

/-- Initial program and runtime store share one immutable domain and live ledger. -/
structure InterpRunReadyFacts
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop extends
    InterpRunPhysicalFacts c stmts count inp N A φf φc aLeft where
  /-- The initial ownership with one allocator walk and the boundary heap
  facts about it (user decision, 2026-09-24: A0's `BootGap`). The ownership
  alone is `InterpRunReadyFacts.ownership`. -/
  boot : ∃ (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame),
    BootHeap c.σ.mem A φf φc stmts count D top brkv chunks bins F
  /-- Q1 (user-approved, 2026-09-23): the represented program fits the stack
  below `interp_run`'s frame. Without it an AST deeper than the 8 MiB stack
  overflows into the heap (INTERP_DESIGN.md §10.4). -/
  stack_admissible : StackAdmissible c.σ.mem stmts count
  /-- Every general register is present in Sail's register map (the loader
  initialises all of them). User decision (2026-09-24, boundary facts): the
  Iris route's global invariant `VsaOk.gpr` needs it at adequacy. -/
  gprs : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome
  /-- `main`'s `s0` is `&_impure_ptr` (`0x80004590: addi s0,gp,1120` before
  `jal interp_run`). `interp_run` spills it and its error line and landing
  reload it. User decision (2026-09-24, boundary facts). -/
  s0_impure : c.σ.regs.get? Register.x8 = some (0x8001b970#64 : BitVec 64)

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

/-! ## Statics — reuse `ImageStaticsLoaded`

The static-data hypotheses are ALREADY fully discharged from one predicate in
`Vsa/Sim/ImageDischarge.lean` (`imageStatics_*`).  `LayoutInstance` re-exports the
single derivation handle so a case can name ONE predicate for all statics: given
`Code.ImageStaticsLoaded c.σ.mem`, every static byte-pin / packaged predicate
(`LldFmtLoaded`, the digit tables, `_impure_ptr`, …) is an O(1) projection. -/

/-! ## `#print axioms` sanity — must be `{propext, Classical.choice, Quot.sound}`. -/

end Vsa.Sim.LayoutInstance
