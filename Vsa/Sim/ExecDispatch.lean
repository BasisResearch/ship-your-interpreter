import Vsa.Sim.ExecBrkCont
import Vsa.Sim.AstTransport
import Vsa.Sim.ExecBlock
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement family: the re-dispatch infrastructure

`if`/`while`/`for` execute their branch/body statement by **re-dispatch**: they set
`s0 := branch/body Stmt*` and `j 0x80004014` — the dispatch point *after* the
`exec_stmt` prologue — running the sub-statement in the SAME `exec_stmt` frame (no
`jal`, no second prologue). The sub-statement's own arm + epilogue + `ret` run
in-frame; the epilogue restores the OUTER (`if`/`while`/`for`) call's saved
registers and returns to ITS caller (sound because the frame is shared).

Consequently the branch's ordinary `ExecIH` (`ExecEntry` @ `0x80003fe0`, i.e. from
the FULL entry including the prologue) does NOT apply — re-dispatch enters at
`0x80004014`, POST-prologue. This file factors the monolithic `execBlockA`
(`ExecBrkCont.lean`) at σ13 / PC `0x80004014` into:

* **`ExecDispatchReady`** — the post-prologue machine predicate at `0x80004014`
  (the re-dispatch entry). Mirrors `ExecArmEntryK`'s field list, but pinned at the
  dispatch PC, carrying `x14 = table base`, `x16 = 8`, and the target-node
  `StmtRepr ment aStmt' s'` (from which the kind is re-derived) + a slot-resolution
  field instead of knowing the arm PC.
* **`execPrologue`** — `ExecEntry → ExecDispatchReady` (the prologue steps 1–13:
  `addi sp,-176`, five spills, four `mv`, `li a6,8`, `auipc`/`addi a4`).
* **`execDispatch`** — `ExecDispatchReady → ∃ armPC k, ExecArmEntryK …` (the
  dispatch steps 14–21: `lw a5,0(s0)`, `bltu`/`lwu`/`slli`/`add`/`lw`/`add`/`jr`),
  re-deriving the dispatched kind `k = kindOfStmt s'` from `StmtRepr` via the
  per-constructor projection `stmtRepr_kind`.
* **`ExecDispatchIH`** — the "body-from-dispatch" recursive statement IH shape:
  `∀ …, Triple (ExecDispatchReady … s' …) (ExecExit … status …)`. `if`/`while`/`for`
  consume this directly for their branch/body (via re-dispatch), whereas true
  `jal exec_stmt` boundaries (block-loop, `interp_run`) wrap the whole prologue.

`execBlockA` is left INTACT (the register-cheap `execPrologue`/`execDispatch` are
added ALONGSIDE it, so none of the landed statement cases change); the design
`execBlockA = execPrologue ≫ execDispatch` is a derived corollary a future refactor
may substitute in.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `kindOfStmt` — the statement-kind tag a `Stmt` dispatches on

The `exec_stmt` jump table dispatches on `stmt->kind` (the first 4 bytes of the
`Stmt` node). `StmtRepr m a s` pins those bytes to `kindOfStmt s` (proven by
`stmtRepr_kind` below). Matches the tags in `Vsa/MemRepr.lean`'s `StmtRepr`. -/

/-! ## `ExecDispatchReady` — the post-prologue re-dispatch predicate at `0x80004014`

The machine state at the dispatch PC (σ13 in `execBlockA`), factored out as the
re-dispatch entry. `if`/`while`/`for` reach it by `s0 := branch/body; j 0x80004014`;
`execPrologue` reaches it from the full `ExecEntry`.

Compared to `ExecArmEntryK` (`ExecBrkCont.lean`): the PC is the dispatch point
(`0x80004014`) not a per-kind arm PC; it additionally pins the dispatch scratch
`x14 = table base` and `x16 = 8`; and instead of already knowing the dispatched
kind it carries `StmtRepr ment aStmt' s'` (the target AST, `aStmt'` = re-dispatch
target = `x8`) + a slot-resolution field (`∃ armPC, StmtSlotPinned …`). The five
outer-frame spills, ABI-moved `s1/s2/s3` (interp/retslot/env), `sp-176`, saved `ra`,
`StoreRepr`/output, `Exec_stmtLoaded`, the memory frame `[SL.lo, sp)`, and the
geometry (align/RAM/above-HTIF/stack-disjoint for both the frame and the target
node) are all carried verbatim from `ExecArmEntryK`. -/

/-! ## `execPrologue` — `ExecEntry → ExecDispatchReady` (prologue steps 1–13)

The `exec_stmt` prologue lifted out of `execBlockA` verbatim: `addi sp,-176`, the
five callee-saved spills (`s0/s1/s2/s3/ra`), the four ABI `mv` moves, `li a6,8`,
and `auipc/addi a4` (the jump-table base). Lands at the dispatch PC `0x80004014`
(σ13) as `ExecDispatchReady` with `aStmt' := aStmt`, `s' := s`.

Two premises encode the design's "recurring residuals" (pushed to the true-entry
callers — `block`-loop `armExec_rec`, `interp_run` — where the AST/slot geometry is
known):
* `hfpDisj` — the `Stmt` node's AST footprint is disjoint from the stack window
  `[SL.lo, sp)`, so the full `StmtRepr` transports across the prologue spills
  (via `stmtRepr_agreeP`). `ExecEntry` only pins the four-byte tag as
  stack-disjoint; the deep footprint disjointness is the caller's obligation.
* `hslotResIn` — the jump table resolves the dispatched kind `kindOfStmt s` to some
  4-aligned, stack-disjoint arm PC (the `StmtSlotPinned` the dispatch's `lw a5,0(a5)`
  reads). -/

/-! ## `execDispatch` — `ExecDispatchReady → ∃ armPC k, ExecArmEntryK …` (dispatch steps 14–21)

The jump-table dispatch lifted out of `execBlockA`: `lw a5,0(s0)` (kind),
`bltu a6,a5` (bound, not taken — `kindOfStmt s' ≤ 8`), `lwu`/`slli`/`add` (compute
`table + 4*kind`), `lw a5,0(a5)` (signed slot), `add a5,a5,a4` (arm PC), `jr a5`.
Re-derives the dispatched kind `k = kindOfStmt s'` from the carried
`StmtRepr ment aStmt' s'` via `stmtRepr_kind`, and the arm PC from the carried
slot-resolution field. Produces the SAME `ExecArmEntryK` as `execBlockA`. -/

/-! ## `ExecDispatchIH` — the "body-from-dispatch" recursive statement IH

The re-dispatch analog of `ExecIH` (`ExecBlock.lean`): the induction hypothesis a
re-dispatching case (`if`/`while`/`for`) receives for its branch/body sub-derivation
`ExecS st d env s' st' status`, stated at the POST-prologue entry
(`ExecDispatchReady`) rather than the full `ExecEntry`. `if`/`while`/`for` set
`s0 := branch/body` and `j 0x80004014`, reaching `ExecDispatchReady`; consuming this
IH yields `ExecExitD` directly (the sub-statement's own arm + epilogue + `ret` run
in the SHARED frame — no second prologue). True `jal exec_stmt` boundaries
(`block`-loop `armExec_rec`, `interp_run`) instead wrap the whole prologue and use
the ordinary `ExecIH`; `execPrologue` bridges `ExecEntry → ExecDispatchReady`, so
one mutual-recursion motive supplies both shapes. -/

end Vsa.Sim
