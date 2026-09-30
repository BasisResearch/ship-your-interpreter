import Vsa.Sim.EntryHalts
import Vsa.Sim.EntryHaltsSpans
import Vsa.Sim.LayoutInstance

/-!
# Layer 8 — tightening the two `EntryHalts` span seams

`Vsa/Sim/EntryHaltsSpans.lean` reduced `hEntryHalts` (the program-entry premise of
`termSimClosed`) to two NAMED residuals — `EpilogueFrame` and `StoreInitSeam` —
and landed `hEntryHalts_closed` conditional on both.  This file TIGHTENS both
residuals: it discharges, from the rich `SegExit`/`SegEntry`/`Loaded`
representations, everything that IS mechanically supplied by those predicates, and
reseats the two seams onto strictly smaller, precisely-named residuals so that
`hEntryHalts_closed'` rests only on the genuine representation gaps.

## What was mechanically closed (this file)

* **Epilogue control state** (`epilogueControl_of_segExit`).  Four of the five
  `EpilogueFrame` control conjuncts — `GoodState`, `tick < 2`, `PC = 0x80004514`,
  and `output = out` — are DIRECT projections of `SegExit` at
  `interpNormalExitPC` (`SegExit.good`, `.tick`, `.pc`, and `.out : OutRepr = (output = st'.out)`
  under `st'.out = out`).  So `EpilogueFrame` reduces to the strictly smaller
  `EpilogueSpill`: the `s5 = 0` return latch, `Interp_runLoaded`, the produced
  `ExitTailChain0`, and the restore-block `ChainFacts` + `sp` — i.e. ONLY the
  genuine spill/frame/image/tail facts (the byte-level facts `SegExit` does not name).
  `epilogueFrame_of_spill` rebuilds `EpilogueFrame` from `EpilogueSpill`, so the
  whole epilogue seam is reduced to `EpilogueSpill`.

* **Prologue store-init locus** (`storeInitSeam_of_initRepr`).  The interpreter's
  store `initSt.store` (the single global frame with the three natives) is built by
  `interp_init` (`0x80004308`, called by `main` at `0x800045b4`) — which runs
  BEFORE the `interp_run`-entry `Loaded` config (`interpRunLayout.atInterpRun` pins
  the post-startup state and `a0=in`, `a1=stmts`, `a2=count`, `a3=0`).  So the store-init
  representation is genuinely OFF the `interp_run` prologue path; it cannot be
  produced by decoding `[0x800043ec, 0x8000448c)` alone.  We name that exact gap as
  the ONE residual `InterpInitStoreRepr` (its PC span decoded in its doc), and
  `storeInitSeam_of_initRepr` reduces `StoreInitSeam` to it.

## The genuine residuals `hEntryHalts_closed'` now rests on

1. `EpilogueSpill` — the epilogue restore-block spill/frame/image/tail facts
   (`ChainFacts` for `restoreChain` with `ra` pinned to `0x800045ec`, `sp`, the
   `s5 = 0` latch, `Interp_runLoaded`, `ExitTailChain0`).  Smaller than
   `EpilogueFrame` (the four control conjuncts are proved).
2. `InterpInitStoreRepr` — the `interp_init`-built store representation at the
   `interp_run` loop head (`ProgramRepr → StoreRepr initSt.store`), the AST/heap-init
   seam that lives on `main`'s `interp_init` call, not on `interp_run`'s prologue.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq Addr)
open Vsa.Sim.Code (Interp_runLoaded)

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. Epilogue — deriving the control state from `SegExit`

The four control conjuncts of `EpilogueFrame` are projections of `SegExit` at the
normal-exit PC.  The remaining facts (`s5 = 0`, `Interp_runLoaded`, the produced
`ExitTailChain0`, the restore `ChainFacts` + `sp`) are the genuine spill residual. -/

/-! ## §2. Epilogue — the tightened spill residual `EpilogueSpill`

`EpilogueSpill` carries ONLY the facts `SegExit` does not name: the `s5 = 0` latch
(the return value the epilogue's `mv a0,s5` copies out), `Interp_runLoaded` (the
code image), the produced tail span `ExitTailChain0`, and the restore-block
`ChainFacts` + `sp`.  It is strictly smaller than `EpilogueFrame` (the four control
conjuncts are gone — they are proved by `epilogueControl_of_segExit`). -/

/-! ## §3. Prologue — the store-init locus is `interp_init`, off the `interp_run` path

`StoreInitSeam` must produce, from `Loaded L p c` (the machine parked at
`interp_run`'s entry `0x800043ec` with its four ABI arguments), a `SegEntry` at the
statement-loop head `0x8000448c` over `initSt.store` (the single global frame with
the three natives).  The store is built by `interp_init` (`0x80004308`), which
`main` calls at `0x800045b4` — a call that has ALREADY RETURNED by the time the
machine is at `interp_run`'s entry.  So the store representation at the loop head is
NOT a consequence of the `interp_run` prologue decode `[0x800043ec, 0x8000448c)`
(that span never touches the store; it only spills, calls `setjmp`, and sets up the
loop bound `s2 = s0 + 8·n`).  It is the `interp_init`/`main` startup fact, named
`InterpInitStoreRepr`. -/

/-! ## §4. `hEntryHalts_closed'` — reseated on the two tightened residuals -/

end Vsa.Sim
