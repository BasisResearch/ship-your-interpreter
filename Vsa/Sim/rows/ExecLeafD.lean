import Vsa.Sim.rows.ExecCaseGeom

/-!
# `ExecLeafD` — the PINNED exec-leaf widener (Wave-0 0a exec-leaf restatement)

The statement-side twin of `EvalLeafD.lean`'s wave-47e `LeafWidenP`/
`leafWidenP_of_entry` payoff, transcribed for the register-only exec leaves
(`brk`/`cont`).

## Why this file exists (the design's exec-leaf record-fill shape)

`experiments/design/singletons.md` §S-exec-leaf specifies hSBrk/hSCont as the
exec-leaf record-fills that ride the `ExecEntry.ground` insertion (LANDED,
wave 47i).  But the census shows they are still `NOT_FOUND`, and the landed
`rows/EntryGroundRows.lean` note is explicit: `execGround_caseGeom_brk`/`_cont`
supply ONLY the slot-pin + table-disjointness conjuncts of `ExecCaseGeom` — "the
widener half is audit class X3, a block re-land."  So the ground insertion alone
does NOT flip the fields; the `ExecLeafWiden` half is separate content.

The eval leaves (hInt/hNull/hBool/hStr — all FOUND) closed this same gap in
wave 47e NOT by re-supplying the plain (unpinned) `LeafWiden` (unprovable from
the entry — the exit's in-stack presence is forgotten by `EvalExit`), but by:

  1. RESTATING the widener at a PINNED exit family (`LeafWidenP` = `Widen` at
     `EvalExitPinned = EvalExit ∧ LeafMemPin`), and
  2. proving that pinned widener from the ENTRY alone (`leafWidenP_of_entry`),
     since the pin's `pres`/`agree` re-supply exactly what the widener needs.

This file transcribes that shape to exec (the design's "restate as the
`StmtArmResid` … conditioned on `m0`" reduced to the concrete brk/cont leaves).

## What is PROVED here (safe, additive, entry-derivable)

* `ExecLeafMemPin` — the exec twin of `LeafMemPin`: presence monotonicity +
  agreement-with-`m0` outside `[SL.lo, sp)` (register-only leaves never touch the
  arena or a retslot — `ExecBrkCont.lean:233` "No arena / retslot write on the
  brk/cont path").
* `ExecExitPinned` / `ExecLeafWidenP` — the pinned exit family + its widener,
  the exec twins of `EvalExitPinned`/`LeafWidenP`.
* `execLeafWidenP_of_entry` — **the payoff**: the pinned widener follows from
  the (47e-widened `[SL.lo,SL.hi)`) `ExecEntry.store_survives` alone, at the
  identity φ-pair, since brk/cont do not change the store (`st' = st`).  This is
  the exec twin of `leafWidenP_of_entry`, and is what makes hSBrk/hSCont a record
  fill ONCE the leaf sims conclude the pin.
* `execExitD_of_pinnedExecExit` — the pinned-family bridge `ExecExitPinned ∧
  ExecLeafWidenP → ExecExitD` (record reshape, exec twin of
  `evalExitD_of_pinnedExit`).

## The remaining residual (the X3 block re-land — a NAMED premise, Law 2)

`execBrkSim`/`execContSim` (`ExecBrkCont.lean`) currently conclude the PLAIN
`ExecExit`.  To close hSBrk/hSCont they must additionally conclude the
`ExecLeafMemPin` (i.e. the pinned exit `ExecExitPinned`).  The internal facts are
already present inside the proof — `execBlockA` derives the arm-level
`hmemframe6 : ∀ a, ¬(SL.lo ≤ a ∧ a < sp.toNat) → σ6.mem[a]? = m0[a]?`
(`ExecBrkCont.lean:726`), and `execBlockD` proves the epilogue LOADS leave memory
unchanged (`hmem7e : σ7.mem = mpre`, `:495`), so the exit `agree` clause is
literally `hmem7e ▸ hmemframe`; only the `pres` (`MemExtends m0 σ7.mem`) needs the
prologue `writeMap8`-spill presence chain threaded to the exit.  That thread is
the bounded block re-land, named here as `ExecBrkContPinReland` so the record-fill
of hSBrk/hSCont is a machine-checked one-liner off it (`field_hSBrk`/`_hSCont`
below).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-! ## MOVED UPSTREAM (wave 48d, X3-c)

`ExecLeafMemPin`/`ExecExitPinned` are now in `Vsa/Sim/ExecBrkCont.lean` (so
`execBrkSim`/`execContSim` can conclude the pinned exit directly, the presence
threaded through `execBlockD`'s `Q`).  `ExecLeafWidenP`/`execLeafWidenP_of_entry`
/`execExitD_of_pinnedExecExit` are now in `rows/ExecCaseGeom.lean` (they are the
`ExecCaseGeom` widener half + its entry-derivation, and need `Widen`/`WidenMeta`
which `ExecCaseGeom` imports).  All are in scope here transitively.  This file is
retained as the historical anchor for the wave-48a/b/c pinned-leaf ladder and its
downstream importer `rows/ExecLeafPin.lean`. -/

end Vsa.Sim

#print axioms Vsa.Sim.execLeafWidenP_of_entry
#print axioms Vsa.Sim.execExitD_of_pinnedExecExit
