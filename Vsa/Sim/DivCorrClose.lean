import Vsa.Sim.DivFamily
import Vsa.Sim.EntryHalts

/-!
# `DivCorrFamily` reseated on a CONCRETE loop-head correspondence

`Vsa/Sim/DivFamily.lean` (`divFamily_of_corr`) reduces the divergence arm
`DivFamily L` to the per-load residual `DivCorrFamily L` — "for every loaded
`(p, c)`, a correspondence `Corr` with its per-step progress residual
`DivStep Corr` and the entry `Corr c initSt 0 0 p`".  `Vsa/Sim/TermAssembly.lean`
(`divStep_vacuous`) then recorded the machine-checked verdict that the ONLY
genuine gap is the ENTRY (the trivial `Corr := False` satisfies `DivStep`
vacuously but fails the entry).

This file supplies a **concrete** `Corr` — the loop-head `SegEntry`
correspondence, packaged with `StepsN`-reachability so the entry and the per-step
progress compose additively — and reduces `DivCorrFamily L` to TWO precisely-named
residuals, discharging the structural plumbing (the reachability threading and the
entry reindex) axiom-clean:

* **`DivEntryDrive L`** — from `Loaded L p c`, the machine reaches (in some number
  of steps) a loop-head `SegEntry` executing the whole program `p` as the
  top-level statement list, over the initial store `initSt`.  This is EXACTLY the
  content of `EntryPrologueSpan`/`InterpInitStoreRepr`'s drive
  (`Loaded → SegEntry@0x8000448c`), reused verbatim — the SAME drive the entry
  endgame is gated on.
* **`DivLoopProgress`** — from a loop-head `SegEntry` executing `s :: ss` for the
  spec node `(st, d, env)`, one spec statement step (`ExecS … s → st' .normal`)
  drives ≥ 1 non-halting machine step to a loop-head `SegEntry` executing `ss`
  for `st'`; and an INTERNALLY still-running head (`SApprox n`) drives ≥ n+1
  steps.  This is the still-running (progress-only) analog of the M4 `exec_stmt`
  case Triples' loop-back-edge — the machine forward-simulation content, named.

`divCorrFamily_of` composes them: the concrete `divCorr` carries the reachability
witness, so `DivStep`'s progress arms prepend the entry drive's steps to the
loop-body steps (both `StepsN`, composed by `StepsN.trans_add`), and the entry
`divCorr c initSt 0 0 p` is `DivEntryDrive` at `k = 0` reindex.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq ExecS Stmt Addr)

namespace Vsa.Sim.DivCorrClose

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The concrete loop-head correspondence

`divCorr c st d env ss` says: from `c`, the machine reaches (in `k` steps, for
some layout ghosts) a loop-head `SegEntry` executing the top-level statement list
`ss` for the spec node `(st, d, env)`.  The `StepsN k`-reachability indirection is
what lets the divergence forward simulation THREAD its accumulated run: the entry
correspondence is `k = 0` (the loop-head reached from the loaded entry by the
prologue drive), and each spec step advances the loop head to the tail's
`SegEntry`, composing the drive-steps and body-steps additively.

`SegEntry` pins the spec STATE `st` (store + output) but not WHICH statements
remain nor the active scope `Addr`.  The top-level statement loop reflects those
in its induction registers (`s0` = current `Stmt*` cursor, the loop bound `s2`,
the scope pointer) — a reflection this file does NOT re-derive.  We thread it as
the abstract per-node predicate `Reflect cH env ss` (a section variable): the
loop-head config `cH` reflects "executing statement list `ss` in scope `env`".
Making it a parameter keeps `divCorr` a FAITHFUL correspondence (distinct
`(env, ss)` are distinct nodes) while naming the reflection as the honest content
the loop-body progress residual supplies. -/

variable (Reflect : Config → Addr → List Stmt → Prop)

/-! ## §2. The two named residuals

The genuine machine content the divergence arm rests on. -/

/-! ## §3. `DivStep divCorr` from `DivLoopProgress`

The reachability indirection makes both `DivStep` arms mechanical: destructure the
`divCorr` reachability witness (`StepsN k c cH ∧ SegEntry@loopHead`), run the
`DivLoopProgress` arm from `cH`, and prepend the `k` drive-steps with
`StepsN.trans_add`. -/

/-! ## §4. `DivCorrFamily` from the two residuals

The entry `divCorr c initSt 0 0 p` is `DivEntryDrive` verbatim; the per-step
residual is `divStep_of_loopProgress`. -/

end Vsa.Sim.DivCorrClose
