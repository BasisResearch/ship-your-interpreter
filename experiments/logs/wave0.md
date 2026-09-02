# Wave 0 — the restatement gate (design-pass shapes)

Executing `experiments/design/MASTER.md` §"WAVE 0" item **0a** (residual→named-
field-structure restatement, bridge-review) on main. Log per landing.

## Standing finding: the codebase moved PAST the design snapshot

The MASTER was written at census 3/58 with the `EvalEntry.ground`/`ExecEntry.ground`
INSERTION listed as MISSING. On main (@a526593) much of Wave-0 0a is **already
landed by wave 47i**:

- `ExecEntry.ground : ExecGround` is INSERTED (`Vsa/Sim/ExecEntry.lean:429`).
- The B2 entry-carry (NegResid/NotResid/logical carry `EvalEntry` as a hypothesis
  field) and the X1 McallPop amendment (dead-byte footprint pair, not ∀-mcall
  totality) are ALREADY applied (`rows/TermRouting.lean`, wave 47i comments).
- `hStr` is already FOUND (census) via `field_hStr` off `ExecEntry.ground` /
  `EvalEntry.ground` (`rows/EntryGroundRows.lean`).

So the remaining 0a surface is narrower than the MASTER text.

## Landing 1 — exec-leaf pinned widener (the design's S-exec-leaf restatement)

`experiments/design/singletons.md` §S-exec-leaf specifies hSBrk/hSCont as
record-fills that "ride the `ExecEntry.ground` insertion". **Machine-checked
correction (Law 4):** the ground insertion alone does NOT flip them. The landed
`rows/EntryGroundRows.lean` note is explicit — `execGround_caseGeom_brk/_cont`
supply ONLY the slot-pin + table-disjointness conjuncts of `ExecCaseGeom`; the
`ExecLeafWiden` conjunct is "audit class X3, a block re-land." Confirmed by probe
(`/tmp/w0probe/Probe.lean`): the plain (unpinned) `ExecLeafWiden` is NOT provable
from `ExecEntry` — the exit's in-`[SL.lo,sp)` presence is forgotten by `ExecExit`
(its `.memFrame` only frames memory OUTSIDE stack∪arena).

The eval leaves (hInt/hNull/hBool/hStr, all FOUND) closed this SAME gap in wave
47e — NOT via the plain `LeafWiden`, but by RESTATING at a PINNED exit family
(`LeafWidenP` = `Widen` at `EvalExitPinned = EvalExit ∧ LeafMemPin`) that
`leafWidenP_of_entry` discharges from the entry alone.

**LANDED** (`Vsa/Sim/rows/ExecLeafD.lean`, axiom-clean {propext, Classical.choice,
Quot.sound}, additive; wired into `Vsa.lean` after `ExecCaseGeom`):

- `ExecLeafMemPin` — exec twin of `LeafMemPin` (`pres : MemExtends` +
  `agree` outside `[SL.lo,sp)`; brk/cont touch no arena/retslot,
  `ExecBrkCont.lean:233`).
- `ExecExitPinned` / `ExecLeafWidenP` — the pinned exit family + widener.
- `execLeafWidenP_of_entry` — **PROVED**: the pinned widener follows from the
  47e-widened `ExecEntry.store_survives` alone at `PhiExtends.refl` (brk/cont
  leave the store unchanged, `st' = st`). Exact exec twin of `leafWidenP_of_entry`.
- `execExitD_of_pinnedExecExit` — the pinned-family bridge → `ExecExitD`.

This is the reusable Wave-0 0a asset the follow-up X3 re-land plugs into directly.

### Remaining X3 residual (a NAMED, bounded block re-land — NOT record-fill)

To flip hSBrk/hSCont, the coupled restatement is: move `ExecCaseGeom` (brk/cont
rows) + `execBrkSimD`/`execContSimD` to the pinned family (as the eval `*SimD`
lemmas use `LeafWidenP`), AND re-land `execBrkSim`/`execContSim` to conclude the
pin. The internal facts EXIST — `execBlockA` derives
`hmemframe6 : ∀ a, ¬(SL.lo ≤ a ∧ a < sp) → σ6.mem[a]? = m0[a]?`
(`ExecBrkCont.lean:726`), and `execBlockD` proves the epilogue LOADS leave memory
unchanged (`hmem7e : σ7.mem = mpre`, `:495`), so the exit `agree` is
`hmem7e ▸ hmemframe`; only `pres` (`MemExtends m0 σ7.mem`) needs the prologue
`writeMap8`-spill presence chain threaded to the exit. That thread is a bounded
block re-land — its own ≤1-session task, not a pure-statement 0a action, and not
safely completable inside this bounded gate under one lean process without
risking the green tree. Named residual, per Law 2/4.

## Design-deltas (adjusted beyond the fuzzed set)

- `ExecLeafMemPin` is a field-for-field transcription of the ALREADY-fuzzed
  `LeafMemPin` (exec stack-window `[SL.lo,sp)` in place of the eval
  `[SL.lo,sp) ∪ [sret,sret+24)`). `statement_fuzz.py --struct` reports the plain
  4-arg structure telescope UNDECIDABLE (discovery limitation, not a refutation);
  its inhabitability is established structurally (`m := m0` witnesses both fields)
  and by non-vacuous consumption in the axiom-clean `execLeafWidenP_of_entry`.

## Census / status

Census UNCHANGED at 4/58 (hBool/hInt/hNull/hStr) — no field flips without the X3
re-land above, which is out of this pure-statement gate's safe scope. Discipline:
OK (9 rules, 751 grandfathered). Landing 1 is additive + axiom-clean.

## Wave 48b — X3 exec-leaf re-seat (this session)

**LANDED** `Vsa/Sim/rows/ExecLeafPin.lean` (additive, all thms axiom-clean
⊆ {propext, Classical.choice, Quot.sound}; wired into `Vsa.lean` after
`EntryGroundRows`; discipline OK 9 rules; Vsa root green):

- `execBrkSimP`/`execContSimP` — the register-only leaf sims re-seated at
  `ExecExitPinned` (= `ExecExit ∧ ExecLeafMemPin`), wrapping the landed
  `execBrkSim`/`execContSim` plain-`ExecExit` `Triple`s with the exit pin.
- `execBrkSimDP`/`execContSimDP` — the `ExecExitD` (`mExecS`-motive) rows, via
  `execExitD_of_pinnedExecExit` + the entry-derivable `execLeafWidenP_of_entry`.
- `execLeafWiden_of_entry` — the PLAIN `ExecLeafWiden` from entry survival + pin.
- `field_hSBrk`/`field_hSCont` + `skelHS{Brk,Cont}_of_pin` — discharge the two
  `assembly_skeleton.tsv` holes (`∀ st, BrkResid st` / `ContResid st`) via
  `ExecEntry.ground` (slot+table) + the widener, MODULO one named premise.

**Machine-checked obstruction (Law 4) — the re-seat DID hit a genuine gap.**
The one unfilled premise is `ExecArmMemExt st .{brk,cont}` = the exit pin
`ExecLeafMemPin SL sp m0 c'.σ.mem`, whose `pres` field is `MemExtends m0 c'.σ.mem`.
`agree` is internally free (`execBlockD`'s `hmem7e ▸ hmemframe`, arena-inclusive).
`pres` is provable ONLY from the prologue `writeMap8`-spill chain
(`ExecBrkCont.lean:621-711`), which lives INSIDE `execBlockA` and is NOT exposed
by `ExecArmEntryK` (whose memory clause is m0-*agreement*, not presence).  Exposing
it is the exec twin of the 47e eval move that amended `blockA_k`'s post to carry
`MemExtends m0 ment` (`EvalSimCommon.lean:907`), but on exec it lands into the
SHARED `ExecArmEntryK` ∧-tower — a ~10-file ITEM-ZERO positional-destructure
fan-out (`ExecBrkCont`/`ExecDispatch`/`ExecRecCommon` + 6 `Stmt*ArmStagePre`
rows).  Machine-verified the tower sites: full destructures at ExecRecCommon:462,
ExecBrkCont:{256,1227,1311}, ExecDispatch:611 + 6 StagePre rows; constructions at
ExecBrkCont:1179 (execBlockA), ExecDispatch:570.  NOT safely completable inside a
bounded single-lean-process gate (sole writer, green-tree risk) — named as X3-b,
its own ≤1-session amendment wave.  The 48a report's "block re-land" was this.

**Census UNCHANGED at 4/58** (hInt/hNull/hBool/hStr; verified `field_census.py
-j4` = {FOUND:4, NOT_FOUND:54}).  hSBrk/hSCont stay `hole` — they carry the named
premise (honest not-found), so the TSV rows are NOT flipped to `done`; the notes
record the scaffold + the X3-b obstruction.  Once `execBlockA` exposes
`MemExtends m0 ment` (X3-b), `field_hSBrk`/`field_hSCont` become unconditional and
the census flips to 6/58 — the scaffold makes that a mechanical premise fill.

## Wave 48c — ExecArmEntryK `MemExtends m0 ment` EXPOSED (recovery; census still 4/58)

**LANDED (green + axiom-clean ⊆ {propext, Classical.choice, Quot.sound}; discipline OK 9 rules).**
Reconstructed + finished the predecessor's dead mid-edit (`ExecBrkCont.lean`, 3 errors).

Fan-out ACTUAL (the "~10-file ITEM-ZERO" the 48b log predicted):
- `ExecArmEntryK` (`ExecBrkCont.lean`): new last conjunct `MemExtends m0 ment`.
  Producer `execBlockA` supplies `hMemExt6` (trans of 5 `memExtends_writeMap8`
  over `hmem6e..hmem2e` + `hmem : c.σ.mem = m0`).
- `ExecDispatchReady` (`ExecDispatch.lean`): twin last conjunct; `execPrologue`
  supplies it (same 5-spill trans), `execDispatch` forwards it to the produced
  `ExecArmEntryK`.
- 8 full-tower destructures given one trailing binder: ExecBrkCont {brk@1241,
  cont@1325}, ExecDispatch@611, ExecRecCommon@462, 5 `Stmt*/Fl*ArmStagePre`
  rows, ArmDispatchCombinatorExec@215 (copy), ExecRetNullGlue@331 (the
  `RetNullPostBeqz` re-cut — split `hral`).  Verified green: all StagePre rows
  (axiom-clean), the 9 Exec* producers, ArmDispatchCombinatorExec,
  ExecRetNullGlue, ExecCaseGeom/ExecRouting/ExecDispatchRows/ExecRecRows,
  TermSimAssembly/TermSimClose/InductionScaffold/FnSummary capstones.
- GOTCHA: `lake env lean` on a downstream file reads the STALE olean of an
  edited import → phantom "Eq.refl 2 fields"/"No goals" errors.  Regen each
  edited file's olean with `lake env lean -o .lake/build/lib/lean/<path>.olean`
  in import order BEFORE compiling consumers.  (ExecBrkcont→ExecDispatch→
  ExecRecCommon→rows.)

**hSBrk/hSCont FLIP — machine-checked obstruction (Law 4), census UNCHANGED 4/58.**
The 48b proposal ("expose ExecArmEntryK MemExtends → flip with zero further
proof") was HALF right.  `ExecArmMemExt st status` is over the POST-EPILOGUE
EXIT (`ExecExit → ExecLeafMemPin SL sp m0 c'.σ.mem`); its `pres` is about the
EXIT memory, not the arm-entry `ment`.  A bare `ExecExit` carries NO presence
(only arena/retslot-excluded `memFrame`), so `∀ ExecExit → pin` is provably
underivable — CONFIRMED (ExecExit/ExecEntry have no `pres`/`memExt` field).
`field_hSBrk`/`field_hSCont` therefore STILL carry the `ExecArmMemExt` premise;
they stay `hole`/NOT_FOUND (honest).  The flip is X3-c: thread presence to the
exit via the SHARED `execBlockD` (7 recursive-case callers) into `ExecExitPinned`
+ re-state `BrkResid`/`ContResid`@`ExecLeafWidenP` + re-point `exec_brk_row`/
`exec_cont_row` (mirroring eval `evalIntSimP`/`IntLeafResid`@`LeafWidenP`/
`Field_hInt`) — a distinct ≤1-session wave, not this bounded gate (recursor
green-tree risk).  Full recipe: observations.md `execarmmemext-exit-not-entry`;
TSV + singletons.md updated.

> COORDINATOR NOTE (live): `lake build` in the proof repo is AUTO-KILLED by a
> watchdog (Law 5 — racing-build protection). It is not an environment fault.
> Use `lake env lean <file>` / `lake env lean <file> -o <olean>` exclusively,
> per your brief and CLAUDE.md.

## Wave 48d — X3-c presence transport LANDED (census 4 → 6/58)

**LANDED (green + axiom-clean ⊆ {propext, Classical.choice, Quot.sound}).**
The X3-c presence transport, mirroring the eval precedent (47e
`blockD_v`-`Q`/`evalIntSimP`/`Field_hInt`) exactly:

- `execBlockDQ` (`ExecBrkCont.lean`): NEW — `execBlockD` with a `Q : Mem → Prop`
  post-parameter carried across the memory-pure epilogue (`Q mpre → Q c.σ.mem`
  via `hmem7e`).  `execBlockD` (plain) is now the `Q := fun _ => True`
  specialization — its 5 recursive-case callers (ExecVarDecl/ExecExprRet/
  ExecVarNull/ExecIf/ExecWhile) are UNTOUCHED (verified `lake env lean` clean).
  So the feared "7-caller green-tree risk" did not materialize: the overload
  isolates the change to the brk/cont leaf.
- `execBrkSim`/`execContSim` now CONCLUDE `ExecExitPinned` (= `ExecExit ∧
  ExecLeafMemPin`).  brk carries the pin via `execBlockDQ`'s `Q :=
  ExecLeafMemPin SL sp m0`; cont inline through its tail.  Pin = ⟨arm
  `MemExtends m0 ment` (48c's `hMemExtArm`), arena-inclusive arm frame
  `hmemframe⟩`.
- `ExecLeafMemPin`/`ExecExitPinned` MOVED UPSTREAM to `ExecBrkCont.lean` (dodging
  the ExecLeafD↓ExecCaseGeom↓ExecBrkCont import cycle); `ExecLeafWidenP`/
  `execLeafWidenP_of_entry`/`execExitD_of_pinnedExecExit` MOVED into
  `ExecCaseGeom.lean` (they need `Widen`/`WidenMeta`).  `ExecCaseGeom` now carries
  the PINNED `ExecLeafWidenP`; `execBrkSimD`/`execContSimD` re-point at
  `execExitD_of_pinnedExecExit`.
- `field_hSBrk`/`field_hSCont` (`ExecLeafPin.lean`) are now PREMISE-FREE — widener
  from `execLeafWidenP_of_entry hc`, slot/table from `hc.ground`.  `ExecArmMemExt`
  and the `execBrkSimP`/`execContSimP`/`*DP` premise-laden wrappers DELETED.

**Census FLIPPED to 6/58** (`field_census.py -j4` = {FOUND:6, NOT_FOUND:52};
FOUND = hBool/hInt/hNull/hStr/**hSBrk/hSCont**).  NO fourth rung emerged — the
eval-mirror hypothesis HELD end-to-end.  Verified via `lake env lean` per-file
(ExecBrkCont + all direct/transitive importers incl. TermAssembly capstone +
5 recursive callers, all clean).  NOTE: `Vsa/Sim/EvalCallClosure.lean` is a
PRE-EXISTING broken ORPHAN (4 errors at HEAD, imported by nothing, not in
`Vsa.lean`) — it breaks whole-tree `lake build` but is irrelevant to the `Vsa`
image / census / axiom audit.  TSV + singletons.md + observations.md updated.

---
## Wave 48e — X2 entry-carry: OBSTRUCTION (both literal cures insufficient), census 6/58

Harvested two cluster provers' artifacts (intcells refutations Field_hI*/hEq/hNe,
unary overquant obstructions, both logs) and, per Law 4, MACHINE-CHECKED that the
literal cures do NOT relight any field.

**Cure A (int/eq cells)** — specced as "add `EvalEntry` hyp to
`BinIntCellResid`/`BinEqCellResid`; value paths relight verbatim". FALSE premise:
`BinIntCellResid` packs a whole `BinArmExtras`, whose `mem_ext`/`frame_pop`/
`x13_pres` are the IDENTICAL `∀m`/`∀mcall` over-quant shape prove-unary refuted.
`EvalEntry`'s finite pins don't force `[SL.lo,sp)` populated ⇒ these are false
as ∀-conclusions. New machine-checked witness:
`experiments/fleet/obstructions/BinArmExtrasMemExtOverquant.lean`
(axioms {propext,Classical.choice,Quot.sound}). The int-cell prover's slot6-only
refutation UNDER-reported this — slot6 becomes entry-supplied, but the memory
closures do not. So the amended `BinIntCellResid` is STILL false; no relight.

**Cure B (6 unary/logic)** — the `∀mcall` presence+memExt pair is the same class
(prove-unary: `UnaryLogic{MemExt,Presence}Overquant.lean`, harvested). Consumer
`evalNegSim` uses them only for the ONE concrete `mcall` from `blockB_unary`, but
`blockB_unary` outputs only `∀a ¬stack → mcall[a]?=m0[a]?`, NOT `MemExtends m0 mcall`
— so even the sim cannot currently derive them; it was relying on the false residual.

**Root cause (unified) + the real cure** — `blockA_binaryArm` ALREADY produces
`MemExtends m0 ment` intrinsically (`blockA_k` 2nd output, `EvalIntSim2.lean:324`
`_hpresM`), so `BinArmExtras.mem_ext` is REDUNDANT. The correct amendment DROPS the
3 memory closures from `BinArmExtras` (+ the 2 from each unary/logic `*Resid`) and
threads the concrete post-dispatch `ment`/`mcall` (a writeMap extension of `m0`)
from `blockA_binaryArm`/`blockB_unary`, with `blockB_unary` extended to also emit
`MemExtends m0 mcall` intrinsically. Cone: `BinArmExtras` + `blockA_binaryArm(_budgeted)`
+ 11 `binRow_*` + 10 `eval*Sim` + 6 unary sims. FEASIBLE (the intrinsic facts exist)
but a multi-file restatement, NOT a one-field statement tweak — not landable green
in one bounded pass. LANDED THIS PASS: harvest + 3 machine-checked obstruction
classes + observations entry. FIELDS FOUND: 0 new (census 6/58, honest).
