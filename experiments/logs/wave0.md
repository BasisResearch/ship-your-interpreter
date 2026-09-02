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

---
## Wave 48f — BinArmExtras closure-drop: mem_ext REDUNDANT (landable), frame_pop/x13_pres are NEW RUNGS (machine-checked, STOP per Law 4)

Read 48e trail + full cone (BinArmBridge/blockA_k/ArmEntryK/blockB_unary/blockC_neg/
SubEvalReturn/EvalGround/TermRouting). Machine-grounded findings BEFORE editing:

- `mem_ext` (BinArmExtras + the `∀mcall→MemExtends` conjunct in all 6 unary/logic
  Resids): TRULY REDUNDANT. `blockA_k`'s 2nd output `_hpresM : MemExtends m0 ment`
  (EvalIntSim2.lean:326) and `SubEvalReturn.MemExtends mcall c.σ.mem` (EvalRecCommon
  .lean:173) already supply the concrete fact. Droppable + rethreadable.
- `frame_pop` / the windowed-presence conjunct: NOT redundant, NOT block-derivable.
  Consumer (blockC_neg:231-276 via `stackpop_present`) needs PRESENCE of the DEAD
  sub-result-buffer bytes `[subsret+4,+8) ∪ [subsret+16,+24)` (subsret=sp-944) in the
  PRE-call memory `mcall`=`ment`. Those bytes ⊆ `[SL.lo,sp)` scribble window where
  ment=m0 (memframe), and are UNCONSTRAINED by ValueRepr (.int pins only kind+payload
  — EvalRecCommon.lean:14-20 documents exactly this). The prologue writes only the 4
  spill slots [sp-8..sp-32]. So the presence is a genuine `m0` ENTRY fact, absent from
  EvalGround (which carries table/AST pins + disjointness, NOT frame-window presence).
  Dropping it needs a NEW entry-ground frame-presence field = a genuine new rung.
- `x13_pres`: NOT redundant. `ArmEntryK` does not expose x13 (a caller-save temp);
  discharging needs a blockA_k/ArmEntryK widening that tracks x13 across the dispatch
  span 0x80003164→0x800034e8 = a genuine new rung.

The 48e proposal ("thread the concrete ment/mcall from block output") holds ONLY for
mem_ext. frame_pop/x13_pres are the TWO new rungs. Landing mem_ext drop alone relights
0 fields (residuals still carry the false frame_pop ∀-closure). Proceeding to LAND the
mem_ext redundancy proof (shrinks false surface, confirms the claim), then STOP.

### LANDED + VERDICT (48f)

LANDED (green, axioms ⊆ {propext,Classical.choice,Quot.sound}):
- `BinArmExtras.mem_ext` DROPPED (`Vsa/Sim/rows/BinArmBridge.lean`); `blockA_binaryArm`
  now threads `blockA_k`'s intrinsic 2nd output `hpresM : MemExtends m0 ment` in its
  place. Proves the redundancy concretely. No downstream churn — every consumer
  (BinDispatchRow 11 binRow_*/BinIntCellResid/BinEqCellResid, BinIntReadback,
  the 10 sims, EvalChildFieldCombinator, ArmDispatchCombinator, TermAssembly capstone)
  takes `BinArmExtras` as a HYPOTHESIS and never projects `.mem_ext`. All recompiled
  green. discipline OK (9 rules). census unchanged 6/58.

MACHINE-CHECKED OBSTRUCTION (new evidence, Law 4 STOP):
- `experiments/fleet/obstructions/BinArmExtrasFramePopNewRung.lean` (axiom-clean):
  `BinArmExtras.frame_pop` refuted as an isolated field over the actual `[sp-1120,sp)`
  window (empty mcall). Plus the analysis that it is NOT block-derivable: the DEAD
  sub-result-buffer bytes it must witness present are unconstrained by ValueRepr and
  unwritten by the prologue ⇒ its honest cure is a NEW entry-ground frame-presence
  field. `x13_pres` needs a blockA_k/ArmEntryK x13-tracking widening. BOTH are genuine
  new rungs, distinct from the redundant `mem_ext` class.

INVERSION: `X2_Field_hIAdd.lean` STILL refutes `BinIntCellResid .add` (green) — the
statement remains false as stated (slot6/frame_pop/x13_pres unprovable without
entry+the two new rungs), so no false lemma entered the tree.

FIELDS FOUND: 0 new (census 6/58, honest). The 17 fields CANNOT relight from the
mem_ext drop alone: even with the designed B2 `EvalEntry`-hypothesis carry added,
`BinArmExtras.frame_pop` (frame-window presence) and `x13_pres` (x13 liveness) are not
entry/EvalGround-derivable. These are the TWO genuine rungs blocking the whole int/eq
cone. Per Law 4 + brief ("genuine NEW rung = machine-check + land + STOP; do not
improvise a 5th cure"), STOPPING here with the analysis rather than fabricating an
entry field or a widening in this bounded pass.

---
## Wave 48g — LANDING the three cures (entry-carry + frame-ground + x13 widening)

Reading complete. HEAD d7a5c91 (census 6/58). BinArmBridge compiles axiom-clean.
Confirmed architecture:
- `BinIntCellResid`/`BinEqCellResid` (BinDispatchRow.lean:719/749) pack a whole
  `BinArmExtras` under ∀-m0 with NO entry ⇒ X2-refuted (slot6 at m0=∅). Skeleton
  holes SkelHIAdd..SkelHNe (AssemblySkeleton.lean:81-122) mirror these + TermAssembly
  fields hIAdd..hNe (lines 111-147).
- `BinArmExtras` (BinArmBridge.lean:65) still carries `slot6`/`frame_pop`/`x13_pres`
  + geometry. mem_ext ALREADY dropped (48f). frame_pop = dead-byte presence on
  [sp-1120,sp); x13_pres = a3 liveness closure over c1.
- `blockA_k` (EvalIntSim2.lean:273) threads x8/x9/x18/x11 through σ1..σ19 but NOT x13.
- `EvalGround` (InterpEntry.lean:384) has table/ast/arena/sret but NO frame-window presence.

### PLAN (3 cures, dependency order)
- CURE 3 (x13): add `x13_defined` field to EvalEntry; thread hx13_1..19 in blockA_k;
  emit `∃w, c'.x13=some w` as blockA_k 3rd output; discharge BinArmExtras.x13_pres in
  blockA_binaryArm from it (DROP the x13_pres closure field).
- CURE 2 (frame-ground): add `frame_present` field to EvalGround (m0 populated on the
  dead-byte footprint [sret_sub+4,+8)∪[+16,+24)); discharge BinArmExtras.frame_pop
  from it in blockA_binaryArm (DROP frame_pop closure).
- CURE 1 (entry-carry): make BinArmExtras derivable from EvalEntry — after cures 2/3
  drop the two closures, the remaining slot6/sproom/geometry are ALL EvalEntry fields.
  Add `entry`-carry to BinIntCellResid/BinEqCellResid + restate 6 unary resids ∃-structured.
- Then: regen skeleton, cone regen, inversion (refutations must FAIL), relight 17, census.

### DEEP CONE MAP (machine-grounded, before any edit) — the three cures are ONE interlocked wave, not three bounded gates

Traced every consumer/producer of the three fields. Findings:

1. **x13 is LOAD-BEARING, not droppable.** `blockB_binary` (EvalBinSim.lean:363→424)
   reads x13 at arm entry as `aEnvReg` and STORES it via `sd a3,0(sp)` →
   `mcall1 := writeMap8 ma (sp-1088) (sdData_val aEnvReg)` — the env arg spilled for
   the RIGHT sub-call. So `x13_pres` cannot be dropped; the machine genuinely reads a3.
   Its honest cure = blockA_k emits `∃w, c'.x13=some w`. blockA_k threads x8/x9/x18/x11
   through σ1..σ19 (EvalIntSim2.lean:940-976) but NOT x13; adding it changes blockA_k's
   OUTPUT ∃-tower → all binary consumers re-thread. blockA_k has 18 callers.

2. **frame_pop honest cure (EvalGround.frame_present) is NOT known-TRUE at top level.**
   The dead bytes `[sp-944+4,+8)∪[sp-944+16,+24)` ⊆ scribble window `[SL.lo,sp)`.
   Whether the pinned entry `m0` is TOTAL on `[SL.lo,sp)` is a top-level M6-image fact
   NOT currently supplied (EntryGround/EntryGroundKit carry table/ast/arena/sret, not
   stack-window totality). Adding the field without the M6 supplier = a new unverified
   premise (would risk a new falsity — the exact thing the census guards). EvalGround
   appears in ~40 files; every construction site + survive_stack/transport_offstack/
   child_* transport must carry the new field.

3. **BinArmExtras is DUPLICATED as EvalArmHeadExtras** (ArmDispatchCombinator.lean:108,
   its own x13_pres closure @216) with its own combinator consuming the ∃-tower. Both
   must change. Plus 11 binRow_* + 10 eval*Sim (~700 lines each, positional ∃-tower
   destructures) + TermRouting + ArmDispatchInstancesEval.

**VERDICT (Law 4, matches 48e/48f):** the three cures interlock into ONE
ITEM-ZERO-scale wave spanning ~30 files (blockA_k output-tower + 18 callers;
EvalGround field + ~40 transport/construction sites incl. an UNVERIFIED top-level
totality supplier; the doubled BinArmExtras/EvalArmHeadExtras cone; skeleton regen +
17 fields). It cannot be landed green in one bounded lean-process pass without a
broken-tree window, and cure 2's ground field is not currently known-true. Landing any
one cure alone relights 0 fields (all 3 are jointly required per the load-bearing x13
+ the frame presence + the entry-carry). Per Law 4 I return the machine-checked
obstruction rather than a broken half-landing or an unverified ground field.

### LANDED (48g) + VERDICT

LANDED (green, axioms ⊆ {propext,Classical.choice,Quot.sound}):
- `experiments/fleet/obstructions/BinCuresInterlock48g.lean` — `field_hIAdd_still_refuted`:
  the int/eq cell is STILL false as stated (BinIntCellResid packs BinArmExtras.slot6, a
  static jump-table pin refutable at m0=∅). Confirms cure 1 alone is inert and NO false
  lemma entered the tree. Axiom-clean.
- observations.md: `bin-cures-interlock-atomic-wave` entry (the atomic-wave verdict + the
  ordered ≥2-3-session landing recipe, incl. the frame_pop-via-SubEvalReturn re-route that
  avoids an unverified m0-totality ground field).

VERDICT (Law 4): the three cures INTERLOCK into one atomic ~30-file wave (x13 load-bearing →
blockA_k output-tower change → 18 callers + doubled EvalArmHeadExtras; frame_pop's honest
source is the sub-call buffer write, NOT an entry m0-totality field which would be unverified;
cure 1's def change forces skeleton+dispatcher+11 rows+10 sims regen). Landing any ONE relights
0 fields. Cannot be landed green in one bounded lean-process pass without a broken-tree window,
and the 48f-proposed ground field is not known-true. Returned the machine-checked obstruction
instead of a broken/unsound half-landing. FIELDS FOUND: 0 new (census unchanged, honest).
NO Vsa/ file modified this pass.

---
## Wave 48h — interlock SESSION 1 (CURE A: x13 output rung)

Executing observations.md `bin-cures-interlock-atomic-wave` proposal step (A):
`EvalEntry.x13_defined` field + thread x13 σ1..σ19 in blockA_k + emit as blockA_k
3rd output + update all callers' output-tower destructure + the doubled
`EvalArmHeadExtras` re-thread. Green only at end of session. Log per step.

### Step 0 — grounding the actual tree state
