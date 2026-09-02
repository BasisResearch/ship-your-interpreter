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
