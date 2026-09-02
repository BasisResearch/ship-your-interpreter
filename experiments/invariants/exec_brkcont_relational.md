# exec brk/cont arm — relational-mined entry bridge (stage-4 pilot)

Design-time only. NOTHING here enters a proof. See invariant-gen-plan.md.

## Case

`hSBrk` / `hSCont` — the register-only exec-statement arms (corpus cluster
`loop-arm`/`leaf-slot`, single dispatch seam). Machine arm PCs
`execArmBrk = 0x80004098`, `execArmCont = 0x800040b8`; dispatch at `0x80004014`.

## Evidence

- **Machine side** (`scripts/gen_trace.py`, probe @ dispatch `0x80004014`
  dumping `s0`=aStmt + the 4-byte kind word at `[s0]`, plus the two arm-entry
  PCs): 636 dispatch events on `while.wl`. Kind tag = low byte of `read32[s0]`.
  brk tag 7 fired **1×** (routed to `0x80004098` arm-entry once); cont tag 8
  fired **50×** (routed to `0x800040b8` arm-entry 50×). `/tmp/rl-trace/brkcont_trace.jsonl`.
- **Spec side** (`experiments/spec_trace_brkcont.lean`, `#eval` of the WHILE
  spec restricted to the brk/cont loop, emitting the REAL `kindOfStmt s` per
  exec-step): brk(7) count = **1**, cont(8) count = **50**; if(3) = **201**
  — matching the machine dispatch counts exactly on every discriminating tag.
- **Relational mining** (`scripts/mine_relational.py`) pairs the two by tag:

```
kind | name  | machine | spec | arm-entry
  3  | if    |   201   | 201  |
  7  | brk   |     1   |   1  |   1
  8  | cont  |    50   |  50  |  50
```

## Mined candidate conjuncts (the bridge)

```lean
-- machine slot word ↔ spec statement kind (the StmtRepr bridge)
read32 m aStmt = some (kindOfStmt s)          -- brk: = 7, cont: = 8
-- jump-table slot routes tag → arm PC (the StmtSlotPinned bridge)
StmtSlotPinned 7 execArmBrk  m                 -- brk
StmtSlotPinned 8 execArmCont m                 -- cont
```

## Match against the LANDED shape — VERDICT: MATCH

The two mined conjuncts are, field-for-field, the landed entry bridge:

- `read32 m aStmt = some (kindOfStmt s)` is **exactly** `stmtRepr_kind`
  (`Vsa/Sim/ExecDispatch.lean:84`, "the one new obligation").
- `StmtSlotPinned 7 execArmBrk m` / `StmtSlotPinned 8 execArmCont m` are
  **exactly** `StmtTablePins.slot7` / `.slot8`
  (`Vsa/Sim/ExecEntry.lean:202-203`), whose definition
  (`ExecEntry.lean:178`) is `stmtJumpTableBase + sext(slotWord) = armPC`
  (base `0x80019fb8`) — the concrete `base + slotWord = armPC` the miner
  grounded from the trace.

Mining found the TRUE bridge-fact statement shape before it was written.

## Fuzz verdict (CTI loop, `statement_fuzz.py --file --struct`)

Hermetic candidate `experiments/invariants/exec_brk_bridge.lean` (ghost
`structure BrkArmEntry` with fields `kindTag`, `armRoute` mirroring the two
conjuncts):

- correct mined instance `brkArmMined` → **SURVIVED** (inhabited / self-consistent, axiom-clean)
- mutant `brkArmMutant` (slot mis-tagged to the cont arm PC) → **REFUTED** (axiom-free witness)

## Inductiveness pre-check

Not applicable: brk/cont are non-looping register-only arms (the corpus card
notes `back-edge/loop` only from the shared epilogue, no per-iteration body).
The bridge is a straight entry fact, discharged by `stmtRepr_kind` +
`StmtTablePins` — no `loopFromBody` obligation.
