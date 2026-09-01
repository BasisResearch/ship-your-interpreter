# Wave 40 — CallClosure premise-freedom remainder + the entry-side spill-image table

Status log, incremental.  Task: (1) the entry-side spill-image table (the dual
of `stackScratchTop`, ledger `segentry-no-caller-spill-image`), (2) the
remaining crux spans (fold back-edge / classification / `.normal` /
status→a0 / env_new-pre marshalling), (3) re-probe
`eval_callClosure_row_fills_hCallClosure` + `callClosureEntrySplice`.

## Item 1 — consumer-surface analysis (BEFORE any edit)

### The gap, re-grounded

`ret` routes restore `s7` from `1016(sp)`:
`ld s7,1016(sp)` at `0x800033b0` (`.ret v` retCopy span) and `0x80003970`
(`.normal` span).  The spill `sd s7,1016(sp)` is at `0x800031cc` — BEFORE
`callDispatchPC = 0x80003254` (verified in `experiments/disasm.txt:3297`).  So
inside the `mCall` row (`∀ g … m0`) the slot content vs `g x23` is underivable:
`SegEntry` links nothing between `m0` and `g`.  Also verified from the disasm:
`s5@1032` (`0x8000328c`), `s3@1048` (`0x800032ac`), `s6@1024` (`0x800032cc`,
restored in-span at `0x80003320`) are ALL in-span spills — `s7@1016` is the
ONLY pre-span slot.  Table content: `0x80003254 ↦ (1016, x23)`.

### OBSTRUCTION to the prescribed seat (SegEntry field) — found in analysis

The prescribed design (named `SegEntry` field guarded by a per-entry-PC table,
wave-38 `stackWin` dual) requires EVERY `SegEntry` PRODUCER to supply the
field.  Producer census (grep `arena_budget :=` + structure literals + `.mk`):

1. `ArmSegSplitSeg.segEntry_of_jalPrefix` — constructs `SegEntry` at a
   ∀-QUANTIFIED `entryPC` (the jal→child marshalling; structure literal at
   `ArmSegSplitSeg.lean:95-106`).  At a generic `entryPC` the vacuity of the
   new field is NOT provable (the table lookup is stuck); the wave-38 escape
   (add a `entrySpillImage entryPC = none` hypothesis, the `segExit_extend`
   precedent) requires EDITING the theorem — but `ArmSegSplit*` is FROZEN
   (sibling-owned this wave).  The hypothesis would further ripple into
   `ArmSegSplitNonEval.SegPreBundle` (frozen) and every pre-bundle supplier in
   `ArmStagesWave34` (frozen).
2. `DriveToLoopHeadSpans.driveToLoopHead_of_spans` — concrete untabled
   `interpLoopHeadPC` (fixable, file not frozen).
3. No other structure-literal producers (`EvalArgs`/`CallEntry`/
   `LoopScaffoldClose` construct `SegExit` from a consumed `SegEntry` only).

⇒ The FIELD seat breaks a frozen file at a generic PC.  Logged to
`experiments/observations.md`
(`segentry-spillimage-field-blocked-by-frozen-generic-producer`) at the moment
of noticing (law 3b).

### The freeze-compatible seat (chosen): the same table + clause, seated as an
### `mCall`-motive hypothesis

The pin must link `m0` and `g` in the PRECONDITION of the `mCall` Triple (for
(m0,g)-inconsistent instantiations the exit `frame` clause `regs x23 = g x23`
is false after the machine restores from `m0[sp+1016..]` — the ledger's
falsity analysis).  The two possible seats are the `SegEntry` structure or the
`mCall` motive BODY.  The motive-body seat:

* `TermSimAssembly.mCall` gains ONE hypothesis
  `Scaffold.EntryImage callDispatchPC g m0 →` before the Triple.  Signature
  UNCHANGED (fully-applied `mCall … a_2` references everywhere are unaffected —
  the scaffold-motive-independent-pq precedent).
* The table (`entrySpillImage`) + the PC-indexed clause (`EntryImage`, vacuous
  at untabled PCs) still land in `InductionScaffold.lean` beside
  `stackScratchTop` — the DUAL pattern verbatim; only the seat differs.  When
  the `ArmSegSplit*` freeze lifts, hoisting the clause from motive-hypothesis
  to `SegEntry` field is a mechanical move (the clause is already stated
  against `(entryPC, g, m0)`).

### Consumer surface of the `mCall` BODY change (verified by grep)

`mCall` referenced in 40 files; classification:

* **Fully-applied premise-type references** (recursor minor premises, `TermCases`
  fields, `TermSimClose`/`TermSimAssembly` recursor applications, every
  `Eval*Row`/`EvalBinSim`-family row that takes `mCall … → …` as an ignored IH,
  `CallResidProviders` wrappers that delegate to the `CallRows` rows): body
  change INVISIBLE.  No edit.
* **Unfolding producers** (must `intro` the new hypothesis):
  - `rows/CallRows.lean`: `eval_callPrint_row` / `eval_callPrintln_row` /
    `eval_callAssertOk_row` (`show`-unfold + `intro`; hypothesis ignored — the
    native routes never touch `1016(sp)`).
  - `rows/CallClosureRow.lean`: `eval_callClosure_row` (+ slot-verify) — the
    hypothesis is USED: threaded into `callClosureSim` → `CallClosureGeom.ret`.
  - `Vsa/Sim/EvalCallClosure.lean` — STALE, not imported by `Vsa.lean`
    (re-verified by grep), excluded.
* **Unfolding consumers** (apply an `mCall` value): `eval_call_row` takes the
  `mCall` IH as ignored `_ihcall` (comment: consumed inside `CallArmSpec`,
  currently unused).  No edit.  FUTURE cost (reported, not owed now): the
  eventual `CallArmSpec` supplier that instantiates the `mCall` IH at its
  (g,m0) must supply `EntryImage` — it CAN: it owns the `0x800031cc` spill
  (`callClosureArgLoopEntrySeg`, `sd s7,1016(sp)` in its write-log).
* `CallClosureGeom.ret` / `CallRetShape` gain the same hypothesis (threaded
  like `BodyGhostTie`/`CallerSpillSlots`); `callClosureSim` passes it through.

### The clause design

```
def entrySpillImage : Nat → Option (Nat × Nat)      -- entry PC ↦ (sp-off, GPR idx)
  | 0x80003254 => some (1016, 23)                    -- callDispatchPC ↦ s7 slot
  | _ => none

def gGpr (g) : Nat → Option (BitVec 64)              -- homogeneous ghost GPR read
                                                     -- (the ghost twin of BlockPilot.gprGet)

def EntryImage (entryPC : Nat) (g) (m0 : Mem) : Prop :=
  ∀ off n, entrySpillImage entryPC = some (off, n) →
    ∀ spv, g x2 = some spv → ∀ w, gGpr g n = some w →
    ∀ i < 8, m0[spv.toNat + off + i]? = some (w.extractLsb' (8*i) 8)
```

Byte-level LE — matches `CallerSpillSlots.s5/.s3` so the ret discharger
consumes uniformly.  `entryImage_of_none` gives the vacuous case for generic
producers; `gGpr_x23 : gGpr g 23 = g Register.x23 := rfl` for the consumer.
Consumer keystone (`rows/CallClosureSplice.lean`): `s7ImageAtBody` =
`EntryImage@callDispatchPC` + `CallerSpillSlots.s7carry` ⇒ the `mB` bytes at
`[sp+1016, sp+1024)` are the arm ghost's `s7` — exactly what the `.normal`/
`.ret` restore segs read back.

## Item 2 — span survey (disasm, verified)

* (a) fold back-edge `0x80003314..1c`: `ld a5,0(sp); addi a5,a5,8;
  bne s6,a5 → 0x800032dc` — TWO polarities (taken = next fold iteration;
  not-taken falls into `0x80003320 ld s6,1024(sp)` = the fold exit, ending at
  `0x80003324`).  bne fields verified: rs1=22, rs2=15, imm13=0x1FC0.
* (b) classification `0x8000337c..0x80003398`: `lw a4,8(s2); addiw a5,a0,-1;
  li a3,1; addiw a4,a4,-1; sw a4,8(s2)` (--call_depth) ▷ `bgeu a3,a5 →
  0x80003cc8` (brk/cont error route — NOT taken under `a_6`) ;; `li a5,3` ▷
  `bne a0,a5 → 0x80003960`.  Under `a_6` + the `beqz` fall-through (`a0 ≠ 0`),
  `a0 = 3` always ⇒ bne NOT taken; the taken polarity is dead code (a0 > 3
  impossible).  ONE seg: both guards not-taken, end `0x8000339c` (the GEN
  retCopy row entry).  bgeu: rs1=13, rs2=15, imm13=0x938; bne: rs1=10, rs2=15,
  imm13=0x5C8.
* (c) `.normal` `0x80003954..74`: `lw a5,8(s2); addiw; sw` (--call_depth) ;
  `mv a0,s1` ▷ `jal value_null` (@0x80003964, link 0x80003968, callee
  0x800027ec — bridge shape, lds-parametric per the wave-39 Gen fix) THEN
  `ld s3,1048(sp); ld s5,1032(sp); ld s7,1016(sp)` ▷ `j 0x800033ec`
  (imm21=0x1FFA78) — the restore seg whose lds readback meets
  `s7ImageAtBody` + `CallerSpillSlots`.
* (d) status→a0: the body IH's `SegExit@callBodyRetPC` does not pin `a0` by
  `status` — the `beqz a0 @0x80003378` split is undecidable from the IH.  The
  `SeqForRows` class (named residual, NOT a motive change this wave): a named
  structure `BodyStatusABI` at the splice layer.
* (e) env_new_pre side conditions: `Env_newLoaded`/`AInv`/`φf cd.env` off
  `StoreRepr` — scoped below after (a)-(d).

All span decode words already have DecodeTable lemmas (checked all 21 words).

## Item 1 — LANDED (nucleus green, cone regen running)

- `InductionScaffold.lean` (ADDITIONS only, no existing statement touched):
  `entrySpillImage : Nat → Option (Nat × Nat)` (`0x80003254 ↦ (1016, 23)`),
  `gGpr` (homogeneous ghost GPR read, the ghost twin of `BlockPilot.gprGet`),
  `EntryImage` (the guard-implication clause, vacuous at untabled PCs),
  `entryImage_of_none`, `gGpr_x23`.  1.7s, axiom-clean.
- `TermSimAssembly.mCall` body: `EntryImage callDispatchPC g m0 → Triple …`
  (ONE hypothesis; signature-free).  Green.
- `rows/CallRows.lean`: the 3 native rows' `show` + `intro _hImg` (ignored).
  Green.
- `rows/CallClosureRow.lean`: `CallClosureGeom.ret` gains the `EntryImage`
  hypothesis (after the `cd.body ≠ []` guard); `callClosureSim` takes + passes
  `hImg`; `eval_callClosure_row` intros it from the unfolded motive.  Row +
  SLOT-VERIFY (`eval_callClosure_row_fills_hCallClosure`) green, axiom-clean.
- `rows/CallClosureSplice.lean`: `CallRetShape` mirrors the hypothesis;
  **`s7ImageAtBody`** = `EntryImage@callDispatchPC` + `CallerSpillSlots.s7carry`
  ⇒ the `mB` bytes at `[sp+1016, sp+1024)` are the arm ghost's `s7` — the
  ledgered `segentry-no-caller-spill-image` residual is now SUPPLIED at this
  seam (the g-image premise class is eliminated from the ret route).
- `TermCaseBundle` / `TermSimClose` / `CallResidProviders` pass UNMODIFIED
  (fully-applied motive references, as predicted).

## Item 2 — the crux spans (landed green + axiom-clean)

- **(a) fold back-edge** — NEW `rows/CallClosureFoldBack.lean`:
  `callClosureFoldBackLoopSeg/Row` (`bne` TAKEN → `callParamFoldPC`, the
  `hBack` piece of `callParamFoldSeam_of`) + `callClosureFoldBackExitSeg/Row`
  (NOT taken ;; `ld s6,1024(sp)` restore → `0x80003324`, the value_null
  staging).  Two-polarity `segToTriple` family, guards in `ChainFacts`,
  `lds`-parametric.  1.8s.
- **(b) classification** — NEW `rows/CallClosureRetClass.lean`:
  `callClosureRetClassSeg/Row` — ONE seg (not a polarity family): under `a_6`
  + the `beqz` fall-through, `a0 = 3` forces BOTH guards (`bgeu` brk/cont
  error route, `bne` dead defensive route) NOT taken; lands at the GEN
  retCopy entry `0x8000339c` with the `--call_depth` word in the log.  1.6s.
- **(c) `.normal` span** — NEW `rows/CallClosureNormalRet.lean`:
  `callClosureNormalDepthBridge` (`bridgeOfSeg`, `--call_depth` + `mv a0,s1`
  ▷ `jal value_null@0x800027ec`, link `0x80003968`, `lds`-parametric) +
  `callClosureNormalJoinSeg/Row` (`ld s3/s5/s7` restores ▷ `j callJoinPC`) —
  the restore seg whose `lds` readbacks meet `CallerSpillSlots.s3/.s5` +
  `s7ImageAtBody`.  1.9s.
- **(d) status→a0** — `BodyStatusABI` (named-field structure in
  `rows/CallClosureSplice.lean`, the `SeqForRows` class): `normal → a0 = 0`,
  `retv → a0 = 3` at the body-exit config; supplier = the eventual
  `mExecSeq`-side seq rows (the same layer owing `stackWin@callBodyRetPC`).
- **(e) env_new_pre marshalling** — `closureRepr_of_storeRepr` /
  `envNewParentLink_of_storeRepr` / `envNewParentSel_of_storeRepr`
  (`rows/CallClosureSplice.lean` §3b): the `parentSpec := some cd.env`
  selector (`φf cd.env = par.toNat ∧ par ≠ 0`) is a pure `StoreRepr`
  projection meeting the dispatch bridge's `ld a0,8(a3)` readback.  NOT
  marshallable from `SegEntry` (named with the stage): `Env_newLoaded` (no
  Loaded clause on `SegEntry`), `M.AInv`/`StackOK`/non-exhaustion
  (contract/layout facts).

Discipline gate: OK (8 rules) after all edits.

## Item 2 addendum — the body-exit split (found in the ret-route audit)

The route audit exposed one more unlanded machine piece between the body IH's
exit (`SegExit@callBodyRetPC = 0x80003378`, parked AT the `beqz`) and the two
return arms: the `beqz a0` split + (on `.normal`) the LAST loop-exit re-check
(`0x80003340..0x80003350 bge → 0x80003954`).  NEW
`rows/CallClosureBodyExit.lean`: `callClosureBodyExitRetRow` (`beqz` NOT
taken, a0=3 → the classification entry `0x8000337c`) +
`callClosureBodyExitNormalRow` (`beqz` taken ;; reload/bump/count ▷ `bge`
taken → `0x80003954`).  Green + axiom-clean, 1.8s.  Mid-loop back-edges (`bge`
NOT taken) are inside the body IH's span (the seq rows' concern).

With this, EVERY machine span of both ret routes is a landed row:
* `.ret v`:   IH ▷ `callClosureBodyExitRetRow` ▷ `callClosureRetClassRow` ▷
  `callClosureRetCopyRow` (GEN, ▷ `j callJoinPC`).
* `.normal`:  IH ▷ `callClosureBodyExitNormalRow` ▷
  `callClosureNormalDepthBridge` ≫ value_null ≫ `callClosureNormalJoinRow`
  (▷ `j callJoinPC`).

## Item 3 — the `hCallClosure` end-state (post-wave-40)

The row + slot-verify are green; `hCallClosure` is filled by
`eval_callClosure_row` conditional on ONE premise, `CallClosureResid`
(∀-closed `CallClosureGeom`).  After this wave there is NO unlanded machine
span and NO known statement-layer gap on any of the three routes — the
remainder is entirely marshalling/composition:

**Machine-row inventory (complete, `0x80003254 → callJoinPC`)**
* dispatch/head: `callClosureDispatchStageBridge` (w38) — incl. the arity/
  depth guards and the s5/s3 spills.
* env_new: `env_new_spec` (real contract, threaded in `callClosureEntrySplice`).
* return staging: `callClosureEnvNewRetBypassRow`/`FoldRow` (w38).
* per-param: `callClosureFoldStageBridge` (w38) ≫ `envDefContract` ≫
  `callClosureFoldBackLoopRow` (w40).
* fold exit: `callClosureFoldBackExitRow` (w40) ≫
  `callClosureValueNullCallBridge` (GEN) ≫ `callClosureBodyEntryRow` (w38).
* body: the recursor's `mExecSeq` IH (free).
* body exit: `callClosureBodyExitRetRow`/`NormalRow` (w40).
* `.ret v` tail: `callClosureRetClassRow` (w40) ≫ `callClosureRetCopyRow` (GEN).
* `.normal` tail: `callClosureNormalDepthBridge` (w40) ≫ value_null ≫
  `callClosureNormalJoinRow` (w40).
* empty bypass: `callClosureBodyBypassRow` (w38) ▷ the same `.normal` tail.

**Statement layer (both wave-37/38 falsity classes now SUPPLIED)**
* s5/s3: `CallerSpillSlots` (w38) + `SegExit.stackWin` firing
  (`callerSlotsSurviveBody`, w38).
* s7: `EntryImage`@`callDispatchPC` (w40, the `mCall` hypothesis) +
  `s7ImageAtBody` (w40) — `segentry-no-caller-spill-image` RESOLVED at this
  seam (seat: motive hypothesis, see the obstruction entry).

**Remaining for premise-freedom (itemized, all marshalling-class)**
1. env_new_pre side-condition assembly at the dispatch seam: `Env_newLoaded`
   (code pin — `SegEntry` carries no Loaded clause; the same class as the
   `Exec_stmtLoaded` premise on `segEntry_of_jalPrefix`), `M.AInv` +
   stability, `StackOK`/`16 ≤ sp`, ra-alignment, the non-exhaustion selector.
   The parent-link selector IS closed (`envNewParentSel_of_storeRepr`, w40).
2. Carrier re-assembly between rows: `GHolds`/writeLog posts →
   `CallParamFoldInv` / `BodyHandoff` / `SegExit@callJoinPC` (register pins
   from the reflected regs, `StoreRepr` φ-transports through
   `PhiExtends`/`storeRepr_allocFrame`/`pushFrameMap` (w38), memFrame from
   log containment, `OutRepr` carry).
3. The env_define contract splice per fold param (`envDefContract` boundary ↔
   `CallParamFoldInv`, the `foundSt_of_storeRepr`/`frameRepr_append` class).
4. The `mExecSeq`-side suppliers (the seq rows, seqfor class): `stackWin` at
   the tabled `callBodyRetPC` (k=168) + `BodyStatusABI` (w40 named structure)
   + the loop-invariant guard for the `bge` at the exit re-check.
5. The value_null contract splices (two sites: post-fold staging, `.normal`
   tail) — `value_null` spec is landed; the splice is jal-seam + post
   marshalling.
6. Per-bridge instantiation obligations (`ChainFacts` via `chain_facts`,
   `hjalSeam` site obs, keys `decide`s) at concrete pins.

Plus, one level up (NOT this row's debt): the eventual `CallArmSpec` supplier
must provide `EntryImage` when instantiating the `mCall` IH — it owns the
`0x800031cc` spill (`callClosureArgLoopEntrySeg`).

## Wiring lines (coordinator; NOT applied)

Vsa.lean (after `import Vsa.Sim.rows.CallClosureBodyEntry`):
  import Vsa.Sim.rows.CallClosureFoldBack
  import Vsa.Sim.rows.CallClosureRetClass
  import Vsa.Sim.rows.CallClosureNormalRet
  import Vsa.Sim.rows.CallClosureBodyExit
check_all axiom-list additions:
  Vsa.Sim.Scaffold.entryImage_of_none        # InductionScaffold (the vacuous case)
  Vsa.Sim.s7ImageAtBody                      # rows/CallClosureSplice (EntryImage ⋈ s7carry)
  Vsa.Sim.closureRepr_of_storeRepr           # rows/CallClosureSplice
  Vsa.Sim.envNewParentSel_of_storeRepr       # rows/CallClosureSplice
  Vsa.Sim.callClosureFoldBackLoopRow         # rows/CallClosureFoldBack
  Vsa.Sim.callClosureFoldBackExitRow         # rows/CallClosureFoldBack
  Vsa.Sim.callClosureRetClassRow             # rows/CallClosureRetClass
  Vsa.Sim.callClosureNormalDepthBridge       # rows/CallClosureNormalRet
  Vsa.Sim.callClosureNormalJoinRow           # rows/CallClosureNormalRet
  Vsa.Sim.callClosureBodyExitRetRow          # rows/CallClosureBodyExit
  Vsa.Sim.callClosureBodyExitNormalRow       # rows/CallClosureBodyExit
