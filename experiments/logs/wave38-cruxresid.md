# Wave 38 — CallClosure residual spans + the exec-motive stack-window clause

Status log, incremental. Task: (1) the motive-family stack-window clause
(statement surgery, ledger `body-ih-no-caller-frame-slots`), (2) the
CallClosureSplice named-residual spans, (3) keep
`eval_callClosure_row_fills_hCallClosure` green.

## Item 1 — consumer-surface analysis (BEFORE any edit)

### The gap, re-grounded in the disasm

The closure-body `mExecSeq` span (`callBodyLoopPC 0x80003354 → callBodyRetPC
0x80003378`, one iteration per statement) at machine sp = the eval frame's sp
(`sp_ev`; eval frame = `[sp_ev, sp_ev + 1088)`, positive offsets):

```
80003354  ld a5,8(a6)          ; stmts array
80003358  slli a4,s0,3
8000335c  addi a3,sp,144       ; ← the RESULT BUFFER ptr (sp_ev+144..167) passed to exec_stmt
80003360  add a5,a5,a4
80003364  ld a1,0(a5)
80003368  mv a2,s3
8000336c  mv a0,s2
80003370  sd a6,0(sp)          ; ← the span ITSELF writes sp_ev+0..7 (a6 spill, per iteration)
80003374  jal exec_stmt        ; callee frame at sp_ev-176 and below
80003378  beqz a0 → 80003340   ; back-edge reloads 0(sp); loop exit 80003350 bge → 80003954
```

So the span's stack writes ABOVE its entry sp are exactly
`[sp_ev, sp_ev+8) ∪ [sp_ev+144, sp_ev+168)` (a6 spill + result buffer; every
callee frame is strictly BELOW `sp_ev`).  The `ret`-route discharger needs the
caller spill slots `s7@1016 / s6@1024 / s5@1032 / s3@1048` (each 8 bytes,
window `[sp_ev+1016, sp_ev+1056)`) and the `.ret` copy source `144..167`
(that one is the body's OUTPUT channel — the status/result-ABI gap,
`seqfor-motive-rows` class, NOT this clause's job).  `SegExit.memFrame`
excuses all of `[SL.lo, SL.hi)` — no survival derivable.  Precedent shape:
`EvalExit.memFrame` ALREADY frames only `[SL.lo, sp)` + the sret carve-out
(eval_expr is a WHOLE callee: its frame sits below the ABI sp).  A mid-function
segment cannot use the bare `[SL.lo, sp)` window: it scribbles `0(sp)` and the
result buffer AT/ABOVE its sp.  So the window must be `[SL.lo, sp + k)` with a
per-segment scratch bound `k`.

### Why `k` cannot be a global or per-motive constant

- Global: the `mCall` producer (`callClosureSim`, LANDED wave 37) scribbles the
  eval frame up to `sp_ev+1055` (s3 spill @1048) and does not restore ⇒ needs
  `k ≥ 1056`; the body-IH consumer needs `k ≤ 1016`.  One constant breaks one
  side.  □
- Per-motive (`mExecSeq`): the closure-body loop needs `k ≥ 168`; the future
  block-seq consumer (exec frame is 176 bytes, spills `s3@136..ra@168`) needs
  `k ≤ 136` for ITS loop.  One `mExecSeq` constant breaks one seq site.  □

⇒ `k` must be keyed per SEGMENT.  The only segment identity `SegExit` carries
is `exitPC` — hence a PC-indexed table.  This also keeps the amendment
signature-free: the sp anchor is the ghost frame (`AbiPreservedNoise x2 = true`
⇒ `SegEntry.frame`/`SegExit.frame` pin machine sp `= g x2` at entry AND exit),
so NO new parameter on `SegEntry`/`SegExit`/any motive.

### The amendment (design)

`InductionScaffold.lean`:

```
def stackScratchTop : Nat → Option Nat
  | 0x80003378 => some 168   -- callBodyRetPC (closure-body ExecSeq loop)
  | _ => none
```

New NAMED FIELD on `SegExit` (memFrame-shaped, guard-implication style; the
existing `memFrame` is UNTOUCHED so its consumers are unaffected):

```
stackWin : ∀ k : Nat, stackScratchTop exitPC = some k →
  ∀ spv : BitVec 64, g Register.x2 = some spv →
  ∀ a : Nat, spv.toNat + k ≤ a → a < SL.hi → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?
```

Semantics: a span landing at a TABLED exit PC scribbles the stack only strictly
below `entry-sp + k`; stack bytes at/above `sp + k` survive to the span's `m0`.
Untabled exit PCs: vacuous (`none`) — exactly the old `SegExit`.  This is the
caller-window-survival clause: the scribble window is `[SL.lo, sp + k)`, stated
the way `memFrame` states its frame.  (The task text's "[SL.lo, sp)" interval is
the whole-callee EvalExit shape; for mid-function segments the honest window
needs the `+k` scratch bound — disasm above is the evidence.)

### Consumer surface (verified by grep before editing)

- Motives (`TermSimAssembly.mEvalArgs/mCall/mForLoop/mExecSeq`): signatures
  UNCHANGED (field addition only).  Scaffold-motive precedent re-verified: all
  recursor consumers (`TermCaseBundle`, `TermSimClose`, `ExecDispatchRows`,
  rows) reference the motives fully applied — no p/q/field surface.
- `SegExit` CONSUMERS (project `.memFrame`/`.store`/…): unaffected — no
  positional destructuring found; new field is additive.
- `SegExit` PRODUCERS (must supply `stackWin`) — the full list by grep
  (`memFrame :=` + structure literals):
  1. `LoopScaffoldClose.segIdentity` — zero-step, `mem = m0` ⇒ trivial.
  2. `CallEntry.evalArgsNil` — zero-step ⇒ trivial.
  3. `EvalArgs.segExit_extend` — rebase adapter mNow→m0: needs a matching
     `hmidWin` hypothesis (window-scoped mNow→m0 frame); caller sites at
     untabled concrete exit PCs discharge it vacuously.
  4. `EvalArgs.evalArgsLoop` (+ any other `segExit_extend` callers) — thread.
  5. `EvalCallNative2`/`EvalCallNative3` — concrete `callJoinPC` (untabled) ⇒
     vacuous field.
  6. Rows (`CallRows`/`CallResidProviders`/`SeqForRows`) construct NO SegExit
     (0 `memFrame :=` hits) — they plumb residual-supplied SegExits through ⇒
     obligations shift INTO the named residual types automatically (statement
     of conditional rows unchanged in shape).
  7. `EvalCallClosure.lean` — STALE, not imported by `Vsa.lean` (grepped);
     excluded from the cone re-verify, noted for the coordinator.
- Import cone of `InductionScaffold`: 118 modules (topo order computed).
  Sibling-owned files in the cone (`ArmStagesWave34`, `StagePre*`,
  `AllocBuild*`, `FnArm*`, `AssignArmStagePre`, `CallArmStagePre`,
  `BlockA*ArmGen`) construct no SegExit; they will be compiled read-only at the
  end (no olean overwrite) to avoid racing the siblings.

### Law-4 checkpoints

If `callClosureSim`/any landed producer cannot supply the field at its exit PC,
that is a table-entry decision (leave untabled ⇒ vacuous), NOT a weakening —
so no Law-4 stop is expected; will re-check per compile error.

## Item 1 — LANDED (cone ALL_GREEN)

- `InductionScaffold.lean`: `stackScratchTop : Nat → Option Nat` table
  (`0x80003378 ↦ some 168`, else `none`) + the new NAMED field
  `SegExit.stackWin` (guard-implication, sp anchored at `g x2`, scoped to
  `[spv+k, SL.hi)` outside the arena).  NO signature change anywhere; all four
  Seg motives inherit it with zero re-statement.
- Producer fixes (the ONLY breakages, as predicted by the analysis):
  `CallEntry.evalArgsNil` (+trivial from `hc.mem`),
  `LoopScaffoldClose.segIdentity` (same), `EvalArgs.segExit_extend`
  (+`hwin : stackScratchTop exitPC = none` hypothesis, field vacuous;
  rebase through an outside-stack-only `hmid` cannot carry a tabled window),
  `EvalArgs.evalArgsLoop`/`evalArgsCons` (+`hqWin` threaded),
  `rows/CallRows.eval_argsCons_row` (`(by decide)` at `evalArgsContPC`).
- Serial cone re-verify: 105/105 modules green with regenerated oleans
  (`/tmp/w38_done.txt`), incl. TermSimAssembly / TermCaseBundle / TermSimClose
  / CallClosureRow / CallClosureSplice / EvalCallNative2+3 / SeqForRows /
  CallResidProviders (the last four passed UNMODIFIED — they plumb SegExit
  through residual premises, obligations shifted into the residual types).
  Excluded: 11 sibling-owned modules (compile read-only at the end; none
  constructs SegExit) + stale unimported `EvalCallClosure.lean`.
- The slot `eval_callClosure_row_fills_hCallClosure` re-verified green in-cone.

## Item 2(e) groundwork — a SECOND statement gap found (ledger appended)

`segentry-no-caller-spill-image`: the ret routes restore `s7` from `1016(sp)`,
spilled BEFORE `callDispatchPC` (at `0x800031cc`) — `m0`-content vs `g x23` is
underivable inside the row (∀ m0).  Named premise this wave; entry-side table
proposal (the dual of `stackScratchTop`) logged in the ledger.  `s5/s3` slots
are in-span spills — carried through `BodyHandoff` below.

## Item 2 — the residual spans (all landed green + axiom-clean)

- **(e) ret routes / the amended motive** — `rows/CallClosureRow.lean`:
  `BodyHandoff` gains a `g` parameter + two NEW named structures threaded
  through it and `ret` (and `callClosureSim`'s Mid2): `BodyGhostTie g g'`
  (sp/s1/s2 agreement across the handoff) and `CallerSpillSlots g spv mB m0`
  (byte-level `s5@1032`/`s3@1048` images + the `s7@1016` m0-carry).
  `rows/CallClosureSplice.lean`: `CallRetShape` mirrors the new `ret` shape;
  **`callerSlotsSurviveBody`** = the stackWin clause FIRING at the tabled
  `callBodyRetPC` (`hexit.stackWin 168 (by decide) …`) — the restore window
  `[sp+1016, sp+1056)` survives the body IH to `mB`.  Ret-route residuals now:
  the status→a0 ABI gap (`seqfor-motive-rows`) + the s7 g-image
  (`segentry-no-caller-spill-image`, NEW ledger entry) + the
  0x80003954/.classification span decodes.
- **(a) dispatch/head span** — NEW `rows/CallClosureDispatchStage.lean`:
  `callClosureDispatchStageSeg` = ONE `#derive_case` chain
  `0x80003254 → 0x800032b8 ▷ jal env_new` (5 blocks, 4 NOT-taken guards
  in-model; subsumes the Gen env_new tail) + `callClosureDispatchStageBridge`
  via `bridgeOfSegFramed` at `AbiExceptS7S5` (reseats exposed in the post
  bundle).  GOTCHA logged: the spilled caller `s5`/`s3` VALUES must be entry
  pins (ChainOK domain needs store sources) — which is exactly the
  `CallerSpillSlots` data.  `lds` parametric (NEW ledger
  `genseg-jal-rows-zero-pin-loads`: Gen jal rows hardcode `lds = []`,
  zero-pinning loads — `callClosureEnvNewCallBridge` is undischargeable as
  emitted).
- **(b) φf'-binding env_new marshalling** — NEW
  `rows/CallClosureEnvNewMarshal.lean`: `allocFrame_inv` (a_4 inversion),
  `pushFrameMap`/`_extends`/`_fresh` (the canonical ∃-bound `φf'`), and
  **`storeRepr_allocFrame`** — the frame-side sibling of
  `storeRepr_pushClosure`, field-for-field.
- **(c) per-param staging** — VERDICT: NOT the 3-step gen_stagepre class; it is
  a 13-instr value-copy + cursor-bump span that WRITES callee-saved `s0`
  (`addi s0,s0,24`).  NEW `rows/CallClosureFoldStage.lean`:
  `callClosureFoldStageSeg` (`0x800032dc → 0x8000330c ▷ jal env_define`,
  subsumes the Gen tail) + `callClosureFoldStageBridge` via `bridgeOfSegFramed`
  at `AbiExceptS0`.  ONE bridge serves EVERY `k` (loop state all in pins);
  the back-edge `0x80003314..0x8000331c` stays inside the named seam family.
- **(d) handoff bridges** — NEW `rows/CallClosureEnvNewRet.lean`
  (`0x800032c0..0x800032d8`, blez two-polarity: `…BypassRow` → `0x80003324`,
  `…FoldRow` → `callParamFoldPC`) + NEW `rows/CallClosureBodyEntry.lean`
  (`0x8000332c..0x8000333c`, bgtz two-polarity: `…BodyEntryRow` →
  `callBodyLoopPC`, `…BodyBypassRow` ▷ `j 0x80003954` for `emptyBypass`) —
  all `segToTriple` rows, guards in `ChainFacts`.

## Final verification state

- Full InductionScaffold cone: 105 modules olean-regen green (serial) + 11
  sibling-owned modules compiled READ-ONLY green + the 6 wave-38 new/amended
  row files green.  Slot `eval_callClosure_row_fills_hCallClosure` green after
  every landing.  Discipline gate OK on all touched files.  Axioms of every
  new/amended theorem ⊆ {propext, Classical.choice, Quot.sound}.
- Transient note: two spurious "object file does not exist" errors on first
  compile attempts (Interop with the sibling agents' lake processes touching
  oleans); both resolved on immediate retry, content unaffected.

## Wiring lines (coordinator; NOT applied)

Vsa.lean (after `import Vsa.Sim.rows.CallClosureSplice`):
  import Vsa.Sim.rows.CallClosureEnvNewMarshal
  import Vsa.Sim.rows.CallClosureDispatchStage
  import Vsa.Sim.rows.CallClosureFoldStage
  import Vsa.Sim.rows.CallClosureEnvNewRet
  import Vsa.Sim.rows.CallClosureBodyEntry
check_all axiom list additions:
  Vsa.Sim.Scaffold.stackScratchTop        # (def; no axiom line needed — listed for the record)
  Vsa.Sim.callerSlotsSurviveBody          # rows/CallClosureSplice (stackWin firing at callBodyRetPC)
  Vsa.Sim.storeRepr_allocFrame            # rows/CallClosureEnvNewMarshal
  Vsa.Sim.allocFrame_inv                  # rows/CallClosureEnvNewMarshal
  Vsa.Sim.pushFrameMap_extends            # rows/CallClosureEnvNewMarshal
  Vsa.Sim.callClosureDispatchStageBridge  # rows/CallClosureDispatchStage (bridgeOfSegFramed @ AbiExceptS7S5)
  Vsa.Sim.callClosureFoldStageBridge      # rows/CallClosureFoldStage (bridgeOfSegFramed @ AbiExceptS0)
  Vsa.Sim.callClosureEnvNewRetBypassRow   # rows/CallClosureEnvNewRet
  Vsa.Sim.callClosureEnvNewRetFoldRow     # rows/CallClosureEnvNewRet
  Vsa.Sim.callClosureBodyEntryRow         # rows/CallClosureBodyEntry
  Vsa.Sim.callClosureBodyBypassRow        # rows/CallClosureBodyEntry

## Crux end-state (what remains for eval_callClosure_row to be premise-free)

The row + slot are green; `CallClosureResid` = the 3-field `CallClosureGeom`,
assembled by `callClosureGeom_of` from:
1. `entryBase` ← `callClosureEntrySplice`, whose named premises are now
   machine-backed as: `hDispatchStage` = `callClosureDispatchStageBridge` ≫
   env_new_pre MARSHALLING (StoreRepr → `Env_newLoaded`/`AInv`/`φf cd.env`
   side conditions — still open) ; `hEnvNewToFold` =
   `callClosureEnvNewRetFoldRow` + `storeRepr_allocFrame`/`pushFrameMap`
   (+ FrameRepr φ-transport at the caller — still open) ; `hFoldSeam` =
   `callClosureFoldStageBridge` ≫ `envDefContract` ≫ the back-edge
   (`0x80003314..1c`, open) via `callParamFoldSeam_of` ; `hFoldToHandoff` =
   Gen value_null bridge ≫ `callClosureBodyEntryRow` (+ the ghost-tie/slot
   marshalling into `BodyHandoff`) ; `hNoParams` =
   `callClosureEnvNewRetBypassRow` ≫ the same tail.
2. `ret` ← `callClosureRet_of_status` + `callerSlotsSurviveBody`; open:
   the classification span `0x8000337c..0x80003398`, the `.normal` span
   `0x80003954..0x80003974`, the status→a0 ABI gap (motive-family, seqfor
   class), the s7 g-image (`segentry-no-caller-spill-image` — needs the
   entry-side table, the proposed dual of `stackScratchTop`).
3. `emptyBypass` ← shared entry splice + `callClosureBodyBypassRow` + the
   `.normal` span.
Plus, one level down: the eventual `mExecSeq` seq rows must now SUPPLY
`stackWin` at `callBodyRetPC` (k=168) — honest per the disasm (scribbles =
`0(sp)` + the result buffer only).
