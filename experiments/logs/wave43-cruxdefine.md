# Wave 43 — the env_define fold splice + carrier re-assembly (lane cruxdefine)

Inherits wave-42 cruxmarsh (bricks: `segToTripleOut`, `outRepr_transport`,
`gholds_reg`+`gprGet_*`, `foldStore_succ`, destructurers).  Task order:
(1) env_define splice per fold param (store-repr `.define`-step into
`CallParamFoldInv (k+1)` via `foldStore_succ`), (2) carrier re-assembly tail
(`CallParamFoldInv`/`BodyHandoff`/`SegExit` off the landed rows), (3) the two
value_null splices, (4) per-bridge ChainFacts where no M6 obs needed.

## Ground survey (before edits)

* `StoreDefineAdvance` (`EnvCallBridge.lean`, committed) already IS the
  whole-store define-step carrier (mutated/others/closures/inj/arena →
  `toStoreRepr`).  What is MISSING for the fold leg:
  - the `Store.define` getElem algebra (define-mutated frame at `a`, survival
    at `b ≠ a`, closures untouched) so a supplier can build
    `StoreDefineAdvance` from the contract post's `FrameRepr` — nobody
    discharges the fields yet (the demos thread it as `NativeDefinePins`);
  - `foldStore` step: `StoreDefineAdvance @ foldStore k → StoreRepr
    (foldStore (k+1))` (via `foldStore_succ`);
  - the env_define-RETURN pin bundle (`FoldDefineReturn`, at PC `0x80003314`)
    + the back-edge composition into `CallParamFoldInv (k+1)` — needs the
    back-edge row re-stated with the RICHER pin list (x2/x8/x19/x21/x22, the
    wave-40 row only pinned x2/x22 so cursor/frameReg/closReg were dropped)
    and in `segToTripleOut` form (OutRepr carry).
* `segEval_sound` DOES prove a register frame fact; unpinned-register carry is
  instead obtained here by enriching L (GHolds carries unwritten pins through).

## Landings

### Item 1 — env_define fold splice: LANDED (`rows/CallCruxMarshal2.lean`,
### green + axiom-clean 1.65s, gate OK)

* §1 `defineFrame` + `define_frames_getElem_self/_ne` + `define_frames_size` +
  `define_closures_eq` — the `Store.define` getElem algebra (the bridge from
  PRE-store-indexed readbacks to `StoreDefineAdvance`'s POST-store-indexed
  fields; `Array.getElem_modify` both polarities).
* §2 `storeDefineAdvance_of` — the named assembler: contract-post `FrameRepr`
  at `defineFrame` + others/closures survival + ANY pre `StoreRepr` (inj/arena
  fields are memory-independent) → `StoreDefineAdvance`.
  `foldStoreAdvance_toStoreRepr` — `StoreDefineAdvance @ foldStore k` →
  `StoreRepr (foldStore (k+1))` via `foldStore_succ` (w42 brick).
* §3 `callClosureFoldBackL5` (the RICHER 5-pin list x2/x8/x19/x21/x22 — the
  wave-40 two-pin row dropped cursor/frameReg/closReg) + `mul8_ofNat_succ` /
  `mul24_ofNat_succ` (index/cursor bump arithmetic) + **`FoldDefineReturn`**
  (named-field pin bundle at the env_define RETURN config `0x80003314`;
  `spill` binds the ld-bytes + back-edge `ChainFacts` in ONE ∃ pair — the
  `structure : Prop` data-field gotcha).
* §4 **`foldDefineReturn_step`** — `Triple (FoldDefineReturn … k)
  (callParamFoldCarrier … (k+1))`: the back-edge run via `segToTripleOut`
  (OutRepr carry), pins off exit `GHolds` by `gholds_reg`+`gprGet_*` rfl,
  bumped index via readback peel + `mul8_ofNat_succ`, store field via
  `foldStoreAdvance_toStoreRepr`, memory-pure log (`rw [hmem']; rfl` idiom).
* §5 **`callParamFoldSeamStep`** — `callParamFoldSeam_of` instantiated: the
  per-param leg closes to `(hStage, hDefine, hPins)` — staging bridge,
  env_define contract, return-pin readback.  `hBack` is DISCHARGED.

### THE 8TH STATEMENT FALSITY — found in item-2 analysis, amended within-wave

Ledger `callparamfold-carrier-n-unreachable` (observations.md).  The
params-fold is a DO-WHILE (disasm 3358-3384): the head PC `0x800032dc`
(`callParamFoldCarrier`'s pin) is entered exactly `n` times (k = 0..n-1);
after the LAST `env_define` the `bne s6,a5 @0x8000331c` compares `8·n` with
`8·n` and FALLS THROUGH — `carrier n` is NEVER reached.  So the wave-37
`callClosureEntrySplice` premises `hFoldSeam` (at k = n-1) and
`hFoldToHandoff` (sourced at `carrier n`) were machine-undischargeable.

* **Obstruction** (`rows/CallCruxMarshal3.lean`, green + axiom-clean 1.1s):
  `foldBackLoop_facts_last_false` / `foldBackLoop5_facts_last_false` — the
  loop-polarity row's `ChainFacts` is UNINHABITED at the last param (bne-TAKEN
  guard reduces to `8·(k+1) != 8·(k+1) = true`; `mul8_ofNat_succ`);
  `foldDefineReturn_last_false` — the §3 pin bundle is uninhabited at
  `k+1 = n`, so `callParamFoldSeamStep` covers exactly the amended range.
* **Amendment** (`rows/CallClosureSplice.lean`, green + axiom-clean 1.9s):
  `hFoldSeam` re-ranged to `k + 1 < n`; `hFoldToHandoff` re-sourced at
  `carrier (n-1)`; proof = `storeChainList` at `n-1` + one `omega`.  NO
  downstream consumers existed (grep: comments only).  Oleans regenerated
  (`lake env lean -o`).

### Items 2+3 — the value_null handoff leg: LANDED
### (`rows/CallCruxMarshal4.lean`, green + axiom-clean ~2s, gate OK w/ one
### justified allow(R7))

* §1 **`JalStepO`** + **`bridgeOfSegOut`** — the sailOutput-carrying twins of
  the FROZEN `BridgeSeg.JalStep`/`bridgeOfSeg` (found: BOTH drop sailOutput —
  the same `rowpost-drops-sailoutput-blocks-outrepr` class; `OutRepr` could
  not cross ANY jal bridge).  Built on `segEval_sound` directly, freeze-safe.
  Reusable for every jal-callee splice that must carry `OutRepr` (both
  value_null sites, and the class generally).
* §2 `valueNullBodyL` (x2/x9/x18/x21 — the body-entry seg RE-STATED through
  `segToTripleOut` with the pass-throughs `BodyGhostTie` reads; wave-38 1-pin
  row untouched) + `gprGet_x9` battery entry.
* §3 **`ValueNullStage`** — named-field carrier at `0x80003324`.  Machine
  residuals as FIELDS (`FoldDefineReturn.spill` idiom, all M6/code-pin class):
  `loaded`, `stagefacts`, `jalSeam` (JalStepO-shaped), `bodyReads`
  (buffer-agreeing-memory function — AST readbacks + bgtz guard).  Survival
  fields `store_survives` (`EvalEntry` idiom, bound store stable under the
  value_null buffer write `[sp+144, sp+168)`), slot images
  `gs5@1032`/`gs3@1048`/`s7@1016`-carry.
* §4 **`valueNullHandoffSplice`** — `Triple (ValueNullStage …) (BodyHandoff g …)`:
  staging ▷ jal (bridgeOfSegOut) ≫ REAL `value_null_spec_full` (EvalNullSim —
  the framed variant with output + memFrame; base `null_post` is too narrow)
  ≫ body-entry seg (segToTripleOut, bgtz TAKEN) → the FULL `BodyHandoff`
  (`g' :=` reached regs so `SegEntry.frame` is `rfl`; `BodyGhostTie`/
  `CallerSpillSlots` via the g-link premises; store via `store_survives`;
  `OutRepr` via the three-leg sailOutput thread).  GOTCHA: `subst` on
  `spv = sp` unmasked the GLOBAL `sp : regidx` — use `rw` instead.
* §5 **`FoldDefineExitReturn`** — the LAST-iteration env_define return bundle
  (`0x80003314`, exit-polarity seg `callClosureFoldBackExitSeg`, 5-pin
  `foldExitL`, payload fields transported verbatim).
* §6 **`foldDefineExitReturn_step`** — exit back-edge run → `ValueNullStage`
  (memory-pure transport, pins via GHolds pass-throughs).
* §7 **`foldToHandoff_of`** — the AMENDED `hFoldToHandoff` composed:
  `(hStage, hDefine, hPins)` ≫ §6 ≫ §4 = `Triple (carrier k) (BodyHandoff …)`.

### What hCallClosure's fold route now reduces to

`callClosureEntrySplice` (amended) needs: `hDispatchStage`, `hEnvNewToFold`,
`hFoldSeam` (per `k+1 < n`: `callParamFoldSeamStep` ⇒ `(hStage, hDefine,
hPins@FoldDefineReturn)`), `hFoldToHandoff` (`foldToHandoff_of` ⇒ `(hStage,
hDefine, hPins@FoldDefineExitReturn)` + g-links/layout premises), `hNoParams`.
The `(hStage, hDefine, hPins)` suppliers = `callClosureFoldStageBridge` (w38)
+ `envDefContract` (EnvDefCompose) + the pin-readback marshalling (the
env_define post → return-bundle fields; `storeDefineAdvance_of` closes the
store field; the rest is ABI/slot-footprint threading of the contract).

### NOT landed (named residuals)

* The `.normal`-route value_null splice → `SegExit@callJoinPC` (item 3 #2):
  needs the full ret-route register-frame re-establishment (s3/s5/s7 restores
  ⋈ `CallerSpillSlots`/`s7ImageAtBody` + the untouched-callee-saved threading
  incl. the x8 question at the join) — the `CallClosureGeom.ret` leg, next
  wave.  `bridgeOfSegOut` + the landed `callClosureNormalJoinRow` (re-stated
  via `segToTripleOut`) are the intended bricks.
* Item 5 per-bridge ChainFacts/hjalSeam at concrete pins: ALL are
  M6/code-pin class (`ProgFactsM` demands `BytePinsM` code-byte pins;
  `hjalSeam` demands the region `site_*` jal obs — now in `JalStepO` form for
  output-threading sites).  None dischargeable in this lane; named on the
  carriers.
* `hEnvNewToFold` / `hDispatchStage` / `hNoParams` (unchanged wave-40 scope).

## Wiring lines (coordinator; NOT applied — Vsa.lean/check_all not owned)

Vsa.lean (after `import Vsa.Sim.rows.CallCruxMarshal`):
  import Vsa.Sim.rows.CallCruxMarshal2
  import Vsa.Sim.rows.CallCruxMarshal3
  import Vsa.Sim.rows.CallCruxMarshal4
check_all axiom-list additions:
  Vsa.Sim.storeDefineAdvance_of          # rows/CallCruxMarshal2
  Vsa.Sim.foldStoreAdvance_toStoreRepr   # rows/CallCruxMarshal2
  Vsa.Sim.foldDefineReturn_step          # rows/CallCruxMarshal2
  Vsa.Sim.callParamFoldSeamStep          # rows/CallCruxMarshal2
  Vsa.Sim.foldBackLoop_facts_last_false  # rows/CallCruxMarshal3 (obstruction)
  Vsa.Sim.foldDefineReturn_last_false    # rows/CallCruxMarshal3 (obstruction)
  Vsa.Sim.bridgeOfSegOut                 # rows/CallCruxMarshal4
  Vsa.Sim.valueNullHandoffSplice         # rows/CallCruxMarshal4
  Vsa.Sim.foldDefineExitReturn_step      # rows/CallCruxMarshal4
  Vsa.Sim.foldToHandoff_of               # rows/CallCruxMarshal4
(re-list `Vsa.Sim.callClosureEntrySplice` — statement AMENDED this wave.)
