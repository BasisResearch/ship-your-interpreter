# Wave 42 — the hCallClosure crux marshalling residue (lane cruxmarsh)

Task: plan queue item 4 — glue the landed wave-40 crux span rows into one chain.
All marshalling-class. Work order: (1) carrier re-assembly, (2) env_define
splice, (3) seq-row suppliers, (4) 2 value_null splices, (5) per-bridge
ChainFacts/hjalSeam.

## The central obstruction (found in item-1 analysis, machine-checked)

Ledger `rowpost-drops-sailoutput-blocks-outrepr` (observations.md).

The wave-40 crux span rows (`callClosureFoldBack{Loop,Exit}Row`,
`callClosureRetClassRow`, `callClosureNormalJoinRow`,
`callClosureBodyExit{Ret,Normal}Row`) each land a `Post` of shape
`GoodState ∧ mem = writeLog m0 log ∧ PC = q ∧ GHolds …`.  To marshal any of them
into the NAMED carriers the next stage consumes (`CallParamFoldInv`,
`BodyHandoff`, `SegExit`) the re-assembly must re-establish `OutRepr`
(console-output correspondence).  `OutRepr σ st = (Machine.output σ = st.out)`
depends ONLY on `σ.sailOutput`; a memory-only span (every crux span is one)
preserves it, and `segEval_sound` DOES prove `σ'.sailOutput = σ.sailOutput`.
But `segToTriple`'s `hpost` (`DeriveCaseRow.lean`) DROPS that fact, so the
landed row Posts cannot carry it — `OutRepr` is underivable at any row-Post.
Confirmed machine-checked (`/tmp/probe2`: `hpost` gives no sailOutput hypothesis).

`DeriveCaseRow.lean` is NOT owned this wave, but `segEval_sound`
(`SegEvalSound.lean`) IS reachable through the `DeriveCaseRow → SegEvalSound`
import — so the fix lands in an OWNED new file without touching the frozen
combinator.

## LANDED — `Vsa/Sim/rows/CallCruxMarshal.lean` (green, axiom-clean, gate OK)

The factored marshalling brick set (CLAUDE.md law 3 — factored ONCE, not
per-seam):

- **`segToTripleOut`** — `segToTriple` with `σ'.sailOutput = s0` threaded into
  `hpost`, built on `segEval_sound` directly.  Precondition `SegPreO` =
  `SegPre` + entry-sailOutput pin `s0`.  This is the combinator every
  span→carrier re-assembly needs to land `OutRepr`.
- **`outRepr_transport`** — from `σ'.sailOutput = σ0.sailOutput` (segToTripleOut's
  fact) + entry `OutRepr σ0 st`, land `OutRepr σ' st` (via
  `outRepr_of_sailOutput_eq`).
- **`gholds_reg`** + the **`gprGet_{x2,x8,x10,x15,x18,x19,x21,x22,x23}`** rfl
  battery — read a concrete GPR pin off a row-Post's `GHolds` into the carriers'
  `regs.get? Register.xN = some v` register fields (one application + one rfl
  cast per pinned register).  `gprGet σ n = regs.get? Register.xN` by `rfl` at
  every concrete GPR (probe-confirmed).
- **`foldBackLoop_passthrough`** / **`normalJoin_exit`** — the two named
  destructurers (CLAUDE.md R7) demonstrating the bricks compose on the landed
  rows: they consume the anonymous row-Post `∧`-towers ONCE and yield
  `GoodState`, the memory equation (`writeLog m0 [] = m0`, both segs memory-pure
  — probe-confirmed nil log), the exit PC, and the pass-through register pins
  (sp=x2, s6=x22) read via `gholds_reg` + `gprGet_*`.  The load-bearing restore
  reads (s3/s5/s7 in the join, a5 in the fold) are left to the callers'
  `SegReadback.gholds_lookup_ld`, threaded through `gholds_reg`.

- **`foldStore_succ`** (item-2 spec side) — `foldStore … (k+1) =
  (foldStore … k).define frame xₖ vₖ`: the `take`-succ decomposition of the
  `List.foldl` params-fold carrier, so the env_define contract's
  `Store.define`-shaped post marshals into `CallParamFoldInv (k+1)`'s `store`
  field without re-running the fold (the successor companion of `foldStore_full`).

Axioms of all 7 theorems ⊆ {propext, Classical.choice, Quot.sound}.

## What hCallClosure now reduces to (delta vs wave-40)

The item-1 blocker (carrier re-assembly needs OutRepr, row Posts drop it) is
RESOLVED by `segToTripleOut`: any crux span row can now be RE-STATED in the
sailOutput-carrying form (`SegPreO`/`segToTripleOut`) and marshalled into a
carrier with `OutRepr` re-established (`outRepr_transport`) and its register
fields read off `GHolds` (`gholds_reg` + `gprGet_*`).  The concrete
per-carrier re-assembly (fold `CallParamFoldInv k+1`, `BodyHandoff`,
`SegExit@callJoinPC`) is now MECHANICAL over these bricks + the wave-38/40
store-frame transports (`storeRepr_allocFrame`, `pushFrameMap`, `s7ImageAtBody`,
`CallerSpillSlots`) — no missing abstraction remains for item 1.

## Remaining (not landed this wave — scoped, not blocked)

- Item 1 tail: the FULL `CallParamFoldInv k+1` / `BodyHandoff` / `SegExit`
  re-assembly is entangled with the env_define post shape (`PostDef` in
  `callParamFoldSeam_of`) — the cursor/idx/frameReg advance happens in the
  staging span + env_define, not the memory-pure back-edge row alone.  The
  bricks are in place; the instantiation is the item-2 boundary.
- Item 2 (env_define splice per fold param): `foundSt_of_storeRepr`/
  `frameRepr_append` class over `foldStore`/`envDefContract` — spec-level store
  marshalling, not yet written (deepest remaining piece; needs the
  `envDefContract` post↔`CallParamFoldInv` bridge at the extended φf').
- Item 4 (value_null splices): the two `bridgeOfSeg` bridges are landed
  (`callClosureNormalDepthBridge`, `callClosureValueNullCallBridge`); the
  `callSeg`/`spliceFold` composition through `value_null_spec` + the post→next
  -row SegPre marshalling is the remaining glue.
- Item 5 (per-bridge ChainFacts/hjalSeam): region-specific `site_*` obs
  (M6/region-owned), discharged where the bridges are instantiated.
- Item 3: `stackScratchTop 0x80003378 => some 168` already in the table
  (wave 38); `BodyStatusABI` supplier is the seq-row (mExecSeq) side, not owned.

## Wiring lines (coordinator; NOT applied — I do not own Vsa.lean)

Vsa.lean (after `import Vsa.Sim.rows.CallClosureNormalRet`):
  import Vsa.Sim.rows.CallCruxMarshal
check_all axiom-list additions:
  Vsa.Sim.segToTripleOut            # rows/CallCruxMarshal
  Vsa.Sim.outRepr_transport         # rows/CallCruxMarshal
  Vsa.Sim.gholds_reg                # rows/CallCruxMarshal
  Vsa.Sim.foldBackLoop_passthrough  # rows/CallCruxMarshal
  Vsa.Sim.normalJoin_exit           # rows/CallCruxMarshal
  Vsa.Sim.foldStore_succ            # rows/CallCruxMarshal
