# Wave 44 — the `.normal`-route splice → join, and THE 9TH FALSITY (lane normalroute)

Inherits wave-42/43 bricks (`bridgeOfSegOut`/`JalStepO`, `segToTripleOut`,
`gholds_reg`/`gprGet_*`, `outRepr_transport`, `normalJoin_exit`,
`s7ImageAtBody`/`CallerSpillSlots`).  Task: land `normalRouteSplice` = the
`.normal` body-exit → `SegExit@callJoinPC` re-assembly, resolving what pins x8
at the join.

## THE 9TH STATEMENT FALSITY — found in the x8 analysis, NOT dischargeable

Ledger `segexit-frame-preepilogue-x8-unrestored` (observations.md).

The stated target — `CallRetShape` / `callClosureRet_of_status`'s `.normal`
conclusion `SegExit g … st' callJoinPC m0` — is UNSATISFIABLE.  The skeleton
`SegExit.frame` field (`InductionScaffold.lean`) is
`∀ R, AbiPreservedNoise R → c.σ.regs.get? R = g R` — EVERY callee-saved restored
to the arm ghost `g` AT `exitPC`.  But `CallExitP`/`motive_*` instantiate
`exitPC := callJoinPC = 0x800033ec`, and THAT is the FIRST epilogue instruction;
the callee-saved restores (ra@1080, **s0@1072**, s2@1056, s1@1064, sp+=1088) all
run PAST the join (`0x800033ec..0x80003404`).  The `.normal` route
(`callClosureNormalDepthBridge ≫ value_null ≫ callClosureNormalJoinRow`) restores
ONLY s3/s5/s7; x8 (s0) is the ExecSeq loop COUNTER (`callClosureBodyExitNormalSeg`
does `addiw s0,s0,1` at `0x80003344`), so at `callJoinPC` x8 = the body statement
count ≠ `g x8` (the caller EX_CALL node ptr, `CallArgLoopInv.node`).
`AbiPreservedNoise x8` holds (`by decide`).  So `SegExit.frame` at `callJoinPC`
demands `x8 = g x8` = `some cnt = some node`, false.  (Same for ra/s1/s2/sp.)

* **Obstruction** (`rows/CallCruxMarshal5.lean §1`, green + axiom-clean 1.5s):
  `segExitJoin_frame_x8_false` — from `SegExit g … callJoinPC m0 c`, the route
  fact `c.σ.regs.get? x8 = some cnt`, the ghost `g x8 = some node`, and
  `cnt ≠ node` ⇒ `False` (via `SegExit.frame x8 (by decide)`).
* **Amendment proposal** (NOT applied — `SegExit`/`InductionScaffold` +
  `motive_*` are cross-lane statement defs; coordinator must ratify):
  weaken the join `frame` to the register set the PRE-epilogue join actually
  restores (a tabled `joinRestored` guard, PARALLEL to the wave-38
  `stackScratchTop`/`stackWin` amendment), leaving the full callee-saved
  restoration to the epilogue — provable only at the RETURNED-TO caller config,
  which is exactly where the caller's `armTail`/`EvalExit` re-establishes `g`.
  Alternative: move the EX_CALL exit PC past the epilogue to the returned-to
  target (the `EvalExit.pc = BitVec.update (r+..) 0` shape) — but the skeleton
  has no return-addr ghost `r`, so this is the larger change.  Recommended =
  the `joinRestored`-guarded `frame` (mirrors the existing `stackWin` precedent).

Because the target is refuted, `normalRouteSplice` into the STATED `SegExit`
cannot be built without the amendment — the machine content is real but its
landing predicate is wrong.  Per Law 4, landed the obstruction + the
output-carrying bricks the amended splice will consume, and STOPPED short of a
workaround exit.

## Landed (`rows/CallCruxMarshal5.lean`, green + axiom-clean ~1.5s, gate OK)

* §1 `segExitJoin_frame_x8_false` — the obstruction (above).
* §2 the two `.normal`-route bricks RE-STATED sailOutput-carrying (the
  `rowpost-drops-sailoutput-blocks-outrepr` fix the join re-assembly needs):
  - `normalDepthBridgeOut` — `callClosureNormalDepthSeg` (`--call_depth` ▷ jal
    value_null) via `bridgeOfSegOut` (`JalStepO`-shaped `hjal`); output twin of
    the frozen `callClosureNormalDepthBridge`.  `hKeysOut`/`hRaOut` are premises
    (the frozen twin's pattern — `evalBlocks`-shaped, not decidable under the
    free `s2v`/`s1v`).
  - `normalJoinRowOut` + `NormalJoinOutPost` — `callClosureNormalJoinSeg`
    (ld s3/s5/s7 ▷ j callJoinPC) via `segToTripleOut`; output twin of the frozen
    `callClosureNormalJoinRow`, parked at `callJoinPC = 0x800033ec` carrying
    `sailOutput = s0` so the join `OutRepr` lands via `outRepr_transport`.

## What the hCallClosure `.normal` route now reduces to

BLOCKED on the amendment.  The four route legs are all landed rows/bridges
(`callClosureBodyExitNormalRow` [0x80003378→0x80003954, writes s0],
`normalDepthBridgeOut`, `value_null_spec_full`, `normalJoinRowOut`
[→callJoinPC]).  Once `SegExit.frame` at `callJoinPC` is amended to the
join-restored register set, `normalRouteSplice` is a 4-leg `Triple.seq`
composition into the amended exit — the store/out/memFrame/stackWin fields read
off the same brick set as `valueNullHandoffSplice` (CallCruxMarshal4 §4): store
via a `store_survives`-style buffer-disjoint agreement (value_null writes only
`[sret, sret+24)`), out via `outRepr_transport` on the threaded `sailOutput`,
s3/s5/s7 restored values via `CallerSpillSlots`/`s7ImageAtBody`, sp untouched.
The M6/code-pin residuals (each leg's `ChainFacts`, the two `JalStepO` seams)
stay NAMED on the carrier (the wave-43 pattern).

## Wiring lines (coordinator; NOT applied — Vsa.lean/check_all not owned)

Vsa.lean (after `import Vsa.Sim.rows.CallCruxMarshal4`):
  import Vsa.Sim.rows.CallCruxMarshal5
check_all axiom-list additions:
  Vsa.Sim.segExitJoin_frame_x8_false   # rows/CallCruxMarshal5 (obstruction §1)
  Vsa.Sim.normalDepthBridgeOut         # rows/CallCruxMarshal5 (§2)
  Vsa.Sim.normalJoinRowOut             # rows/CallCruxMarshal5 (§2)

AMENDMENT (coordinator-owned, cross-lane): weaken `SegExit.frame`
(`Vsa/Sim/InductionScaffold.lean`) at a PRE-epilogue join per the proposal
above; re-verify `CallExitP` consumers.  Until then the `.normal`-route (and
symmetrically the `.ret`-route) splice into `SegExit@callJoinPC` is genuinely
unclosable.
