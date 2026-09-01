# Wave 45 — falsity #9 amendment (`SegExit.frame` @ pre-epilogue join) + route splices (lane segexit9)

Status log, incremental.  Task: (1) apply the RATIFIED falsity-9 amendment
(ledger `segexit-frame-preepilogue-x8-unrestored`): weaken `SegExit.frame`
(`Vsa/Sim/InductionScaffold.lean`) to a `joinRestored`-guarded register set at
tabled exit PCs (wave-38 `stackWin` table pattern); (2) land `normalRouteSplice`
into the amended `SegExit@callJoinPC`; (3) probe/land the symmetric `.ret`
route; (4) report the `hCallClosure` residual.

## §0 Consumer/producer census (BEFORE any edit — grep-verified)

`SegExit` construction sites (complete: every construction must supply
`stackWin`, so `stackWin :=` is a complete census; no `SegExit.mk` / anonymous
constructor sites exist):

1. `Vsa/Sim/LoopScaffoldClose.lean:57` — `segIdentity` (`frame := hc.frame`
   from the FULL `SegEntry.frame`; needs the weaken adapter).
2. `Vsa/Sim/CallEntry.lean:323` — `evalArgsNil` (same shape).
3. `Vsa/Sim/EvalArgs.lean:173` — `segExit_extend` (SegExit→SegExit rebase at
   the SAME `exitPC`: guarded→guarded, type-identical — NO edit).
4. `Vsa/Sim/rows/NativeArmSplice.lean:276-320` — `nativeJoin` (proves the FULL
   frame at `callJoinPC` for the native routes — the native arm never clobbers
   the callee-saveds; supplies the weakened field by ignoring the guard:
   `intro R hR _`).

`.frame`-projection consumers of a `SegExit` value (complete grep over all 25
`SegExit`-referencing files + the `CallExitP`/`EvalArgsExit` abbrev users):

5. `Vsa/Sim/rows/CallCruxMarshal5.lean:114` — the falsity-9 obstruction itself
   (`segExitJoin_frame_x8_false`, BREAKS BY DESIGN under the amendment; I own
   the file — restated over the explicit PRE-amendment clause, name kept for
   check_all line 1041).

NO other `.frame` consumer exists (EntrySeams/EntryHaltsSpans project only
`good`/`tick`/`pc`/`out`; CallClosureSplice projects `stackWin`;
CallArmEpilogue/ExecSeqLoop/DriveToLoopHeadSpans `frame :=` sites are
EvalExit/ExecSeqExit/SegEntry, not SegExit).  Fully-applied references
(`motive_*`, `TermCases` fields, `TermSimClose`/`TermSimAssembly`,
`CallRows`/`CallResidProviders`/`SeqForRows`/`ScaffoldRows` rows,
`CallRetShape`/`CallClosureGeom`) are invisible to the field change (wave-40
`mCall` precedent).

## §REVERT (coordinator, end of wave 45)

Same treatment as the sentryc lane: the `SegExit.frame` weakening +
`joinRestored` guard landed in InductionScaffold with the CallEntry/
LoopScaffoldClose/NativeArmSplice adapters, but `segExitJoin_frame_x8_false`'s
restatement (rows/CallCruxMarshal5 — "BREAKS BY DESIGN, I own the file") and
the normalRouteSplice/.ret-route items were not landed before the stall.
All segexit9-lane edits REVERTED to wave-44 state for the green push; the
census in §0 above is the re-landing checklist for wave 46.
