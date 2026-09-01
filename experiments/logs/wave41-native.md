# Wave 41 — native lane (#26 nativeArmSplice)

Task: the 3 native RemainingWork fields (NativeAssertOkSpec / NativePrintSpec /
NativePrintlnSpec) via 3 missing abstractions: (1) the native dispatch/join
wrapper factored ONCE, (2) `nativeAddr_of_valueRepr`, (3) fn-body Triples
(assertOk first).

## Ground survey (read before building)
- `EvalCallNative2.lean` (COMMITTED): `nativeAssertInternal` = the WHOLE
  native_assert internal run `naEntry → naExit` (0x80002df4 → ret), green.
  GAP: `naExit` does NOT carry an ABI callee-saved frame clause (no
  x8/x9/x18/x19-x27 restoration stated, though machine-true) — outside my file
  ownership to amend.
- `EvalCallNative3.lean` (COMMITTED): `site_800039f4_nw` (the jalr a6 site over
  `stepObs_jalr`) + `jalr_native_target` (bit-0-clear no-op at 4-aligned).
  Compose note at bottom = the exact residual map.
- `NativeWrapperSites.lean`: 18 `_nw` sites (dispatch 0x80003254..0x8000327c
  beq-TAKEN + arm marshal 0x800039e0..0x800039f0 + join 0x800039f8/0x800039fc).
- ABI CORRECTION (EvalCallNative3): at the jalr, a0=sret a1=interp a2=argc
  a3=sp+240=argsBase a4=scratch a6=N.addr f ra=0x800039f8. naEntry matches.
- Join restore: `ld s7,1016(sp)` — the slot is tabled in `entrySpillImage
  callDispatchPC = some (1016, 23)` (EntryImage, InductionScaffold wave 40);
  `stackScratchTop callJoinPC = none` ⇒ SegExit.stackWin vacuous at the join.
- Reuse: `JalStep` (BridgeSeg), `sext_reassemble` (EnvNewSpec), `sext_full`
  (ValueTruthySpec), `StepFrameOut.of_alu/of_jr` (StepFrameOut),
  obs_jalr_* (SnprintfSitesRet5), `storeRepr_agreeP` (ReprSurvival).

## Plan (top-down)
1. rows/NativeAddrResolve.lean — nativeAddr_of_valueRepr (+kind destructurer) +
   jalrStep_of_obs (indirect-call JalStep glue, the jalr twin of
   BridgeSeg.jalStep_of_obs) + nativeJalrStep (the concrete 0x800039f4 seam).
2. rows/NativeArmSplice.lean — NativeBodyPost (named-field boundary at
   0x800039f8), the JOIN machine Triple NativeBodyPost → CallExitP (2 sites +
   SegExit rebuild), nativeArmSplice (Mid-abstract dispatch ≫ body ≫ join),
   3 instantiations producing the RemainingWork field types.
3. rows/NativeArmDispatch.lean — #derive_case seg 0x80003254→0x800039f0
   (beq TAKEN) + bridgeOfSegFramed at AbiExceptS7 + jalr seam.
4. rows/NativeBodyAssert.lean — Triple Mid_assert NativeBodyPost from
   nativeAssertInternal (named residual: the naExit ABI-frame gap).

## Landings
- **rows/NativeAddrResolve.lean** GREEN + axiom-clean (propext, Classical.choice,
  Quot.sound), discipline OK. `nativeAddr_of_valueRepr` / `nativeKind_of_valueRepr`
  / `nativeName_of_valueRepr` (the R6 destructurers for the `.native` ValueRepr
  tower; abstraction 2 of the observation), `jalrStep_of_obs` (the INDIRECT-call
  `JalStep` glue — jalr twin of BridgeSeg.jalStep_of_obs, reusable for any
  fn-pointer dispatch), `nativeJalrStep` (the concrete 0x800039f4 seam:
  JalStep a6v 0x800039f8 from the parked arm state). GOTCHAS: `NativeFn`/`Addr`
  must be qualified `Vsa.While.*` under these opens (a Sail name shadows).
- **rows/NativeArmSplice.lean** GREEN + axiom-clean, first pass. Abstraction 1:
  `NativeBodyPre`/`NativeBodyPost` (named-field boundary structures at the
  native entry / the 0x800039f8 return link), `nativeJoin` (the join leg
  MACHINE-DISCHARGED: site_800039f8_nw ld-s7 + site_800039fc_nw j, s7 ghost
  restored via `sext_reassemble` off the s7slot bytes, SegExit rebuilt —
  stackWin vacuous since `stackScratchTop callJoinPC = none` by rfl),
  `nativeArmSplice` (Mid-abstract dispatch ≫ body ≫ join), and the 3
  instantiations `nativeAssertOkSpec_of_splice` / `nativePrintSpec_of_splice` /
  `nativePrintlnSpec_of_splice` producing EXACTLY the RemainingWork field types.
  Per-native residuals after this file: hDispatch (Triple CallEntryP Mid) +
  hBody (Triple Mid NativeBodyPost).  KEY moves: `StepFrameOut.of_alu/of_jr`
  for the 2-step frame+out threading (noise-membership grind done once);
  OutRepr transported by `unfold Vsa.Machine.output; rw [sailOutput-eq]`.
- **rows/NativeArmDispatch.lean** GREEN + axiom-clean. The dispatch-leg machine
  body: `nativeDispatchStageSeg` = #derive_case 2-block chain 0x80003254 →
  0x800039f0 (the closure dispatch's first block VERBATIM, beq polarity
  flipped to `.br bop.BEQ true` → chains to the 0x800039e0 arm marshal block),
  `nativeDispatchStageBridge` via `bridgeOfSegFramed` at `AbiExceptS7` (REUSED
  from BridgeSegFramed:398 — do NOT redefine, clashes), and
  `nativeDispatchJalSeam_of` DISCHARGING the jalr-seam residual from
  `nativeJalrStep` given hpcEq (seg-static, closes at concrete lds) + the
  x16=a6v out-regs pin + code-survival + 4-alignment. Residuals of this leg:
  hfacts (ChainFacts w/ the kind=5 TAKEN-beq guard, from
  nativeKind_of_valueRepr) + the CallEntryP→register-pins geometry (the
  SegEntry skeleton names no a5/argc/staged-fv — the M6/arm caller's seam,
  SAME class as the closure hDispatchStage).
- **rows/NativeBodyAssert.lean** GREEN + axiom-clean, first pass. The assertOk
  body leg: `NativeAssertExtra` (config-dependent assert facts: 3 callee code
  pins + payDisj), `NativeAssertInternalAbi` (the ONE named residual — the
  ABI-framed variant of nativeAssertInternal; observation
  `naexit-lacks-abi-frame-clause` logged: naExit omits the frame clause though
  the proof tracks the values; coordinator amends EvalCallNative2),
  `nativeBodyAssert` (Triple (NativeBodyPre ∧ Extra) NativeBodyPost — the
  ENTIRE naEntry construction from the boundary + naExit→NativeBodyPost
  rebuild landed: g_na := entry-config reads makes naEntry's tie rfl and the
  framed exit hands back entry values; loaded_eval_expr_agreeP +
  storeSurv + hmemF' compositions all by omega over the window premises),
  `nativeAssertOkSpec_of_dispatch` (NativeAssertOkSpec conditional on ONLY
  hDispatch + hInternal + geometry).

## Residual map after wave 41 (per RemainingWork field)
- hCallAssertOk (NativeAssertOkSpec): `nativeAssertOkSpec_of_dispatch` needs
  (1) hDispatch : Triple CallEntryP (NativeBodyPre ∧ NativeAssertExtra) —
  machine body EXISTS (nativeDispatchStageBridge + nativeDispatchJalSeam_of);
  the CallEntryP→pins marshalling is the caller's (SegEntry carries no
  a5/argc/staged-fv ABI — same seam class as closure hDispatchStage; the
  ghost-quantified Triple at fixed ghosts is NOT provable from bare CallEntryP,
  so the arm assembly discharges it at its own configs); (2) hInternal =
  NativeAssertInternalAbi (one naExit amendment away).
- hCallPrint/hCallPrintln (NativePrintSpec/NativePrintlnSpec):
  `nativePrintSpec_of_splice`/`nativePrintlnSpec_of_splice` reduce each to
  hDispatch + hBody. The bodies (native_print loop = loopFromBody over
  value_print/htif appends; println = print + fputc newline) are UNBUILT —
  no site battery for the print internals exists yet; multi-wave per the
  observation's warning. The wrapper/join/dispatch layers are SHARED and DONE.

## Smoke tests (not landed)
- `evalBlocksPC 0x80003254 (init L [k0..k4]) nativeDispatchStageSeg =
  0x800039f4` closes by `rfl` at any concrete-SHAPE lds (5 slots, symbolic
  bytes) — the `hpcEq` residual of nativeDispatchJalSeam_of is honestly
  dischargeable by the caller.

## Observations appended this wave
- `naexit-lacks-abi-frame-clause` (the NativeAssertInternalAbi residual +
  amendment plan for EvalCallNative2's naExit)
- `nonra-gpr-dispatch-duplicated-jal-jalr` (factor the 30-branch GPR
  dispatch before a third linking-step class appears)

## Wiring (coordinator — NOT applied by me)
- Vsa.lean (after `import Vsa.Sim.EvalCallNative3`):
    import Vsa.Sim.rows.NativeAddrResolve
    import Vsa.Sim.rows.NativeArmSplice
    import Vsa.Sim.rows.NativeArmDispatch
    import Vsa.Sim.rows.NativeBodyAssert
- scripts/check_all.sh axiom list:
    Vsa.Sim.nativeAddr_of_valueRepr Vsa.Sim.nativeKind_of_valueRepr
    Vsa.Sim.nativeName_of_valueRepr Vsa.Sim.jalrStep_of_obs
    Vsa.Sim.nativeJalrStep Vsa.Sim.nativeJoin Vsa.Sim.nativeArmSplice
    Vsa.Sim.nativeAssertOkSpec_of_splice Vsa.Sim.nativePrintSpec_of_splice
    Vsa.Sim.nativePrintlnSpec_of_splice Vsa.Sim.nativeDispatchStageSeg_seg
    Vsa.Sim.nativeDispatchStageBridge Vsa.Sim.nativeDispatchJalSeam_of
    Vsa.Sim.nativeBodyAssert Vsa.Sim.nativeAssertOkSpec_of_dispatch
  (all verified ⊆ {propext, Classical.choice, Quot.sound})
- discipline: all 4 new files pass strict (no grandfathering needed).
- coordinator amendment REQUEST: EvalCallNative2.naExit + one clause
  `∀ R, AbiPreservedNoise R → c.σ.regs.get? R = g R` (values already tracked
  in the proof) — discharges NativeAssertInternalAbi verbatim.
