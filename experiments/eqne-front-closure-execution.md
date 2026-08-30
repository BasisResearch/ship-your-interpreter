# eq/ne front closure — concrete execution notes (task 3 wiring)

Companion to `eqne-front-closure-plan.md`. Records the exact seams so task 3 can be
executed fast once Blocker A (sailOutput `o`/`out` through strcmp+value_equal) and
Blocker B (buffer reprs out of the reflected dispatch) land.

## Verified facts (as of dispatch)
- **Loads are `sigmaPost_alu` class** (`site_80006f84` lbu → `obs_alu_rd`). So `chain_out`
  (`ChainFrameOut.lean`) already covers every strcmp step — NO load case needed for A.
- `chain_out [hobs…]` closes `σN.sailOutput = σ0.sailOutput`; `.trans hPreOut` lands `= o`.
- Only 6 sigmaPost classes exist (alu/jal/jump_x0/branch_taken/branch_nottaken/store).

## Piece inventory (all present unless marked NEW)
- `TwoSubReturn` @0x8000351c — `EvalBinSim.lean:117`. Value-generic; hands `ValueRepr … (sp-968) vl`
  and `… (sp-944) vr`. This is the front's entry.
- `evalEqChain_dispatch` / `evalNeChain_dispatch` — `EvalEqNeArm.lean:94/200`. Run the eq/ne
  dispatch to `EqDispatchPostS`/`NeDispatchPostS` @0x8000371c / 0x8000376c
  (`σ.mem`, `σ.sailOutput`, `fun R => σ.regs.get? R`).
- `EqDispatchPostS` / `NeDispatchPostS` — `EqNeDispatchStrong.lean:33/49`. Parked at jal PC,
  x10=sp+0x40 (bufa), x11=sp+0x20 (bufb), x2=sp, tick<2, sailOutput=out0, callee frame.
  Blocker B strengthens these (or a sibling lemma) to ALSO conclude the two buffer `ValueRepr`s.
- `ve_pre` — `ValueEqualSpec.lean:189`. PC 0x8000285c; needs `Value_equalLoaded`, `JumpTable`,
  `mem=m0`, x10=bufa, x11=bufb, x1=r, `ValueRepr m0 N φc bufa.toNat va`, `… bufb vb`,
  `VERegion bufa/bufb`, `(update (r) 0 0).toNat%4=0`, `NotWrittenVE` frame.
  **After Blocker A: + `o` param, + `out : σ.sailOutput = o`.**
- `value_equal_spec_full` — `ValueEqualSpec4.lean`. Produces `ve_str_post` (stack-window post).
  **After Blocker A: threads `sailOutput = o`.**
- `ve_str_post` — `ValueEqualSpec4.lean:60`. `ve_post` weakened: mem agrees off `[entry_sp-16, entry_sp)`.
- `VeReturn` — `rows/EvalEqNeRow.lean:85`. What `blockC_eqne` consumes. Fields: hG, hpc(=link+0 upd),
  hx10(cond equal), hx9(sret), hsp(x2=fbase), hmi, htick, hout(=out0), hmemframe(off [fbase-16,fbase)),
  hMemExt(MemExtends mEnt σ.mem), hframe(NotWrittenVEStr except x9,x19).
- `blockC_eqne` — `rows/EvalEqNeRow.lean:160`. VeReturn → PreEpilogueVD @0x800033ec (middle+box+epilogue). Shared eq/ne.
- `evalEqNeSim` — `rows/EvalEqNeRow.lean:571`. Currently composes blockB ≫ (hblockC RESIDUAL) ≫ blockD_v_rec.
  `hblockC` = ∀c2, TwoSubReturn … → out-fact → ∃ c3 …, Steps c2 c3 ∧ φ-extends ∧ PreEpilogueVD.

## NEW lemmas to build (models in parens)
1. **`eqnePreBridge`** (model = `divPreBridge`, `EvalDivValueTail.lean:47`).
   From `EqDispatchPostS sp lds m0 out0 gpre` (parked at jalPC) + the two buffer reprs (Blocker B)
   + value_equal-entry obligations as hyps (Value_equalLoaded/JumpTable on post-dispatch mem,
   VERegion bufa/bufb, r%4=0, φc/native facts, str-witness) → step the single `jal value_equal`
   @jalPC (0x800036f→ actually 0x8000371c eq / 0x8000376c ne; VERIFY jal target = 0x8000285c) →
   deliver `ve_pre g bufa bufb r N φc vl vr mA o`. `out'` via `hobs.out, sailOutput_sigmaPost_jal`.
   Parameterise by `jalPC` so one bridge serves eq+ne (byte-identical dispatch).
2. **`veReturnBridge`** (NEW; no direct model). `ve_str_post` (from value_equal_spec_full) → `VeReturn`.
   Thread x9=sret, x2=fbase, MemExtends mEnt, and the NotWrittenVEStr frame from the surrounding
   dispatch/caller context (all callee-saved across value_equal). hout rides A's `out`.
3. **`EqResid`** bundle (model = `DivResid`). Value_equal caller obligations:
   StrcmpLoaded/MaskPinned/JumpTable/Value_equalLoaded, r%4=0, φc/native injectivity, str-witness `hstrwit`.
4. **`blockC_eqne_front`** — composes evalEqChain_dispatch ≫ (B) ≫ eqnePreBridge ≫
   value_equal_spec_full ≫ veReturnBridge ≫ blockC_eqne → discharges `hblockC`.
5. Reseat `evalEqNeSim` to prove `hblockC` internally from an `EqResid` precondition (div-parity),
   keeping `evalEqSim`/`evalNeSim` thin.

## Precise models found (post A+B merge)
- **`blockC_div`** (`rows/EvalDivRow.lean:202`) — EXACT shape for `blockC_eqne_front`:
  `Triple (TwoSubReturn ∧ <resid conjuncts>) (∃ mpre φfm φcm φfe φce, PhiExtends×4 ∧ PreEpilogueVD …)`.
  Copy its skeleton; swap the div dispatch/__divdi3/box for evalEqChain_dispatch → B-reprs →
  eqnePreBridge → value_equal_spec_full → veReturnBridge → blockC_eqne.
- **`divPreBridge`** (`EvalDivValueTail.lean:47`) — EXACT model for `eqnePreBridge` (jal → callee pre).
- **`DivResid`** (`rows/EvalDivRow.lean:662`) + **`evalDivSim`** (`:751`, goal `EvalDivSimGoal` `:705`) —
  EXACT model for `EqResid` + reseated `evalEqNeSim`. The reseat: precondition carries
  `(∀ c', TwoSubReturn … → EqResid … c')`; body runs `blockB_binary` → `hResid c2 hTS` → `blockC_eqne_front` → `blockD_v_rec`.
- **B repr lemmas** (`EqNeReprReadback.lean:276/293/310/326`): `eqDispatch_bufa_repr`/`bufb`/`ne…`.
  Conclude `ValueRepr (writeLog m0 (evalBlocks eqDispatch (init (eqDispL sp) [b0..b5])).log) N φc (sp+0x40) vl`
  (bufa) / `(sp+0x20) vr` (bufb). Inputs: `hsp: sp.toNat+4096≤2^64`, 3×`LPins8` per buffer, `hpaydisj`,
  source `ValueRepr m0 N φc (sp+0x78) vl` / `(sp+0x90) vr`.
- **`evalEqChain_dispatch`** (`EvalEqNeArm.lean:94`): σ@0x8000351c (+big pin bundle, `FrameBundle`) →
  `∃ c' lds, Steps ∧ EqDispatchPostS sp lds σ.mem σ.sailOutput (fun R=>σ.regs.get? R) c'`.
  INTEGRATION: its existential `lds` must be the six-elt `[b0..b5]` B's lemmas expect (six loads in eqDispatch).
- **`ve_pre`** now `ve_pre g bufa bufb r N φc va vb m0 o c` (o after m0); `value_equal_spec_full` threads `sailOutput=o`.
- **`veReturnBridge`** (NEW, no direct model): `ve_str_post g r sp va vb m0 o` → `VeReturn g (sp-1088) sret vl vr link out0 mEnt`.
  Reconcile x9=sret, x2=fbase, MemExtends mEnt, hmemframe off [fbase-16,fbase) from the surrounding callee-saved frame.

## Gate
Full `lake build` + `scripts/check_all.sh` green; `#print axioms evalEqSim evalNeSim` clean.
Add capstones to check_all THEOREMS if newly gated.
