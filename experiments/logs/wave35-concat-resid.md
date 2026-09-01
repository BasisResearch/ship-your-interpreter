# Wave 35 — closing the 3 named residuals of `binArmStrResid_of_cblock`

Target: `Vsa/Sim/rows/BlockCConcat.lean`'s three residuals:
1. `ConcatDispatchResid` — operator-dispatch + str-branch chain (kind=3 twin of evalAddChain_run)
2. R staging seg @0x80003a44 (clobbers s2/s3 callee-saved) — via `bridgeOfSegFramed`+AbiExceptS2S3
3. int-tail `StringifyContract` discharge (snprintf %lld)

## genseg audit (Residual 2 root cause)
`scripts/genseg.py:388` emits `(by show WrChainAvoidAbi {seg}; decide)` UNCONDITIONALLY
for every jal-terminated span. When the span writes a callee-saved register (s2=x18,
s3=x19 here), `WrChainAvoidAbi seg` reduces to `False`, so `decide` cannot produce a
proof term. HOW IT MANIFESTS AS sorryAx: `decide` on a `False`-reducing proposition
elaborates to `of_decide_eq_true (Eq.refl false)` style — actually it FAILS to typecheck
and Lean's error-recovery inserts `sorryAx` into the partial term so the rest of the file
still elaborates; the `#print axioms` then shows `sorryAx` but a casual "did it compile"
glance (no error at the theorem site if error-recovery swallowed it) misses it. FIX: genseg
should (a) compute wrChain of the seg and, if any written reg is AbiPreserved, emit the
`bridgeOfSegFramed`+restricted-predicate path instead of `bridgeOfSeg`; OR (b) at minimum
guard line 388 with a static check and refuse to emit (error out) rather than emit an
unprovable `decide`. Reported in observations.md.

## R span decode (0x80003a44 → 0x80003a68, jal stringify@0x80002fc0)
```
80003a44  ld a3,144(sp)   0x09013683
80003a48  ld a4,152(sp)   0x09813703
80003a4c  ld a5,160(sp)   0x0a013783
80003a50  mv s2,a0        0x00050913  (addi x18,x10,0) — CLOBBERS s2=x18 (callee-saved)
80003a54  mv s3,a0        0x00050993  (addi x19,x10,0) — CLOBBERS s3=x19 (callee-saved)
80003a58  addi a0,sp,64   0x04010513
80003a5c  sd a3,64(sp)    0x04d13023
80003a60  sd a4,72(sp)    0x04e13423
80003a64  sd a5,80(sp)    0x04f13823
```
wrChain writes {x13,x14,x15,x18,x19,x10}; x18/x19 are AbiPreserved. avoid-set = AbiExceptS2S3.

## RESULTS — all 3 residuals CLOSED (axiom-clean)

### Residual 1 — ConcatDispatchResid (CLOSED)
`Vsa/Sim/rows/ConcatDispatchChain.lean` (new):
- `evalConcatDispatchChain_run` — κ-parametrized dispatch chain 0x8000351c→0x80003888
  (the exponentiating move: evalAddChain_run proof is kind-VALUE-agnostic; only the 6
  `2#64` literals → `κ`; axiom-clean first run, zero proof edits).
- `concatStrHead` block + `evalConcatDispatch_run` — κ=3 chain ▸ taken beqz → 0x80003a20.
- `concatDispatch_toTriple` + `ConcatDispatchPost` — packaged as `Triple P ConcatDispatchPost`.
Verify: 3 thms, all ⊆ {propext, Classical.choice, Quot.sound}. discipline OK (1 allow:
R6 on the copied block_facts ld pin-bundle, same idiom as grandfathered evalAddChain_run).

### Residual 2 — R staging seg (CLOSED)
`Vsa/Sim/rows/ConcatStringifyRArg.lean` (new):
- `concatStringifyRArgSeg` (#derive_case) + `AbiExceptS2S3` + `concatStringifyRArgBridge`
  via `bridgeOfSegFramed` (NOT a new bridgeOfSegClobber — used the existing avoid-set-generic
  framed bridge, exactly like entryBaseReseat_framed/AbiExceptS7). Exposes full GHolds bundle
  (carries s2=s3=a0v) + restricted ABI frame.
Verify: 2 thms axiom-clean.

### Residual 3 — int-tail StringifyContract (CLOSED)
`Vsa/Sim/rows/StringifyIntTail.lean` (new):
- `stringifyContract_int_of_call` — `.int n` closes through the SHARED strdup tail via the
  v-generic `stringifyContract_of_call` + `stringifyDisplay_int` (display (.int n)=intToString n).
  NO new snprintf machinery: snprintf_lld_spec + stringifyStrdupTailContract are LANDED interior;
  named the one honest int-arm dispatch/staging seam as `IntBranchCallResid` +
  `intBranchCallResid_of_halves`.
Verify: 3 thms axiom-clean.

### Re-instantiation
`Vsa/Sim/rows/BlockCConcat.lean` (edited): imports the 3 new files; added
`concatDispatchResid_closed` (inhabits ConcatDispatchResid from concatDispatch_toTriple) +
`blockC_concat_str_closed` (re-instantiates blockC_concat_of_dispatchResid with the BUILT
dispatch Triple). All 7 thms axiom-clean.

## Wiring lines (report-only, NOT applied)
Vsa.lean (after `import Vsa.Sim.rows.ConcatSeams`):
  import Vsa.Sim.rows.ConcatDispatchChain
  import Vsa.Sim.rows.ConcatStringifyRArg
  import Vsa.Sim.rows.StringifyIntTail
  (BlockCConcat already imports these transitively; import BlockCConcat as before.)
check_all.sh axiom list — add:
  Vsa.Sim.{evalConcatDispatchChain_run, evalConcatDispatch_run, concatDispatch_toTriple,
    ConcatDispatchPost, concatStringifyRArgSeg_seg, concatStringifyRArgBridge, AbiExceptS2S3,
    IntBranchCallResid, stringifyContract_int_of_call, intBranchCallResid_of_halves,
    concatDispatchResid_closed, blockC_concat_str_closed}

## Remaining (honest gaps beyond this wave's scope)
- The `segL/segR/segP` staging seams still need `segToTriple`-marshalling from the bridge
  shapes (concatStringifyLArgBridge/RArgBridge produce `∃ σ2...`, not directly `Triple`) —
  the same marshalling BlockCConcat's abstract slots leave open; not blocking the residuals.
- Residual 3's `IntBranchCallResid` interior (int-arm dispatch→snprintf-entry marshalling→
  j-join) is the one unbuilt straight-line seam; snprintf_lld_spec + strdup tail are LANDED.
