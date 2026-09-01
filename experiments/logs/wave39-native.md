# Wave 39 — native contracts (#49) + memcpy word-route framed epilogue (#15)

## Consumers (the specs, read first)
- `Vsa/Sim/EvalCallPrint.lean`: `NativePrintSpec`/`NativePrintlnSpec` = full
  `Triple (CallEntryP … callDispatchPC) (CallExitP … callJoinPC)` with output
  grown by `printArgs st.store vs (++ "\n")`, store UNCHANGED. `callPrint`/
  `callPrintln` consume these as `hNative` and return them verbatim.
- `Vsa/Sim/EvalCallNative.lean`: `NativeAssertOkSpec` = `Triple (CallEntryP)
  (CallExitP … st unchanged)`. `callAssertOk` consumes as `hNative`.
- All three residuals are the WHOLE native branch: dispatch decode (0x80003254
  native beq → 0x800039e0 arm) → indirect `jalr a6 = N.addr f` → the native fn
  body (print loop / value_truthy) → value_null → return to join 0x800033ec,
  threading `StoreRepr`/`OutRepr`/memFrame/φ over the whole spec store.

## Scope assessment (SIGNAL)
- The native `NativeAssertOkSpec`/`NativePrintSpec`/`NativePrintlnSpec` are
  END-TO-END `SegEntry ⇒ SegExit` Triples over the FULL store representation.
  Building them requires: (a) the fval-kind dispatch machine run threading the
  whole StoreRepr unchanged, (b) the `jalr a6` indirect resolution from
  `ValueRepr .native` (a StoreRepr ghost — NOT yet extracted as a lemma), (c)
  the ENTIRE native fn body as a machine run with per-char HTIF `OutRepr`
  appends composed against `htif_store_putchar` over a `Triple.loop`, (d) the
  value_print/value_truthy/value_null sub-call contracts (value_print routes
  through the %lld/snprintf render path — heavy). This is multi-wave machine
  content, NOT a single-wave deliverable. See per-contract status at bottom.

## memcpy word route (#15) — TRACTABLE, scoped
- `memcpy_spec` (MemcpySpec4:789) ALREADY covers the word route unframed
  (case C: `dispatch_to_word` ≫ `word_loop_spec` ≫ `epilogue_{notail,tail}`).
- `memcpy_spec_framed_byte` (MemcpySpecFramed) covers ONLY byte routes
  (misaligned ∨ n<8), carrying the ABI frame `∀ R AbiPreserved, get?=gm`.
- MISSING: the framed WORD route. `NotWrittenW` written GPRs = {x13,x15,x16},
  none AbiPreserved (x2/x3/x4/x8/x9/x18-27) ⇒ `AbiPreserved ⊆ NotWrittenW`.
  So same strategy as byte route: re-run `dispatch_to_word` carrying the ABI
  conjunct (`dispatch_to_word_framed`), thread word_loop + epilogue.
- OBSTRUCTION for the "free transport" trick: `AtBd4` has NO ghost/hframe
  field, and `dispatch_to_word` lands `∃ g' PreW g'` (fresh snapshot) — cannot
  peek inside to transport the ABI conjunct without a framed re-run.

## memcpy word route — DONE ✅
`Vsa/Sim/MemcpySpecFramedWord.lean` — green + axiom-clean (propext,
Classical.choice, Quot.sound only). Verify: `lake env lean` OK.
- `abiPreserved_notWrittenW` (AbiPreserved ⊆ NotWrittenW, by cases+simp)
- `dispatch_to_word_framed` (12-site AtBd4→∃g'PreW re-run carrying ABI conjunct
  via strlenFrame_alu/_bnottaken — the to_bd4_framed idiom)
- `wordloop_abi` (PreW g'→StWDone g' ABI transport FREE via g', bytepath_abi
  pattern — same g' over NotWrittenW at both ends)
- `epilogue_notail_framed` (9-site re-run: 7 ALU + bltu-nottaken + ret, via
  strlenFrame_alu/_bnottaken/_jr; word-exact 8*(n/8)=n case)
- `epilogue_to_bytehead_framed` + `epilogue_tail_framed` (8-site re-run to byte
  head + transport through byte loop+ret via g'' over NotWrittenB — the
  8*(n/8)<n byte-tail case)
- `memcpy_spec_framed_word` (top-level, BOTH sub-cases via by_cases on
  8*(n/8)=n): route hyps = halign_xor ∧ hbig ∧ hda ∧ hfit — EXACT framed
  analogue of memcpy_spec's route (C). Post = (∃ g', memcpy_bytepath_post g') ∧
  ABI, IDENTICAL to memcpy_spec_framed_byte ⇒ memcpy_framed_ainv_stable +
  EnvDefCompose.envDefMemcpyFramed apply VERBATIM (post-only). Consumer just
  routes to _word vs _byte on hroute; no other change.

## Native contracts — OBSTRUCTION (not one-wave; observation logged)
print/println/assertOk: STOPPED per Law 3. The residuals are full
StoreRepr/OutRepr-preserving SegEntry(callDispatchPC)→SegExit(callJoinPC)
Triples — same character/scale as the closure Call crux (waves 22-37). The
per-site batteries EXIST (NativeWrapperSites site_*_nw, NativeAssertSites
site_*_na, Native_print/println pins, value_null_spec/value_truthy_spec) but the
StoreRepr-preserving wrapper (the BULK) does not, and three abstractions are
missing: (1) native-entry-dispatch seam CallEntryP→SegEntry(native arm), (2) the
jalr a6 native-addr resolution lemma (ValueRepr .native → read64(fv+16)=N.addr f),
(3) the native-fn-body Triple (assert = value_truthy≫value_null; print/println =
loopFromBody char loop w/ OutRepr-append invariant via chain_out). Full detail +
proposal (nativeArmSplice wrapper + nativeAddr_of_valueRepr) in
experiments/observations.md @ 2026-09-01 native-call-segentry-wrapper.

## CallSpec fit note
CallSpec (Vsa/Sim/CallSpec.lean) records callees with explicit clobber sets for
spliceFold. The native contracts, once the nativeArmSplice wrapper + fn-body
Triples exist, would fit as CallSpec records (value_null/value_truthy/value_print
as sub-callees with their clobber sets; the sailOutput-invariance postSide idiom
for assert's no-output arm). But there is nothing to make a CallSpec record OF
yet — the fn-body Triples are unbuilt. Not applicable this wave.

## WIRING (coordinator — do NOT applied by me)
- Vsa.lean: add `import Vsa.Sim.MemcpySpecFramedWord`
- scripts/check_all.sh axiom list: add
    Vsa.Sim.memcpy_spec_framed_word
    Vsa.Sim.dispatch_to_word_framed
    Vsa.Sim.wordloop_abi
    Vsa.Sim.epilogue_notail_framed
    Vsa.Sim.epilogue_tail_framed
    Vsa.Sim.epilogue_to_bytehead_framed
    Vsa.Sim.abiPreserved_notWrittenW
  (all ⊆ {propext, Classical.choice, Quot.sound})
- scripts/discipline_grandfather.txt: Vsa/Sim/MemcpySpecFramedWord.lean ADDED
  (legacy memcpy hand strlenFrame_* idiom, same as grandfathered sibling
  MemcpySpecFramed.lean — no reflected BBlock chain exists for the memcpy
  site_* battery so FrameMeta cannot apply).
- EnvDefCompose consumer: route to memcpy_spec_framed_word on the word hroute
  disjunct (dst%8=0 ∧ 8*(n/8)≤64 ∧ n≥8); post IDENTICAL to _byte so
  memcpy_framed_ainv_stable + envDefMemcpyFramed apply verbatim.
