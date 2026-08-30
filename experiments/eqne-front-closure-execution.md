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

---

## Execution log (2026-08-30) — task 3 wiring LANDED

New file `Vsa/Sim/rows/EvalEqNeFront.lean` (green via `lake env lean`, ~3.0s, olean generated),
wired into `Vsa.lean:151` and `scripts/check_all.sh`. All new theorems axiom-clean:
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

Deliverables landed:
1. **`eqDispatch_lpins` / `neDispatch_lpins`** — extract the six source `LPins8 m0` from the
   dispatch `ChainFacts` (blocker-B readback inputs). Statement drift vs the parked WIP: the
   WIP proof (`exact hmf5.2`) FAILED — the `MemFacts` per-load carries
   `LPins8 m0 (eaddrM …).toNat ((stepLdsM^k lds).headD [])`, which does NOT reduce definitionally
   to `LPins8 m0 (sp+0xNN).toNat (lds.getD k [])`. Fix: per-load `change` to the `sext`-offset form
   + `rw` of `sext 0xNN = 0xNN#64` (address), and two new list lemmas `eqDisp_headD_getD0` /
   `eqDisp_tail_getD` (`(stepLdsM^k lds).headD [] = lds.getD k []`, by `cases lds <;> rfl`).
2. **`eqnePreBridge`** (model `divPreBridge`) — `jal value_equal @jalPC` → `ve_pre`. Parameterised
   by `jalPC`/`link`/`jImm` + the jal site lemma so ONE bridge serves eq (0x8000371c/0x80003720)
   and ne (0x8000376c/0x80003770). Key drift: `ve_pre`'s frame is over `NotWrittenVE` which
   INCLUDES x1 (the jal's write target), so the output `g` MUST be the identity value_equal-entry
   snapshot `fun R => c'.σ.regs.get? R` (not an external frame) — else the frame is unsatisfiable
   at x1. Also exposes `x2=sp`, `x9=sret`, and a `NotWrittenVEStr\{x1}` frame collapse to a
   passed `gpre`, needed downstream.
3. **`veReturnBridge`** (NEW) — `ve_str_post gsnap link fbase … → VeReturn g fbase sret …`. x9=sret
   from the snapshot; eval-frame collapse via a passed `hsnapEval`. `MemExtends mEnt→return` is
   taken as an explicit hypothesis — the exposed `ve_str_post` carries only outside-window agreement
   (the str-path ra spill window), so presence-inside is not derivable from the contract as exposed;
   a stronger `ve_str_post` would carry it. Documented in the lemma.
4. **`EqFrontData` / `EqResid`** (model `DivResid`) — the post-dispatch front residual: dispatch-run
   `Steps c2 cD`, the transported `value_equal` caller obligations on the post-dispatch memory `mA`
   (`Value_equalLoaded`/`JumpTable`/`StrcmpLoaded`/`MaskPinned`, both `VERegion`s), the two operand
   `ValueRepr`s read back at `bufa`/`bufb` on `mA`, the str-witness, `φ`-chain + `EqNeBoxPre` box.
5. **`blockC_eqne_front`** (model `blockC_div`) — `EqFrontData ⇒ eqnePreBridge ≫
   value_equal_spec_full ≫ veReturnBridge → VeReturn`. **`eqBlockC_bridge`** — `EqResid ⇒
   blockC_eqne_front ≫ blockC_eq/blockC_ne → hblockC` (the `∃ c3 mpre φfe φce, Steps ∧ PhiExtends×2
   ∧ PreEpilogueVD` shape), φ chain threaded through the shared box.
6. **`evalEqSimD` / `evalNeSimD`** — the div-parity reseat. Precondition carries
   `(∀ c2, TwoSubReturn … → EqResid … c2)` (exactly as `evalDivSim` carries `∀ c', TwoSubReturn →
   DivResid`); body discharges the shared row core's `hblockC` via `eqBlockC_bridge`. They live in
   the FRONT file (not the row) because the reseat consumes `blockC_eqne_front`, which is downstream
   of `EvalEqNeRow` in the import DAG; the row's original `evalEqSim`/`evalNeSim` (shared cores)
   are unchanged.

### What is closed vs still conditional
The eq/ne front is now closed to div-parity: `evalEqSimD`/`evalNeSimD` are conditional ONLY on
`EqResid` (front machine-transport), the same shape `evalDivSim` is conditional on `DivResid`.
The genuinely-new bridges (`eqDispatch_lpins`, `neDispatch_lpins`, `eqnePreBridge`, `veReturnBridge`,
`blockC_eqne_front`, `eqBlockC_bridge`) all landed green + axiom-clean and are reusable.

`EqResid` currently bundles the whole dispatch-run + post-dispatch transport as its content — i.e.,
the item-1 dispatch step (`evalEqChain_dispatch`) + the frame-transport of the loaded predicates onto
the post-dispatch memory `mA` + the `lds`-to-6-list truncation that feeds the blocker-B readback
lemmas (`eqDispatch_bufa_repr`/`bufb_repr`) is NOT yet in-lined into `blockC_eqne_front`; it is the
`EqResid.hFront` residual. That in-lining (mirroring `blockC_div`'s ~100-line `divDispatch_mem_frame`
+ loaded-image `agreeP` transport, plus a `evalBlocks`-log-depends-only-on-first-6-lds truncation
lemma so `eqDispatch_mem_tower`'s `lds=[b0..b5]` shape holds) is the one remaining lift to make the
front UNconditional on the dispatch-run, and is the natural next step. The reusable readback lemmas
themselves (`valueRepr_of_reflected_copy`, `eqDispatch_bufa/bufb_repr`, blocker B) are already green.

---

## Execution log (2026-08-30, session 2) — dispatch-run lift: items 1 & 2 LANDED; item 3 blocker identified

Goal: make the eq/ne front UNconditional on the dispatch-run (eliminate `EqResid.hFront`
bundling of `Steps c2 cD` + `EqFrontData`), reaching true div-parity where `DivResid` is
stated purely about the POST-`TwoSubReturn` config `c'` and `blockC_div` runs the dispatch
INTERNALLY.

### Landed (all green via `lake env lean`, ~3.1s, olean regenerated; axiom-clean ⊆ {propext, Classical.choice, Quot.sound})

1. **`eqDispatch_mem_frame` / `neDispatch_mem_frame`** (item 1) — the eq/ne analogue of
   `divDispatch_mem_frame`.  Outside `[base, base+0x108)` the post-dispatch memory
   `writeLog m0 (evalBlocks eqDispatch (init (eqDispL base) lds)).log` agrees with `m0`.
   Every `eqDispatch` store is `x2`-relative at offset ≤ 0x108 (decide), so via the generic
   `evalBlocks_frame_offsets` + `writeLog_getElem_disjoint` + `evalBlocks_init_log_width`.
   The two generics `evalBlocks_log_shift`/`evalBlocks_frame_offsets` live in `EvalDivRow`
   (NOT in this file's import DAG), so reproved locally verbatim.

2. **`eqDispatch_log_trunc` / `neDispatch_log_trunc`** (item 2, the truncation) — the
   reflected log depends only on `lds`'s first 6 loads: `lds → lds6 lds` (the six-element
   `getD` normal form) leaves the log unchanged, **by `rfl` after a six-case `cons` split of
   `lds`**.  LANDED SPECIFIC (eqDispatch + neDispatch), not general: a general
   "log depends on `lds.take (loadCount bs)`" lemma is NOT `rfl` for arbitrary `bs` (needs a
   `loadCount` recursion + non-`rfl` induction on block bodies), whereas the concrete block
   reduces definitionally — the six-case `rfl` IS the exponentiating move for this chain.
   Measured 0.5s standalone.

3. **`eqDispatch_bufa_repr_lds` / `bufb_repr_lds` / `ne…`** (item 2 wired) — the readback
   at the *existential* dispatch `lds`.  `eqDispatch_bufa_repr` (`EqNeReprReadback`) requires
   the six-element `[b0..b5]` shape; these wrappers rewrite the tower via
   `eqDispatch_log_trunc` and feed the six `LPins8` from `eqDispatch_lpins` (whose `getD k`
   outputs ARE `lds6`'s elements) — so the readback now lands on the actual
   `EqDispatchPostS`/`NeDispatchPostS` memory for the dispatch's opaque `lds`.

check_all THEOREMS extended with the 8 new capstones (mem_frame ×2, log_trunc ×2,
repr_lds ×4).

### Item 3 (the full internal reseat) — NOT landed; exact blocker

The front is STILL closed only to the current `EqResid` (which bundles `Steps c2 cD` +
`EqFrontData`, i.e. the dispatch-run + post-dispatch reprs `hReprA`/`hReprB` on `mA` given).
To make `blockC_eqne_front` run the dispatch internally (div-parity, `EqResid` a `DivResid`-
shaped structure on `c2`), I established the exact composition:

  `TwoSubReturn c2` → run `evalEqChain_dispatch` (0x8000351c → EqDispatchPostS, `lds` opaque)
  → `eqDispatch_mem_frame` (transport 5 loaded predicates m0→mA: `valueEqualLoaded_of_agree`,
    `jumpTable_of_agree`, `strcmpLoaded_of_agree`, `maskPinned_of_agree`, `loaded_bool_agreeP`,
    `loaded_eval_expr_agreeP` — ALL already exist, `ValueEqualSpec3`/`EvalNotSim`/`EvalSimCommon`)
  → `eqDispatch_{bufa,bufb}_repr_lds` (operand reprs on mA) → `eqnePreBridge`
    ≫ `value_equal_spec_full` ≫ `veReturnBridge` (all landed).

**BLOCKER (hard, scope): the readback needs the six `LPins8 m0 (base+0x78..) (lds.getD k)`,
which come ONLY from the dispatch `ChainFacts` — and `EqDispatchPostS` (the post that
`evalEqChain_dispatch` produces) DISCARDS the `ChainFacts`/`lds` pins.**  `EqDispatchPostS`
carries only `mem = writeLog m0 (evalBlocks eqDispatch (init (eqDispL sp) lds)).log`; the
semantic fact "`lds.getD 0` = the m0 bytes at `base+0x78`" (i.e. `LPins8 m0 (base+0x78)
(lds.getD 0)`) is guaranteed by the machine `ld` semantics but is NOT recoverable from that
post.  `eqDispatch_lpins` extracts the `LPins8`s from `ChainFacts`, but nothing between
`evalEqChain_dispatch` and `blockC_eqne_front` carries a `ChainFacts`.

Two feasible routes, BOTH out of the sanctioned scope ("existing statements unchanged
except within `rows/EvalEqNeFront.lean`"):
  (a) strengthen `EqDispatchPostS`/`NeDispatchPostS` (in `EqNeDispatchStrong.lean`) — and
      `evalEqChain_dispatch`/`evalNeChain_dispatch` (in `EvalEqNeArm.lean`) — to ALSO expose
      the six `LPins8 m0 (base+off) (lds.getD k)` (or the whole `ChainFacts`).  Then
      `blockC_eqne_front` feeds them straight into `eqDispatch_{bufa,bufb}_repr_lds`.  This
      is the RIGHT fix (~1 extra conjunct on the strong post + rethread through the two arm
      bridges); the readback wiring on this side is DONE.
  (b) re-derive the entry linkage 0x8000351c→0x800036e4 INLINE via `evalBinopChain_run`
      (mem unchanged, `σ'.mem = σ.mem`), then call `eqDispatch_facts` at the arm-entry σ'
      MYSELF (keeping its `ChainFacts`/`lds`) and run `eqDispatchRowS` on that `lds`.  All
      pieces exist and are front-reachable, but this duplicates `evalEqChain_dispatch`'s
      ~150-line geometry/pin discharge (op-token/kind bytes, slot pins, operand-word bytes
      from the two source reprs) verbatim — a large single-file addition (host `EvalDivRow`
      runs an 8M heartbeat budget for the analogous body; this file is capped at 120s).

Additionally, item 3 needs the `EqNeBoxPre` bundle (consumed by `blockC_eq`/`blockC_ne` in
`eqBlockC_bridge`) stated on the post-dispatch `mA`, so `EqResid` (on c2) must supply it
frame-conditionally (`∀ mA agreeing outside [base,base+0x108) → EqNeBoxPre … mA`) and
`blockC_eqne_front` instantiate it via the same mem_frame — the box slots at
`sp-40..sp-8` are ABOVE the dispatch window (`sp-1088+0x108 = sp-824`), so they survive; the
`Value_boolLoaded`/`Eval_exprLoaded`/store-survival clauses transport via the same agreeP
lemmas.  This is mechanical once route (a)/(b) supplies the `LPins8`s.

### Verdict
- Front unconditional on the dispatch-run NOW? **No** — still gated on `EqResid.hFront`.
- Remaining residual classes vs `DivResid`: `EqResid` currently carries STRICTLY MORE than
  `DivResid` (it bundles the dispatch-run `Steps c2 cD` + post-dispatch reprs, which `DivResid`
  does not).  Everything needed to reach parity is landed EXCEPT the `LPins8`-exposure from
  the dispatch post (blocker above).  Reachable div-parity residual (once unblocked): loaded
  images (`Value_equalLoaded`/`JumpTable`/`StrcmpLoaded`/`MaskPinned`/`Value_boolLoaded`) +
  operand reprs + geometry + str-witness + φ box — same shape class as `DivResid`.
- Truncation: landed SPECIFIC (eqDispatch + neDispatch), not general — rationale above.
- Elab: whole `rows/EvalEqNeFront.lean` = ~3.1s (well under 120s); truncation standalone 0.5s.
