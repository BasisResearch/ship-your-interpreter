# Wave 34 — `blockC_concat` + `binArmStrResid_of_cblock` (STR-arm EvalIH lift)

## Goal
Build the middle span `blockC_concat` (arm entry → `concatHeapCore.P@0x80003a74`) and
`binArmStrResid_of_cblock` = `blockA_binaryArm ≫ blockC_concat ≫ concatCBlockTriple_of
≫ blockD_v_rec` → `StrConcatCBlockResid`.

## Structural findings (verified against disasm.txt, 2026-09-01)

CONTROL FLOW into the concat arm `0x80003a20` (disasm 3728-3731):
```
80003888  addi a5,a0,-3 ; beqz a5,80003a20   (LEFT operand kind==3==str → concat)
80003890  addi a5,a6,-3 ; beqz a5,80003a20   (RIGHT operand kind==3==str → concat)
```
`0x80003888` is the ADD-int arm entry, reached by the `.add` operator-dispatch span
`TwoSubReturn@0x8000351c → 0x80003888`.  Both operands are ALREADY evaluated (a0/a6
are the two operand kind tags = results of blockB_binary's two eval_expr sub-calls).

So the TRUE pipeline is:
  blockA_binaryArm (dispatch@0x800034e8)
  ≫ blockB_binary (TWO operand eval_expr sub-EvalIH; post = TwoSubReturn@0x8000356c)
  ≫ [operator-dispatch span → 0x80003888]        ← shared with blockC_add's chain
  ≫ [str-kind beqz TAKEN → 0x80003a20]           ← NEW branch (blockC_add takes fallthrough)
  ≫ [arm 0x80003a20 → 2×stringify → P@0x80003a74]  ← the two-stringify staging span
  ≫ concatHeapCore.P … concatCBlockTriple_of
  ≫ blockD_v_rec

KEY: `evalAddChain_run` (EvalAddChain.lean) ALREADY reflects the dispatch span
`0x8000351c → 0x80003888` — BUT hardcodes int×int (hyps `hc`/`hk` force kind loads = 2,
lands `x10=2, x16=2`, so both beqz's NOT taken → fallthrough to add-int).  The str case
needs the SAME `bblock_sound_bt` dispatch span but with a kind load = 3, landing at
0x80003888 with x10=3 (or x16=3) → beqz TAKEN → 0x80003a20.  That is a NEW block-reflection
chain (`evalConcatChain_run`), NOT a hand battery — but it is genuine new machine content
(the str-kind twin of evalAddChain_run + the taken-branch bblock).

Two-stringify span `0x80003a20 → 0x80003a74` (disasm 3830-3851):
```
80003a20-3c  staging (ld×3, addi a0,sp,64, sd×4)      set stringify(L) arg
80003a40     jal stringify(L)  → a0; mv s2,a0; s3,a0   [HYP StringifyContract]
80003a44-64  staging (ld×3, mv s2/s3, addi a0, sd×3)   set stringify(R) arg
80003a68     jal stringify(R)  → a0; mv s0,a0; s5,a0   [HYP StringifyContract]
80003a6c-70  mv s0,a0 ; mv s5,a0                        → reaches P@0x80003a74
```
This span = 2 straight staging segs + 2 jal seams (`bridgeOfSeg`/`callSeg` over the two
StringifyContract hypotheses, which ARE StrConcatCBlockResid's hypotheses).  Tractable
via the combinator table.

## Plan / status — LANDED
- [x] `Vsa/Sim/rows/BlockCConcat.lean` (green + axiom-clean + discipline OK):
      - `concatStringifySpan` (0x80003a20 → P) = callSeg over 2 stringify callees + 3 seams
      - `blockC_concat` = `Triple.seq disp (concatStringifySpan …)`  (B → P)
      - `binArmStrResid_of_cblock` = blockA ≫ blockB ≫ blockC_concat ≫ cblock ≫ blockD
        as a Triple.seq tower (the whole-node EvalIH lift, pure algebra)
      - `ConcatDispatchResid` + `blockC_concat_of_dispatchResid` (names the dispatch span)
- [x] `Vsa/Sim/rows/ConcatStringifyLArg.lean` (green + axiom-clean) = the FIRST
      stringify-arg staging seg (0x80003a20, `concatStringifyLArgBridge` via genseg's
      bridgeOfSeg).  L span writes only caller-saved regs → ABI-frame holds.
- [~] R staging seg (0x80003a44) NOT landed: `mv s2,a0 ; mv s3,a0` clobbers callee-saved
      x18/x19, so `WrChainAvoidAbi` is FALSE and bridgeOfSeg's ABI no-op fails
      (genseg emitted a false `decide` → sorryAx).  Removed the broken file; kept toml.
      Needs a `bridgeOfSegClobber` variant.  Logged to observations.
- [~] `ConcatDispatchResid` NOT built: the str-kind twin of evalAddChain_run + taken beqz.
      Genuine new block-reflection content.  Named + logged.

## Three honest named residuals remaining (all logged to observations.md)
1. `ConcatDispatchResid` — the operator-dispatch + str-branch block-reflection chain.
2. The R staging seg (segR slot) — needs bridgeOfSegClobber (ABI-clobber).
3. The two `StringifyContract` discharges — str LANDED, int-tail assembled.

## Verify results
- `lake env lean Vsa/Sim/rows/BlockCConcat.lean` — 5 thms, all ⊆ {propext, Classical.choice, Quot.sound}
- `lake env lean Vsa/Sim/rows/ConcatStringifyLArg.lean` — concatStringifyLArgBridge, axiom-clean
- oleans regenerated (-o); `check_discipline.py` OK.

## Wiring (report-only, NOT applied — do not touch Vsa.lean/check_all.sh)
- Vsa.lean: `import Vsa.Sim.rows.ConcatStringifyLArg` and `import Vsa.Sim.rows.BlockCConcat`
  (after `import Vsa.Sim.rows.ConcatSeams`).
- check_all.sh axiom list: add
  `Vsa.Sim.{concatStringifySpan, blockC_concat, binArmStrResid_of_cblock,
  ConcatDispatchResid, blockC_concat_of_dispatchResid, concatStringifyLArgBridge}`.

## Feasibility verdict
The FULL machine build is NOT one combinator: it needs a str-kind twin of the
`evalAddChain_run` block-reflection chain (the operator dispatch landing at 0x80003888
with a str kind tag, then the taken beqz).  That is legitimate block-reflection work
(bblock_sound_bt), not a hand battery, but it is a new ~1-chain build.  The two-stringify
span IS a clean combinator composition.  Landing strategy: build the two-stringify span
as a reusable Triple, name the dispatch+branch span as ONE typed residual
`ConcatDispatchResid`, and expose `blockC_concat` + `binArmStrResid_of_cblock` composing
over it.  The dispatch residual is the honest remaining machine content (logged to
observations).
