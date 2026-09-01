import Vsa.Sim.rows.ConcatSeams
import Vsa.Sim.rows.StringifySpec
import Vsa.Sim.DeriveCallSeg

/-!
# `BlockCConcat` — the STR-arm middle span `blockC_concat` + `binArmStrResid_of_cblock`

Task Wave-34.  This file lands the concat arm's MIDDLE span as pure
`callSeg`/`Triple.seq` composition algebra, closing the gap the prior wave named
(`experiments/observations.md`, 2026-09-01 blockc-concat-shape): the plan's
`blockA_binaryArm ≫ blockB_binary ≫ concatHeapCore ≫ blockD_v_rec` is not
type-correct because the concat C-block `0x80003a20` is NOT reached by `blockB_binary`'s
arithmetic value-combine tail — it is the STR-kind branch of the operator dispatch.

## Verified control flow (disasm.txt 3728-3851, 2026-09-01)

Both operands are evaluated FIRST (`blockB_binary`'s two `eval_expr` sub-calls,
post = `TwoSubReturn`@`0x8000356c`).  Then the `.add` operator-dispatch span reaches
the ADD-int arm entry `0x80003888`, where the two operand kind tags are tested:

```
80003888  addi a5,a0,-3 ; beqz a5,80003a20   (LEFT  kind==3==str  → concat)
80003890  addi a5,a6,-3 ; beqz a5,80003a20   (RIGHT kind==3==str  → concat)
   … (fallthrough = the int×int ADD path blockC_add develops)
80003a20  ld×3 ; addi a0,sp,64 ; sd×4         (stringify(L) arg staging)
80003a40  jal stringify(L)  → s2/s3           [StringifyContract, the CBlock HYP]
80003a44  ld×3 ; mv s2/s3 ; addi a0,sp,64 ; sd×3  (stringify(R) arg staging)
80003a68  jal stringify(R)  → s0/s5           [StringifyContract, the CBlock HYP]
80003a6c  mv s0,a0 ; mv s5,a0                  → concatHeapCore.P@0x80003a74
```

`evalAddChain_run` (`EvalAddChain.lean`) already reflects the dispatch span
`0x8000351c → 0x80003888` but HARDCODES int×int (kind loads = 2, lands `x10=2,x16=2`,
both `beqz` NOT taken).  The str case needs the SAME `bblock_sound_bt` dispatch span
with a kind load = 3, landing at `0x80003888` and taking the `beqz` to `0x80003a20`.
That is genuine new block-reflection content (the str-kind twin of `evalAddChain_run`
plus the taken-branch block) — NOT a hand site-battery, but a fresh chain.  We name it
precisely as ONE typed residual `ConcatDispatchResid` (logged to observations), and
compose the two-stringify staging span onto it.

## What this file lands (pure composition algebra)

* `concatStringifySpan` — the two-stringify staging span `armEntry → P` as `callSeg`
  over the two `StringifyContract` callee slots (which ARE `StrConcatCBlockResid`'s
  hypotheses) + the two arg-staging seams + the `mv s0/s5` head seam.  Every piece is
  a NAMED `Config→Prop`-boundary Triple, exactly the `concatHeapCore` idiom.
* `blockC_concat` — `TwoSubReturn-post → P` = `ConcatDispatchResid ≫ concatStringifySpan`.
* `binArmStrResid_of_cblock` — the whole-node lift:
  `blockA_binaryArm ≫ blockB_binary ≫ blockC_concat ≫ concatCBlockTriple_of ≫ blockD_v_rec`
  as a `Triple.seq` tower over the seven named residuals (dispatch, staging seams,
  stringify contracts, C-block callee contracts, blockD).  The two `stringify`
  contracts thread from `blockC_concat`'s two stringify slots straight into the
  C-block's `EvalIH` obligation.

The honest remaining machine content is exactly the named residuals: the dispatch+branch
chain `ConcatDispatchResid` (the block-reflection twin), the arg-staging seams (straight
`#derive_case` segs), and the two `StringifyContract` discharges (the per-kind stringify
Triples, LANDED for str, int-tail assembled).  All composition is pure `Triple` algebra.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats` bump.
Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open LeanRV64DExecutable (Register RegisterType)

namespace Vsa.Sim

/-! ## `concatStringifySpan` — the two-stringify staging span `armEntry → P`

Five sub-segments, two of them the `stringify` callees:

| span                          | boundary Triple | marshals                          |
|-------------------------------|-----------------|-----------------------------------|
| `0x80003a20 ld×3;addi;sd×4`   | `segL : Triple E S1`   | stringify(L) arg → a0        |
| `0x80003a40 jal stringify(L)` | `strL : Triple S1 S1'` | [StringifyContract L]        |
| `0x80003a44 ld×3;mv;addi;sd×3`| `segR : Triple S1' S2` | s2/s3 = L-ptr ; stringify(R) arg |
| `0x80003a68 jal stringify(R)` | `strR : Triple S2 S2'` | [StringifyContract R]        |
| `0x80003a6c mv s0,a0;mv s5,a0`| `segP : Triple S2' P`  | s0/s5 = R-ptr → P            |

This is the `concatHeapCore.concatFront` idiom (three callees, two seams) at the
stringify scale (two callees, three seams).  The two `stringify` callee Triples are
the arguments the caller threads from the `StrConcatCBlockResid` hypotheses; the
three staging seams are `#derive_case` segs (the honest straight-line residual). -/
theorem concatStringifySpan {E S1 S1' S2 S2' P : Config → Prop}
    (strL : Triple S1 S1')             -- jal stringify(L) callee
    (strR : Triple S2 S2')             -- jal stringify(R) callee
    (segL : Triple E S1)               -- arm entry ▷ stringify(L) arg staging
    (segR : Triple S1' S2)             -- ▷ mv s2/s3 (L-ptr) ; stringify(R) arg staging
    (segP : Triple S2' P) :            -- ▷ mv s0/s5 (R-ptr) → P
    Triple E P :=
  -- (E ≫ segL ≫ strL) ≫ segR ≫ strR ≫ (segP into P)
  callSeg (callSeg segL strL segR) strR segP

/-! ## `blockC_concat` — `TwoSubReturn-post → concatHeapCore.P`

The operator-dispatch + str-kind-branch span `disp : Triple B armEntry` (from the
`blockB_binary` post `B` = `TwoSubReturn` at `0x8000356c`, through the `.add`
operator dispatch to `0x80003888`, taking the str-kind `beqz` to the concat arm
entry `armEntry`@`0x80003a20`) composed with the two-stringify staging span.  `disp`
is the NAMED typed residual `ConcatDispatchResid` — the str-kind twin of
`evalAddChain_run` plus the taken branch (genuine block-reflection content, logged). -/
theorem blockC_concat {B E S1 S1' S2 S2' P : Config → Prop}
    (disp : Triple B E)                -- TwoSubReturn-post ▷ dispatch ▷ str-branch → armEntry
    (strL : Triple S1 S1') (strR : Triple S2 S2')
    (segL : Triple E S1) (segR : Triple S1' S2) (segP : Triple S2' P) :
    Triple B P :=
  Triple.seq disp (concatStringifySpan strL strR segL segR segP)

/-! ## `binArmStrResid_of_cblock` — the whole-node STR-arm `EvalIH` lift

Composes the standard binary-arm pipeline into `StrConcatCBlockResid`'s shape.  Both
slots of `StrConcatCBlockResid` (left literal-`.str`, right literal-`.str`) share this
composer; the only difference is which operand carries the literal, so the whole node
is stated GIVEN the two `stringify` contracts (as `StrConcatCBlockResid` demands) and
the `EvalIH` from `EvalEntry` to `EvalExitD` is:

  `blockA` (EvalEntry → blockB entry)
  ≫ `blockB` (two operand eval_expr sub-EvalIH → TwoSubReturn post `B`)
  ≫ `blockC_concat` (`B → P`)
  ≫ `cblock` (`concatCBlockTriple_of`: the concat C-block `P → V`, i.e. malloc/memcpy/
     strcpy/free×2/value_str with the three MallocContract slots pre-plugged)
  ≫ `blockD` (`blockD_v_rec`: `V → EvalExitD`).

Every stage is a `Triple` at matching `Config→Prop` boundaries; the composition is a
`Triple.seq` tower.  The two `StringifyContract`s thread from `blockC_concat`'s two
stringify slots (`strL`/`strR`) into `cblock`'s obligation — wiring gap-1 into gap-3
exactly as `StrConcatCBlockResid` carries them as hypotheses.

We state the composer over abstract stage boundaries `A0 B0 E S1 S1' S2 S2' P V Q`
(the concrete predicates are `EvalEntry`/`TwoSubReturn`/`ConcatMallocPre…`/`EvalExitD`)
so the file remains pure algebra; the caller instantiates them from the landed halves. -/
theorem binArmStrResid_of_cblock {A0 B0 E' E S1 S1' S2 S2' P V Q : Config → Prop}
    (blockA : Triple A0 B0)            -- blockA_binaryArm: EvalEntry → blockB entry
    (blockB : Triple B0 E')            -- blockB_binary: → TwoSubReturn post
    (disp : Triple E' E)               -- dispatch + str-branch → concat arm entry
    (strL : Triple S1 S1') (strR : Triple S2 S2')
    (segL : Triple E S1) (segR : Triple S1' S2) (segP : Triple S2' P)
    (cblock : Triple P V)              -- concatCBlockTriple_of: C-block P → value_str post
    (blockD : Triple V Q) :            -- blockD_v_rec: → EvalExitD
    Triple A0 Q :=
  Triple.seq blockA
    (Triple.seq blockB
      (Triple.seq (blockC_concat disp strL strR segL segR segP)
        (Triple.seq cblock blockD)))

/-! ## `ConcatDispatchResid` — the ONE named honest residual

The `disp` slot of `blockC_concat`/`binArmStrResid_of_cblock`: the operator-dispatch +
str-kind branch span from the `blockB_binary` post to the concat arm entry.  Named as a
`Config → Prop`-boundary Triple residual (the caller supplies concrete `B`/`E`).  Its
honest machine content is the block-reflected dispatch chain `0x8000351c → 0x80003888`
(the str-kind twin of `evalAddChain_run`, kind load = 3 instead of 2) followed by the
taken `beqz → 0x80003a20`.  Left as the one named residual (not a hand battery); logged
in `experiments/observations.md`. -/
def ConcatDispatchResid (B E : Config → Prop) : Prop := Triple B E

/-- `blockC_concat` restated with the dispatch span exposed as `ConcatDispatchResid`. -/
theorem blockC_concat_of_dispatchResid {B E S1 S1' S2 S2' P : Config → Prop}
    (hdisp : ConcatDispatchResid B E)
    (strL : Triple S1 S1') (strR : Triple S2 S2')
    (segL : Triple E S1) (segR : Triple S1' S2) (segP : Triple S2' P) :
    Triple B P :=
  blockC_concat hdisp strL strR segL segR segP

#print axioms concatStringifySpan
#print axioms blockC_concat
#print axioms binArmStrResid_of_cblock
#print axioms ConcatDispatchResid
#print axioms blockC_concat_of_dispatchResid

end Vsa.Sim
