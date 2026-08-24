# Layer-validation experiments for PLAN-InterpSim

Small probes run before execution, one per plan risk. Files in this
directory are the artifacts; each finding lists its plan impact.

## E-census — binary recon (`disasm.txt`)
25,336 instructions, 66 mnemonics (~40 real classes after pseudo-instruction
aliasing: `mv`=`addi`, `j`=`jal`, `beqz`=`beq`, …). All planned symbols
present (`interp_run` 0x800043ec, `eval_expr`, `exec_stmt`, `malloc`,
`setjmp`/`longjmp`, `__muldi3`/`__divdi3`). **Plan holds**: Layer-0 battery
size ~40–60 lemmas; Layer-3 inventory as listed.

## E1a–e — decoder state footprint (`E1d_decode.lean`, `E1e_footprint.lean`)
`encdec_backwards` is stateful but consults only
**{misa, cur_privilege, mseccfg}** beyond `sail_model_init`'s writes
(`mseccfg` via the Zicfilp landing-pad check; `Unreachable` errors =
`readReg` on missing keys). **Plan holds**: `GoodState` needs to pin very
few registers for decode; footprint discovery by bisection works.

## E1g/h — kernel-defeq route is DEAD (`E1g_decode_rfl.lean`, `E1h_probe.lean`)
`rfl`/`whnf` cannot reduce *any* stateful model computation, even on fully
concrete states: `Std.ExtDHashMap`/`ExtHashMap` (register file, memory) are
extensional (quotient-backed) and not definitionally reducible.
**Plan amendment (Layer 0):** no `rfl`-style evaluation of stateful goals,
ever. All state reasoning goes through the Std Ext-map *lemma* interfaces
(`get?_insert`, read-over-write) driven by `simp`; canonical states are
insert-chains rewritten propositionally. Pure bitvector side goals still
close by `decide`.

## E1i — symbolic decode lemma PROVED (`E1i_decode_staged.lean`)
For arbitrary σ with the three register reads pinned by hypotheses:

```
(encdec_backwards 0x00000513#32).run σ = .ok (ITYPE (0, x0, x10, ADDI)) σ
```

closed in ~3.5 s by a *staged* discipline: (1) `simp only [encdec_backwards]`,
(2) one `simp_all` pass with the monad plumbing set (`simp_sail`, bind/pure/
run, `get`/`throw` instances, `currentlyEnabled`, `readReg`), (3) a small
`simp +decide` pass with just the matcher/backwards helpers on the reachable
path, (4) `BitVec.eq_of_toNat_eq; decide` for width-coerced residuals.
Feeding the full ~100-helper battery in one pass instead times out — the
staging is load-bearing. **Validates the Layer-0 methodology** (the M1
spike's hardest half). Note: `Decidable` synthesis fails on goals whose
bitvector *widths* contain unreduced `Int.toNat` arithmetic — route through
`toNat` equalities instead.

## E4 — mutual recursor usable (`E4_recursor.lean`)
`@EvalE.rec` generates with all 8 motives over the mutual big-step block.
**Layer 4 machinery exists**; the 40-case induction is mechanical.

## Not probed, accepted risk
- Layer 1 (Triple logic): model-independent relation algebra of the kind
  already proved in `Vsa/Machine.lean` (`Steps` determinism/confluence);
  low risk.
- Fetch through the model's memory-read chain: same Ext-map lemma-interface
  situation as E1i's register reads; covered by the M1 spike proper.
- The full `try_step` skeleton lemma: that *is* M1, not a pre-experiment —
  E1i de-risks its technique (staged simp scales linearly with reachable
  clauses; the decoder's ~200-clause chain closed in seconds).
