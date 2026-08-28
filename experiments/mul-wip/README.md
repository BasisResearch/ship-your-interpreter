# MUL eval-case WIP (captured 2026-08-28) — NOT building, NOT in the build path

Work-in-progress `EvalE.binary .mul` row from a background agent that ran out of
budget before a green build. Preserved here so it is never lost. These files are
NOT imported by Vsa.lean and do NOT build as-is.

## State
- `EvalMulChain.lean`, `EvalMulRow.lean`, `MulTailSites.lean` — the mul row (chain
  dispatch 0x351c->0x80003834, S1/S2 store ladder, the __muldi3 seam, blockC_mul,
  evalMulSim), cloned from the sub recipe.
- `Muldi3Spec.lean` — a MODIFIED base file: adds an `o : Array String` sailOutput
  field to the muldi3 `St` invariant (needed so value_int's `sailOutput = out0`
  survives the __muldi3 call). Threaded through the tr_* lemmas.
- `Vsa.lean` — the agent's import list (for reference).
- `multail_sites.tsv` — helper table.

## Residual to finish (the reason it isn't green)
1. **Missing `Vsa/Sim/DecodeTable/BatchMul.lean`** — the two `.mul` branch-word
   decode lemmas `decode_42d81c63` and `decode_3d051a63` (the S1/S2 `bne`
   terminators) were never created, so `EvalMulChain` has `Unknown identifier
   decode_3d051a63`.
2. **Unbound `hmi2` in `EvalMulChain.lean`** (~line 674/680) — a minstret witness
   not obtained before use.

## Machine facts (verified)
- mul op token 13; op-jump-table slot base+8 = 0x80003834 (bytes b0 98 fe ff).
- Clone `sub` (not add). Value bridge needs `BitVec.mul_comm` (machine computes
  Wr*Wl). muldi3_spec at Muldi3Spec.lean:917 supplies x10 = x*y.

To finish: create BatchMul.lean (2 decode lemmas, mirror an existing DecodeTable
batch entry), bind hmi2, then build the modified Muldi3Spec + these files.
