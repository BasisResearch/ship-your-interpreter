# Historical output-alias prefix checkpoint

The earlier all-source build passed for 1,380 modules: 2 rebuilt, 1,378 reused,
exit zero, 5.17 seconds. A separate fingerprint check found no stale or missing
objects. `loaded-proof-receipt.json` records exact source hashes, log hashes,
and the retained manifest hash.

The public declarations below report only `propext`, `Classical.choice`, and
`Quot.sound`. The retained-cache audit is copied to `loaded-axioms.log`.

| Declaration | Proved fact |
|---|---|
| `LoadedOutputAlias.program_bigStep` | Source output is one newline. |
| `OutputAliasLoaded.snapshot_loaded` | The exact finite RAM/register snapshot satisfies the complete current `Loaded` premise. No hypotheses. |
| `OutputAliasLoaded.snapshot_firstTrace` | Fourteen actual instructions from that snapshot reach the first call seam, with exact memory/GPR/output/HTIF facts. |
| `OutputAliasLoaded.snapshot_logRead` | Every logged memory lookup reduces through the proved finite initial byte interface. |
| `OutputAliasLoaded.TraceHolds.segment` | A reflected segment with proved `ChainFacts`/`ChainOK` preserves the exact reached trace state. |
| `OutputAliasLoaded.TraceHolds.jal` / `.jalr` | Actual call instructions preserve the reached trace state and set the return address. |
| `OutputAliasLoaded.TraceHolds.putchar` | The actual HTIF character store appends output while preserving GPRs and ordinary memory. |
| `writeLog_getElem?_logRead` | Computable, exact byte lookup through arbitrary finite write logs. |
| `LoadedOutputAliasMutation.expr_str_not_surviving` | Updating the aliased buffer to LF destroys its empty-string representation under the stated header/byte reads. |

`OutputAliasProgram.lean` contains the source semantics proof. The experimental
`LoadedOutputAliasSemantics.lean` is now an import-and-axiom-check wrapper.
The mutation source is unchanged. Both experimental wrappers compiled with
exit zero; their commands used the private dependency overlay and requested no
repository object files.

The new files pass the forbidden-proof-token and diff checks. The discipline
gate retains 58 earlier findings (28/18/11/1); none concern these files.
The proof ELF is unchanged. No repository `.olean` files were produced.

At this checkpoint, full execution of the dense snapshot remained unproved. The separate sparse
replay halts after 1,861 instructions with two newlines and exit zero; it is
untrusted trace evidence. The subsequent complete execution and refinement
refutation are documented in `TRACE_CERTIFICATION.md`. The hashes in this
receipt describe the earlier prefix checkpoint.
