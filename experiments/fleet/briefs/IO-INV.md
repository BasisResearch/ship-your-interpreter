# Fleet batch IO-INV — invariant candidates for the 17 mining-silent io cases

You are in a THROWAWAY CLONE. Work here only; NEVER touch the main repo or c/.
ONE lean process at a time. NEVER `lake build` in this repo (auto-killed);
`lake env lean` only. Emulator copies in /tmp MAY be lake-built.

CASES (from experiments/invariants/BATCH-REPORT.md): io_value_print, io_fflush, io_fflush_r, io_fputc_r, io_fputs_r, io_fwrite_r, io_putc_r, io_sbprintf, io_sflush_r, io_sfvwrite_r, io_snprintf, io_svfprintf_r, io_swbuf_r, io_swrite, io_vfprintf_r, io_write, io_write_r

For EACH case, in order:
1. Read its corpus summary `experiments/corpus/<case>.md` (loop-head PCs, regs).
2. MECHANICAL FIRST: run the machine-loop mining path — `python3 scripts/invgen.py
   --case <case>` after wiring loop-head probes (mine.py T1-T5; the _write loop in
   `experiments/invariants/io_write_loop.lean` + the mining recipe in
   `experiments/invariant-gen-plan.md` round 2 are the model). Many of these will
   mine fully mechanically once probes are wired.
3. ONLY where mining stays silent (no loop reached by the .wl corpus, or
   non-loop structure): PROPOSE a candidate yourself from the landed zoo —
   few-shot models: WInv (rows/FnWriteFold.lean), WRGOk (FnWriteRFold), SWGOk
   (FnSwriteFold), the io_write artifacts. Emit `experiments/invariants/<case>.lean`
   in the same hermetic-struct idiom as the batch's KindBridge files.
4. EVERY candidate (mined or proposed) MUST be fuzzed:
   `python3 scripts/statement_fuzz.py --file <file> --prop <name> --struct <struct>`
   — record SURVIVED/REFUTED in `experiments/invariants/<case>.md`. A REFUTED
   proposal: repair once (the witness tells you what over-claims), refuzz; if
   still refuted, record the honest verdict and move on.
5. Log each case verdict to `experiments/logs/fleet-io-inv.md` AS YOU GO.

Final message: per-case table (mined-mechanically / LLM-proposed+SURVIVED /
refuted / unreachable), nothing else.
