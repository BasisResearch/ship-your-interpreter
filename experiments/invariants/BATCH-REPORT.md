# invgen batch report

Cases: 97.  Verdict classes (after the wave-45 io machine-loop pass, 2026-09-02):

- **candidate-mined+SURVIVED**: 56  (54 + io_swbuf_r, io_sbprintf)
- **proposed-from-seed+SURVIVED**: 4  (io_fflush_r, io_sflush_r, io_vfprintf_r, io_fputs_r — S1/S3/S5 seeds instantiated with mined constants)
- **landed-skip**: 7  (io_write, io_write_r, io_swrite, io_snprintf, io_svfprintf_r, io_sfvwrite_r, io_value_print — invariant already proven; SEEDS-io triage)
- **no-trace-path / unreachable**: 30  (26 error/straight + io_putc_r, io_fputc_r, io_fwrite_r, io_fflush — dead code on this ELF's print path)
- **mining-silent-needs-LLM**: 0  (CLOSED — the 17 io cases were silent only because invgen wired no machine-loop probe; wired via gen_trace T1-T5 this pass)

## io machine-loop pass delta (mining-silent-needs-LLM: 17 → 0)

The 17 io cases were silent ONLY because invgen wired no machine-loop probe;
the relational kind-seam path (its only wired path) never applied.  This pass
wired gen_trace.py T1-T5 probes for each PC, drove the whole print chain
(println/print multi-char + println(int) forcing the snprintf→vfprintf→
sbprintf→flush→swrite path), segmented, and mined.  Resolution:
  - 7 landed-skip (already-proven invariants; no mining needed)
  - 6 reachable + SURVIVED (2 mined-outright: io_swbuf_r S2, io_sbprintf S4;
    4 proposed-from-seed with mined constants: io_fflush_r/io_sflush_r S1,
    io_vfprintf_r S3, io_fputs_r S5)
  - 4 UNREACHABLE (io_putc_r/io_fputc_r/io_fwrite_r/io_fflush — dead on every
    print driver; interp uses unbuffered _fflush_r→__sflush_r→_swrite directly)
KEY FINDING: stdout is unbuffered (main.c setvbuf _IONBF) so the flush/drain
loops (S1) FALL THROUGH with empty buffer — the mined invariant is the
degenerate-drain instance (written=0, out unchanged, _flags=0x10009 pinned),
which is a real SURVIVED fact, not a loop stride.  Candidate .lean files
elaborate axiom-clean and pass statement_fuzz --descend.

## Contradiction shortlist (mined facts vs design-pass statement shape)

- (none: no mined fact contradicted a design-pass shape this run)

## Cluster rollups

- **env-seam**: candidate-mined+SURVIVED×13
- **error-jal-seam**: no-trace-path×19
- **io-fold**: landed-skip×1
- **io-loop-fold**: landed-skip×6, candidate-mined+SURVIVED×2, proposed-from-seed+SURVIVED×4, unreachable×4
- **leaf-slot**: candidate-mined+SURVIVED×1
- **loop**: candidate-mined+SURVIVED×2
- **loop-arm**: candidate-mined+SURVIVED×36
- **oracle-no-span**: no-trace-path×1
- **str-seam**: candidate-mined+SURVIVED×1
- **straight-span**: no-trace-path×6
- **value-box-tail**: candidate-mined+SURVIVED×1

## Per-case

- `hArgsCons` [env-seam] → candidate-mined+SURVIVED
- `hArgsNil` [env-seam] → candidate-mined+SURVIVED
- `hCall` [env-seam] → candidate-mined+SURVIVED
- `hCallAssertOk` [env-seam] → candidate-mined+SURVIVED
- `hCallClosure` [env-seam] → candidate-mined+SURVIVED
- `hCallPrint` [env-seam] → candidate-mined+SURVIVED
- `hCallPrintln` [env-seam] → candidate-mined+SURVIVED
- `hInitStore` [env-seam] → candidate-mined+SURVIVED
- `hSBlock` [env-seam] → candidate-mined+SURVIVED
- `hSForStart` [env-seam] → candidate-mined+SURVIVED
- `hSVarInit` [env-seam] → candidate-mined+SURVIVED
- `hSVarNull` [env-seam] → candidate-mined+SURVIVED
- `hVar` [env-seam] → candidate-mined+SURVIVED
- `err_80002e90` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80002ebc` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_800034e4` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003950` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003b54` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003b9c` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003bc8` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003c10` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003c7c` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003cc4` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003ce8` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003d14` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003d5c` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003da0` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003de8` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003e98` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003f58` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003fac` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `err_80003fdc` [error-jal-seam] → no-trace-path — error-jal-seam: no spec seam / machine loop not wired
- `io_value_print` [io-fold] → landed-skip
- `io_fflush` [io-loop-fold] → unreachable
- `io_fflush_r` [io-loop-fold] → proposed-from-seed+SURVIVED (S1)
- `io_fputc_r` [io-loop-fold] → unreachable
- `io_fputs_r` [io-loop-fold] → proposed-from-seed+SURVIVED (S5)
- `io_fwrite_r` [io-loop-fold] → unreachable
- `io_putc_r` [io-loop-fold] → unreachable
- `io_sbprintf` [io-loop-fold] → candidate-mined+SURVIVED (S4)
- `io_sflush_r` [io-loop-fold] → proposed-from-seed+SURVIVED (S1)
- `io_sfvwrite_r` [io-loop-fold] → landed-skip
- `io_snprintf` [io-loop-fold] → landed-skip
- `io_svfprintf_r` [io-loop-fold] → landed-skip
- `io_swbuf_r` [io-loop-fold] → candidate-mined+SURVIVED (S2)
- `io_swrite` [io-loop-fold] → landed-skip
- `io_vfprintf_r` [io-loop-fold] → proposed-from-seed+SURVIVED (S3)
- `io_write` [io-loop-fold] → landed-skip
- `io_write_r` [io-loop-fold] → landed-skip
- `hSCont` [leaf-slot] → candidate-mined+SURVIVED
- `hEpilogueSpill` [loop] → candidate-mined+SURVIVED
- `hSBrk` [loop] → candidate-mined+SURVIVED
- `hAndFalse` [loop-arm] → candidate-mined+SURVIVED
- `hAndTrue` [loop-arm] → candidate-mined+SURVIVED
- `hAssign` [loop-arm] → candidate-mined+SURVIVED
- `hDivOv` [loop-arm] → candidate-mined+SURVIVED
- `hEq` [loop-arm] → candidate-mined+SURVIVED
- `hIAdd` [loop-arm] → candidate-mined+SURVIVED
- `hIDiv` [loop-arm] → candidate-mined+SURVIVED
- `hIGe` [loop-arm] → candidate-mined+SURVIVED
- `hIGt` [loop-arm] → candidate-mined+SURVIVED
- `hILe` [loop-arm] → candidate-mined+SURVIVED
- `hILt` [loop-arm] → candidate-mined+SURVIVED
- `hIMod` [loop-arm] → candidate-mined+SURVIVED
- `hIMul` [loop-arm] → candidate-mined+SURVIVED
- `hISub` [loop-arm] → candidate-mined+SURVIVED
- `hNe` [loop-arm] → candidate-mined+SURVIVED
- `hNeg` [loop-arm] → candidate-mined+SURVIVED
- `hNot` [loop-arm] → candidate-mined+SURVIVED
- `hOrFalse` [loop-arm] → candidate-mined+SURVIVED
- `hOrTrue` [loop-arm] → candidate-mined+SURVIVED
- `hSExpr` [loop-arm] → candidate-mined+SURVIVED
- `hSIfFalse` [loop-arm] → candidate-mined+SURVIVED
- `hSIfNone` [loop-arm] → candidate-mined+SURVIVED
- `hSIfTrue` [loop-arm] → candidate-mined+SURVIVED
- `hSRet` [loop-arm] → candidate-mined+SURVIVED
- `hSRetNull` [loop-arm] → candidate-mined+SURVIVED
- `hSWhileBreak` [loop-arm] → candidate-mined+SURVIVED
- `hSWhileFalse` [loop-arm] → candidate-mined+SURVIVED
- `hSeqConsAbrupt` [loop-arm] → candidate-mined+SURVIVED
- `hSeqConsNormal` [loop-arm] → candidate-mined+SURVIVED
- `hSeqNil` [loop-arm] → candidate-mined+SURVIVED
- `hStrAddL` [loop-arm] → candidate-mined+SURVIVED
- `hStrAddR` [loop-arm] → candidate-mined+SURVIVED
- `hStrGe` [loop-arm] → candidate-mined+SURVIVED
- `hStrGt` [loop-arm] → candidate-mined+SURVIVED
- `hStrLe` [loop-arm] → candidate-mined+SURVIVED
- `hStrLt` [loop-arm] → candidate-mined+SURVIVED
- `hDivCorr` [oracle-no-span] → no-trace-path — oracle-no-span: no spec seam / machine loop not wired
- `hFn` [str-seam] → candidate-mined+SURVIVED
- `vparm_VP_BOOL` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `vparm_VP_CLOSURE` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `vparm_VP_INT` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `vparm_VP_NATIVE` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `vparm_VP_NULL` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `vparm_VP_STR` [straight-span] → no-trace-path — straight-span: no spec seam / machine loop not wired
- `hStr` [value-box-tail] → candidate-mined+SURVIVED
