# invgen batch report

Cases: 97.  Verdict classes:

- **candidate-mined+SURVIVED**: 54
- **no-trace-path**: 26
- **mining-silent-needs-LLM**: 17

## Contradiction shortlist (mined facts vs design-pass statement shape)

- (none: no mined fact contradicted a design-pass shape this run)

## Cluster rollups

- **env-seam**: candidate-mined+SURVIVED×13
- **error-jal-seam**: no-trace-path×19
- **io-fold**: mining-silent-needs-LLM×1
- **io-loop-fold**: mining-silent-needs-LLM×16
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
- `io_value_print` [io-fold] → mining-silent-needs-LLM
- `io_fflush` [io-loop-fold] → mining-silent-needs-LLM
- `io_fflush_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_fputc_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_fputs_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_fwrite_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_putc_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_sbprintf` [io-loop-fold] → mining-silent-needs-LLM
- `io_sflush_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_sfvwrite_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_snprintf` [io-loop-fold] → mining-silent-needs-LLM
- `io_svfprintf_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_swbuf_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_swrite` [io-loop-fold] → mining-silent-needs-LLM
- `io_vfprintf_r` [io-loop-fold] → mining-silent-needs-LLM
- `io_write` [io-loop-fold] → mining-silent-needs-LLM
- `io_write_r` [io-loop-fold] → mining-silent-needs-LLM
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
