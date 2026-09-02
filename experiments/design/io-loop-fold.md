# Cluster design — io-loop-fold (16 fields) + io-fold (io_value_print)

> **RECONCILED @ea30e22.** These 16+1 cases are machine functions on the print
> path, NOT `TermResidualsCore` census fields — they feed hCallPrint/Println/
> AssertOk (all still OPEN). Landed: io_write loop-fold (FnWriteFold / P1),
> `ValuePrintContract` structures (Fputs/Fwrite/Fprintf), `LayoutVpTableGen` vp
> jump-table pins (w44/45), snprintf %lld path (M3). The io-buffering falsity was
> RETRACTED (setvbuf _IONBF — `IoEmits` is a direct byte-equality post, correct as
> stated). Still MISSING: the flush-chain loop-folds, io_value_print dispatch,
> `IoGround`, the CallPrint* compose. T-IO-reachability-audit (prune vfprintf) still
> do-FIRST. vfprintf is a flagged hard item. See `experiments/REMAINING.md`.

**Cases.** io_write, io_write_r, io_swrite, io_putc_r, io_fputc_r, io_fputs_r,
io_fwrite_r, io_sfvwrite_r, io_sbprintf, io_swbuf_r, io_sflush_r, io_fflush_r,
io_fflush, io_svfprintf_r, io_vfprintf_r, io_snprintf, + io_value_print (io-fold).

These do NOT map 1:1 to record fields. They all feed the SAME three record
fields — `hCallPrint` / `hCallPrintln` / `hCallAssertOk` — through the native
`rows/ValuePrintContract` three contracts. So the "16 fields" are 16 machine
functions on the print call-path that must each get a callee contract so the
three native rows compose end-to-end (value_print → fputs/fwrite/fprintf →
_write_r → _write → tohost).

## (a) Amended / new statement shapes

Two shapes. First, the per-function **loop-fold contract** (io_write byte loop,
the flush loops, the vfprintf digit loop). The round-2 pilot VALIDATED this:
mining + `loopFromBody` collapses the 873-line `FnWriteFold` to a ~4-line
arithmetic residual. Restate each loop's invariant as a named-field structure
(NOT the flat `WInv` ∧-tower):

```lean
/-- io_write tohost byte loop (mined round-2, fuzz SURVIVED). One per io loop. -/
structure WriteLoopInv (a1 a2 a3 a4 : Nat) : Prop where
  guard    : a1 < a3                 -- cursor < end
  stride   : True                    -- a1' = a1+1 (a step relation, stated in the body oracle)
  entryRel : a3 = a1 + a2            -- end = start + len  (mined linear)
  cmdWord  : a4 = 0x0101_0000_0000_0000  -- per-call constant putchar command word (mined)
```

Second, the **native-print dispatch contract** feeding the three record fields.
`ValuePrintContract` already houses `FprintfContract`/`FwriteContract`/
`FputsContract` (LANDED structures). The io functions supply the bodies of
those contracts. Restate the three native rows' residuals
(`CallPrintResid`/`CallPrintlnResid`/`CallAssertOkResid`) as named-field
structures over the io-fold posts:

```lean
structure CallPrintResid (st : SpecSt) (d : Nat) (vs : List Value) : Prop where
  dispatch : ValuePrintDispatch st vs        -- value_print jump-table arm (io_value_print)
  emit     : IoEmits (renderPrint vs) st      -- the byte-fold post (tohost stream = rendered)
  frame    : PrintFramePreserved st            -- SnprintfFrameContract / StoreClosuresBounded
```

`renderPrint`/`IoEmits` are the spec-level "stdout stream equals the rendered
values" post (buffering RETRACTED — io contracts TRUE as stated,
`setvbuf _IONBF`, per the empirical-tester memory; StreamRepr cancelled). So
`IoEmits` is a direct byte-equality post, not a buffered-stream relation.

## (b) Invariants / bridges to mine — HIGHEST mining yield in the whole pass

Order of attack (from invariant-gen-plan §"Order of attack" item 1):
1. **Pure machine loops** — io_write (DONE, round-2), then the flush chain
   (__sflush_r/_fflush_r), the vfprintf digit loop, __sfvwrite_r,
   __swbuf_r. T1-T5 mining suffices; NO relational. Each: probe the loop head,
   segment on cursor-restart (`segment.py --stride`), mine `WriteLoopInv`-shape.
2. **Straight-line shims** — io_write_r, io_swrite, io_snprintf, io_sbprintf:
   short call-relay slices; T1 constants + call-splice (`callSeg`). Minimal
   mining, mostly `bridgeOfSeg`.
3. **value_print dispatch** — io_value_print: jump table `0x80019f10`, 3 blocks.
   Relational-lite (align spec Value kind → vp arm PC), like the exec brk/cont
   pilot. Grounds the 6 vparm arms (see singletons doc).

Probes: loop heads per corpus (io_write `0x8000004c`, etc.), mem window at the
tohost address `0x80001200`-area (`sd a5,-856(a6)` in io_write), the buffer
cursor regs (a1/a3). Tools: `gen_trace.py --case io_write` (built-in), then per
function.

## (c) Supplier DAG (bottom-up; the compose order)

```
tohost SEAM (htif_store_exit)          ── LANDED
io_write loop-fold (WriteLoopInv)      ── LANDED (P1 FnWriteFold; relight as structure)
io_write_r → _write                    ── LANDED shim
io_swrite → _write_r (_lseek_r NONE)   ── _lseek_r on a non-taken path? verify in slice
__swbuf_r / __sflush_r / _fflush_r     ── loop-folds, MISSING (mine + loopFromBody)
__sfvwrite_r (memchr NONE)             ── MISSING; memchr is a small callee
_vfprintf_r / _svfprintf_r             ── LARGE (28 blocks); snprintf %lld path LANDED (M3)
fputs/fwrite/fprintf Contracts         ── LANDED (ValuePrintContract structures)
io_value_print dispatch                ── MISSING (3-block jump table, easy)
    └─▶ CallPrintResid/PrintlnResid/AssertOkResid ─▶ hCallPrint/Println/AssertOk
```

Key finding: the print-path record fields (hCallPrint*) do NOT need the FULL
printf machinery — `print`/`println`/`assert` on the interpreter's Values route
through `value_print` → fputs/fwrite/fprintf with SIMPLE format strings, and the
`%lld` snprintf wrapper is already LANDED (M3). The heavy vfprintf functions
(io_vfprintf_r, io_svfprintf_r) are on the path only for int rendering, already
covered by `snprintf_lld_spec`. So io_vfprintf_r/io_svfprintf_r are likely
GRANDFATHER-blocked-but-not-needed for the three record fields — VERIFY by
tracing which io functions the three native print arms actually reach.

## (d) Proving-task decomposition (bounded, ≤1 session each)

1. **T-IO-relight** (×1): restate `WInv`→`WriteLoopInv` structure + the three
   `CallPrintResid` as named-field structures. Template: round-2
   `io_write_loop.lean` + `ValuePrintContract`.
2. **T-IO-flushloops** (×3, one per loop fn): __swbuf_r, __sflush_r/_fflush_r,
   the digit loop — mine + `loopFromBody` + back-edge `bblock_sound_bt`.
   Template: round-2 `io_write_skeleton.lean` (~4-line arithmetic residual).
3. **T-IO-shims** (×2): io_write_r/io_swrite/io_snprintf/io_sbprintf call-splices
   via `callSeg`/`bridgeOfSeg`. Template: `bridgeOfSeg` shim.
4. **T-IO-valueprint** (×1): io_value_print 3-block dispatch + the 6 vparm arms
   (shared with singletons doc). Template: brk/cont relational pilot.
5. **T-IO-compose** (×1): assemble CallPrintResid/PrintlnResid/AssertOkResid from
   the folds, discharge hCallPrint/Println/AssertOk. Template: `ValuePrintContract`.
6. **T-IO-reachability-audit** (×1, do FIRST): trace which io functions the three
   native arms reach — prune io_vfprintf_r/io_svfprintf_r/io_sfvwrite_r if
   off-path for the record fields (the %lld path is LANDED).

Bounded tasks: **≈8** (with audit T6 pruning possibly 2-3 large fns). io_write
+ shims + value_print are near-landed; the flush loops are the mineable middle.
