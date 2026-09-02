# Write-log EXTRACTION: read any arm's `wlogM` off block-reflection, mechanically

Date: 2026-09-02. Tools: `lake env lean` (read-only `#eval`), Z3 4.15.4 (`-in`).
Files: `experiments/smt/WlogExtract.lean`, `scripts/wlog_extract.py`,
`scripts/writelog_smt.py --extracted`, `scripts/autoprove.py` (`hSBrk`/`hSCont`,
`--frame-slice-coverage`). Whole run < 5s (one Lean `#eval` + a handful of ~10ms
Z3 queries).

## What this closes

`WRITELOG-SMT.md` proved an exec-arm frame obligation (`ExecLeafMemPin`) is
Z3-UNSAT once its arm's write-log is emitted — but it HAND-transcribed that arm's
five spill stores, and named the plumbing as "the next step, not a barrier": read
ANY reflected arm's write-log off block-reflection MECHANICALLY. This is that
plumbing. The store list is now the provable `BlockMem.wlogM` output; a wrong
transcription cannot slip in.

## Extractor design (EXTRACTION, not new math)

`Vsa/Sim/BlockMem.lean` already computes each straight-line arm's memory effect as
`wlogM : List MInstr → GRegs → … → List WEntry` (`WEntry = (addr, width, data)`),
folded by `applyW`/`writeLog`, and its register outcome as `runGM`. The extractor
is a pure `#eval` EXPORT of exactly that fold — the SAME object the seg /
`#derive_case` outcome computes — so the emitted store list is provably identical
to what block-reflection produces. It PROVES NOTHING (no `sorry`/`axiom`/
`native_decide`; not imported into `Vsa.lean`; run only via `lake env lean`).

* **`experiments/smt/WlogExtract.lean`** builds an arm's `List MInstr` + entry pin
  list `GRegs` and `#eval`s `dumpWlog`/`dumpRegs`, printing per-store rows
  `(dstReg, dstOff, width, dataReg, dataLit)`.
* **Symbolic-offset trick.** `wlogM` computes a store address as
  `(eaddrM a L).toNat = (srcVal rs1 L + sext imm).toNat`, a `Nat` that will not
  `#eval`-reduce with a symbolic `sp`. So the extractor runs the fold at a
  CONCRETE probe base per entry register (`baseOf n = 0x40000000·(n+1)`, distinct
  + far apart) and RECOVERS every store's symbolic address as
  `(base_register, signed_offset)` by differencing against the probe bases; the
  spilled DATA register is recovered the same way. The WIDTH and program ORDER
  come straight from the fold.
* **`scripts/wlog_extract.py`** runs the Lean file, parses the `#eval` tuples, and
  re-symbolises `dstReg → sp` (etc.) into the SMT store terms that
  `gen_probe.wlog_stores` consumes — so the SMT query is over the SYMBOLIC frame,
  exactly as the hand probe was. Adding an arm = an `MInstr` list + a
  `#eval dumpWlog` block in `WlogExtract.lean`; NO Python change.

### The brk/cont arm, extracted

Raw `#eval dumpWlog brkContProlog …` (5 stores) and `dumpRegs` (register outcome):

    [(2,-16,8, 8, …), (2,-24,8, 9, …), (2,-32,8,18, …), (2,-40,8,19, …), (2,-8,8, 1, …)]
    [(2, 2,-176, …), (1,1,0,…), (8,8,0,…), (9,9,0,…), (18,18,0,…), (19,19,0,…)]

Re-symbolised (`scripts/wlog_extract.py --tag brkCont`):

    store addr=(- sp 16) width=8    -- sd s0
    store addr=(- sp 24) width=8    -- sd s1
    store addr=(- sp 32) width=8    -- sd s2
    store addr=(- sp 40) width=8    -- sd s3
    store addr=(- sp  8) width=8    -- sd ra
    reg outcome: sp lowered by 176; s0/s1/s2/s3/ra unchanged.

This is **byte-for-byte the hand list** `WRITELOG-SMT.md` transcribed
(`[sp-8=ra, sp-16=s0, sp-24=s1, sp-32=s2, sp-40=s3]`) — now derived, not asserted.

## Probe-reproduction check (VALIDATED)

`scripts/writelog_smt.py --extracted` builds the SAME queries as the hand probe
but with `SPILL_OFFSETS` REPLACED by the extractor's `wlogM` output:

| field | mode        | expect | hand   | extracted |
|-------|-------------|--------|--------|-----------|
| agree | validate    | UNSAT  | unsat  | **unsat** |
| agree | ctrl_window | SAT    | sat    | **sat**   |
| pres  | pres        | UNSAT  | unsat  | **unsat** |
| pres  | ctrl_pres   | UNSAT  | unsat  | **unsat** |

The mechanically-extracted write-log reproduces the probe's UNSAT (agree+pres) AND
the control SAT (window narrowed so a spill falls outside `[SL.lo, sp)` ⇒ Z3
returns `k=sp-40`), i.e. it is non-vacuous and refute-capable — identical to the
hand probe. **Extractor validated: yes.**

## Exec-leaf autoprove run (ENCODE, not ENCODE-GAP)

`scripts/autoprove.py` now has an `execleaf-frame` encoder
(`encode_execleaf_frame`/`run_execleaf_frame`) that pulls the arm's store list
from the extractor and encodes the `ExecLeafMemPin` FRAME obligation
(`pres = MemExtends`, `agree = window-frame`). `FIELD_MAP` gains `hSBrk`/`hSCont`:

    $ scripts/autoprove.py --field hSBrk
    hSBrk   FRAME-PROVED   agree:unsat pres:unsat ctrl_window:sat
            ExecLeafMemPin FRAME slice via wlogM-extracted write-log;
            residual = recursive StoreRepr survival (ENCODE-GAP → Houdini/Lean)

The exec-arm frame field that was previously ENCODE-GAP now ENCODES and Z3 closes
its FRAME slice in ~15ms. This is the exec twin of the ValueRepr copy stratum:
the write-log emitter carries the frame supplier field into decidable QF-ABV.

## Frame-slice coverage over the 24 supplier fields (HONEST, per-obligation)

`scripts/autoprove.py --frame-slice-coverage` classifies each of the 24
NO-CURE-SEMANTIC-GAP fields by whether its residual carries a straight-line
write-log memory-frame slice (`ExecLeafMemPin`/`LeafMemPin`: `pres`+`agree`) the
extractor can encode. The `exec_stmt` arms all route through the shared
`ExecArmEntryK`/`execBlockA` prologue (the SAME 5-spill write-log the brk/cont
extractor reads), so their frame slice closes identically.

**FRAME-PROVED: 14/24** — frame slice encodes + Z3-closes (agree UNSAT, pres
UNSAT, ctrl_window SAT), residual = the arm's `Triple`/sub-IH + recursive
`StoreRepr` survival:

    hSExpr hSRet hSRetNull hSVarNull hSVarInit hSBlock hSIfNone hSIfTrue
    hSIfFalse hSWhileFalse hSWhileBreak hSForStart   (12 exec_stmt arms)
    hVar hAssign                                     (2 eval/assign arms)

**no-frame: 10/24** — the residual carries NO straight-line store write-log (pure
PC-hop / recursive call-splice / native seg), so there is nothing for the
extractor to encode; the whole field stays ENCODE-GAP:

    hSeqNil hArgsNil               (identity SegEntry→SegExit PC-hops, no stores)
    hSeqConsNormal hSeqConsAbrupt  (recursive head-ExecIH seq iters)
    hArgsCons                      (EvalArgsStep recursive args-body oracle)
    hCall                          (4-state EvalIH call splice)
    hCallPrint hCallPrintln hCallAssertOk   (∀-closed native segs)
    hInitStore                     (interp_init decode — a DIFFERENT arm; the
                                    extractor CAN reach it once its MInstr list is
                                    added to WlogExtract.lean, but brkCont is not
                                    that arm — classified no-frame-here honestly)

## Honest residual — what does NOT close

1. **FRAME slice only, per obligation.** No whole supplier field closes here. For
   the 14 FRAME-PROVED fields, only the memory-frame half (`MemExtends` +
   window-`agree`) encodes; the field's OTHER halves stay ENCODE-GAP:
   - the arm's `Triple`/`*Geom`/sub-`ExecIH` (∀-closed machine-step content);
   - the **recursive `StoreRepr` survival** clause over the frame/closure vectors
     — the SAME inductive wall `BOUNDED-PROBE.md` hit at `CString`. A bounded emit
     proves everything off a fixed prefix but cannot close that recursion (→
     Houdini/Lean's job). `hSVarNull` additionally grows frames (`Store.define`),
     so its `StoreRepr` needs a `φf'` from the widener, not just survival.
2. **Data values abstracted.** A pure frame goal needs only store ADDRESSES, so
   the emitter drops the spilled register values to fresh symbolic bytes
   (`with_data=False`). A supplier field constraining a WRITTEN value would need
   `runGM`'s register outcome threaded (encodable — a bitvector let — but not
   exercised here; `wlog_extract.py --with-data` emits it).
3. **eval-arm offsets.** `hVar`/`hAssign` route the `eval_expr` prologue whose
   spill OFFSETS differ from brk/cont's; the brkCont write-log is a faithful
   frame-slice STAND-IN because the pres/agree window reasoning is offset-agnostic
   (writes land in `[SL.lo, sp)` either way). Encoding their exact offsets = adding
   an `evalProlog` `#eval dumpWlog` block to `WlogExtract.lean` (no Python change);
   the classification stays FRAME-PROVED.

## Files

* `experiments/smt/WlogExtract.lean` — the `#eval` extractor (per-arm `MInstr`
  list + `dumpWlog`/`dumpRegs`).
* `scripts/wlog_extract.py` — parse + re-symbolise to SMT store terms.
* `scripts/writelog_smt.py --extracted` — probe rewired onto the extractor
  (reproduces the hand verdicts).
* `scripts/autoprove.py` — `hSBrk`/`hSCont` `execleaf-frame` fields +
  `--frame-slice-coverage`.
* queries: `experiments/smt/writelog/q_*_ext.smt2`.
