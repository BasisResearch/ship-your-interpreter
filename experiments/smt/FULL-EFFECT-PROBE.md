# FULL-EFFECT probe — the COMPOSITION-DEFER residual is an encoder gap, not a wall

Date: 2026-09-02. Tools: Z3 4.15.4 (`z3 -in`, pure oracle); `lake env lean`
(read-only, extractor only). Files: `experiments/smt/bounded/gen_fulleffect.py`,
`scripts/autoprove.py --full-effect <field>`. Whole run < 0.1s (a handful of
~5ms Z3 queries + the landed frame/survival certificates).

## Thesis under test

`SUPPLIER-BATCH.md` sliced each exec-arm supplier field into FRAME-Z3-CLOSED +
SURVIVAL-IH-VALIDATED + **COMPOSITION-DEFER**, and reported the composition-defer
(the arm's `Triple`/`*Geom`/sub-`ExecIH` conclusion) as ∀-closed machine-step
content "out of solver scope". THESIS: that residual is NOT un-encodable — the
prior encoder only emitted the memory-FRAME slice, not the FULL arm effect. The
exit-`Triple`/`*Geom` exit relation decomposes into the SAME three branches over
the full post-config: (A) bounded-machine-effect → Z3; (B) given-sub-result →
recursor-IH hypothesis; (C) exit-Repr → the landed Houdini base/step.

## Structural decomposition (from the tree, verbatim)

The exec-arm exit relation `ExecExprGeom`/`ExecExit`/`SubExecReturn`
(`Vsa/Sim/rows/ExecRecRows.lean:115`, `Vsa/Sim/ExecEntry.lean:453`,
`Vsa/Sim/ExecExprRet.lean:111`) is a named-field bundle whose fields are EXACTLY:

| exit field | source in the machine model | branch |
|---|---|---|
| `PC = update(r+0, bit0:=0)` (ret target) | `endPCM` fall-through after epilogue | (A) |
| `x1=r`, `x2=sp`, `x18=aRet`, `minstret ∃`, callee-saved `= g R` | `runGM` register outcome | (A) |
| `x10 = StatusCode status` | the arm's `li a0,N` (in `runGM`) | (A) |
| `OutRepr σ st' = (Machine.output σ = st'.out)` | HTIF output effect (no `putchar` store) | (A) |
| memory `read64` spills, `MemExtends`, window-`agree` | `wlogM` write-log | (A)=landed frame |
| `∃φc', ValueRepr σ.mem N φc' subsret vsub` | GIVEN by the sub-call `EvalIH` | (B) |
| `∃φf'φc', StoreRepr σ.mem … st'.store` (+ survival) | recursive Repr survival | (C)=landed Houdini |

Branch (A) is entirely first-order (bitvector reg outcomes, a concrete end-PC, an
output-count counter, the write-log memory). Branch (B) is the ONE fact the arm
does not compute — it is handed by the recursor IH. Branch (C) is the recursion
that Houdini already reaches.

## The extension (`gen_fulleffect.py`)

The prior stack (`gen_probe`/`wlog_extract`/`autoprove --frame-slice-coverage`)
encoded ONLY the (A)-memory slice. `gen_fulleffect.py` adds:

* **(A1) reg+PC** — the `runGM`/`endPCM` outcome as SMT bitvector lets
  (`outPC=bvand r ~1`, `outSP=(sp-176)+176`, `outRA=r`, `outA0=StatusCode`), the
  `ExecExit` reg/PC/`a0` fields NEGATED as a disjunction. UNSAT ⇒ proved.
* **(A2) HTIF/output** — `Machine.output σ = st.out` modelled as an output-count
  `out_exit = out_entry + #putchar-stores`; the brk/cont/expr write-log has NO
  tohost store (spills land far below the HTIF window), so `#putchar = 0` and the
  count is preserved. UNSAT(neg) ⇒ the output branch of `OutRepr` closes.
* **(B) given-sub-result** — the exit `ValueRepr σ.mem N φc' subsret vsub`
  encoded with the SOURCE side an UNINTERPRETED IH-supplied
  `ValueRepr(subMem) subsret vsub` (the `EvalIH` fact) + the 24-byte buffer
  frame-agreement the arm establishes (the sub-buffer sits inside the frame,
  untouched by the epilogue) ⇒ the exit `ValueRepr`. Same copy-readback shape
  `gen_probe` closes, now with the source an IH hypothesis rather than a concrete
  value.

Each branch ships a CONTROL twin (corrupt `a0` / phantom `putchar` / drop a
buffer byte) that must be SAT — refute-capable, non-vacuous.

## Pilot results (all < 0.01s per query)

### `hSBrk` (shallowest exec-arm; a LEAF, `st'=st`, no sub-call)

    (A1) reg+PC (runGM/endPCM)        : neg UNSAT   control(corrupt a0)     SAT
    (A2) HTIF output (output=st.out)  : neg UNSAT   control(phantom putchar) SAT
    (A3) memory frame (wlogM, landed) : FRAME-PROVED (agree/pres UNSAT, ctrl SAT)
    (B)  given-sub-result             : N/A (leaf: st'=st, no sub-call)
    (C)  StoreRepr survival (Houdini) : VALIDATED (base UNSAT, step UNSAT, wall SAT)

The WHOLE exit relation is Z3/Houdini-certified: every branch UNSAT (or landed),
every control SAT. Nothing is composition-defer.

### `hSExpr` (shallowest RECURSIVE arm — (B) is a real IH hypothesis)

    (A1) reg+PC                       : neg UNSAT   control SAT
    (A2) HTIF output                  : neg UNSAT   control SAT
    (A3) memory frame                 : FRAME-PROVED
    (B)  given-sub-result vsub=null   : neg UNSAT   control SAT
                          vsub=bool   : neg UNSAT   control SAT
                          vsub=int    : neg UNSAT   control SAT
                          vsub=str    : neg  SAT    control SAT   (see below)
    (C)  StoreRepr survival           : VALIDATED (base/step UNSAT, wall SAT)

The `vsub=str` sub-result is SAT — the CString payload window at the sub-result's
pointer is free to disagree past the bounded recursion cut. Supplying the SAME
`cstring_agreeP@payload` window IH that Houdini rediscovers in branch (C):

    str + CString-payload IH cut (given by recursor/Houdini) : UNSAT

So `vsub=str` is NOT a new wall — it routes to the exact `cstring_agreeP` cut the
survival branch already provides. The recursive part of (B) IS the recursive part
of (C).

## The recursor-IH hypothesis (what (B) had to be)

For `hSExpr`, branch (B) is closed under ONE named hypothesis, precisely the
`EvalIH`-supplied conjunct of `SubExecReturn`:

    IH:  ∃ φc', PhiExtends φc φc' nc  ∧  ValueRepr subMem N φc' subsret vsub

i.e. "the sub-derivation returned a value `vsub` represented at the sub-result
buffer `subsret`". Given that + the arm's 24-byte buffer frame-agreement
(from `wlogM`), Z3 derives the exit `ValueRepr exitMem N φc' subsret vsub`. For
`vsub=str` the hypothesis additionally carries the `cstring_agreeP` payload cut
(the recursion tail) — the same cut branch (C) supplies. This is a NAMED typed
premise (`EvalIH`), exactly as the discipline's Law 2 requires for a genuine gap.

## Verdict — thesis CONFIRMED

The COMPOSITION-DEFER residual is NOT un-encodable; it was the encoder emitting
only the memory-frame slice. The full exit relation decomposes into
(A) bounded-machine-effect (Z3-UNSAT, from `runGM`/`endPCM`/`wlogM`/output),
(B) given-sub-result (Z3-UNSAT under the `EvalIH` hypothesis), and
(C) exit-Repr survival (landed Houdini base/step). Every flat branch is a Z3
query; the recursive branches route to the landed Houdini IH. No branch hits a
construct that does not encode — the `vsub=str` SAT is the SAME CString cut, not
a wall.

**Honest residual = Lean transcription ONLY.** The remaining work is to map each
Z3-UNSAT branch to its landed lemma and thread the `EvalIH` as the named premise
(`segToTriple`/`bridgeOfSeg`/`ExecRecWiden` already exist for exactly this). The
solver stack certifies the invariants + their sufficiency at bounded depth; it
does not discharge the Lean obligation (bounded UNSAT ≠ proof), but there is no
solver-side wall left in the composition.

## Reproduction

* `scripts/autoprove.py --full-effect hSBrk` — the leaf pilot (all branches closed).
* `scripts/autoprove.py --full-effect hSExpr` — the recursive pilot (B = IH hypothesis).
* `experiments/smt/bounded/gen_fulleffect.py --field <hSBrk|hSExpr> [--json]` — direct.
* Ground truth: `Vsa/Sim/rows/ExecRecRows.lean` `ExecExprGeom`; `Vsa/Sim/ExecEntry.lean`
  `ExecExit`; `Vsa/Sim/ExecExprRet.lean` `SubExecReturn`; `Vsa/Sim/BlockMem.lean`
  `runGM`/`wlogM`/`endPCM`; `Vsa/RuntimeRepr.lean` `OutRepr`/`StatusCode`.
