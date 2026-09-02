# Write-log SMT probe: an exec-arm frame supplier field, ENCODE-GAP → UNSAT

Date: 2026-09-02. Tools: Z3 4.15.4 (`-in`, ALL logic). Harness:
`scripts/writelog_smt.py` (+ generated `experiments/smt/writelog/q_*.smt2`).
Whole probe runs in <0.2s.

## Thesis under test

The reason exec-arm supplier fields hit ENCODE-GAP is NOT that the Sail step is
unencodable — it is that we never emitted the arm's WRITE-LOG as SMT. Each arm's
instructions are concrete (pinned bytes / disasm), and block-reflection
(`Vsa/Sim/BlockMem.lean`) ALREADY computes the arm's effect as a write-log

    wlogM / writeLog : List WEntry   where   WEntry = Nat × Nat × BitVec 64
                                             (addr, width, data)

folded over the entry memory by `applyW`/`writeLog` (BlockMem.lean:386-396). The
per-width store image `(a,8,d) ↦ writeMap8 m a …` is eight consecutive byte
inserts. Emitting that list as SMT array-stores over a symbolic input memory
yields the arm's post memory as a small closed formula; Z3 then checks
`machine-post ⟹ goal`, exactly as the bounded copy-probe
(`experiments/smt/bounded/gen_probe.py`, BOUNDED-PROBE.md) did for the ValueRepr
COPY readback — which was itself a hand-written write-log of copy stores.

## Arm chosen (shallowest exec supplier field that ENCODE-GAPs)

The `ExecS.brk` / `ExecS.cont` register-only leaf's **`ExecLeafMemPin`** field —
the memory-frame obligation the `ExecCaseGeom` widener must establish
(`Vsa/Sim/ExecBrkCont.lean:212`; consumed via `ExecLeafWidenP` in
`Vsa/Sim/rows/ExecCaseGeom.lean`). This is the exec twin of the eval leaves'
`LeafMemPin`, and the file's own comment records that the *plain* universal
`Widen` over bare `ExecExit` is "provably UNDERIVABLE" (the wave-48c machine
obstruction) — i.e. it is a genuine ENCODE-GAP field, currently supplied only by
restating it at a PINNED exit family.

### The arm's write-log (from block-reflection / the `exec_stmt` prologue)

The `exec_stmt` prologue lowers `sp` by 176 and spills ra/s0/s1/s2/s3 with five
8-byte `sd`s (`es_off168..es_off136`, ExecBrkCont.lean:88-106). The arm itself is
`li a0,N` (a register write, no memory) and the epilogue is five `ld`s + `addi` +
`ret` (all memory-pure). So the ENTIRE entry→exit memory delta is the 5-entry
write-log, every entry inside the stack window `[SL.lo, sp)`:

    log = [ (sp-8 , 8, r  )   -- sd ra ,168(sp')
          , (sp-16, 8, v8 )   -- sd s0 ,160(sp')
          , (sp-24, 8, v9 )   -- sd s1 ,152(sp')
          , (sp-32, 8, v18)   -- sd s2 ,144(sp')
          , (sp-40, 8, v19) ] -- sd s3 ,136(sp')
    m = writeLog m0 log

## Encoding sketch

* `Mem = (def : Array Int Bool, val : Array Int (BV 8))`, `m[a]?=some b ↦
  (select def a) ∧ (select val a)=b` (identical to the working QF_ABV model in
  `gen_probe.py`).
* `writeMap8 m a d` ↦ eight `(store … (+ a j) …)` on `def` (to `true`) and `val`
  (to a fresh symbolic BV8 — the data value is IRRELEVANT to a FRAME obligation;
  only WHERE we wrote matters). The 5-fold is emitted as `define-fun` array
  chains so `select` reduces.
* Layout side facts the recursor supplies: `176 ≤ sp`, `SL.lo ≤ sp-40` (window
  covers all spills).
* GOAL = `ExecLeafMemPin SL sp m0 m` (ExecBrkCont.lean:212):
  - `pres : MemExtends m0 m` = `∀ a b, m0[a]?=some b → ∃ b', m[a]?=some b'`
    (EvalSimCommon.lean:60). Negation: some `a` present in `m0` absent in `m`.
  - `agree : ∀ k, ¬(SL.lo ≤ k < sp) → m[k]? = m0[k]?`. Negation: some `k`
    outside the window where `m` and `m0` disagree (def or val).

## Z3 verdict

| field | mode         | expect | verdict | time |
|-------|--------------|--------|---------|------|
| agree | validate     | UNSAT  | **UNSAT** | 0.02s |
| agree | ctrl_window  | SAT    | **SAT**   | 0.10s |
| pres  | pres         | UNSAT  | **UNSAT** | 0.02s |
| pres  | ctrl_pres    | UNSAT  | **UNSAT** | 0.02s |

* **agree validate → UNSAT** = the memory-frame supplier field is a Z3 THEOREM
  once the write-log is emitted. The five `writeMap8` inserts all land in
  `[SL.lo, sp)`, so outside the window every byte still reads `m0` — proved as
  pure QF_ABV array reasoning in 20ms.
* **agree ctrl_window → SAT** (non-vacuity + refute-capability): narrowing
  `SL.lo` to `sp-8` puts the `sp-40` spill OUTSIDE the claimed window; Z3 returns
  a countermodel `k = sp-40` where `m` differs from `m0`. So the encoding is
  faithful — it does not vacuously prove `agree`, and it refutes when the frame
  really is violated.
* **pres → UNSAT** = presence-preservation proved: inserts never delete.
* **pres ctrl_pres → UNSAT** = the attempt to force a dropped byte is itself
  unsatisfiable — inserts CANNOT drop presence, a positive confirmation (this
  "control" is UNSAT by design, not a failed refutation).

## Conclusion — THESIS CONFIRMED

For this exec-arm supplier field, the ENCODE-GAP was the EMITTER, not a barrier.
The Sail step never needed encoding: block-reflection already reduces the arm to
a write-log of concrete `(addr,width,data)` stores, and emitting THAT as
array-stores puts the whole `ExecLeafMemPin` frame obligation into decidable
QF_ABV. Z3 discharges it (both `pres` and `agree`) in ~20ms, and the discharge
corresponds exactly to what the Lean side proves by hand — `memExtends_writeMap8`
(EvalSimCommon.lean:67) for `pres`, and the `getElem_writeMap8_disjoint` /
`*_low_miss` window-miss lemmas (BlockMem.lean:400-429) for `agree`. The
SMT proof and the Lean proof are the same object, just as in the copy case.

This upgrades the exec-arm frame fields to the same status BOUNDED-PROBE.md
established for `ValueRepr .null/.bool/.int` readback: a fast UNSAT is a
replayable proof, a SAT flags a real frame violation, and the cost is negligible.

## Honest residual — what still does NOT encode

1. **This is the FRAME half only.** The chosen field is memory-frame
   (`MemExtends` + window-`agree`), which is genuinely leaf QF_ABV. The
   surrounding `ExecCaseGeom` bundle also carries the jump-table slot pin and the
   `StoreRepr ment N A φf φc st.store` survival clause. `StoreRepr` is a
   RECURSIVE predicate over the frame/closure vectors — that is the SAME
   inductive wall BOUNDED-PROBE.md hit at `CString` (str, k=3). A bounded emit
   proves everything hanging off a fixed prefix; it CANNOT close the `StoreRepr`
   recursion. So the write-log emitter answers the frame supplier field, not the
   representation-survival supplier field.

2. **Data values are abstracted.** A pure frame goal only needs the store
   ADDRESSES, so the emitter drops the spilled register values (`r/v8/v9/…`) to
   fresh symbolic bytes. A supplier field that constrains the WRITTEN value (e.g.
   a readback of a specific spilled register, as in the copy case) would need the
   value threaded from the block-reflection register outcome (`runGM`) — encodable
   (it's a bitvector let), but not exercised here.

3. **The emitter here is hand-transcribed from the disasm.** To make this a
   general triage oracle, the write-log should be READ OFF `wlogM`/`writeLog` of
   the actual reflected block (via a `DumpSmtLib`-style extractor) rather than
   hand-listed per arm — same fold, mechanized. That plumbing is the next step,
   not a barrier: the fold is already the SMT array-store fold, verbatim.

File: `scripts/writelog_smt.py`, queries `experiments/smt/writelog/q_*.smt2`.
