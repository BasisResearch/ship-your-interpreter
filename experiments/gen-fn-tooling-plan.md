# gen_fn tooling — ONE focused Fable pass (plan a)

Goal: extend the exponentiating layer one rung, from per-seg to per-FUNCTION.
Deliverable = a whole-function summary generator (`scripts/gen_fn.py` + a thin
Lean support layer) validated by a three-stage pilot on the real HTIF output
path. After this lands, every io-callee / native-serial / m6-decode residual
becomes a minutes-scale generator run (plan b:
`experiments/post-tooling-fanout-plan.md`).

## Laws (verbatim reminders — CLAUDE.md governs; these are the ones you will hit)

- NEVER raise `maxHeartbeats`/timeouts. A timeout = wrong construction: check
  ground literals first, then more abstraction. One small `decide` per fact;
  reflect on the first-order write-log, never whnf Sail state; emit terms.
- No `sorry`/`axiom`/`native_decide`/`bv_decide`. A genuine gap is a NAMED
  typed premise with a doc comment saying what supplies it.
- Verify with `lake env lean <file>` ONLY. Never `lake build`, never LSP.
  Axioms of every new theorem ⊆ {propext, Classical.choice, Quot.sound}.
- Duplicated/mechanical work → STOP, append to `experiments/observations.md`
  (format at its top) BEFORE any workaround.
- Named-field structures for every new predicate; never anonymous ∃/∧ towers;
  never positional `.2.2.2` chains.
- WORK INCREMENTALLY: log every landing in
  `experiments/logs/gen-fn-tooling.md` (create it first; it is the
  stall-recovery seed). Any named residual you create gets a row in
  `experiments/residuals.tsv` AT LANDING TIME (format: see its header).

## Pre-flight (do all before writing code)

1. `scripts/abs_inventory.sh` — reuse by name; grep its seg index before any
   `#derive_case`.
2. Read `scripts/genseg.py` top-of-file spec + `scripts/genseg/lib.py` + one
   worked arm in `scripts/arms/`. gen_fn EMITS arm descriptions and reuses
   this library — do not duplicate its emission code.
3. Read the model files: `Vsa/Sim/EnvDefSeg.lean` (seg idiom),
   `Vsa/Sim/DeriveCallSeg.lean` (`callSeg`/`callSegConseq`),
   `Vsa/Sim/DeriveLoop.lean` (`loopFromBody`), `Vsa/Sim/DeriveCaseRow.lean`
   (`segToTriple`), `Vsa/Sim/BridgeSeg.lean` (`bridgeOfSeg`, jal seam).
4. Read `experiments/logs/` for the latest wave log conventions.

## Grounded facts (measured 2026-09-01; do not re-derive)

The HTIF output path, from `experiments/disasm.txt`:

| routine | entry | instrs | branches | calls / terminator notes |
|---|---|---|---|---|
| `_write` | 0x8000003c | 12 | 2 (beqz guard, bne back-edge) | leaf; counted byte loop `sd` to `tohost`@0x8001ad00; ret |
| `_write_r` | 0x800104fc | ~10 | — | wraps `jal _write` + errno |
| `__swrite` | 0x8000efd4 | 34 | 1 (bnez append-mode) | join at 0x8000eff8; `jal _lseek_r` on one path; TAIL-`j` into `_write_r` |

Tail-`j` into another function is a terminator kind genseg does not model as a
call: treat it as `TKind.j` with the target function's `FnSummary` spliced at
the join — this is the one genuinely new seam (name it, e.g.
`tailJump_of_summary`).

De-risk pass results (2026-09-01, all verified in-tree — REUSE, do not rebuild):

- **The HTIF leaf semantics is DONE, including the instruction-step glue**:
  `Vsa/Sim/Htif.lean` `htif_store_putchar` (model fn) +
  `mem_write_value_tohost_putchar` + `Vsa/Sim/HtifLift.lean` (the sd-step
  dispatch) — the `_write` loop's `sd` of `(0x101<<48)|byte` to
  `tohost`@0x8001ad00 appends the byte to `sailOutput`. P1's per-iteration
  fact is lemma lookups, not new work.
- **The tohost store is a SEAM, not a seg instruction** (it side-effects
  sailOutput; write-log reflection cannot contain it). The landed idiom is
  `ExitPathSeg.lean`: the seg runs UP TO and PARKS AT the store site, the
  store is an explicit step via the lift lemmas, then the next seg resumes.
  gen_fn MUST model `store-to-tohost` as its own terminator class (like jal):
  P1 = body seg parked at the `sd` + putchar step + back-edge, folded by
  `loopFromBody`. Do not try to put the `sd` inside a seg.
- **The `output' = output ++ bytes` phrasing is correct at EVERY layer**
  (empirically confirmed 2026-09-01, observation
  `io-buffering-falsity-RETRACTED`): `main.c:155` setvbufs stdout to _IONBF,
  so fputs/fwrite/fprintf write through immediately. The earlier line-buffering
  warning here was WRONG; the wave-44 contracts are true as stated. The io
  contracts' Pre pins the post-setvbuf stdout FILE state (__SNBF) — see plan
  b item 0.
- **Composition-cost evidence**: `EnvDefCompose.lean` = 8 callSeg splices in
  2.2s; `CmpDispatchSeg` = a whole dispatch ladder as ONE seg (~15 lines).
  The join-fold budget (≤2s/file) is realistic, not aspirational.
- `loopFromBody` consumers to model from: `EnvDefBridges4.lean`,
  `EnvDefMarshal.lean`, `TermBundles.lean`.
- The `value_print` layer above this pass is already landed
  (`rows/ValuePrintArms.lean`, `rows/ValuePrintContract.lean`, `vpHandler`,
  mkind-lwu) — your pilots feed it from below; do not touch it.
- **Byte pins are a scripted pre-step, not work**: code-region pins come from
  `experiments/gen_code_lemmas.py` (47 modules in `Vsa/Sim/Code/`, e.g.
  `_exit.lean` is the 6-instruction model); the ELF is
  `c/while-riscv-htif.elf`, objdump at `/opt/homebrew/bin/riscv64-elf-objdump`
  — both verified present. Generate `_write`/`_write_r`/`__swrite` modules
  before P1.
- **`loopFromBody`'s per-iteration obligation is a plain Triple** (DeriveLoop
  doc: invariant + guard-true + measure-decrease ⇒ body lands at head), so
  P1's seam-composed body (seg parked at the `sd` ≫ putchar step ≫ back-edge)
  satisfies it directly; `ExitPathSeg.lean:327-330` is the landed
  `Steps.single`-chaining model for the seam step.
- **Live toolchain baseline (this session)**: warm oleans;
  `rows/ValuePrintContract.lean` elaborates in 1.1s wall via
  `lake env lean`; `genseg.py --help` runs. The ≤2s/file budget is measured,
  not assumed.

## Deliverables (in order; each verified green before the next)

### D0. The MKind decoder mail-merge (BLOCKS EVERYTHING — do first)

`MKind` (`Vsa/Sim/BlockMem.lean`) today = {addi add sub lw lwu ld lbu sw sd sb
addiw slli srli slti slt subw auipc xori slliw}. Measured mnemonic census over
the whole io DAG (2026-09-01): MISSING kinds, by use count —
`andi`×52, `lh`×30, `sh`×15, `lui`×14, `lhu`×13, `ori`×11, `or`×5, `and`×5,
`addw`×4, `srai`/`sraiw`/`srl`/`srliw` ×1 each. Even P1 needs `.or`
(`_write`'s `or a5,a5,a4`); P3 needs `.lh`/`.sh`/`.lui`/`.and`/`.andi`.
Pseudo-ops need NO new kinds: mv/li→addi, sext.w→addiw, not→xori, negw→subw,
zext.b→andi.

**The recipe is EXECUTED, not just precedented** (2026-09-01 probe session, COW
clone at /tmp/vsa-probe — may still exist as a warm sandbox):

- `.andi` (ITYPE, one-source) AND `.or` (RTYPE, two-source clone of `.sub`)
  both landed: `experiments/probe-mkind.diff` (351 lines, 4 files). Measured
  per-kind chain: BlockMem ~3s + BlockDecode ~0.9s + BlockTerm ~1.4s +
  LoopStep ~1.3s, green + axiom-clean. Real words decode by `rfl`
  (`0x1007f693`→`.andi`, `_write`'s `0x00e7e7b3`→`.or`). Downstream canary
  (`EnvDefSeg.lean`) green. APPLY THE DIFF FIRST, clone for the remaining 11
  kinds. Olean regen: `lake env lean <file> -o .lake/build/lib/lean/<mod>.olean`
  in order BlockMem → BlockDecode → BlockTerm → LoopStep. `or`/`and` as
  constructor names cause NO clashes (probed).
- **The width-2 memory lemmas are ALSO pure clones — PROVEN**:
  `experiments/probe-lh-width2.lean` has green axiom-clean `exec_lhu_bm` and
  `exec_lh_bm` (1.2s), built on the EXISTING `vmem_read_data_two` +
  width-generic `execute_load_{unsigned,signed}_char`. Lift them verbatim.
  `sh`: `vmem_write_addr_2` exists (`MemStore.lean:1738`); clone `exec_sw`
  (`ValueSites.lean:95`) with a 2-insert map. Gotcha from the probe: the file
  needs BlockMem's exact opens (`LeanRV64DExecutable.Functions Sail
  ConcurrencyInterfaceV1` + PreSail) or nothing resolves.
- All RTYPE/RTYPEW/ITYPE char lemmas already exist in `ExecuteAlu.lean`
  (or/and/srl/sra/addw/ori — verified); shifts clone the srli/slliw
  SHIFTIOP/SHIFTIWOP rows; `lui` clones auipc's UTYPE row (uop.LUI).
- **THE P1 BODY SEG IS ALREADY GENERATED AND GREEN**: with `.or` landed,
  `genseg.py` compiled the real `_write` loop body `0x8000004c→0x8000005c`
  (lbu/addi/or/auipc, parking at the `sd` seam) straight from the arm TOML —
  `experiments/probe-writeBody.toml` → `probe-writeBody-generated.lean`,
  elaborates in 1.0s, axiom-clean row. Reuse both files verbatim in P1.
- **Byte pins verified live**: `python3 experiments/gen_code_lemmas.py _write`
  emitted `Vsa/Sim/Code/_write.lean` (12 sites), green in 0.8s.

If any remaining kind exceeds the measured ~7s chain cost by >3×, STOP and log.

Second probe round (same session) — three MORE items moved to green-artifact:
- **`exec_sh` PROVEN**: `experiments/probe-sh-width2.lean` (1.2s, axiom-clean),
  clone of `exec_sw` over the existing `vmem_write_addr_2` + `writeMap2`
  (PinW.lean already ships the sh store image). D0 has NO remaining item of
  unexecuted shape — every class (ITYPE, RTYPE, width-2 load signed/unsigned,
  width-2 store) has a green probe.
- **`exec_sd_tohost_putchar` PROVEN**: `experiments/probe-sd-putchar.lean`
  (1.0s, axiom-clean) — the P1 seam step (the `_write` console `sd` as an
  instruction-level characterization, `sigmaPutchar` post = HTIF register
  tower + `sailOutput.push`, memory UNCHANGED). Clone of `exec_sd_tohost_exit`
  with `mem_write_value_tohost_putchar`. Lift verbatim; P1 has no
  missing-lemma risk left — only the `loopFromBody` fold remains un-assembled.
- **Discipline-gate wrinkle (probed)**: generated `Code/` modules trip
  `R6-anon-projection-tower` (the 45 existing ones are ALL grandfathered).
  Before landing new Code modules, extend `experiments/gen_code_lemmas.py` to
  emit `-- discipline: allow(R6-anon-projection-tower) generated code-pin
  projections` on the flagged lines (or named-field posts). Do NOT add files
  to the grandfather list.
- Byte-level ground truth for the fmt family (objdump .rodata): 19008="true",
  19010="false", 19018="null", 192c0="%lld", 192c8="<fn %s>", 192d8="<native %s>".
  NOTE: `rows/StringifySpec.lean`'s bool-arm doc comment had true/false
  SWAPPED (fixed 2026-09-01, machine statements unaffected) — when writing
  stringify pins, trust the ELF bytes, not prose.

Third probe round — P1 is now assembly-only; P2's one gap characterized:
- **EVERY span of `_write` is a green generated artifact**:
  `experiments/probe-write{EntryTaken,EntryFall,Setup,BackTaken,BackFall,Exit}.lean`
  + the earlier body row — entry beqz both arms, setup, loop body, back-edge
  bne both arms (taken → loop head 0x4c ✓), mv/ret exit (jr terminator). All
  genseg-generated from TOMLs (also archived), all elaborate clean.
- **`try_step_tohost_putchar` PROVEN** (`experiments/probe-trystep-putchar.lean`,
  1.1s, axiom-clean): the FULL Step-level putchar transition
  (dispatch/fetch/decode/execute/postlude), incl. `sigmaPutcharFinal` and the
  6-insert-over-3-register frame adaptation. `Steps.single` on it exactly as
  ExitPathSeg does with the exit store. P1 residue = loopFromBody marshalling
  ONLY.
- **The `.lh` MKind wiring is EXECUTED** (in `probe-mkind.diff`, now
  andi+or+lh, 540 lines): inductive+decodeM+astOfM+widthOfM+bytesVal
  (sign-extend width-2)+MemFacts (2 pins + %2 align)+KindOK+instDec+the
  BIG-PROOF case threading `exec_lh_bm`+BlockTerm/LoopStep arms — green,
  real `__swrite` word `0x01059783` decodes by `rfl`, canary green. `lhu`/`sh`
  MKind wiring = the same recipe with the other two proven probe lemmas.
- **P2 gap precisely characterized**: genseg REFUSES `_write_r`'s jal span
  (writes callee-saved s0) with a correct pointer to `bridgeOfSegFramed`
  (model `rows/ConcatStringifyRArg.lean`), but has NO framed emission mode.
  D2 sub-item: add `framed = true` + `avoid = [...]` TOML options emitting
  `bridgeOfSegFramed`. Until then P2's bridge follows the hand model.

Fourth probe round — the loop-marshalling seam is CLOSED:
- **`segToTripleFramed` PROVEN** (`experiments/probe-segToTripleFramed.lean`,
  1.0s, axiom-clean): segToTriple keeping segEval_sound's frame clause AND
  sailOutput preservation (both discarded by plain segToTriple). `noiseRegs`
  (`RegPins.lean:58`) excludes the HTIF registers, so the frame clause
  preserves `htif_payload_writes`/`htif_tohost` across any body seg — the
  loop invariant's CSR thread is this ONE lemma. Land it beside segToTriple
  (and have gen_fn emit it when a span parks at a tohost-store seam).
- **Symbolic outcome readbacks reduce by `rfl` on the REAL body seg**
  (`experiments/probe-writeBody-readback.lean`): `lookupG` on the computed
  outcome gives a6 = `0x8001b058` (auipc tohost base — and `0x8001b058 +
  sext(-856) = tohostAddr` is a `decide`), a5 = `zero_extend b ||| cmdBase`
  (the SYMBOLIC putchar word), a1 = `bufPtr + 1` (loop progress). Consume via
  the EXISTING `gholds_lookup_ld` (`SegReadback.lean:104`). Every
  `try_step_tohost_putchar` hypothesis is now dischargeable from the framed
  post: rs-reads via readback (+ the ExitPathSeg rX marshalling idiom), haddr
  by `decide`, hpw/hth via the frame clause, byte pins from `Code/_write.lean`.
  The P1 loop residue is literally: state the invariant Prop, stack these.

### D1. `Vsa/Sim/FnSummary.lean` — the Lean support layer (small)

- `structure FnSummary` (named fields, `: Prop` where quantified): entry PC,
  exit condition (ret to `ra` / tail-target), the derived post as a named-field
  structure parameter, clobber set (reuse `FrameMeta.abiFrame_of_wrChain`
  shapes), memory footprint (`FrameMeta.memFrame_of_chain` shapes), sailOutput
  delta (thread via `chain_out` idiom).
- The fold combinators, ALL built from existing pieces: seq of two summaries
  (`Triple.seq`), call splice (`callSeg` around a callee `FnSummary`),
  `tailJump_of_summary` (new), `FnSummary.weaken` (consequence).
- NO new proof machinery beyond marshalling; if a fold step needs a genuinely
  new lemma, name it, doc-comment its supplier, log it, continue.

### D2. `scripts/gen_fn.py` — the CFG assembler (Python does analysis, Lean does trust)

Input: `--fn <name> --entry <pc>` (+ optional `--pin k=v` path-restriction
pins, e.g. a fixed a2/fmt). Reads `experiments/disasm.txt`.

Pipeline: extract body → partition into blocks at branch targets/joins →
classify terminators (fallthrough/br/j/jal/tail-j/ret) → emit ONE `.lean` file
into `Vsa/Sim/rows/` containing: per-block arm sections via the genseg lib, one
named-field `Post` structure PER JOIN POINT (this is load-bearing: it is what
keeps elaboration linear — never let two paths merge into a raw ∨/∃ tower),
and the top-level `FnSummary` theorem folding the blocks.

Hard budgets (enforce in the script, fail loudly):
- Emitted file ≤ 40 lines + ~12 lines/block. Expanded terms live in the
  kernel only, never in source.
- Refuse functions > 150 instrs or > 20 branches without `--pin` restriction
  (print which pins the branch conditions need). This keeps misuse impossible.
- Self-verifying like genseg: run `lake env lean` on the output + sorryAx grep,
  hard-error on failure.

Loops: recognise the counted byte-store shape (the `_write` loop: monotone
pointer, `bne` back-edge, fixed body write) and instantiate a `loopFromBody`
invariant template. Any unrecognised loop → emit a NAMED invariant hole with a
doc comment (graceful degradation, not failure).

### D3. The pilot ladder (the success gate — all three, in order)

- **P1 `_write`**: exercises entry-branch + the loop template + ret. Success:
  a derived `FnSummary` stating the output bytes appended = the a1..a1+a2
  byte string (reuse `htif_store_exit`/JmpSpec machinery if applicable —
  check inventory), ZERO hand-written contract.
- **P2 `_write_r`**: exercises the call splice consuming P1's summary.
- **P3 `__swrite`**: exercises the join structure + `tailJump_of_summary`
  (non-append path; the `_lseek_r` path may be pinned off via the `bnez` pin —
  document the pin as a precondition field).

Per-pilot criteria: green under `lake env lean`, axiom-clean, elab ≤ 2s/file,
`scripts/check_discipline.py` clean (add a discipline rule catching hand-rolled
multi-block assemblies if D2 is bypassable by hand — see CLAUDE.md "Extending
the discipline"), `scripts/check_all.sh` still fully green at the end.

## Elaboration-budget guardrails (the ONE real risk — treat as first-class)

Reflect each block on its write-log exactly as segs do now; fold at term level
with one `decide` per block; canonical normal form at every join so seams are
`rfl`. If any fold step exceeds ~2s or hits whnf depth: STOP, do not push
through — record the obstruction in the log + observations.md with the failing
term shape. A recorded obstruction on P3 with P1/P2 green is a SUCCESSFUL pass
outcome (it tells us exactly what the join fold needs); a hand-worked-around
P3 is a failed one.

## Non-goals (do not touch)

- No `RemainingWork`/`TermResidualsCore` edits, no statement amendments, no
  fan-out beyond the three pilots, no `lake build`, no new files in
  `scripts/discipline_grandfather.txt`.

## Definition of done

P1–P3 green + committed conventions: `gen_fn.py` + `FnSummary.lean` +
3 pilot row files + log + ledger rows + (if created) observations entries.
Final report: per-pilot elab times, emitted line counts, and the named list of
any residual holes — these numbers gate plan b.
