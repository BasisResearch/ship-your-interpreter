# gen_fn tooling pass — landing log (stall-recovery seed)

Plan: `experiments/gen-fn-tooling-plan.md`. Session start 2026-09-01.
Conventions: one dated entry per landing, newest at bottom. Every named
residual gets a `experiments/residuals.tsv` row AT LANDING TIME.

## State at start

- Probe artifacts all present (`experiments/probe-*.lean`, `probe-mkind.diff`
  540 lines = andi+or+lh wired through BlockMem/BlockDecode/BlockTerm/LoopStep).
- /tmp/vsa-probe COW sandbox still exists (warm oleans).
- Working tree: StringifySpec.lean doc fix + observations.md (pre-existing,
  unrelated — do not revert).

## Landings

(entries appended below)

### 2026-09-01 D0 part 1 + D0b LANDED
- probe-mkind.diff applied to main tree (andi/or/lh through BlockMem/BlockDecode/
  BlockTerm/LoopStep); chain verified green + oleans regenerated (BlockMem 2.9s,
  BlockDecode 0.5s, BlockTerm 1.4s, LoopStep 1.1s); canary EnvDefSeg 1.1s green.
  observations.md entry io-contracts-buffering-falsity was already present.
- D0 part 2 (remaining 10 kinds: ori srai and srl addw sraiw srliw lui lhu sh)
  dispatched to background agent working in main tree; safety diff at
  /tmp/d0-part1-safety.diff.
- D0b: gen_code_lemmas.py extended to emit `-- discipline: allow(R6-...)` on
  generated projection towers (chunk proj ci>=3, site proj ii>=1). Generated
  Code/_write.lean (12 sites), Code/_write_r.lean (23), Code/__swrite.lean (34);
  all green ≤0.8s, discipline OK.

### 2026-09-01 D0 part 2 LANDED (9/10 kinds) — .sh obstruction found + amendment dispatched
- ori/srai/and/srl/addw/srliw/sraiw/lui/lhu all wired through the 4-file chain
  by mail-merge agent: BlockMem 3.5s, BlockTerm 1.7s, BlockDecode 1.0s,
  LoopStep 1.6s, canary EnvDefSeg 1.6s. srli decodeM row refined on funct6
  (0x00→srli, 0x10→srai), regression rfl survives. exec_lhu_bm lifted from
  probe. Real-word rfl smoke tests for all 9 + srli/lh regressions.
  block_mem_run/block_mem_sound/exec_lhu_bm axiom-clean.
- .sh BLOCKED: {1,4,8} width set hard-coded in ~8 files (see observations.md
  wentry-width-set-hardcoded). Amendment pass dispatched (width set →
  {1,2,4,8} + writeMap2 disjoint branch + .sh store rows).
- D1 FnSummary.lean LANDED (green 1.4s, axiom-clean): PCAt + FnSummary
  structure + weaken/seq/callSplice/tailJump_of_summary/tailJump. olean built.
- D2 gen_fn.py analysis+emission WORKING: CFG on all 3 pilots correct
  (_write 5 blocks + counted-loop recognised w/ tohost seam; _write_r jal+join;
  __swrite tailj+jal+join). Emits genseg-idiom arms (7 arms for _write).
  Budget formula widened to 40+36·arms+instrs+12 (measured genseg arm size —
  plan's 12/block unreachable with the established emission; no-expanded-terms
  invariant enforced by construction). Fold emission pending P1 template.
- HtifStepObs agent (putchar stepObs layer) still running.

### 2026-09-01 GoodState falsity #10 + framed layer + P1 fold drafted
- HtifStepObs agent landed the FULL putchar Step/StepObs layer (green 1.9s,
  axiom-clean) and FOUND falsity #10: GoodState.htif_tohost pins the VALUE
  (ofNat tohostAddr) but the putchar tower zeroes the register —
  machine-checked not_goodState_sigmaPutcharFinal. observations.md entry
  goodstate-htif-tohost-overpin (by agent). Amendment = presence-only ∃ v.
- Amendment VALIDATED in sandbox /tmp/vsa-probe: GoodState.lean field → ∃-form;
  ALL `case htif_tohost => rw [...]; exact hG.htif_tohost` consumer arms
  typecheck UNCHANGED (rw under non-dependent binder); only 8 direct-use sites
  repo-wide, none needing edits beyond HtifStepObs itself. Topo regen of the
  fold's 157-module closure: 125+/157 OK, 0 failures (topo runner at
  /tmp/topo_regen.py, order /tmp/regen-order.txt). DecodeTable is OUTSIDE the
  GoodState closure (588 dependents total, cheap regen).
- Vsa/Sim/SegToTripleFramed.lean LANDED (green 1.5s, axiom-clean):
  segToTripleFramed (probe lift) + FrameOK + gprGet_of_frame (31-case
  dependent-type transport) + gholds_keep_of_frame + FramedSegPre/FramedSegPost
  (named-field, th ∃-form) + segRowFramed (generic framed block row, 2 decides
  per instantiation). gen_fn block rows = instantiations of segRowFramed.
- P1 FOLD DRAFTED COMPLETE (/tmp/vsa-probe/Vsa/Sim/rows/FnWriteFold.lean,
  ~740 lines): WG/WGOk ghosts, pushBytes/putStr + take-succ lemma, BitVec
  no-wrap arith helpers, writeExitJrSeg (jr in-model), 7 chain_facts lemmas,
  WInv/WAtBne/WAtExit join structures, WriteFnPre/Post,
  wEntryTaken/wEntryFall/wIter(putchar seam)/wBackT/wBackF/wExit/wLoop
  (loopFromBody)/wTail, write_summary : FnSummary 0x8000003c. NOT yet
  verified — blocked on regen completion + GoodState re-add in stepObs
  (agent dispatched: goodstate_sigmaPutcharFinal/-Tick + GoodState clause
  after i'<2 in stepObs_tohost_putchar).
- gen_fn.py D2 status: analysis+arm emission validated (arms file green 2.3s
  in sandbox); fold emission = this hand template, to be encoded after P1
  verifies.

### 2026-09-01 P1 GREEN (main + sandbox) — write_summary landed
- Vsa/Sim/rows/FnWriteFold.lean (~800 lines): write_summary g : FnSummary
  0x8000003c (WriteFnPre g) (WriteFnPost g) — GREEN, axiom-clean
  {propext, Classical.choice, Quot.sound}, 1.49s elab in MAIN, discipline OK.
  Post: PC = ra0, a0 = len, mem = m0 UNCHANGED, sailOutput = pushBytes out0
  bytes (EXACT byte string), ra/sp/gp/s0 preserved, HTIF mailbox re-armed.
- Vsa/Sim/rows/FnWrite.lean regenerated by gen_fn (jr-in-model exit arm mode
  added; jal arms now park-at-seam, replacing bridgeOfSeg mode). 2.05s.
- GoodState amendment LANDED IN MAIN: 589-module closure regen 585 OK + 2
  genuine consumers fixed (ExitPathSeg obtain-form — green; EvalCallClosure
  PRE-EXISTING red from wave-45 SegExit revert, untouched by this session,
  not in check_all battery) + 2 skipped dependents of those.
- Gotchas found (observations.md): chain_facts silently no-ops if ANY tactic
  precedes it (chain-facts-no-op-after-have); shift_bits_left does NOT rfl-
  reduce (deep recursion) — two-step structural-rfl + closed decide idiom;
  gholds_lookup in bare `have` needs explicit (n := _); FrameOK needs a
  Decidable instance + key-list (not GRegs) parameter for closed decides;
  by_contra absent (Classical.byContradiction).

### 2026-09-01 D2 COMPLETE — gen_fn --fold reproduces the proven P1 summary
- scripts/gen_fn.py: full CFG assembler (leaders/terminator classes
  fallthrough/br-twins/j/tailj/jal-park/jr-in-model/tohost-seam), counted
  byte-store loop recogniser, budgets (≤150 instrs / ≤20 branches refusal;
  line budget), self-verify (lake env lean + sorryAx grep), and --fold:
  instantiates scripts/genfn_templates/counted_loop_fold.lean.tmpl (the
  parameterized P1 fold — 30 substitution slots computed from the analysis:
  block names, PCs, seam word/bytes/imm/regs/decode-lemma, auipc base, li+slli
  command literal). Regenerated FnWriteFold.lean is byte-identical to the
  hand-proven file modulo the doc title → the generator emits the WHOLE
  derived FnSummary with zero hand-written contract. Unrecognised loops fail
  loudly with a pointer to the model file (graceful degradation per plan).
- P2 fold agent in flight (write_r_summary; call splice via stepObs_jal +
  callSplice consuming write_summary; store/reload stack marshalling).

### 2026-09-01 P2 GREEN — write_r_summary landed (call-wrapper fold)
- Vsa/Sim/rows/FnWriteRFold.lean (~920 lines): write_r_summary g : FnSummary
  0x800104fc (WriteRFnPre g) (WriteRFnPost g) — GREEN 2.8s wall in main,
  axiom-clean {propext, Classical.choice, Quot.sound}, discipline OK
  (zero #derive_case — all segs consumed from generated rows/FnWriteR.lean).
- Shape: entry seg (segRowFramed, keep=[]) → jal SEAM (stepObs_jal
  decode_b1def0ef + obs_jal_* accessors) → P1 write_summary instantiated at
  wrWG1 (m0 := wrM1 = writeLog of the REIFIED 3-store entry log; ra0 :=
  0x80010524; sp0 := wrSpE; s00 := reent) → beq-fall arm (len ≠ -1 from the
  hiram bound, no extra ghost) → epilogue seg with lds := the writeMap8 store
  images; ld readback via getElem_writeMap8_k + sext_reassemble; sp restore =
  PtrArith.sp_dec16_restore. gp pinned CONCRETE 0x8001b510 (prompt's 0x8001b530
  was wrong; verified from disasm _start + errno@0x8001ba08 - 1272).
- Code/pin transport onto wrM1: wrM1_getElem_lo (3-store peel) + generated
  per-byte rebuilds writeLoaded_of_agree_lo (48 bytes) /
  write_rLoaded_of_agree_lo (92 bytes) — scriptable, gen_fn can emit.
- GOTCHAS (new, hard-won):
  (a) `rfl` on `writeLog (wrM1 g) segLog = wrM1 g` NATIVE-overflows the
      unifier (unfolds wrM1 on both sides into ExtHashMap internals). Fix:
      collapse segLog to [] via a per-seg rfl lemma FIRST, then writeLog_nil.
  (b) branch-guard `show` through mkLine (write_rX0524F li+beq) native-
      overflows; seg_guard_close's simp-set works but its `<;> decide` tail
      cannot close guards over SYMBOLIC pins (len) — inline the simp-set, then
      rw the computed a5 literal + beq_eq_false_iff_ne + the len≠-1 fact.
  (c) minus-K sp arithmetic: PtrArith already has sext_ff0_toNat/ptr_sub_toNat/
      ptr_addoff/sp_dec16_restore — REUSE; the kernel gotcha is documented in
      its header (simp toNat_add+toNat_ofNat+big-literal+omega dies).
- No named residuals created; WRGOk carries only static Pre side conditions
  (buffer mirror of P1's WGOk + sp window/align + buf/stack/errno
  disjointness + concrete-gp pin + both code regions loaded).

### 2026-09-01 P3 GREEN — swrite_summary landed (tail-`j` seam; FINAL pilot)
- Vsa/Sim/rows/FnSwriteFold.lean (~825 lines): swrite_summary g : FnSummary
  0x8000efd4 (SwFnPre g) (SwFnPost g) — newlib __swrite, GREEN ~5.7s wall,
  axiom-clean {propext, Classical.choice, Quot.sound}, discipline OK
  (zero #derive_case — segs consumed from generated rows/FnSwrite.lean;
  F-twin entry arm + tail arm only; the _lseek_r append arms f024/f044 pinned
  off by SWGOk.append_off).
- THE POINT — the tail-`j` seam works exactly as designed: body =
  Triple.seq(entryArm, tailArm) landing at (PCAt 0x800104fc ∧ WriteRFnPre
  (swWRG g)); splice = `tailJump_of_summary body (write_r_summary (swWRG g))
  (fun _ h => h)`; SwFnPost g := WriteRFnPost (swWRG g) BY DEFINITION — the
  target returns FOR the caller, no suffix, no re-expression of the post.
  Marshalling INTO WriteRFnPre = one structure literal (ok := swWRG_ok, regs
  via gholds_lookup + addi0_env/sext_reassemble/sp_dec48_restore rewrites,
  mem via `rw [h1.mem]; rfl` onto swM2).
- WIDTH-2 lanes (first exercise of the mkind-lwu/lh/sh amendment in a fold):
  lh MemFacts = ⟨⟨lo, +2 hi, htif DISJUNCTION, %2⟩, pin0, pin1⟩ (two bare
  pins, not an LPins2); sh MemFacts = flat 4-conj with tohostAddr+16 ≤ addr
  (stores demand above-HTIF; forced SWGOk.fp_htif — FILE struct must sit
  above the mailbox, true for newlib .data __sf). sh log entry = (addr, 2,
  val); writeLog width-2 case = raw insert-insert, peeled by
  getElem_writeMap2_disjoint directly.
- GUARD SURPRISE (better than P2): the bnez guard over the 8-instr entry
  chain closed by a plain `show (bytesVal MKind.lh [fl0,fl1] &&&
  sign_extend 0x100#12 != 0#64) = false; rw [append_off]; decide` — the deep
  defeq through 8 mkLines did NOT overflow (P2's overflow was the li+beq
  COMPUTED-arith shape, not chain depth). No seg_guard_close simp-set needed.
- Probe file experiments/probe-swrite-fold.lean: every computed outcome
  (both logs incl. the lui/addi mask term `sext(0xfffff +++ 0x000) +
  sext(0xfff)`, all readback regs, both writeLog image shapes, the guard) rfl-
  verified BEFORE the fold — zero guessed-form misses again.
- Transports: swriteLoaded_of_agree_lo python-emitted (136 bytes, 3 chunks);
  P2's writeLoaded_of_agree_lo / write_rLoaded_of_agree_lo REUSED verbatim on
  swM2_agree_lo (theorems are memory-generic — emit once per Code module,
  reusable in every downstream fold).
- One new-in-kind gotcha: WRGOk-at-(swWRG g) omega goals see OPAQUE
  projections ((swWRG g).sp0) — `show` the g-projected statement first
  (structure-literal projection is defeq), then omega.
- No named residuals; SWGOk carries only static Pre side conditions (P2's
  buffer/stack/errno mirror + FILE window pins fl0/fl1/fd0/fd1 + fp
  htif/hi/align/stack-disj/buf-disj + append_off guard equation).

### 2026-09-01 P2 + P3 GREEN — all three pilots landed
- P2: rows/FnWriteRFold.lean write_r_summary (913 lines, 2.8s, axiom-clean,
  ZERO residuals) — jal seam via stepObs_jal, P1 spliced at m1 = writeLog m0
  (3-store spill/errno log), spilled-ra/s0 read back via PtrArith + probe
  idiom, per-byte code transports python-emitted, gp pinned 0x8001b510
  (verified from _start, brief's 0x8001b530 corrected by agent).
- P3: rows/FnSwriteFold.lean swrite_summary (825 lines, 5.7s, axiom-clean,
  ZERO residuals) — THE tail-j seam: tailJump_of_summary consumes
  write_r_summary (SwFnPost := WriteRFnPost (swWRG g) BY DEFINITION — the
  target's exit IS the caller's exit); append path pinned off via append_off
  FILE-flag static; lh/sh width-2 lanes exercised end-to-end (fl/fd halfword
  pins, sh flags write-back in the footprint).
- All wired: Vsa.lean imports + check_all THEOREMS (segToTripleFramed,
  segRowFramed, tailJump_of_summary, stepObs_tohost_putchar,
  goodstate_sigmaPutcharFinal, write_summary, write_r_summary,
  swrite_summary). Discipline rule R9 (scoped, gen_fn allow-stamped).
  Remote pre-build in flight; final gate = rbuild check.

### 2026-09-01 EXTENDED MANDATE (t1-t6) — t6 LANDED, t4 already done, t5 done by lead
- Plan b REWRITTEN mid-run: item 0 CANCELLED (io-buffering-falsity-RETRACTED
  — main.c:155 setvbuf(_IONBF): stdout UNBUFFERED, wave-44 contracts TRUE as
  stated, empirically confirmed via lean_riscv_emulator). Two-run contract:
  t1-t6 tooling tail belongs to THIS run. NEVER build in c/ (proof ELF
  sha256-guarded).
- t6 LANDED: experiments/gen_assembly_skeleton.py parses TermResidualsCore
  (62 fields + supplier doc notes; local-notation capture needed for SpecSt)
  → Vsa/Sim/rows/AssemblySkeleton.lean (Skel<Field> hole abbrevs +
  termResidualsCore_of_skeleton total assembler — elaborates GREEN, proving
  hole≡field for all 62 TODAY) + experiments/assembly_skeleton.tsv work-list.
  Wired into Vsa.lean; discipline OK.
- t4 was already landed this run (D0b: gen_code_lemmas.py allow-emission).
- t1 (repack tactic, Vsa/Sim/RepackTac.lean) + t2 (genseg framed/avoid →
  bridgeOfSegFramed emission) + t3 (scripts/gen_transport.py per-byte
  transport emitter) dispatched to two agents.

### 2026-09-01 t1 GREEN — repack marshaller (Vsa/Sim/RepackTac.lean)
- `repack h₁, h₂, …` tactic LANDED: field-matching bundle→bundle metaprogram
  over the R6/R7 named-field `structure … : Prop where` bundles. Whnfs the
  goal (default transparency → abbrev-wrapped + parameterized bundles reduce)
  to a structure app, builds the constructor with one synthetic-opaque mvar
  per field TAGGED with the field name, then for each field tries the whole
  hypothesis + every hypothesis projection (declaration order, first defeq
  wins, probe via withoutModifyingState then commit). Unmatched fields stay
  as `case <field> =>` goals; ZERO matches with ≥1 hypothesis = throwError
  (loud-failure rule from the chain-facts-no-op-after-have lesson — pinned
  in-file by a #guard_msgs negative test).
- Demos (all in-file): A = synthetic superset→subset, fields RENAMED +
  reordered + ∃-typed + abbrev-wrapped goal, one `repack h` (axiom-FREE);
  B = FramedSegPost → thinner reordered RepackSegOutcome carrier (the live
  gen_fn block-handoff shape), one `repack h`; C = WInv→WAtBne-style hop
  where kle/klt20 are light rewrites of klt → left as tagged goals, closed
  manually (the leftover-goals contract). B/C axioms exactly
  {propext, Classical.choice, Quot.sound}.
- Elab: 1.0s total file (`lake env lean Vsa/Sim/RepackTac.lean`), discipline
  OK (9 rules). NOT wired into Vsa.lean yet (tool file, imports only
  SegToTripleFramed for the demo).
- Scope note (documented in header): non-dependent flat Prop bundles — all of
  the repo's; matching is by TYPE not field name; hypothesis-side fields use
  getStructureFieldsFlattened(no subobjects), goal side must be flat (no
  `extends`).
- Next instantiations (this run): crux-marshal(5), stagepre-marshal(1),
  bridge-twin(2), SqEntry/noneval twins.

### 2026-09-01 t2 GREEN — genseg `framed = true` / `avoid = [..]` (bridgeOfSegFramed emission)
- `scripts/genseg.py`: jal arms accept `framed = true` + `avoid = [2, 8]`-style
  (the ABI-preserved reg indices the span writes). When framed,
  `emit_jal_row_framed` emits a `bridgeOfSegFramed`-based row mirroring
  `rows/ConcatStringifyRArg.lean` exactly: per-arm restricted avoid-set
  `def <name>Avoid (R) : Bool := Vsa.Alloc.AbiPreserved R && !(R == Register.xN) && …`,
  the same have+`decide` idiom (hkeys/hwf/hnoiseP/hAvoidP), the
  `Bool.and_eq_true` peel for `P → AbiPreserved` (k-fold, one `.1`-wrap per
  avoid entry), and the `obtain … := bridgeOfSegFramed …` splice; the written
  regs' new values stay EXPOSED in the `GHolds` post bundle.
- `_check_abi_writes` DOWNGRADES under framed: every ABI-preserved write must
  be listed in `avoid` (hard-error naming the missing sites otherwise); the
  unframed hard-error still fires (re-verified on concatStringifyRArg.toml).
  The check map was widened from s0..s11 to the REAL `Vsa.Alloc.AbiPreserved`
  set (+ sp/gp/tp = x2/x3/x4) — the old map would have let an sp-writing span
  through to the silent-sorryAx decide failure. ARM_SPEC + module doc updated;
  framed default imports add Vsa.Sim.BridgeSegFramed.
- Regression artifact: `scripts/arms/writeRPrefixFramed.toml` = the REAL
  `_write_r` prologue 0x800104fc→0x80010520 ▷ jal _write@0x8000003c,
  avoid=[2,8] (NOT the planned [8]: the span's `addi sp,sp,-16` writes sp,
  which IS AbiPreserved — avoid=[8] is rejected by the downgraded check, and
  its `WrChainAvoids` decide would be false). Pins in first-use order
  a1 sp s0 a2 a0 a3 ra gp (planned list missed s0 — `sd s0,0(sp)` reads it;
  matches FnWriteR.write_rX04fcL). Emitted file verified `lake env lean` green
  1.2s, axioms exactly {propext, Classical.choice, Quot.sound}, discipline OK
  (9 rules); .lean DELETED per brief (P2 fold owns the span), TOML kept.
- CAVEAT (see observations.md `bridge-row-ra-pin-unfillable-hRaOut`): this
  span reads `ra`, so the bridge row's `hRaOut` hypothesis is unsatisfiable —
  the artifact exercises the emission path, not a consumable row.

### 2026-09-01 t3 GREEN — scripts/gen_transport.py (per-byte code/pin transport emitter)
- `python3 scripts/gen_transport.py <fn-symbol>... [-o] [--check]` promotes the
  P2/P3 ad-hoc python-emitted transports to a real generator: for each symbol
  it emits `Vsa/Sim/rows/Transport<Fn>.lean` with
  `<fn>Loaded_of_agree_lo : (∀ j < tohostAddr, m'[j]? = m[j]?) → <Fn>Loaded m
  → <Fn>Loaded m'`, built per-byte EXACTLY like the hand-landed models
  (obtain the chunked byte-conjunction, rebuild each fact as
  `(hlo 0x<addr> (by decide)).trans h<i>`; single-chunk = flat pattern,
  multi-chunk = one nested `⟨…⟩` per chunk). Parsing reuses
  `experiments/gen_code_lemmas.py`'s own `parse`/`lean_ident`/`CHUNK`
  (imported), so conjunct order always matches the generated `<Fn>Loaded`
  layout. Hard-errors if any code byte ≥ tohostAddr (the `by decide`s would
  be false). `--check` self-verifies via `lake env lean`; `-o` prints to
  stdout.
- Emitted lemmas live in `namespace Vsa.Sim.Code` (beside the predicates), so
  they CANNOT collide with the fold files' landed local copies in `Vsa.Sim`.
- Validated on `_write`: `Vsa/Sim/rows/TransportWrite.lean` KEPT (uncommitted,
  not wired into Vsa.lean), green 0.7s, axioms exactly
  {propext, Classical.choice, Quot.sound}, discipline OK (9 rules; no R6
  towers — the obtain/rebuild shape needs no allow markers). Multi-chunk
  shapes exercised via `_write_r` (2 chunks) + `__swrite` (3 chunks), both
  green + axiom-clean (verified from /tmp, files not kept).
- DEFEQ-COMPAT CHECKED vs FnWriteRFold: probe imported both
  (TransportWrite.olean regenerated via `lake env lean -o`) and proved (a)
  each of `Vsa.Sim.Code.writeLoaded_of_agree_lo` /
  `Vsa.Sim.writeLoaded_of_agree_lo` inhabits the common stated type, and (b)
  `@generated = @landed := rfl` (type-level defeq + proof irrelevance). Same
  statement shape; the fold files keep their local copies FOR NOW — dedup
  (reseat FnWriteRFold/FnSwriteFold on Transport* imports and delete the 3
  local copies) is a later cleanup.

### 2026-09-01 t1/t2/t3 LANDED — extended mandate COMPLETE; final gate in flight
- t1: Vsa/Sim/RepackTac.lean `repack` tactic (field-TYPE matching bundle→bundle
  marshaller; loud-failure contract pinned by #guard_msgs negative test; demos:
  synthetic reorder/rename, FramedSegPost→thin carrier, WInv→WAtBne-style with
  leftover goals). Wired into Vsa.lean. Next instantiations: crux-marshal(5),
  stagepre-marshal(1), bridge-twin(2), SqEntry/noneval twins.
- t2: genseg framed=true/avoid=[..] → bridgeOfSegFramed emission (ABI check
  widened to full AbiPreserved incl. sp/gp/tp — old s0..s11 map would pass
  sp-writing spans to silent sorryAx); regression TOML
  scripts/arms/writeRPrefixFramed.toml; caveat bridge-row-ra-pin-unfillable-
  hRaOut logged (ra-reading spans need a dropKey-1 bridge variant).
- t3: scripts/gen_transport.py (per-byte <Fn>Loaded transport emitter, reuses
  gen_code_lemmas parser; rows/TransportWrite.lean kept unwired; defeq-compat
  vs the P2/P3 fold-local copies proven; dedup = later cleanup).
- EvalCallClosure red is PRE-EXISTING and OUTSIDE the build graph (lakefile
  builds Vsa.lean's closure only; file unimported since the wave-45 revert).
- FINAL GATE: scripts/rbuild.sh check (fresh sync incl. all pilots + t1-t6,
  remote lake build + check_all --skip-build) in flight with stall detector
  (first remote attempt hung at 990/1349 with zero remote lean procs; killed).

### 2026-09-01 FINAL GATE GREEN — pass COMPLETE
- rbuild check: remote full build 1352 jobs OK (all pilots + skeleton +
  RepackTac in-graph); check_all --skip-build: discipline OK (9 rules),
  stage b OK (1233 files), stage c 883/883 theorems audited (875→883: the 8
  new battery entries). check_all: OK.
- Proof ELF untouched (sha256 b146c6ed… prefix verified, c/ clean).
- Plan-a definition of done + extended mandate t1-t6: ALL met.
