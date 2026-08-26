# Exponentiation plan — collapse the InterpSim endgame to trivial table rows

Status: both top-level theorems (`term_sim`/`stuck_sim`) are STRUCTURALLY ASSEMBLED
(`TermSimAssembly.term_sim_of_cases`, `ErrorSimFull.errorSimFull`) — every constructor has a
conditional Triple and the mutual recursors compose them. What remains is DISCHARGE volume:
~50 M4 case residuals + 42 M5 error-site residuals + 3 exit-path segments + the geometry/marshalling
each carries + `env_define`/`realloc` + the M6 Layout. Grinding this case-by-case is months.

**Thesis.** Convert `O(cases × sites)` hand-proof volume into `O(1)` reusable machinery + `O(cases)`
trivial rows, where **each row is CONSTANT elaboration cost** (one small kernel `decide` + term-level
composition, per `memory/fast-reflection-rules.md`). The abstractions are the multipliers; the rows are
`#derive_case`/`by geom`/`loopStep` one-liners. No `native_decide`/`bv_decide` (kernel `decide`/`rfl` only).

**Non-negotiable:** every file obeys `memory/fast-reflection-rules.md` (the 7 laws). The invariant that
makes this "exponentiating" and not "slower" is **constant elaboration overhead per row** — enforced by a
per-file `lake env lean` timing witness; a >~10% rise or a leaf `decide` over ~2s means a stray
`simp`/search/`Int`/WF-recursion/`HashMap` crept in → revert.

---

## The abstraction stack (each layer: COLLAPSES / MECHANISM / OWNS / DEPENDS)

### L0 — `GeomFacts` (IN FLIGHT, agent owns `Vsa/Sim/GeomFacts.lean`)
- COLLAPSES: every case's geometry bundle (`*Extras`, `htableStk`, `StmtSlotPinned`, region-disjointness,
  alignment, bounds, headroom) → `by geom` (O(1) field projection).
- MECHANISM: one projected `structure GeomFacts` derived from the `Layout`; generalizes `ImageDischarge`.
- The M6 residual-unification interface: M6 provides ONE `GeomFacts`, every case projects.

### L1 — `SegEval` (reflective per-block executor)
- COLLAPSES: straight-line + branch machine decodes (M4 case tails, M5 error-sites, exit-path segs) →
  `by seg_eval` instead of hand-threaded `StepObs`.
- MECHANISM: fuel-indexed `def evalBlock : WriteLog → List MInstr → WriteLog` on the ABSTRACT write-log
  model (rule 1); `evalBlock_sound : evalBlock … = wl → Steps σ (apply wl σ)` bridging to `Machine.Steps`
  ONCE. Extends `BlockMem.block_mem_sound`/`BlockTerm` to branch terminators + a multi-block CFG fold.
  Fast-elab: rules 1-3 (first-order model, structural/fuel `Nat.rec`, one small `decide` per block,
  term-level composition — O(instrs) not O(instrs²)).
- OWNS: `Vsa/Sim/SegEval.lean` + `Vsa/Sim/SegEvalSound.lean`. DEPENDS: reuse `BlockMem`/`BlockTerm`/`BlockDecode`.

### L2 — `FrameCalc` (marshalling / frame calculus)
- COLLAPSES: entry→`ArmEntryK` and exit→`PreEpilogue` marshalling (ValueRepr copy, spill reload,
  φ-threading) → `by marshal`.
- MECHANISM: canonical write-log normal form (rule 5) so block N+1 pre = block N post syntactically →
  seams compose by `rfl`; a `marshal` tactic discharges the standard frame obligations by projection.
- OWNS: `Vsa/Sim/FrameCalc.lean`. DEPENDS: L1 + reuse `RegPins`/`SlotFrame`/`KeepRegs`/`FrameOn`/`WriteLogNF`/`PtrArith`.

### L3 — `#derive_case` / `#derive_segment` (the multiplier elaborator)
- COLLAPSES: a whole case = `#derive_case name (pc,word)-list pre post value-fn`.
- MECHANISM: meta-composes L1(`seg_eval`)+L2(`marshal`)+L0(`geom`), searches at ELAB time, EMITS A PLAIN
  TERM (rule 4 — no `simp`/`omega` in output). Generalizes Stage-D `#gen_block`.
- OWNS: `Vsa/Sim/DeriveCase.lean` (elaborator). DEPENDS: L0,L1,L2.

### L4 — `loopStep` / `callStep` combinators
- COLLAPSES: the per-iteration step contracts (`ExecWhileStep`/`ExecForStep`/`EvalArgsStep`/block-`hstep`)
  → `loopStep <seg> <branch>`; and the call seam → `callStep`.
- OWNS: `Vsa/Sim/LoopStep.lean`. DEPENDS: L1,L2.

### L5 — `HeapOps` (env_define / realloc — the one genuinely NEW spec)
- COLLAPSES: `env_define`'s composed contract (strlen+malloc+memcpy+realloc) → a `HeapArena` op-algebra;
  unblocks `Call.closure`, `assign`, `varDecl` unconditional.
- MECHANISM: a `HeapArena` invariant + allocator-op lemmas composing EXISTING `MemcpySpec`/`Muldi3Spec`/
  malloc facts; `realloc = malloc + memcpy + free-noop`. NOT reflection — real spec work, but abstracted so
  each callsite is one lemma. This is the critical-path unknown; start it EARLY in parallel.
- OWNS: `Vsa/Sim/HeapOps.lean` + `Vsa/Sim/ReallocSpec.lean` + `Vsa/Sim/EnvDefineClose.lean`. DEPENDS: reuse
  `MemcpySpec`/`EnvDefSpec*`/`EnvNewSpec`.

### L6 — error-site + exit-path reflection (M5 discharge)
- COLLAPSES: the 42 per-error-site residuals + the 3 remaining exit-path segments → `#derive_error_site`
  (each "reaches `jal runtime_error`" via `seg_eval`, composed with `errorTailHalts`).
- OWNS: `Vsa/Sim/ErrorSites.lean` + extend `Vsa/Sim/ExitPathSeg.lean`. DEPENDS: L1,L3 + `errorTailHalts`.

### L7 — assembly close (feed generated rows into the recursors)
- COLLAPSES: instantiate `term_sim_of_cases`/`errorSimFull` with the generated case-lemmas + discharge
  via `geom`/`HeapOps` → `term_sim`/`stuck_sim` conditional ONLY on `GeomFacts` + `HeapArena`.
- OWNS: `Vsa/Sim/TermSimClose.lean` + `Vsa/Sim/StuckSimClose.lean`. DEPENDS: L0,L3,L5,L6 + all case rows.

### L8 — M6 Layout + final theorem
- COLLAPSES: read the concrete `Layout L` off the binary; provide the ONE `GeomFacts` + `Loaded` facts;
  plug `term_sim`+`stuck_sim` into `Vsa.Refine.refinement`; final `#print axioms` ⊆ {propext,Classical.choice,Quot.sound}.
- OWNS: `Vsa/Sim/LayoutInstance.lean` + the final assembly in a new `Vsa/Sim/InterpSimFinal.lean`.
  DEPENDS: L0,L7.

The M5 divergence-sim + trichotomy proof are orthogonal (classical, don't reflect) — one dedicated agent,
owns `Vsa/Sim/DivergeSim.lean` + `Vsa/While/Trichotomy.lean`; DEPENDS: `Approx`/`errorSimFull` only.

---

## Dependency DAG + parallelization waves

```
Wave A (parallel, independent, START NOW):   L0(running)   L1   L5(heapops)   DivergeSim/Trichotomy
Wave B (needs L1):                           L2            L6(needs L1,L3→ start after L3)
Wave C (needs L0,L1,L2):                      L3   L4
Wave D (FAN-OUT — needs L3): the ~50 M4 case rows + 42 error rows as #derive_case one-liners  ← N-way parallel
Wave E (needs all rows + L5): L7 close        Wave F (needs L7): L8 final
```

- The SPINE (L0→L1→L2→L3) is few files, build one abstraction per agent, serial-ish. L5 + DivergeSim run
  in parallel with the spine (disjoint files, no shared deps).
- **Wave D is where parallelism pays exponentially:** once `#derive_case` (L3) exists, every case becomes a
  trivial disjoint file; fan out many agents, each owning `Vsa/Sim/rows/Eval<Case>Row.lean` etc.

---

## Coordination protocol (multi-agent, no toe-stepping)

1. **One NEW file per agent.** Each agent creates + owns disjoint file(s) under the paths above. NEVER edit
   another agent's in-flight file. The row files go in a fresh `Vsa/Sim/rows/` dir (one file per case) to
   guarantee disjointness across the Wave-D fan-out.
2. **Shared-file edits are append-only, single-line, specific-add.** `Vsa.lean` (imports) and
   `scripts/check_all.sh` (THEOREMS) are the only shared files; agents `git add <their files> Vsa.lean scripts/check_all.sh`
   (NEVER `git add -A`), appending ONE import / ONE THEOREMS line. To avoid interleave conflicts, prefer:
   the coordinator (me) does the `Vsa.lean`/`check_all.sh` integration after each agent reports its module
   name — agents leave their file self-contained and NAME the import line to add.
3. **Build-hazard mitigation (concurrent `lake` corrupts oleans + saturates the process table — root cause
   of the last restart).** Two modes:
   - SERIAL (default, safe): one build-heavy agent at a time (what the coordinator runs now). Zero collision.
   - PARALLEL fan-out (Wave D): dispatch agents with `isolation: "worktree"` (each gets its own git worktree
     + `.lake` → no olean collision), BOUNDED to ≤2-3 concurrent, each instructed "never >1 `lean` yourself".
     Coordinator merges worktrees serially (all trivial disjoint files → clean ff). Do NOT exceed the bound
     (process-table saturation is per-machine, not per-worktree).
4. **"Keep the old proof until the new is green"** (the migration invariant). A `#derive_case` row REPLACES a
   hand-proof case only after the row is green + axiom-clean; delete the hand proof in the SAME commit.
5. **Green frontier + gate every commit:** `check_all.sh` OK, axioms ⊆ {propext,Classical.choice,Quot.sound},
   AND the elab-time witness for the touched file did not regress.
6. **Avoid the current L0 work:** while `GeomFacts` (L0) is in flight, no other agent touches
   `Vsa/Sim/GeomFacts.lean` or the case it retrofits; L1/L5/DivergeSim agents work on their disjoint files.

---

## Elaboration-budget invariant (why this stays fast)

- Every LEAF is a small kernel `decide` on a first-order write-log state; every SEAM is `rfl`/lemma-application.
  Total = O(total instructions), FLAT per case — faster than the current hand-cases (which re-pay marshalling
  per site). Measured, not hoped: each abstraction file ships a `#eval`/comment timing witness; CI-style gate
  = the file's `lake env lean` time + the retrofitted-case time must not regress >10%.
- Kernel-cost guards: no `Int`/`HashMap`/`Classical.dec`/WF-recursion in any `decide`/`rfl` path (rule 2);
  states kept as `Array (BitVec)` small normal forms; one decide per block (rule 3).

## The trivialization endpoint (definition of done)

Every residual is a one-liner: geometry `by geom`, machine run `by seg_eval`/`#derive_case`, loop step
`loopStep …`, heap op one `HeapOps` lemma. `term_sim`/`stuck_sim` close conditional ONLY on
`{GeomFacts from Layout, HeapArena}`; M6 (L8) provides both from the concrete `Layout`; the final theorem is
`Vsa.Refine.refinement (termSimClose …) (stuckSimClose …)` with `#print axioms` clean.

## Risk register (what does NOT reflect — stays hand-bridged, small/bounded)

- Indirect `jalr`, the frame-marshalling seams, PMP/`tick_clock` reset quirks: small hand lemmas, not reflected.
- The non-reducible `ExtHashMap` state: SegEval NEVER touches it (stays on the write-log; soundness bridge only).
- `env_define`/`realloc` (L5): genuinely new spec; abstraction composes it but it is real work — start early.
- M5 trichotomy/divergence: classical (`Classical.em` + fuel fold), uniform but not mechanical.
- `native_decide`/`bv_decide`: BANNED everywhere (`ofReduceBool` = native trust). Kernel `decide`/`rfl` only.

---

## LIVE OWNERSHIP LEDGER (read before picking up work — avoid duplication; update when you claim/finish)

Two coders on `main`. We already duplicated DivergeSim once — CLAIM a slice here before starting it.
Committed as of `ed7b17c`: L0 GeomFacts, L1 SegEval, L2 FrameCalc, L3 #derive_case, L4 LoopStep,
L5 HeapOps/ReallocSpec + EnvDefineClose(brick1), L6 ErrorSites. term_sim_of_cases + errorSimFull +
DivergeSim/stuckSim structure all assembled (conditional on residuals).

- **CLAIMED by coder-A (interp-impl / M5+close lane):** the M5 **error-site row fan-out** (`Vsa/Sim/ErrorSiteRows.lean`,
  discharging errorSimFull's 42 residuals via `errRow`/`#derive_case`; pilot `ed7b17c` = 3 leaf rows done, ~37 remain);
  and **L7/L8 the final close** (`TermSimClose`/`StuckSimClose`/`LayoutInstance`/`InterpSimFinal`) when rows are done.
- **Presumed coder-B lane:** the M4 case-row fan-out (`#derive_case` over the ~50 term_sim cases), L4/L5 completion
  (loop-step application, env_define/realloc close), the abstraction stack.
- **UNCLAIMED / grab-and-mark:** M4 Wave-D rows; the per-iteration step contract discharges via LoopStep; the
  exit-path `InterpContSeg`/`MainErrorSeg`/`Crt0ExitSeg` decode; the M6 Layout constants.

Rule: one new file per coder; specific `git add` (never `-A`); gate `lake build` on `ps | grep '[l]ake build'` clear.

---

## PINNED FINISH LINE (from L7/L8 capstone `a10ffc7`, interpSim_conditional assembled, 173/173 axiom-clean)

`interpSim_conditional L hterm hstuck : InterpSim L` is ASSEMBLED. What remains = discharge this named bundle.
Divide it here; claim before starting.

### M4 term bundle (termSimClosed / execSeq_sim_of_cases — 50 premises)
- MAPPED to landed case lemmas: all leaf/unary/logical/add-sub-lt EvalE, EvalArgs nil/cons, ExecS
  expr/block/if×3/while/forStart/ret/retNull/brk/cont/varInit/varNull(=execVarDeclNullSim, MAPPED — capstone's
  "execVarNullSim OPEN" was a NAME miss), ExecSeq nil/cons, callAssertOk/Print/Println.
- **OPEN — coder-B lane (env_define/realloc, L5 EnvDefineClose in progress):** `hCallClosure` (crux, d<maxCallDepth),
  `hAssign` (native-store).
- **OPEN — coder-A (me):** the `EvalExit→EvalExitD` SHAPE-GAP re-landing of the 5 leaf EvalE cases (EvalRecCommon
  residual); `hEntryHalts` (M6 program-entry bridge: interp_run prologue→stmt-loop→clean-exit + Loaded↔SegEntry);
  the loop-scaffold minor premises (ForCond/ExecStep/ExecInit SegEntry→SegExit).
- MECHANICAL-pending (grab-and-mark): le/gt/eq/ne/mul/div/mod binary ops.

### M5 stuck bundle (stuckSimClosed)
- `htri : Trichotomy` residual (Trichotomy.lean) — coder-A.
- `hdivFam : DivFamily` = Corr + DivStep + entry Corr (divergenceSim interface) — coder-A.
- `herrFam : ErrFamily` = 42 per-error-site rows (13 landed: ErrorSiteRows/ErrorSiteRows2; ~29 remain) — coder-A;
  the real per-row artefact is materializing each site's segment Triple `T` (decode→#derive_case→marshal→RuntimeErrorAt).

### Final close order (capstone's recipe)
(1) loop-scaffold + hAssign/hCallClosure; (2) re-land leaf EvalE at EvalExitD; (3) hEntryHalts entry bridge;
(4) Trichotomy residual + DivStep/Corr + remaining error rows → instantiate interpSimClosed_of_families → axiom audit.
CLAIM: coder-A takes (2)+(3)+M5 bundle; coder-B takes env_define crux + M4 mechanical ops + loop-scaffold.
