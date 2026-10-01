# Abstraction-discovery round 6: the WHILE→RV64 compiler (2026-10-01)

Branch `exp-R6`, from `exponentiate-next` 7b26c89d (PR #14 snapshot 4). Target: `Vsa/Compiler`
(83 files, 19,478 lines), the compiler for the full language, its subset predecessor, the checked
allocation-cost variant, and their correctness proofs. The directory came from main's tool lanes
(97 commits over Sep 27–29) and has not been through a round.

## 0. Primary measure (stated before the bake-off)

The directory costs 330 user-CPU seconds as single-file compiles (import floor ≈ 0.9 s per file,
≈ 70 s in total). Excluding three modules dominated by kernel evaluation of concrete programs
(§1c), no module exceeds 14 s, and profiles of the rule-case modules split evenly between `simp`,
tactic execution and kernel checking. Time is not where the cost is; lines are. The primary
measure is therefore **agent effort: proof-body lines of statement-identical re-proofs of
held-out theorems, plus failed compiles**, with the abstraction's setup lines counted separately
(break-even). Secondary: user-CPU seconds of touched modules; a candidate that wins on lines may
lose at most 10% of the touched modules' time.

## 1. Census

Data: per-module user-CPU of a single-file compile (`LEAN_NUM_THREADS=1 lake env lean
-Dbackward.isDefEq.respectTransparency=false`, copies outside the repo, load 7–11 on 32 cores); a
meta script over the `Vsa` environment listing every constant of `Vsa.Compiler.*` with kind,
source range, conclusion head (after stripping ∀/→; for `=`/`↔` the head of the left side) and
membership in the constant closure of the roots (§11).

Roots: `compileG_correct`, `compileChecked_correct`, `compile_correct`, every declaration of the
`whilec` executable (`WhileC.lean`, the only user of the compiler outside the directory), and the
two example-program modules `CompiledG` and `WhileWl` (their theorems are results, kept).

### 1a. Reachability

Every module but one has constants on the path. Off-path declarations inside live modules total
534 lines, mostly lemmas: `cseq_next`/`cseq_targets` (100, CompileFacts), `WP_mono` and four `WP_li*`
variants (87), `wf*_sound` (55, Check), `cstmt_length_le` (41), `strs*` (24), `cseq_tail` (14).
(The parser's `partial def`s appear off-path only because their bodies live in compiler-internal
constants; they are used.) The directory is not dead weight; the cut is small and was left to the
rollout.

### 1b. Clusters

1,162 of 1,991 theorems are on the path. Clustered by conclusion head, the directory is one large
cluster and several small ones:

| cluster | theorems | lines | files | module-s |
|---|---:|---:|---:|---:|
| K-frag: per-source-rule simulation and failure cases (`ESpec`, `SSpec`, `CSpec`, `ASpec`, `QSpec`, `FLSpec`, `SimE`, `EStuck`, `SStuck`, `CStuck`, `FLStuck`, `TSpec`, `SFail`, `SeqFail`, `Sims`, and `Reaches` in Sim*/Stuck*/Stmt*) | 153 | 5,028 | 41 | 124 (whole files) |
| K-rt: runtime-routine runs (fixed code with loops; `Reaches` with `Has`/`Keep`/memory-frame posts; RT*, PrintInt, Setup*, SimNative, WP, Run) | 56 | 2,725 | 11 | 77 (whole files) |
| layout (`Seg` splits per construct, code lengths: `Eq:List.length`, `Seg`, `*_segs`) | ≈ 90 | ≈ 400 | 20 | — |
| post algebra (`VGrow.trans`, `Within.add`, `StackKeep.trans`, `ObjAgree.trans`, `Room.*`, `MS.transport`) | ≈ 60 | ≈ 400 | 10 | — |
| K-lift: abstract machine step ↦ Sail steps (`StepsCorr`, `step_sim`) | 6 | 331 | 1 | 6.5 |
| K-dec: symbolic-field instruction decode (`Eq:EStateM.run`) | 12 | 290 | 2 | 41 |

The largest conclusion head is `Reaches` (93 theorems, 4,516 lines, 34 files). The subset compiler
(`compile`, `compile_correct`) has its own parallel route (Compile, Rel, ExprSim, CompileFacts,
StmtRel, StmtFrag, StmtCases, StmtShape, StmtT, StmtS, Correct: ≈ 3,000 lines) with the same
obligation shapes over a different invariant (`SR`/`At` instead of `MS`).

All proofs are 2–4 days old; per-case cost is flat by construction (no learning curve to measure).

Use counts of existing abstractions in this directory: machine-layer rules `stepObs_exec`,
`Fetched`, `RetireReads` 1 each (in Lift); `decodeW`/`#simp_nf` 0; reflective executors
`symRun`/`sym_run`/`symRunX`/`xrun` 0; region keys `RegionCore`/`Win` 0; arm descriptors
`ArmCore`/`ArmEval` 0. Inside the directory: `ESpec.bind` 23 uses against 85 raw `ex_bind` and
86 `reaches_mono`; `SPost.seq` 9; `WP_mono` proved and unused.

### 1c. Time

| module | user-s | what |
|---|---:|---|
| Encode | 40.8 | 18 `simp` calls of 0.5–0.75 s deciding `ext_decode` on words with symbolic fields; 2 kernel checks of 2.4 s |
| CompiledG | 25.9 | `decide +kernel` on `compileG p` length, support and cost for four example programs (kernel 22.9 s) |
| RTOps | 14.1 | runtime arithmetic/comparison routines (`simp` 5.9 s, tactic 4.6 s) |
| RTDisplay | 13.0 | display/concat routines (`simp` 2.9, tactic 3.4, kernel 2.7) |
| Checked | 12.5 | `decide +kernel` cost bound of the `while.wl` example (kernel 11.6 s) |
| 78 others | 223.9 | median 2.3 s |

The kernel-evaluation modules (38 s) run the compiler and the cost semantics on concrete programs;
they are results about examples, outside the proof vocabulary. Encode is the one proof-side time
target; its cost is the Sail decoder's `match` unfolding per instruction format.

### 1d. Profile of one instance, and obligation shapes

Profile (`run_cs`, RTDisplay; `run_entry`, SimFnEntry): `simp` 0.8–2.9 s, tactic 2.8–3.4 s,
kernel 2.7–3.5 s per module; no single tactic dominates. The cost is the number of lines a case
needs, not their speed.

Classification of the 7,544 proof lines of K-frag + K-rt (first matching pattern): segment and
position bookkeeping (`hseg.append`, `List.length_append`, `.cast (by omega)`, `posOK_le`) 8%;
driving (`wp_simp`, `reaches_mono`, `ex_bind`) 7%; register goals (`reg_simp`, `Keep.*`) 6%; post
composition and the error branch 5%; address arithmetic 3%; register-fact conversion
(`have k := has_mem h (by decide); have e := srcVal_of_has h; simp only [a0] at k e`) 2%; memory
frame 2%; field-by-field `MS` rebuild 1%; other 66% (destructuring posts, case splits on source
data, statement headers, 8–10-premise positional applications of child specs, `by omega` side
conditions: 1,292 `by omega` in the directory).

A random sample of ten members (seed 20261001): `sVarNull` (segment split, WP run, MS transport,
post), `run_storeSlot` (register facts, six address facts, WP, store relation, 12-field MS
rebuild), `tExpr` (case split, child spec), `fDecl` (segment split, child spec, failure
propagation), `noE` (recursion skeleton), `it_copy` (loop invariant, register facts,
read-over-write), `run_print'`, `run_up` (induction over the scope chain), `sBool` (WP, post),
`for_body` (child spec with ten premises, error branch, post composition). Every member contains
at least one of the obligations the laws below discharge; none consists of them only.

## 2. Laws

All five are already true as lemmas in some form; the stall is in applying them.

| law | statement | check |
|---|---|---|
| L-bind | error-or-post sequencing: `Reaches A (Err_{V,n1} ∨ Post1)` and, from every `Post1` state with `Within V V1 n1`, `Reaches B (Err_{V1,n2} ∨ Post2)` give `Reaches A (Err_{V,n1+n2} ∨ Post2)` | proved (`Room.not_within`, `ESpec.bind`); applied by hand 171 times |
| L-evolve | `VGrow ∧ Within n ∧ StackKeep ∧ ObjAgree` is reflexive and transitive with grades adding | proved per component; composed by hand in every post |
| L-layout | `Seg code pos (a ++ b) ↔ Seg code pos a ∧ Seg code (pos + a.length) b`; `PosOK` of a later point gives every earlier one | proved (`Seg.append`, `posOK_le`); 233 `.append` and 175 `posOK_le` uses |
| L-reg | registers outside a segment's write set keep their values; clobber sets compose | proved (`Keep.*`, `has_gset`); 474 `reg_simp` uses |
| L-mem | reads outside the windows a fragment writes are unchanged; windows are fixed regions | proved per instance (`rdW_upd`, `OutFrames`, `Agree`) |

## 3. Held-out suite (drawn before any candidate was built)

`abstractions/ROUND-6-heldout.json` (commit fc553c2e). Population: on-path theorems of the target
conclusion heads with ≥ 8 lines (167), stratified by size: S ≤ 25 (73), M 26–60 (51), L > 60 (43).
`random.Random(20261001)`: `sample(L,5)`, `sample(M,5)`, `sample(S,4)`; the first 3/3/2 are
primary, the rest fresh (run after the first pilots). Baseline = non-blank proof-body lines.

| case | stratum | file | body lines |
|---|---|---|---:|
| `run_cc` | L | RTDisplay | 69 |
| `walk_read` | L | SimVar | 67 |
| `sLogFull` | L | SimLogic | 62 |
| `run_leave` | M | SimBlock | 37 |
| `fIfSome` | M | StuckStmt | 32 |
| `fIfSome₀` | M | StmtS | 29 |
| `stmtT` | S | StmtT | 22 |
| `fCons₀` | S | StmtS | 20 |
| fresh `run_add` | L | RTOps | 71 |
| fresh `sim_all` | L | SimAll | 167 |
| fresh `sim_not` | M | ExprSim | 32 |
| fresh `sCall` | M | SimCallE | 46 |
| fresh `fBlockS` | S | StuckStmt | 14 |
| fresh `dp_ret` | S | RTDisplay | 7 |

Primary baseline 338 body lines; fresh 337. The draw put three failure-dual cases (`fIfSome`,
`fIfSome₀`, `fCons₀`) and a recursion skeleton (`stmtT`) in the primary set; that is what the
cluster contains.

## 4. Blind ontologists

Six agents (five seeded by random 256-character strings, one by a random dictionary sentence) got
the semantics, the census, the laws, the eight primary statements verbatim, a forbidden list (hand
`Seg` splitting and casts, `posOK_le`, manual `ex_bind`/`reaches_mono` with two-way case splits,
per-register `Has`/`Keep` threading, the `has_mem`/`srcVal_of_has` idiom, hand `.trans` chains,
field-by-field `MS`, per-construct layout lemmas, generators, SMT, "write a tactic"), the list of
unused project abstractions with use counts, and the decision-procedure restrictions. Each
returned 4–5 candidates in 100–170 s.

| candidate (as proposed) | agents | rules = laws | decided by |
|---|---:|---|---|
| G. graded error-or-post monad `Run W n Q` over an evolution preorder `Evo` (grow/within/stack/obj as one graded morphism); bridges to the frozen specs | 6/6 | L-bind, L-evolve | syntactic `refine`; grades by `rfl`/`omega` |
| S. placed-code / span judgment (`Seg ∧ PosOK` fused; one append rule; midpoints matching the generator's positions) | 6/6 | L-layout | `simp` on `++` + defeq midpoints; `omega` fallback |
| R. register row / key-register fiber of `MS` (`MS ↔ Core ∧ Keys`), write sets, reseat | 6/6 | L-reg | `decide`/`rfl` on literal register keys |
| M. region-keyed memory agreement (`Agree R m m'`), disjointness by a closed table | 6/6 | L-mem | `decide` on region kinds, `omega` on parametric bounds |
| F. failure as an absorbing set + source-side blame inversion + one arm-fails theorem over a descriptor | 6/6 | L-bind (dual) | `rcases` on blame; syntactic |
| L. list-fold loop rule for runtime routines | 2/6 | — | invariant supplied |

Variants proposed by one agent each (kept for variation): the layout predicate defined by the same
recursion as the generator (children are fields, projection instead of splitting); a
selector-indexed child projection per generator; spans with existential midpoints and a ceiling;
reflection over instruction templates with atom environments (`xfer`), reusing `symRun`; a 32-bit
register bitmask; a `Blame` inductive per construct; plans with two readings (simulation and
failure) from one descriptor.

Theories cited: graded/parametric effect monads (Katsumata), Dijkstra monads, Lawvere metric
spaces, Kripke worlds; double-entry bookkeeping and budget constraints; action additivity, the
thermodynamic arrow of time, gauge fields and fiber bundles, Noether conservation, light cones;
attribute grammars, CKY chart spans, TeX boxes and glue, finger trees and ropes, piece tables,
Allen's interval algebra, path categories; lenses and view update, 3NF decomposition, incremental
view maintenance, predicate/range locks, write-ahead logs, sharding; rely-guarantee, variables as
resource, dynamic frames, region logic, Tofte–Talpin regions; Montague grammar, tagless-final
interpretation, operads; absorbing Markov states, fault trees, presupposition projection.

## 5. Retrieval by law

All five candidates are **known**:

- G: graded monads (Katsumata, POPL 2014) over a Kripke world preorder — the world-extension
  relation of step-indexed/Kripke logical relations (Ahmed, Dreyer et al.) with a resource grade
  (time credits, Charguéraud–Pottier). This project already proves a graded lag rule on the Iris
  route (`Wp.lagRun`), not at this layer.
- S: code-relative specifications with labels/positions, composed by concatenation (Saabas &
  Uustalu, TCS 2007, compositional Hoare logic for low-level code; Tan & Appel, VMCAI 2006;
  Kennedy, Benton, Jensen & Dagand, PPDP 2013, "Coq: the world's best macro assembler?";
  Myreen's `code` predicate).
- R: registers as resources (Bornat, Calcagno & Yang 2006; Myreen & Gordon, TACAS 2007); the
  project's block executor already reasons over a first-order register write log.
- M: dynamic frames (Kassios, FM 2006), region logic (Banerjee, Naumann & Rosenberg, ECOOP 2008);
  the project already has `RegionCore`/`Win` keys decided by one `decide`.
- F: divergence/going-wrong propagation in big-step compiler proofs (Leroy & Grall 2009) and
  first-failure inversion; the project's `ArmCore` descriptor pattern exists at the interpreter layer.

Recognition, not invention: each law is proved somewhere in this directory, and each candidate is a
theory the project uses at another layer.

## 6. Variation

Ordered by generality (the lattice view that found round 5's winner), the candidates sit on two
axes: *what the rule quantifies over* (a new datatype — `Run`, `Span`, a row, a region syntax — or
the existing terms `Reaches`, `Seg`, `MS`, `Keep`) and *where the premises are discharged* (at the
use site or inside one rule). The meet of each new-datatype candidate with the incumbent is the
same rule stated over existing terms, with no new datatype: an iff-simp form of `Seg.append` with
end-bound propagation, bind lemmas for every spec family generalising `ESpec.bind`, a one-shot
post composition, and register lemmas that let the WP simp set consume `Has` facts. Piloted as P4.

Pilots (built in parallel worktrees from fc553c2e):

* P1 = G + S (the stack all six agents recommended first): `sLogFull`, `fIfSome`, `fIfSome₀`,
  `fCons₀`, `stmtT`.
* P2 = R + M: `run_leave`, `walk_read`, `run_cc`.
* P3 = F, standalone over raw `Reaches`: `fIfSome`, `fIfSome₀`, `fCons₀`.
* P4 = the meet (no new datatypes): all eight primary cases.


## 7. Bake-off

Each candidate was built by its own agent in its own worktree from fc553c2e (suite committed
first; `.lake` and the path dependency's `riscv-lean/*/.lake` copied; `lake build --no-build`
confirmed up to date). Commits: P1 1b25ff08, P2 62cef60f, P3 68368ebd, P4 85777700 (branches
`exp-R6-P1` … `exp-R6-P4`). Every pilot ended with `lake build Vsa.Compiler.CorrectG
Vsa.Compiler.Correct Vsa.Compiler.Checked` green and the touched theorems' axioms within
{propext, Classical.choice, Quot.sound}.

**What each built.**

* **P1 = G + S** (142 code lines): `R6Span` (`Placed := Seg ∧ PosOK-end`, one right-associated
  append rule, `Seg.cat`), `R6Run` (`Evo` with refl/comp/mono; `Run` as an abbreviation of
  `Reaches` with the error branch and a fixed origin; `Run.done`, `Run.bind` with `Room.not_within`
  inside; bridges `ESpec.run`/`ESpec.of_run`; `MS.keep`; glue `run_trCall`), `R6Stuck`
  (`Fail.bindE`, `run_condP`), `R6Old` (`At.step`). The defeq-midpoint claim held for the
  unifier.
* **P2 = R** (147 code lines; M not built): `R6Row` (register rows `Models L ks vs` with literal
  keys, `Keep.models` decided by `decide`, `models_gset`, `Models.wp`), `R6Scope` (`HeadFrame`,
  `StoreRel.headFrame`, scope pop), `R6Keys` (`Keys`, the five key registers as one structure;
  `MS.keys`, `Keys.setEnv`, `MS.reseat`, `MS.popScope`). The region half was not applicable: none
  of the three statements contains a memory agreement a region type could discharge (`run_cc`'s
  frame clause is already one existing lemma), and `RegionCore`/`Win` live in `VsaIris`, which
  `Vsa/Compiler` does not import.
* **P3 = F** (207 code lines: 125 generic, 82 in three per-construct layout lemmas): `R6Blame`
  (source-only `IfBlame`, `ConsBlame` with inversion), `R6FailOld`/`R6Stuck` (failure binds over
  the two compilers' result shapes, child-site descriptors, generic arms `condSel_stuck`,
  `condSel_fail₀`, `seqArm₀`, and the layout lemmas `ifSome_sites`, `ifSome_sites₀`, `cons_sites₀`).
* **P4 = the meet** (161 lines, no new datatypes or predicates): `R6Layout` (`seg_app_iff`,
  `segP_app`: an iff over `Seg ∧ PosOK-end` used as a pre-rewrite), `R6Reg` (`Has.wp`: an autoParam
  normalises the register name so `wp_simp [h.wp]` consumes a `Has` fact; `frame_consts`,
  `obj_consts`, a `rt_pos` simp attribute on runtime positions), `R6Expr` (`MS.keep`, `MS.reenv`,
  `ESpec.bindTr`: child spec then the truthiness call with the error branch absorbed once),
  `R6Stuck` (`EStuck.cond`), `R6Old` (`At.after`, `Fail.cond`, `TSpec.fail`).

**Held-out proof-body lines (statement unchanged), failed compiles in brackets.**

| case | incumbent | P1 | P2 | P3 | P4 |
|---|---:|---:|---:|---:|---:|
| `run_cc` | 69 | — | 55 [3] | — | 41 [1] |
| `walk_read` | 67 | — | 51 [1] | — | 48 [2] |
| `sLogFull` | 62 | 44 [10] | — | — | 22 [2] |
| `run_leave` | 37 | — | **8** [0] | — | 15 [0] |
| `fIfSome` | 32 | 22 [0] | — | 3 [0] (+23 layout lemma) | 12 [0] |
| `fIfSome₀` | 29 | 19 [1] | — | 3 [0] (+37) | 11 [2] |
| `stmtT` | 22 | 22 [0] | — | — | 22 [0] |
| `fCons₀` | 20 | 14 [1] | — | 4 [0] (+22) | 13 [2] |

Per territory (body + failed compiles; incumbent = existing bodies):

| territory | incumbent | own candidate | P4 on the same cases |
|---|---:|---:|---:|
| P1 (`sLogFull`, `fIfSome`, `fIfSome₀`, `fCons₀`, `stmtT`) | 165 | 121 + 12 = 133 | 80 + 6 = 86 |
| P2 (`run_leave`, `walk_read`, `run_cc`) | 173 | 114 + 4 = 118 | 104 + 3 = 107 |
| P3 (`fIfSome`, `fIfSome₀`, `fCons₀`) | 81 | 10 + 82 per-construct = 92 | 36 + 4 = 40 |
| all eight | 338 | — | 184 + 9 = 193 (−43%) |

P3's three-line bodies are real but move the layout into one lemma per construct and compiler,
which no other case reuses; counted where the cost lands (skill step 1), P3 is more expensive than
the incumbent on its own cases. `stmtT` (a term-mode dispatch of one-line arms) is untouched by
every candidate.
