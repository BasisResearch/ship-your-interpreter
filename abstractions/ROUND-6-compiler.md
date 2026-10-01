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

**Time** (user-CPU, `LEAN_NUM_THREADS=1`, min of 3, all five variants interleaved per file in one
window, load 13.3–16.3 on 32 cores; files a pilot did not touch are its copy of the base file):

| module | incumbent | P1 | P2 | P3 | P4 |
|---|---:|---:|---:|---:|---:|
| RTDisplay | 11.93 | (12.68) | 13.79 | (12.47) | 13.74 |
| SimVar | 4.00 | (3.92) | 3.74 | (4.00) | 3.80 |
| SimLogic | 7.80 | 4.87 | (7.65) | (7.64) | 4.61 |
| SimBlock | 1.91 | (1.90) | 1.72 | (1.95) | 1.86 |
| StuckStmt | 3.15 | 3.13 | (3.11) | 2.87 | 2.97 |
| StmtS | 1.85 | 1.73 | (1.88) | 1.52 | 1.68 |
| sum | 30.64 | 28.23 | 31.89 | 30.45 | 28.66 |

Untouched copies vary by up to 6% (RTDisplay 11.93–12.68), the noise floor of this window. The new
layer modules each cost about the import floor (0.4–1.4 s). The one real regression is RTDisplay
(+15% under P2 and P4: register rows and `Has.wp` autoParams run `simp`/`decide` inside `wp_simp`);
SimLogic is 40% faster under both P1 and P4 (one generic truthiness bind replaces two inline runs).

**Fresh cases on the combination** (P4 + P2's key-register fiber, branch `exp-R6-C`; the six fresh
cases, run after the pilots; no new abstraction code allowed beyond fixes, which count as setup):

| case | incumbent | combination | failed compiles | note |
|---|---:|---:|---:|---|
| `run_add` | 71 | 57 | 1 | `Has.wp` ×5, `rt_pos` |
| `sim_all` | 167 | 167 | 0 | recursor wiring of 51 case lemmas into 9 mutual recursors; no rule applies |
| `sim_not` | 32 | 29 | 0 | `segP_app` on the older compiler |
| `sCall` | 46 | 40 | 0 | `segP_app` replaces the split/naming/cast block |
| `fBlockS` | 14 | 11 | 0 | `segP_app` |
| `dp_ret` | 7 | 4 | 1 | `Has.wp` |
| total | 337 | 308 (−8.6%) | 2 | 170 → 141 (−17%) without `sim_all` |

Layer change during the fresh run: +1 line net 0 (a `reg_def` simp set). Defects the fresh cases
found (E15): `Has.wp`'s autoParam elaborated register names at the use site, so a local variable
named `t1` captured the register name and the facts silently stopped firing (fixed by the
`reg_def` attribute); `run_at'` with whole-routine unfolding hits `maxRecDepth` on a 126-instruction
routine (left: explicit `run_seg` lists remain for large routines); `↓segP_app` cannot share a
`simp` call with `List.length_append`; helper lists must be unfolded in the same `simp`. (The
combination's first commit eefcbc32 did not parse — a staging slip by the coordinator, caught by
the fresh agent and fixed in 2b7affe8.) Module CPU: SimCallE 5.62 → 2.96, ExprSim 6.66 → 6.00,
RTOps 13.97 → 14.24, RTDisplay 12.04 → 12.96, StuckStmt unchanged.

The calibration gap between the primary set (−43%) and the fresh set (−8.6%, −17% without the
skeleton) has one cause: the primary set held `sLogFull`, whose truthiness-call pattern P4's
`ESpec.bindTr` packages exactly (62 → 22), and three failure duals whose child calls the stuck
binds absorb; the fresh set held a recursion skeleton and runtime routines whose residue is
per-routine register bookkeeping after calls.

## 8. Decision

**Adopted: the combination** — P4's rules over existing terms (layout iff `segP_app`, `Has.wp`,
`MS.keep`/`MS.reenv`, `ESpec.bindTr`, `EStuck.cond`, `Fail.cond`/`TSpec.fail`/`At.after`, the
`rt_pos`/`reg_def` simp sets) plus P2's key-register fiber (`Keys`, `MS.reseat`, `MS.popScope`,
register rows `Models`). Reasons, by the measures fixed in §0:

* Primary: on all eight cases P4 needs 184 lines + 9 failed compiles against the incumbent's 338
  (−43%); it beats every new-vocabulary candidate on that candidate's own territory (P1 133 vs 86,
  P2 118 vs 107, P3 92 vs 40). P2's fiber wins one case (`run_leave` 8 vs 15) and is kept.
* Setup 161 + 147 lines; fresh cases cost no new layer code.
* Secondary: touched modules within noise in sum (30.64 → 28.66 s for P4); RTDisplay +15% is
  recorded as the layer's named cost (rows and autoParams run `simp` inside `wp_simp`).

Not adopted: P1's `Run`/`Evo` monad and `Placed` type (the defeq midpoints satisfy the unifier but
not `omega`/`simp` dischargers, so the new types added lines back: 10 failed compiles on
`sLogFull`); P3's blame arms (bodies of 3–4 lines, but the layout moves into one lemma per
construct and compiler, which nothing else reuses); the region half of P2 (no case contains a
memory agreement it could discharge; the existing region keys live in `VsaIris`, unreachable from
`Vsa/Compiler`).

As in round 5 (E25), the winner is the meet: the laws stated over the project's existing terms,
with no new datatype.

Route (this branch has no CLAUDE.md or discipline script; per E16 the rule text is recorded here
for the branch that carries them):

| task shape (Vsa/Compiler) | use |
|---|---|
| child `Seg`/`PosOK` premises of a generated construct | `segP_app` (`R6Layout`), never `hseg.append` + `.cast (by omega)` + `posOK_le` |
| a `Has` fact feeding `wp_simp` | `h.wp` (`R6Reg`), never `have k := has_mem h …; have e := srcVal_of_has h` |
| `MS` after a register-only step | `MS.keep` / `MS.reenv` / `MS.reseat` (`R6Expr`, `R6Keys`), never a 12-field rebuild |
| child expression then the truthiness call | `ESpec.bindTr` |
| stuck condition / old-compiler failure binds | `EStuck.cond`, `Fail.cond`, `TSpec.fail` |

Discipline rules (TSV lines for `scripts/discipline_rules.tsv`; after the rollout the first has
no remaining hits; the second has eight, in SimIf (3, the private `run_cond` adapter and two
goal-side `SPost.cast`), SimWhile (3, packaged layout), SimFn and SimStmt1 (1 each), to be listed in
`scripts/discipline_grandfather.txt`):

```
R16	Vsa/Compiler/**/*.lean	have [A-Za-z0-9_']+ := has_mem	register facts into wp_simp go through Has.wp (R6Reg), not has_mem/srcVal_of_has
R17	Vsa/Compiler/**/*.lean	\.cast \(by omega\)	child layout premises come from segP_app/seg_app_iff (R6Layout)
```

## 9. Rollout

Pre-rollout snapshot 632cc95a (`exp-R6-C` merged). Six agents, disjoint file groups balanced by
cluster lines (≈1,290 each), one shared worktree, a written brief (the layer's idioms as in §8, the model diffs of the 14 held-out re-proofs, the import positions),
single-file compiles only, the coordinator's full build at the end; they could not edit the layer
and reported needed helpers instead. Commit 5921f423 (40 files, +501 −1,017), consolidation
d935339d (`At.after` moved beside `At` in `StmtFrag`, removing the layer copy and one private
duplicate). Full `lake build` (1,549 jobs, all default targets including executables) green after
each.

Migrated per group (body lines before → after, a selection; full lists in the agents' notes):
RTOps `run_sub` 31→24, `run_mul` 35→27, `run_div`/`run_mod` 42→33, `cmp_sel` 119→108, `run_cmp`
112→99, `run_eq` 115→101, `add_cat` 84→72; RTLeaf `run_sc` 120→106, `run_nf` 60→46, `run_ps`
64→54; RTItos `it_step` 81→70, `run_it` 127→119; SimFnEntry `run_entry` 176→162; SimCond
`run_cond` 28→11; SimLogic `sLogShort` 40→18; StuckExpr `fLogical` 62→41, `fBinary` 63→49; SimExit
`run_exitTo` 35→21 (`MS.reenv` replaces a 12-line rebuild); StuckStmt `fIfNone` 26→12; StmtS
`fIfNone₀` 17→10; SimBin `sBinary` 73→59; CorrectG `RTLoaded.of` 22→7; SimCallCode `CCSegs.of`
11→4; StmtT `tIfSome` 47→38.

Members left, by reason (109 of 207 cluster members unchanged):

* no obligation the layer discharges: recursion skeletons and dispatch tables (`sim_all`,
  `noE`/`noA`, `stmtT`/`seqT`, `StuckAll`), one-line wrappers, source-side lemmas;
* import position: `Run`, `Frag`, `WP`, `RTBase`, `PrintInt` sit below every layer module
  (`R6Layout` imports `Run`, `R6Reg` imports `RTBase`), and `SimUnary`/`SimWhile`/`SimFor` sit below
  `R6Expr`/`R6Stuck` although `sNot` has exactly `ESpec.bindTr`'s shape;
* memory-changing `MS` rebuilds (`run_storeSlot`, `run_enterFrame`, `MS.stored`, `MS.heap`):
  `MS.keep`/`MS.reseat` are same-memory rules;
* packaged layouts (`while_segs`, `ForSegs`, `hok.segs`) whose `posOK_le` uses derive from the
  construct's end, not from an append split;
* migrated with no gain and reverted (`sIfNone`, `run_strTab`).

Layer defects and gaps the rollout found (the next round's input, E22):

1. `↓segP_app` is a pre-order rewrite: on an already left-nested append (after `generalize`,
   `dsimp`, or an equation lemma such as `fnCode_eq`) a `List.append_assoc` in the same `simp`
   call does not re-associate first, the split lands at the wrong association, and an `rcases -`
   on a PosOK component fails with "dependent elimination failed". A separate re-association
   step is required (found by three groups).
2. `↓segP_app` splits every `++`; prefixes that must stay whole for `run_whole` need
   `segP_app.mp` once or `rw [segP_app]` (an outer-split form is missing).
3. Goal-side positions are not normalised: the generator writes `x+3`, the split produces
   `x+1+2`, and `omega` treats `opCode (x+2+4)` and `opCode (x+6)` as different atoms; fixed per
   use by `simp only [Nat.add_assoc, Nat.reduceAdd]` or by naming the position.
4. `ESpec.bindTr`'s post is fixed to `errPos ∨ R`; failure-side callers wrap it in
   `reaches_mono … fail_err` (a `Fail` variant would save 1–2 lines per use).
5. `frame_consts`/`obj_consts` omit `codeBase`, `stackLo`, `stackHi`, `maxFS`, `bufBase`,
   `maxCallDepth` (still `have … := rfl` in eight theorems).
6. No split-segment `run_cond` (one private adapter in SimIf).
7. `run_at'` with whole-routine unfolding hits `maxRecDepth` on a 126-instruction routine.

## 10. Measurements (fc553c2e → d935339d)

| measure | before | after |
|---|---:|---:|
| `Vsa/Compiler` lines (incl. 316 non-blank layer lines) | 19,478 | 19,164 |
| theorem declaration lines (excluding the layer) | 14,866 | 14,121 (−745) |
| cluster members changed | — | 98 of 207 (+8 outside the cluster heads) |
| declaration lines of the 106 changed theorems | 5,718 | 4,968 (−13%) |
| cluster declaration lines (195 matched by name) | 7,705 | 6,997 (−9.2%) |
| `has_mem`/`srcVal_of_has` uses | 184/186 | 1/3 (both definitions; one equality use) |
| `.append` / `posOK_le` / `.cast (by omega)` uses | 268 / 175 / 13 | 130 / 93 / 8 |
| module user-CPU, single-file, base and new interleaved, min of 2 (load 10.6–20.3) | 344.8 s | 341.2 s (332.3 s without the 9 layer modules, 8.9 s ≈ import floor) |
| largest module changes | | SimLogic 8.48→4.01, StuckExpr 8.37→4.86, SimCallE 5.94→3.02; RTDisplay 13.46→14.55 |

Statement check: a meta script over both environments (every non-internal constant of
`Vsa.Compiler.*`, type hashed) finds 0 changed types; the only missing names are compiler-generated
`match_` auxiliaries, the added ones the layer, `At.after`, and auxiliaries. `compileG_correct`,
`compileChecked_correct`, `compile_correct`: [propext, Classical.choice, Quot.sound]; the 14-line
axioms file unchanged (WhileLogic adequacy [propext, Quot.sound]). No `sorry`, `axiom`,
`native_decide`, `bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth` in `Vsa/Compiler`.

Calibration: held-out primary −43%, fresh −8.6% (−17% without the skeleton), rollout −9.2% of
cluster lines and −13% on the members it touched. The primary draw over-represented the two
patterns the layer packages best (the truthiness-call bind and the stuck-condition bind); about
half the cluster contains none of the obligations the laws discharge (E21).

## 11. What remains

* The cost that is left is not in the five laws. It is (a) per-routine register bookkeeping after
  runtime calls (`have g := hk.has (by decide) (by reg_simp; exact …)`, 452 `reg_simp` uses
  remain), (b) the positional 8–10-premise applications of child specs and the hand-built source
  derivations in failure cases (`fun ⟨st', t, D⟩ => hne ⟨…⟩`), and (c) memory-changing `MS`
  rebuilds. P3's blame layer addressed (b) for failure cases but put the layout into one lemma
  per construct; the next round should state child descriptors over `segP_app` so the layout part
  is shared, and add a memory-changing reseat (`MS.reseat` with a heap/frame step).
* Layer defects 1–7 of §9.
* Encode (41 s, symbolic-field decode) and the kernel-evaluation example modules (38 s) are the
  time targets; neither is a proof-vocabulary problem.
* 534 lines of off-path declarations (§1a) remain.
* The census script (`decls.tsv`: constant closure and conclusion heads) and the statement-hash
  script are in §12.

## 12. Scripts

Census (run with `lake env lean Census.lean` from the worktree; writes
`module, name, kind, start, end, on-path, conclusion head`):

```lean
import Vsa
import WhileC
open Lean Meta

partial def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet.toList do
          if !seen.contains m then stack := m :: stack
        if let .inductInfo ii := ci then
          for c in ii.ctors do stack := c :: stack
  return seen

def headOf (e : Expr) : String :=
  let rec strip : Expr → Expr
    | .forallE _ _ b _ => strip b
    | .mdata _ b => strip b
    | e => e
  let b := strip e
  let nm := match b.getAppFn with | .const n _ => n.toString | _ => "?"
  if nm == "Eq" || nm == "Iff" then
    let args := b.getAppArgs
    let lhs := if nm == "Eq" then args[1]! else args[0]!
    nm ++ ":" ++ (match lhs.getAppFn with | .const n _ => n.toString | _ => "?")
  else nm

def run (env : Environment) : IO Unit := do
  let mods := env.header.moduleNames
  let isComp (i : Nat) : Bool := (mods[i]!.toString).startsWith "Vsa.Compiler."
  let mut roots : List Name := [`Vsa.Compiler.compileG_correct, `Vsa.Compiler.compileChecked_correct,
     `Vsa.Compiler.compile_correct]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mn := mods[idx.toNat]!.toString
      if mn == "WhileC" || mn == "Vsa.Compiler.CompiledG" || mn == "Vsa.Compiler.WhileWl" then
        roots := n :: roots
      else if !isComp idx.toNat then
        for m in ci.getUsedConstantsAsSet.toList do
          if let some j := env.getModuleIdxFor? m then
            if isComp j.toNat then roots := n :: roots
  let cl := closure env roots
  let h ← IO.FS.Handle.mk "decls.tsv" .write
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if isComp idx.toNat && !n.isInternal then
        let kind := match ci with
          | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | _ => "other"
        let rng := match declRangeExt.find? env n with
          | some r => s!"{r.range.pos.line}\t{r.range.endPos.line}" | none => "0\t0"
        h.putStrLn s!"{mods[idx.toNat]!}\t{n}\t{kind}\t{rng}\t{cl.contains n}\t{headOf ci.type}"

#eval show Elab.Command.CommandElabM Unit from do run (← getEnv)
```

Statement check: the same skeleton printing `module, name, kind, hash ci.type, range` for every
non-internal `Vsa.Compiler.*` constant, run in both environments and joined by name.
