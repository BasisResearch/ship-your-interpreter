# Abstraction-discovery round 5: the ISA instruction-semantics layer (2026-09-30)

Branch `exp-R5`, from `exponentiate` 95acd019 (after ROUND-3). Target: `Vsa/Sim/*.lean`, the layer
that connects the Sail RV64 model's `execute`/`try_step`/`stepOnce` to the first-order write-log
semantics of the block executor. Sibling projects copy this layer verbatim.

## 0. Primary measure (stated before the bake-off)

The layer is cheap to build: its 204 modules took 333 of the tip's 3,283 module-seconds, and about
200 of those are the import floor (≈1 s per module). The primary measure is therefore **agent
effort: proof lines of held-out re-proofs plus failed compiles**, with the abstraction's setup
lines counted separately (break-even). Module-seconds of the touched modules are secondary; a
candidate that wins lines may lose seconds by at most 10% of the touched modules' time.

## 1. Census

Per-module seconds from the clean build of the tip (`tip-modtimes.txt`), lines from the tree,
declaration data from a meta script over the `VsaBoot` environment (every constant of `Vsa.Sim.*`
with its kind, source range, conclusion head, and whether it is in the constant closure of the
roots: `endToEnd_refinement`, `proofElf_halts`, and every declaration of `Vsa.Sim.Boot.Audit`,
`Vsa.Lang.*`, `VsaIris.Lang.Route`). The script is in §11.

### 1a. Reachability (dead weight)

79 of the 204 top-level `Vsa/Sim` modules have **no constant** in the closure of the roots
(5,593 lines, 115 module-seconds, among them the hottest module of the layer, `ExecBrkCont`,
18 s for one dead 649-line theorem). Most are the legacy per-arm simulation route
(`ExecEntry`, `EvalChildArm`, `StmtChildArm`, `TruthyCopy`, `ExitFootprint`, `TermSim*`,
`ArmSegSplit*`, `Approx*`, `Div*Close`, …) that the V2 Iris route (`VsaIris/Interp`) superseded.
Six of them are elaboration-only (attributes, `#derive_case`, macros) and were kept, as were the
modules whose definitions still appear in the statements of surviving (possibly dead)
declarations: `StrcmpSpecCond`, `SnprintfSpec18`, `KeepRegs`, `FrameOn`, `SnprintfSpec20`,
`RamReadPins`, `EnvGetSites{,2}`, and the chain `SegFrameFactsAuto` needs (`EqNeDispatchSeg`,
`SegFrameFacts`, `ExitFootprint`, `EntryGroundKit`, `EvalIntSim2`, `EvalSimCommon`,
`EvalRecCommon`, `EvalExprSites`, `ExecEntry`, `InterpEntry`, `StaticImageSupport`,
`BlockAdapter`).

**Cut (commit 100962e9):** 50 top-level modules and the 14 dead `rows/` modules that imported them
(3,907 lines) deleted; 19 live modules take the deleted modules' surviving imports; full build
green, headline axioms unchanged. Inside surviving modules, 6,188 further declaration lines are
off the path (e.g. `Dispatch` 24 of 411 constants used, `ExecuteBranch` 10/98, `Pmp` 12/51); they
were not removed this round.

Files of the layer used only by other files of the layer: every `Vsa/Sim` ISA module except the
observational-step interface (`StepObs.stepObs_*`), the register lemmas (`RegAccess`, used by
`VsaIris/Vsa/StepGen`, `StepRules`, `JalSite`, `AllocSltu`, `MallocFastJal`, `Interp/CallJalr`),
and the block/read layers consumed by `VsaIris` (`BlockMem`, `BlockTerm`, `RamRead*`).

### 1b. Clusters (ISA core: 56 files, 15,720 lines, 121 module-seconds)

Clustered by conclusion head (e.g. `Eq:EStateM.run[execute]=ok`, 73 theorems) and name stem.

| cluster | files | theorems | on path | lines | dead decl lines | module-s |
|---|---:|---:|---:|---:|---:|---:|
| C-step: per-kind chain `try_step_K → stepOnce_K_{tick,notick} → step_K_* → stepObs_K`, K ∈ {alu, store, branch taken/not, jal, jalr, j, jr}, plus per-K post-state reads | 12 | 133 | 117 | 3,973 | 153 | 19.3 |
| C-width: 1/2/4/8-byte copies of the load/store chain | 21 | 170 | 144 | 4,515 | 659 | 33.1 |
| C-reg: `rX_bits_xN`/`wX_bits_xN` and 31-arm batteries over them | 2 | 62 | 62 | 710 | 0 | 7.5 |
| C-exec: per-op `execute` characterisations | 3 | 46 | 46 | 698 | 0 | 6.9 |
| C-block: block executor (one 37-arm `cases kind`, ≈2,000 lines) and terminators | 4 | 112 | 54 | 4,150 | 59 | 13.4 |
| C-sys: fetch, decode, interrupts, tick, HTIF, PMP under the pins | 14 | 98 | 94 | 1,674 | 5 | 40.3 |

The largest conclusion-head cluster is `EStateM.run … = ok` (308 declarations, 8,225 lines,
a third of the layer): `execute` 73, `try_step` 11 (959 lines), `stepOnce` 19 (827),
`checked_mem_read`/`_write` 16 (852), `wX_bits`/`rX_bits` 66 (675), `vmem_*` 19 (830).

Profile of one instance of each kind (MemStore 11.2 s user: `simp` 4.8 s, tactic 2.1 s; BlockMem
6.7 s: tactic 3.1 s): time is not where the cost is; lines are.

Sample of cluster members (the held-out draw below, 14 cases) and the obligation shapes they contain:

* `try_step_K` (≈80 lines each): a 35-line front identical in every kind (interrupt dispatch,
  fetch, decode, landing pad, each pin transported across `afterPrelude`), four register reads on
  the kind's post-execute state by peeling `insert`s, then the existing kind-independent
  `try_step_execute_char`.
* `stepOnce_K_{tick,notick}`, `step_K_*`, `stepObs_K`: the same text per kind modulo the state
  abbreviation.
* `get?_sigma*_K`: one `get?_insert` peel per write.
* width copies: the same unfolding with 1/2/4/8 byte hypotheses and per-width `extractLsb` facts.
* register lemmas and batteries: one unfolding repeated 31 times; batteries dispatch on the number.

## 2. Laws

| law | statement | check |
|---|---|---|
| L-reg | for n ∈ [1,31], `rX_bits (Regidx n)` reads `xreg n`, `wX_bits (Regidx n) d` inserts `d` at `xreg n`; n = 0 reads 0, writes nothing | holds per instance (62 proved lemmas) |
| L-front | every retiring instruction: pins + fetched word + `execute ast` = `RETIRE_SUCCESS σ3` + four reads of σ3 ⇒ `try_step = ok false (σ3[PC:=npc][minstret+=1])` | already proved once (`try_step_execute_char`); the stall is discharging its premises per kind |
| L-frame | a post-execute state is the prelude state plus a small write set; registers outside it read as before; pins outside it survive | holds per instance (`get?_sigma*` lemmas, `GoodState.insert_nonpinned`) |
| L-step | `stepOnce` (tick or not), `Step` and the observational step follow from L-front's conclusion for every kind | per-kind proofs are textually identical modulo abbreviations |
| L-width | for w ∈ {1,2,4,8}, aligned in RAM off HTIF: loads return the little-endian w bytes, stores insert them | true for the newer read chain (`checked_mem_read_ram_scalar`); older per-width copies re-prove it |
| L-exec | per operation family, `execute` = read sources, write `f op sources` (or set nextPC on `cmp op`) uniformly in `op` | per-op lemmas are 7–12 lines each; not a cost centre |
| L-block | the block executor's per-kind arm = kind characterisation + L-step + first-order update | 37 arms of 40–50 lines |

## 3. Held-out suite (drawn before any candidate was built)

Population: on-path theorems of the 56 ISA files with ≥ 5 lines (426), stratified by size
(S ≤ 15, M 16–40, L > 40), seed 20260930. Primary: 3 L, 3 M, 2 S. Fresh (run after the first
pilot): 2 per stratum. Baseline = proof-body lines of the existing proof (statement excluded).

| case | stratum | file | body lines |
|---|---|---|---:|
| `try_step_j` | L | StepJump | 64 |
| `stepOnce_j_tick` | L | StepJump | 22 |
| `checked_mem_write_1` | L | MemStore | 58 |
| `step_branch_taken_tick` | M | StepBranch | 7 |
| `obs_gpr_rd` | M | BlockPilot | 33 |
| `checked_mem_read_of_split` | M | CheckedSplitRead | 32 |
| `get?_sigmaPost_store` | S | StepStore | 6 |
| `get?_sigma3_alu_pinned` | S | StepAlu | 4 |
| fresh `vmem_write_addr_4` | L | MemStore | 69 |
| fresh `stepObs_jal` | L | StepObs | 17 |
| fresh `vmem_write_addr_1` | M | MemStore | 17 |
| fresh `stepObs_branch_taken` | M | StepObs | 15 |
| fresh `rX_bits_x29` | S | RegAccess | 4 |
| fresh `forIn'_const` | S | Pmp | 1 |

Primary baseline total: 226 body lines.

## 4. Blind ontologists

Six agents (five seeded by random 256-character strings, one by a random dictionary sentence) got
the semantics, the census and the laws, the held-out statements verbatim, and a forbidden list
(per-register/per-width lemmas, per-kind state abbreviations, `simp only` lists, `cases kind`
batteries, `ReadsLike`, code generators, SMT, "write a tactic"). Each had to say how every rule is
decided at a use site and what happens with symbolic data.

| candidate (as proposed) | agents | rules = laws | decided by |
|---|---:|---|---|
| A. patch/delta states: every post-state is `apply Δ σ` for a literal list of dependent register updates (+ memory patch) | 6/6 | read-over-write (L-frame), pins conserved by pin-free patches (L-frame) | `decide` on key lists (claimed) |
| B. retirement certificate / commit protocol: one theorem per step layer quantified over {ast, Δ, npc, exec}, per-kind content as data | 6/6 | L-front, L-step, L-block | syntactic application; `decide` for side conditions |
| C. width as data: byte codec / split plan with symbolic `w ∈ {1,2,4,8}`, chunk-fold loop invariant | 6/6 | L-width | `omega` for bounds, `rfl` at concrete `w` |
| D. register representability: hoist the 32-way `match` once (`rX_bits (Regidx i) = if i = 0 then 0 else readReg (xreg i)`) | 5/6 | L-reg | one 32-case split inside one proof |
| E. family-level `execute` characterisation with symbolic `op` via the normal-form tool | 4/6 | L-exec | rewrite + `rfl` |

Theories cited (distant fields): ARIES redo logs and incremental view maintenance (databases);
lenses and their put/get laws (bidirectional programming); McCarthy's select/store arrays;
separation-logic frame rule; Mazurkiewicz traces and independence (concurrency); Darcs patch
theory; reorder-buffer retirement (Tomasulo; Smith–Pleszkun); two-phase commit; proof-carrying
code; algebraic effects and handlers; Myreen–Gordon decompilation into logic; Islaris; CompCert
`Pregmap.gss/gso` and `match_states`; Reynolds–Wadler parametricity; Bird–Meertens list
homomorphisms; defunctionalisation; representable functors; Noether's theorem and gauge
invariance (the tick as a gauge on `mcycle/mtime/mip`); the Heisenberg picture.

One-offs kept for variation: register class `cls R` so that `xreg n ≠ R` is decided from the class
alone; conservation ledger for pins; tick as gauge quotient; Darcs-style commutation of disjoint
patches.

## 5. Retrieval by law

All five candidates are **known**: read-over-write is McCarthy's array theory and CompCert's map
lemmas; the commit rule is the per-instruction specification of machine-code Hoare logics
(Myreen–Gordon 2007; Sail-based proofs, Armstrong et al. POPL 2019; Islaris, PLDI 2022) and the
reorder-buffer commit of microarchitecture; width genericity is parametricity; the register rule is
the finite-index representation of a register file. Each is already used at another layer of this
project: the first-order executor keeps memory as a write log (`writeLog`/`applyW`), the front
half of the commit rule exists (`try_step_execute_char`, used by every kind but never lifted to
`stepOnce`/`Step`/`stepObs`), the read side already has a width-generic split plan
(`SplitReadPlan`, `checked_mem_read_ram_scalar`). Recognition, not invention, is the win.

## 6. Variation (ideonomy: tree-finding, dimension-identification; lattice; source, autonomy, reversibility)

Ordered by generality, the candidates form a lattice: per-kind lemma < per-family certificate <
certificate over a literal patch Δ < commit over an **abstract** σ3 plus four named reads. The top
element had been built only at the `try_step` level. Variants kept:

* V3 (meet of A and B, "Δ-free commit"): the commit theorems stated over an abstract σ3 with a
  `RetireReads` structure; the existing per-kind abbreviations are instances by definitional
  unfolding; reads are discharged by a decision procedure over the existing `insert` chain — no
  patch datatype. The cheapest pilot, and it became P1.
* V1 (source: extracted): σ3 and its reads computed by the normal-form tool from `execute`. Not
  piloted (L-exec is not a cost centre).
* V2 (autonomy: kernel): every certificate side condition by one `decide`. Tested inside P2.
* V4 (siblings): the same commit rule for the HTIF store step and the block terminators.

## 7. Bake-off

Each candidate was built in its own worktree from 4ef8d9a6 (suite committed first; build outputs
copied, including the path dependency's `riscv-lean/*/.lake`). Times: user CPU of
`lake env lean -Dbackward.isDefEq.respectTransparency=false` (the lakefile's option; without it
some pristine files do not compile), min of 3, incumbent and candidates interleaved, load 7–11 on a
shared 16-core machine.

**Candidates.**

* **P1 = B in the V3 form** (`Retire.lean`, 177 lines with docs): `Fetched`, `RetireReads`,
  `retirePost`, `tickPost`; `try_step_retire` (front), `stepOnce_retire_{notick,tick}`,
  `step_retire_{notick,tick}`, `stepObs_retire` (in `StepObs`), `GoodState.retirePost/.tickPost`;
  decision procedure `reg_reads [facts]` (simp over `get?_insert` with `decide` on key comparisons).
* **P2 = A + B** (P1's commit layer plus `Patch.lean`, 45 lines): `Patch.apply`, `Patch.Off`,
  `get?_miss`, `get?_last`; reads by the patch rules.
* **P3 = C** (in `MemStore`/`MemLoad`, 377 lines of generic lemmas, 72 of them needed for the
  primary case): `checked_mem_write_w`, `memWriteLE`/`write_ram_w`, `mem_write_value_w`,
  `mem_write_ea_w`, `vmem_write_addr_ram_w`, and on the read side `checked_mem_read_data_w_of_ram`
  and its two wrappers.
* **P4 = D** (in `RegAccess`, ≈40 lines): `gpr_cases n => tac` (splits 1..31, discharges the rest
  by `omega`), `rX_bits_gpr`, `wX_bits_gpr` proved once; the register-number definitions moved from
  `BlockPilot` to `RegAccess`.

**Held-out proof-body lines (statement unchanged), failed compiles in brackets.**

| case | incumbent | P1 | P2 | P3 | P4 |
|---|---:|---:|---:|---:|---:|
| `try_step_j` | 64 | 3 [1] | 9 [2] | – | – |
| `stepOnce_j_tick` | 22 | 3 | 3 | – | – |
| `step_branch_taken_tick` | 7 | 3 | 3 | – | – |
| `get?_sigmaPost_store` | 6 | 1 | 2 [1] | – | – |
| `get?_sigma3_alu_pinned` | 4 | 1 | 2 | – | – |
| `checked_mem_write_1` | 58 | – | – | 2 | – |
| `checked_mem_read_of_split` | 32 | – | – | no gain | – |
| `obs_gpr_rd` | 33 | – | – | – | 2 |
| fresh `stepObs_jal` | 17 | 3 | – | – | – |
| fresh `stepObs_branch_taken` | 15 | 3 | – | – | – |
| fresh `vmem_write_addr_4` | 69 | – | – | 2 | – |
| fresh `vmem_write_addr_1` | 17 | – | – | 2 | – |
| fresh `rX_bits_x29` | 4 | – | – | – | 1 |
| fresh `forIn'_const` | 1 | – | – | – | – |
| setup failed compiles | | 3 | 1 (+P1) | 4 | 7 |

`checked_mem_read_of_split` is already the generic rule (its loop goes through
`splitReadLoop_trace`); no candidate shortens it. `forIn'_const` is in no candidate's territory.

**Compression of existing siblings (refactor part).** P3: `checked_mem_write_{2,4,8}` 59–65 → 2
each, `mem_write_ea_*` 44 → 2, `vmem_write_addr_{2,8}` ≈70 → 2, `split_on_page_boundary_store_*`
21 → 1, `within_mmio_readable_ram_false_*` 26 → 1, `checked_mem_read_data_*_of_ram` 51 → 2;
MemStore + MemLoad net −556 lines. P4: all 62 register lemmas become one-line instances;
RegAccess + BlockPilot net −296 lines.

**Time (user s).**

| file | incumbent | P1+P4 | P2 | P3 |
|---|---:|---:|---:|---:|
| StepJump | 3.95 | 3.76 | 3.53 | |
| StepBranch | 2.19 | 2.22 | 2.19 | |
| StepStore / StepAlu / StepObs | 1.35 / 1.34 / 1.51 | 1.31 / 1.44 / 1.51 | 1.31 / 1.38 / 1.45 | |
| RegAccess | 57.90 | **8.98** | 60.30 | |
| BlockPilot | 3.85 | 2.90 | 3.71 | |
| MemStore / MemLoad | 11.81 / 3.97 | | | **4.74 / 3.13** |

(The census's module-seconds are wall time of a parallel build; `RegAccess` elaborates its 62
proofs on 8 threads, so 58 s of CPU showed as 5 s of wall.)

**Defects found by the pilots.** (1) Blind agents said patch side conditions are "decided by
`decide` on key lists"; `decide` refuses any goal with free variables, and the patch's values are
free, so P2 needs `simp` with `decide` or an anonymous constructor from the hypotheses. (2) The
dependent register type: `σ.regs.get? (gprReg n) : Option (RegisterType (gprReg n))` does not
reduce for symbolic `n`, so L-reg is stated through the non-dependent `gprGet`. (3) `iterate n`
stops silently when its body fails; `gpr_cases` therefore splits first and runs the per-register
tactic under `all_goals`, which reports the failing register. (4) Case splits leave numerals as
`0 + 1 + 1`; `gpr_cases` normalises them before the per-register tactic. (5) The width law needs
the single-page condition as a premise (`w = 3` falsifies deriving it from alignment); instances
discharge it by `omega`. (6) `MemLoad` and `MemStore` cannot be imported together (both define
`split_misaligned_aligned_w`), so the read side cannot reuse the store side's lemmas.

**Decision.** P1 beats P2 on its territory (11 vs 19 body lines, 1 vs 3 failed compiles, same
time): the patch datatype adds only notation over the `insert` chain the per-kind abbreviations
already are. P3 and P4 win their disjoint clusters outright, including on time (MemStore 2.5×,
RegAccess 6.4×). The three winners touch disjoint files and share no rule, so the combination was
merged (0ad6935e, full build green) without a separate iteration; the fresh cases above were each
run after their candidate's primary cases.

## 8. Rollout

A fan-out over disjoint files (four agents, one worktree and one compiler each, one written brief
with the model proofs), then a consolidation pass on the layer.

| wave | files | lines before → after | CPU before → after (s) | failed compiles |
|---|---|---|---|---:|
| W1a commit rule | StepJump, StepBranch | 1,662 → 1,060 | 5.99 → 4.23 | 0 |
| W1b commit rule | StepAlu, StepStore, StepObs, HtifStepObs, TermEntry | 2,029 → 1,195 | 7.96 → 6.29 | 4 |
| W2 register rule | BlockPilot, BlockTerm, BlockMem, SegToTripleFramed, SymObs | 4,119 → 3,905 | 14.98 → 13.8* | 4 |
| W3 width layer | ExecuteLoad, MemLoadTotal, ExecLoadTotal, ValueSites, RamReadVirtual | 1,161 → 808 | 6.75 → 5.49 | 0 |

\* after consolidation; W2's first version was 0.3–0.8 s slower per file (see below).

Migrated: every `try_step_K`, `stepOnce_K_*`, `step_K_*`, `stepObs_K` of the eight kinds and the
HTIF putchar step; every per-kind post-state read and good-state lemma (reads by `reg_reads`,
good states by `GoodState.retirePost`); every 1..31 register battery (`rX_src`, `wX_gpr`,
`obs_gpr_rd`, `obs_gpr_other`, `obs_gpr_frame_bt`, `obs_gpr_store`, `gprGet_of_frame`,
`gprGet_obs_rd`); the per-width read chain (`vmem_read_addr_data_ram_w`, `vmem_read_data_ram_w`,
`exec_store_w`). 29 per-kind helper lemmas and 12 per-width copies became unused and were deleted.

Left, with reasons: `stepOnce_tohost_G` halts (no retire shape); `StepAddi`'s reads cannot import
`Retire` (cycle Retire → Frame → StepBeq → StepAddi); nine execute-side reads in HtifStepObs stay
on `rw` because `reg_reads` costs 50–170 ms per call on 6–8 `insert` layers; `read_ram_one_total`
needs a width-1 `bytesT` conversion that lives in a module `MemLoadTotal` cannot import;
`checked_mem_write_tohost_8` is MMIO-only; the 37-arm `cases akind` of `block_mem_run` (C-block)
and the C-exec/C-sys clusters were outside the bake-off.

Defects found by the rollout (fixed in the consolidation commit 832e7baf unless noted):
1. `gpr_cases` split by iterated `rcases` and normalised numerals with `simp … at *` in every
   case: 0.3–0.8 s slower per battery file than the hand batteries. Now it substitutes literals
   from one decided lemma (`gpr_range_fin : ∀ n : Fin 32, 1 ≤ n → n = 1 ∨ … ∨ n = 31`, by `decide`)
   with `rfl` patterns built outside the quotation's hygiene: parity or faster (BlockTerm 2.38 →
   2.35, BlockMem 6.43 → 6.37, SymObs 2.02 → 1.42).
2. Duplicate `rX_bits_x5/x6` (StepBeq) and `rX/wX_bits_x10` (Execute) beside RegAccess's: deleted;
   both files import RegAccess.
3. `htif_tohost` is pinned, so `GoodState.insert_nonpinned` does not apply to its write; W1b added
   a local `GoodState.insert_htif_tohost` (belongs in `Frame.lean`; not moved).
4. `by decide` side conditions inside a `gpr_cases` body meet unassigned metavariables when the
   register is fixed only by a later argument; `refine … ?_ … <;> decide` is the working form.

Calibration (E21): held-out bodies fell 194 → 15 lines (−92%, excluding the already-generic
case); whole files of the migrated clusters fell 36% (C-step 3,973 → 2,527), because the per-kind
statements, 15–30 lines each, are kept verbatim by the rule that used lemmas keep their
statements. Removing the per-kind statements themselves (callers instantiate the generic rule)
is the next step and needs the callers in `VsaIris` to move.

## 9. Measurements (95acd019 → 832e7baf)

| measure | before | after |
|---|---:|---:|
| `Vsa/Sim/*.lean` (top level) | 204 files, 28,519 lines | 155 files, 22,196 lines |
| ISA core (the 56 files of §1b, plus `Retire.lean`) | 15,720 lines | 12,953 + 177 lines |
| all project Lean (without `riscv-lean`) | 154,067 lines | 147,374 lines |
| modules in the build | 730 | 667 |
| module-seconds, clean build (lake wall per module) | 3,283 | 2,974 |
| of which top-level `Vsa/Sim` | 333 | 232 |
| of which ISA core | 121 | 106 |
| diff | | 105 files, +1,724 / −8,158 |

Clean build of the final tip: 1,022 jobs, 9 min 59 s wall, 70 min user, load 12–19. The tip's
numbers come from `tip-modtimes.txt` (same method, earlier window), so single modules carry ±10%.
CPU of single-file compiles (min of 3, interleaved, same window): RegAccess 57.9 → 9.4 s, MemStore
11.8 → 4.7, MemLoad 4.0 → 3.1, StepJump 3.8 → 2.6, StepBranch 2.2 → 1.6, HtifStepObs 2.3 → 1.8.
One named cost: `RegAccess`'s two generic rules each split 31 cases inside one theorem, which the
build cannot spread over threads; its wall time rose 5.2 → 6.6 s while its CPU fell 6×.

Axioms: `endToEnd_refinement` and `proofElf_halts` (and every audited theorem in
`Vsa.Sim.Boot.Audit`) on `[propext, Classical.choice, Quot.sound]`; headline statements untouched
(no file under `VsaIris/Interp` or `Vsa/Sim/Boot` changed). No `sorry`, `axiom`, `native_decide`,
`bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth` added (two `set_option` lines removed
from the emptied `StepBeq`). Every theorem kept in a changed file has its statement unchanged
(checked by diffing statement text against 95acd019); 40 per-kind/per-width helpers were deleted
after checking they had no remaining use.

## 10. Decision and adoption

**Adopted** (primary measure met on every held-out case in each territory, fresh cases included;
time at parity or better except the one named cost above):

1. the **commit rule** over an abstract post-state (`Retire.lean`) with `reg_reads` as the decision
   procedure for reads through `insert` chains — law L-front + L-step + L-frame (reads);
2. the **register rule** (`gpr_cases`, `rX_bits_gpr`, `wX_bits_gpr`, `gpr_range_fin`) — law L-reg;
3. the **width layer** (`checked_mem_write_w`, `memWriteLE`/`write_ram_w`, `mem_write_value_w`,
   `mem_write_ea_w`, `vmem_write_addr_ram_w`, `checked_mem_read_data_w_of_ram`,
   `vmem_read_addr_data_ram_w`, `vmem_read_data_ram_w`, `exec_store_w`) — law L-width;
4. the **dead-weight cut** (§1a).

**Not adopted:** the patch datatype (P2): same commit rule, more lines, more failed compiles.

This branch carries no `CLAUDE.md` or `scripts/` (E16). On merge into the branch that does, add to
the CLAUDE.md table:

| Task shape | Use (never hand-roll) |
|---|---|
| Machine step of a retiring instruction (`try_step`, `stepOnce` tick/no tick, `Step`, observational step) | `try_step_retire (Fetched.of_bytes …) hexec ⟨reg_reads …⟩`, then `stepOnce_retire_*` / `step_retire_*` / `stepObs_retire`, `GoodState.retirePost`/`.tickPost` (`Vsa/Sim/Retire.lean`) — NEVER re-derive the fetch/decode front or the four retire reads per kind |
| Register read through a chain of `insert`s | `reg_reads [facts]` |
| Property of all 31 register numbers; `rX_bits`/`wX_bits` at a register number | `gpr_cases n => tac`; `rX_bits_gpr`, `wX_bits_gpr` (`RegAccess`) — NEVER a 31-arm battery or a new per-register lemma |
| 1/2/4/8-byte load or store through the Sail chain | the `_w` lemmas of `MemStore`/`MemLoad`/`ExecuteLoad`/`ValueSites` — NEVER a per-width copy |

and to `scripts/discipline_rules.tsv` (id, glob, regex, message):

```
R16	Vsa/Sim/*.lean	fetch_F_Base	a retiring step re-derives the fetch front: use try_step_retire (Retire.lean)
R17	Vsa/Sim/*.lean	COUNT>8:^  \| [0-9]+, 	a 1..31 register battery: use gpr_cases / rX_bits_gpr / wX_bits_gpr
R18	Vsa/Sim/*.lean	^theorem [a-z_]+_(one|two|four|eight|1|2|4|8)(_[a-z_]+)?$	a per-width copy: state it for w and instantiate
```

(`Retire.lean` and `Fetch.lean` are the two allowed users of `fetch_F_Base`.)

## 11. What remains

* The block executor's 37-arm `cases akind` (≈2,000 lines, C-block) is the largest untouched
  cluster; law L-block with a per-kind table of execute characterisations consuming
  `stepObs_retire` is its candidate.
* The per-kind statements of the step chain (15–30 lines each) stay only because callers in
  `VsaIris` name them; moving the callers to the generic rule removes about half of C-step's
  remaining lines.
* 6,188 lines of declarations off the path inside surviving `Vsa/Sim` modules (e.g. `Dispatch`
  24/411 constants used) were not removed; the reachability script, run per declaration instead of per module, lists them.
* `GoodState.insert_htif_tohost` belongs in `Frame.lean`; `MemLoad` and `MemStore` should not both
  define `split_misaligned_aligned_w`, so that the read and write layers can share lemmas; a
  width-1 `bytesT` conversion would move `read_ram_one_total` onto the generic lemma.
* C-exec (698 lines) and C-sys (1,674 lines) were not piloted; their per-case cost is already low.

Reachability script (run from the worktree with `lake env lean --run Reach.lean`; writes
`module<TAB>used<TAB>total` per module):

```lean
import VsaBoot
open Lean

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

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `VsaBoot}] {} (loadExts := false)
  let rootMods : List Name := [`Vsa.Sim.Boot.Audit, `Vsa.Lang.Basic, `Vsa.Lang.Runs,
    `Vsa.Lang.SmallStep, `Vsa.Lang.Densify, `VsaIris.Lang.Route]
  let mut roots : List Name := [`Vsa.Sim.EndToEnd.endToEnd_refinement, `Vsa.Sim.Boot.proofElf_halts]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if rootMods.contains env.header.moduleNames[idx.toNat]! then roots := n :: roots
  let cl := closure env roots
  let mods := env.header.moduleNames
  let mut used : Std.HashMap Nat Nat := {}
  let mut total : Std.HashMap Nat Nat := {}
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      total := total.insert idx.toNat (total.getD idx.toNat 0 + 1)
      if cl.contains n then used := used.insert idx.toNat (used.getD idx.toNat 0 + 1)
  let h ← IO.FS.Handle.mk "reach.tsv" .write
  for i in [0:mods.size] do
    h.putStrLn s!"{mods[i]!}\t{used.getD i 0}\t{total.getD i 0}"
```

## 12. Follow-up after rollout (branch `exp-M2`, 2026-09-30)

From `exponentiate` f16fdb8d. Four tasks: move callers onto the generic rules and delete the
per-kind statements left without users; collapse the block executor's `cases akind`; give
`MemLoad` and `MemStore` one width layer; remove off-path declarations inside live files.
Commits: ac12fe86 (tasks 1–3), ecde2758 (task 4), e1e4cf81 (`stepObs_jal` on the rule), plus this
record. Full `lake build` green after each batch (1,008 jobs).

### Task 1: callers on the generic rules

One observational commit rule was missing: `stepObs_retire` needs a `try_step` fact, so every
caller went through a per-kind `stepObs_K`. Added `stepObs_exec npc vm (F : Fetched σ pc ast)
hexec (R : RetireReads σ3 npc vm) (hG3 : GoodState σ3) hi` (`StepObs`) and
`GoodState.prelude` (`Retire`: the two prelude inserts keep the pins). A call site now reads
`stepObs_exec npc vm (Fetched.of_bytes …) (execute_K_char …) ⟨reg_reads …⟩
((hG.prelude _).insert_nonpinned …) hi`; its `ReadsLikePost σ' (retirePost σ3 npc vm)` is
definitionally the old `sigmaPost_K` form, so consumers (`jalStep_of_obs`, `StepFrameOut.of_alu`,
`aluStep_of_obs`, …) take it unchanged.

Moved: `BlockTerm.term_step_bt` (branch taken/not taken, `j`, `jr`), the Jmp/Memcpy4/Strlen sites,
`stepObs_jalr` (statement kept, body one line), `stepObs_jal` (same), `JalSite.exec`,
`AllocSltu`, `SymObsStep`, and the `StepGen` templates (ALU observation, `jalr`, `jalr ra`).
`jalExec_word`, `MallocFastJal` and the generated `jal` lemma now instantiate `JalSite.exec`
with a decided `Cert` instead of repeating the step (four copies of the same 15-line block before).
Every `rX_bits_xN`/`wX_bits_xN` call outside `VsaIris/Interp` uses `rX_bits_gpr`/`wX_bits_gpr`.

Deleted as unused: `try_step_{alu,store,branch_taken,branch_nottaken,jal,jalr,j,jr}`, every
`stepOnce_K_{tick,notick}`, `step_K_{tick,notick}`, `sigmaTick_K`, `goodstate_sigmaPost_K`,
`stepObs_{alu,store,branch_taken,branch_nottaken,j,jr}`, 57 of the 62 register instances,
`get?_sigmaTick_jalr`. The step-chain files fell 1,648 → 349 lines (`StepJump` 703 → 72).

Left, with their callers:

| declaration | caller | rewrite |
|---|---|---|
| `stepObs_jalr`, `rX_bits_x16`, `wX_bits_x1` | `VsaIris/Interp/CallJalr.lean` 191–204 | below; checked by compiling a copy of the file against this branch |
| `stepObs_jal`, `wX_bits_x1`, `get?_sigmaPost_jal`, `sailOutput_sigmaPost_jal` | `Vsa/Compiler/Lift.lean` 306–311 (pr13 tool; not on this branch) | same shape as `JalSite.exec`; not compiled here |
| `stepObs_tohost_putchar`, `stepOnce_tohost_G` | `Console`, `Vsa/Compiler/Lift` | HTIF steps have no retire shape (halt, pinned `htif_tohost`) |
| `sigma3_K`, `sigmaPost_K`, `get?_sigmaPost_K` | statements of `ObsStep`, `SymJalr`, `Tools`, `AluStep`, `SymObs`, `StepFrameOut` | kept: they name states in live statements |

`CallJalr` rewrite (replaces the `stepObs_jalr … hi` term of the `obtain`):

```lean
    stepObs_exec (u := c.steps) (Sail.BitVec.update (tgt + sign_extend (m := 64) (0x000#12)) 0 0#1) vm
      (Fetched.of_bytes hG hpc hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
        (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
        (Vsa.Sim.decodeW (w := 0x000800e7#32) (afterPrelude c.σ)
          (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
          (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
          (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg)))
      (execute_jalr_char (0x000#12) (regidx.Regidx 0x10#5) (regidx.Regidx 0x01#5) _ tgt _ _
        (by reg_reads [hG.misa]) (by reg_reads [hG.cur_privilege]) (by reg_reads [hG.mseccfg])
        (by reg_reads [])
        (rX_bits_gpr _ 16 (by decide) (by decide) tgt
          (by show (afterNextPC (afterPrelude c.σ) (0x800039f4#64)).regs.get? Register.x16 = _
              rw [get?_afterNextPC c.σ (0x800039f4#64) _ (by decide) (by decide)]; exact hrs))
        (by rw [htgt]; exact hal)
        (wX_bits_gpr _ (BitVec.addInt (0x800039f4#64) 4) 1 (by decide) (by decide)))
      ⟨by reg_reads [hG.hart_state], by reg_reads [], by reg_reads [], by reg_reads [hmi]⟩
      (((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned (by decide) _) hi
```

`Lift` rewrite (unchecked): `stepObs_exec (u := u) (A.pc + sign_extend (m := 64) (evenJ off)) vm
(Fetched.of_bytes hG hc.pc hb0' hb1' hb2' hb3' hlo hhi hal (by rw [bytes_word, encode_rvc])
(bytes_word _) hdec) (execute_jal_char (evenJ off) (gprIdx 1) _ A.pc _ _ _ (by reg_reads [])
(by reg_reads [hc.pc]) (by reg_reads [hG.misa]) htgt (wX_bits_gpr _ _ 1 (by decide) (by decide)))
⟨by reg_reads [r4, hG.hart_state], by reg_reads [r1], by reg_reads [r2], by reg_reads [r3, hvm]⟩
(((hG.prelude _).insert_nonpinned (by decide) _).insert_nonpinned r5 _) hc.tick`, where `hbk'` are
its four `by rw [hmem]; … hb k …` byte facts. After both rewrites `stepObs_jal`, `stepObs_jalr`,
`try`-free `StepJump` reads aside, the last three register instances can go.

### Task 2: `block_mem_run`

The 37-arm `cases akind` (≈2,000 lines) became two families on the commit rule, split by
`isStoreM : MKind → Bool`: one fetch front (`Fetched.of_bytes`), one commit and one IH application
per family. The per-kind content is two tables: `exec_reg_kind` (33 kinds, one `execute_*_char`
or `exec_*_ramv`/`_totv` application of about two lines each, producing
`sigma3_alu … (gprRT a.rd (wvalM a L bs))`) and `exec_store_kind` (4 kinds, producing
`sigma3_store σ a.pc (applyW σ.mem (wentryM a L))` and the unchanged bytes below `tohostAddr`).
Family bookkeeping (`stepGM_reg`, `wlogM_store`, …) is proved by `cases k <;> first | rfl | cases h`.
`block_mem_run` and every declaration of `BlockMem` named elsewhere keep their statements;
`exec_sb_bm`/`exec_sh_bm` became three-line instances of `exec_store_w`. 2,664 → 894 lines,
6.21 → 4.12 s (same oleans, interleaved).

### Task 3: one width layer

`MemWidth` (132 lines, imported by both) holds `effectivePrivilege_machine` (any access other
than instruction fetch; replaces `effectivePrivilege_data`/`_store`), `tmod_toNatInt_of_mod`,
`to_bits_ofNat`, the single `split_misaligned_aligned_w`, and `pmaCheck_ram` for
`acc = Load Data ∨ acc = Store Data` (replaces `pmaCheck_ram_read`/`_write`, which were the same
60-line proof). `MemLoad` + `MemStore`: 1,817 → 881 lines (with task 4's per-width copies);
4.47 → 2.67 s and 6.34 → 4.99 s interleaved, `MemWidth` 1.9 s.

### Task 4: off-path declarations

Per-declaration reachability (the §11 script, extended to write, for every ranged constant, its
owner declaration, source range, liveness and direct users). Roots: `endToEnd_refinement`,
`proofElf_halts`, all of `Vsa.Sim.Boot.Audit`, `Vsa.Lang.*`, `VsaIris.Lang.Route`; every
declaration of `BlockTerm`, `DivSpec3`, `HtifLift`, `HtifStepObs`, `Muldi3Spec`, `StepCount`
(imported by the tools in main); and every `Vsa/Sim` declaration named in the sources pr13 adds
(`Vsa/Compiler`, `Vsa/AbsInt`, `VsaIris/WhileLogic`, `Vsa/While`, …; read with `git show pr13:…`,
matched by unique short name or by qualified suffix). Scope: `Vsa/Sim/*.lean` and `Vsa/Sim/rows`
(not `Boot`, not the generated `Code`). A block (maximal declaration range, including a
structure's fields) is removed when no constant in it is live, every direct user is itself
removed (fixpoint), no remaining source text names it outside comments (simp lists, tactic
arguments, tools), and it defines no syntax, macro or elaborator. 4,598 lines left 68 files; 15
modules were emptied and deleted, their importers taking their imports. The build was green on
the first try; a second round finds nothing more.

Defects found: (1) emptying a `mutual … end` block leaves a parse error; the pass now drops empty
`mutual` blocks. (2) A textual check on short names alone keeps whole modules alive through
common field names (`transport`, `mono`, `ra`); names shared by several declarations are matched
by their qualified suffix, and a structure's fields count as the structure. (3) `local macro` is
not caught by the syntax guard; the only instance was used only by a dead theorem in the same file.

### Measurements

Lines (`wc -l`) and user CPU of `lake env lean` at 8 threads, min of 3. The machine ran two other
builds throughout (load 27–29 on 32 cores), so separate before/after runs drift: files that did
not change were 14% slower in the after run (median) and `VsaIris` files 40–60% slower. Where the
old file still compiles against the new oleans, the two versions were timed interleaved
("paired"); the other rows are separate runs.

| file | lines before | lines after | CPU s |
|---|---:|---:|---|
| `BlockMem` | 2,664 | 894 | 6.21 → 4.12 (paired, same oleans) |
| `StepJump` | 703 | 72 | 3.54 → 1.41 (paired) |
| `StepBranch` | 357 | 96 | 1.96 → 1.21 (paired) |
| `StepAlu` | 187 | 35 | 1.28 → 0.85 (paired) |
| `StepStore` | 160 | 33 | 1.52 → 1.21 (paired) |
| `StepObs` | 241 | 113 | 1.03 → 1.12 (separate) |
| `RegAccess` | 518 | 188 | 11.36 → 11.52 (paired) |
| `MemLoad` | 710 | 196 | 4.47 → 2.67 (paired) |
| `MemStore` | 1,107 | 685 | 6.34 → 4.99 (paired) |
| `MemWidth` | 0 | 132 | 1.93 (new) |
| `ExecuteLoad` | 422 | 347 | 2.02 → 2.34 (separate) |
| `BlockTerm` | 870 | 880 | 2.33 → 3.41 (separate) |
| `SnprintfSitesRet5` | 146 | 116 | 0.88 → 1.36 (separate) |
| `OutputAliasPhysical` | 463 | 278 | 22.48 → 11.09 (paired) |
| `MemRegion` | 283 | 109 | 1.88 → 1.24 (paired) |
| `ValueSpec` | 207 | 174 | 8.05 → 7.09 (paired) |

| measure | before (f16fdb8d) | after (e1e4cf81) |
|---|---:|---:|
| `Vsa/Sim/*.lean` (top level) | 155 files, 22,196 lines | 143 files, 15,915 lines |
| `Vsa/Sim/rows` | 193 lines | 62 lines |
| changed `Vsa/Sim` files (72) | 14,266 lines | 7,985 lines |
| all project Lean (without `riscv-lean`) | 147,374 lines | 140,891 lines |
| build jobs | 1,022 | 1,008 |
| CPU, 41 paired files that survive | 104.2 s | 85.1 s |
| CPU, 6 deleted modules whose old version compiles | 6.7 s | 0 |
| CPU, all `Vsa/Sim` top level, separate runs | 221.4 s | 215.4 s (after run at ≈1.14× load) |
| diff vs `exponentiate` | | 82 files, +707 / −7,190 |

One named cost: a call site of `stepObs_exec` discharges its four retire reads with `reg_reads`
where the per-kind lemma had done it once. Measured in isolation, 30 ALU-style retire reads plus
their `GoodState` terms cost 2.7 s single-threaded (≈90 ms each). `BlockTerm` (four arms) and
`SnprintfSitesRet5` carry it; the generated `jalr` and observed-ALU step lemmas carry it per
site. The generator-driven `VsaIris` modules slowed by the same factor as `VsaIris` modules the
change does not touch, so the aggregate effect is within the noise of this machine.

Axioms of `endToEnd_refinement`, `proofElf_halts`, `block_mem_run`, `stepObs_exec`, `pmaCheck_ram`:
[propext, Classical.choice, Quot.sound]. No file under `Vsa/Sim/Boot` or `VsaIris/Interp` changed.
No `sorry`, `axiom`, `native_decide`, `bv_decide`, `ofReduceBool`, `maxHeartbeats` or `maxRecDepth`
added (`MemWidth` has no `set_option`).

### Open next

* The two rewrites above (`CallJalr`, `Lift`) delete `stepObs_jal`, `stepObs_jalr` and the last
  three register instances.
* Retire reads as rules instead of `reg_reads`: `RetireReads.prelude hG hmi` for
  `afterNextPC (afterPrelude σ) pc` and `RetireReads.insert` for an insert of a register outside
  the four (one decided `RetireFree r`), so a call site builds its reads as a term. That removes the
  per-site cost above and shortens every `stepObs_exec` call by a line.
* The CLAUDE.md row proposed in §10 for machine steps should name `stepObs_exec` as the
  observational entry point.
