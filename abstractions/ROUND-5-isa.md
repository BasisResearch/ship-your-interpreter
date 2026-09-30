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
`Vsa.Lang.*`, `VsaIris.Lang.Route`). The script is `Census.lean` / `Reach.lean` (kept outside the
repo; recipe in §7).

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
