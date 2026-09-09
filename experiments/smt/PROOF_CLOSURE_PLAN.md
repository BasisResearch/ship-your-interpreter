# Proof closure plan

Prove `remainingWork_closed : RemainingWork interpRunLayout`, then discharge
the `RemainingWork` hypothesis of `endToEnd_refinement`.

## Status

**36 of 63 base fields certified; 27 remain.** `DivWork`, `ErrWork`, and the
final constructor remain open. The certified fields cover literals, unary and
logical operations, nine integer cells, break/continue, both initializers,
all four while cases, the expression statement, all three `if` cases, all
four for-loop cases, and the null return. Their shared entry and ownership
suppliers still need integration.

The null return, the null declaration, the initialised declaration, the
block, and the for-loop start are on the helper-call layer (`HelperCall`,
task 4): the generic in-frame call of a runtime helper from any parked
state, one adapter per callee, and the shared retslot/declaration tails.
`hSRetNull` is closed. `hSVarNull` and `hSVarInit` are closed down to the
`env_define` contract (`EnvDefineContract`), plus for `hSVarInit` the payload
window (`VarInitPayloadOff`); `hSBlock` and `hSForStart` are closed down to
the `env_new` contract (`EnvNewContract`). Both contracts are proved from
named per-entry ledgers of external facts (allocator invariant and runs,
ownership, pinned `gp`, geometry; task 2), so every statement field above
rests on those ledgers only. The child's coherent exit is the recursor
motive (`mEvalE := EvalReturnIH TrivialOwned`), not a premise. The three
legacy files of these leaves (1,548 lines) are removed.

The expression statement, the three `if` cases, and the four for-loop cases
are closed by the parametric statement-arm layers (`EvalChildArm`,
`StmtChildArm`, `TruthyCopy`, see task 4): generic dispatch of an expression
or statement child (from the statement entry or from an in-frame arm state),
exit kits, condition copy with `value_truthy`, reflected routes from any
parked return, the normal-exit and return heads, the loop-head re-entry, and
the map/memory rebase, instantiated per arm by a descriptor and
certificates. The value-return arm is closed on the layer down to one named
payload premise; the initialised-declaration arm's resume needs the
`env_define` contract (task 4).

The four string-comparison cells (`hStrLt`, `hStrLe`, `hStrGt`, `hStrGe`) are
on the string-comparison cell layer (`StrCmpCell`, task 4): one descriptor and
one decided certificate per operator instantiate ONE generic proof of the
dispatch, the kind check, the `strcmp` call, the rejoin, the operator's sign
tail, and the `value_bool` box. Each cell is closed down to the two residuals
the layer shares, `StrCmpOperandsSupply` (both operand payloads are
`strcmp`-admissible regions at the actual return) and `StrLeftSurvivesSupply`
(the left string survives the right child). The second is the `hVlSurv`
premise of `blockB_binary_data`, recorded below as an obstruction for arena
payloads; it is the same premise the equality cells carry.

The last completed checkpoint passed 1,587 modules (private resumed build
after the sequence-boundary amendment), 1,054 declaration axiom audits
(1,040 with exactly {propext, Classical.choice, Quot.sound}, 14 axiom-free),
four boundary regressions, 200 Python tests, and the generator checks.
There are 56 inherited discipline findings (unchanged by this checkpoint).
Receipt: `/private/tmp/vsa-helpercall/receipt.json`.

Indexed child returns and the shared coherent epilogue now pass the full
1,539-module build and cache-fingerprint verification. Log:
`/private/tmp/vsa-indexed-child/integration.log`. The parametric layers, the
closed expression statement, the three `if` cases, and the four for-loop
cases pass the resumed private build, the complete-library census (35 FOUND
of 65 inventoried fields), the four boundary regressions with a refreshed
input lock, 200 Python tests, and the axiom audit of every new declaration.
Evidence: `/private/tmp/vsa-evalchildarm/` (`integration*.log`,
`all-fields*/`, `boundary-lock-changes*.json`, `discipline-delta*.json`).

The helper-call layer and its three fields pass the resumed private build
(1,566 modules, exit 0; log `/private/tmp/vsa-helpercall/logs/integration.log`)
and the census of the affected fields (`hSRetNull` FOUND; `hSRet`,
`hSVarNull`, `hSVarInit` NO_MATCH, each with a hypothesis-taking supplier;
`/private/tmp/vsa-helpercall/census/`), the four boundary regressions with
the input lock refreshed for the eight changed proof sources
(`/private/tmp/vsa-helpercall/boundary/summary.json`,
`boundary-lock-changes.json`), 200 Python tests, and the generator checks.
The discipline gate (stage a4) reports 32 inherited findings and none in the
new files (`discipline-delta.json`); the gate stops there, so stage c was
run by hand against the private build. Twelve audit entries naming
declarations no longer present (`execVarNullSimD`, `bin_add_cell_ofBundle`,
`argsConsResid_of_oracle`, `argsNilResid_of_hop`, the three
`native*Spec_of_span`, `errFamily_ofArmLinks`,
`divEntryDrive_of_driveToLoopHead`, and the commented-out `errFamilyClosed`,
`errFamilyClosed_ofClasses`, `errFamily_ofShared`) were pruned, and
`rows/EvalVarBridgeCallee` (compiled but never imported by `Vsa`) is wired so
its two audited theorems resolve. The hand-run audit of the 987 remaining
entries reports every axiom set within `propext`, `Classical.choice`,
`Quot.sound` (13 entries axiom-free; no `sorryAx`, `native_decide`, or
`ofReduceBool`; log `/private/tmp/vsa-helpercall/logs/stagec.log`). The full
SMT/fuzzer campaigns are pending.
The string-comparison cell layer passes the resumed private build (1,591
modules, 25 rebuilt, exit 0; log
`/private/tmp/claude-501/-Users-kirancodes-Documents-code-verified-semantic-abstraction/3f98120e-d469-40e3-ab61-f89a096c4e7c/scratchpad/integration.log`),
the backend verification, the four boundary regressions with the input lock
refreshed for the fifteen changed proof sources (`boundary/summary.json` and
`boundary-lock-changes.json` in the same directory), 200 Python tests, the
generator checks, and the discipline gate with the 56 inherited findings
unchanged and none in the new files. The stage c audit (run by hand, the gate
stopping at stage a4 as before) covers 1,060 entries after replacing the seven
retired scaffolding names by the seven new theorems and removing eight
duplicate names from the list; every axiom set is within `propext`,
`Classical.choice`, `Quot.sound` (`stagec3.out` in the same directory).

The induction-hypothesis tower (task 0) passes the resumed private build
(1,621 modules, 455 rebuilt, exit 0), the backend verification, the four
boundary regressions with the input lock refreshed for 26 changed sources,
241 Python tests, the four generator drift checks, stage b, and the
discipline gate with the 56 inherited findings unchanged and none in the 41
new files; the stage c audit (run by hand) covers 1,081 entries after adding
the tower's key theorems. Evidence under the session scratchpad
(`integration2.log`, `boundary2/summary.json`, `boundary-lock-changes-2.json`,
`stagec4.out`).

The allocator layer (task 2) lands `Vsa/Sim/AllocOff.lean` and
`Vsa/Sim/AllocLedger.lean`: one run-global `AllocLedger` in place of the
allocator fields each per-entry ledger restated, one `OwnedOff`/`EntryOff` proof
in place of the per-lane separation derivations, ledger movement
(`HeapOwned.fresh`/`.free`/`.pushClosure`), and the `malloc`/`free` call adapters
`mallocReturn_of_parked`/`freeReturn_of_parked`. The two modules add 48
declarations, 26 of them audited by `#print axioms` at exactly `propext`,
`Classical.choice`, `Quot.sound`. Three landed sites are
reseated on it: `envNewPushedRepr` and the `env_define` append and grow lanes
(53 hand lines of separation replaced by 24, all of it projection). Discipline
rule R14 catches a hand-rolled allocator ledger field; the gate reports 68
findings, the 56 inherited ones plus the 12 per-entry ledger declarations the
new `of_alloc` projections supply and the reseat will delete.

Verified over the eleven-module dependency closure of the change plus `Vsa` and
`VsaRun`, all thirteen compiling clean in 62 s with every axiom set inside
`propext`, `Classical.choice`, `Quot.sound`; the generator drift checks pass and
no source of this change is a boundary-lock input, so the input lock needs no
refresh. Log: `rebuild.log` under the session scratchpad. NOT yet run for this
change: the complete-library census and the full resumed integration build, both
deferred because a second session holds concurrent in-flight edits to the
induction-hypothesis tower in the same checkout.

Recompute the census before changing the certified count.

## Remaining tasks, in dependency order

### 0. Induction-hypothesis clauses through the tower

A new fact about a child's execution (a memory footprint, payload ownership,
shared-byte agreement) is a CLAUSE, never an edit of `mEvalE` or of a landed
row's post. The tower that makes a clause cheap:

1. Effect summaries: every arm block has a footprint-carrying sibling
   (`blockC_<cell>_footprint`, `blockB_*_footprint`, `blockD_v_rec_footprint`)
   and every row an `EvalIHF F` supplier (`Vsa/Sim/ExitFootprint.lean`, the
   `*Footprint.lean` modules). The landed theorem is always the projection of
   its sibling, so no certified row changes statement.
2. Clause metatheorems: a clause SHAPE is one lemma over `MemFootprint`
   (`Vsa/Sim/IHClauseFootprintMeta.lean`); the per-case steps of a clause are
   generic over arms (`Vsa/Sim/IHClauseGeneric.lean`, allocating arms in
   `IHClauseGenericAlloc.lean` over the allocator contracts).
3. Generation: `scripts/ih_clauses.tsv` + `scripts/gen_ih_clause.py` emit the
   clause's `EvalIHWithM` motive, one named `Residuals` field per recursor
   case, and the recursion (`rows/IHClause_<Name>.lean`); declaring a clause
   never breaks the build.
4. Automation: `scripts/ih_clause_status.py` (WIRED/HOOK/MANUAL per field,
   backend lemma probe, `--suggest` drafts), `ih_clause_fuzz.py`
   (refute-before-prove), `ih_clause_ledger.py`, `proof_slice --structure`,
   `check_all.sh` stage a5.

Open steps on the tower, in order: (a) DONE: the generator has a `guard`
column (`scripts/gen_ih_clause.py`, `scripts/ih_clauses.tsv`) — a guard makes
the `EvalE` motive `<guard> → EvalIHWithM extraM …`, and the new tag
`unguarded:<term>|<proj_1>|…|<proj_k>` wires a step stated without it. Clause
`FootprintNA` (`Vsa/Sim/rows/IHClause_FootprintNA.lean`, guard
`IHClauseGeneric.noAllocExpr e = true`) has 13 of 15 fields wired: the three
allocating cases vacuously (`footprintNA.{hAssign,hFn,hCall}`), the four leaves
from the unguarded closed leaf steps, and `hNeg`/`hNot`/the four logical steps
from `footprintNA.<case>` applied to the closed row contracts of
`Vsa/Sim/IHClauseGenericSupply.lean`. Clause `Footprint` wires the four closed
leaves and the six one-child arms (`IHClauseGeneric.footprint.<case>`) and keeps
five `generic:footprint` hooks (`hVar`, `hBinary`, and the three allocating
cases, which are FALSE at `noArenaFoot`). OPEN in (a):
`FootprintNA.hVar` (supply from `Rows.evalVarIHF` over `Rows.VarLeafResidF`;
`footprint.hVar_of`'s `VarPinnedSim` is uninhabitable as stated) and `FootprintNA.hBinary` (`footprint.hBinary_of_cells` needs
`BinaryFootprintCells`), i.e. step (b); the guarded clause is a stepping stone —
allocating arms need the `allocFoot` family of task 2. (b) LANDED except the var
leaf (`Vsa/Sim/IHClauseGenericSupply.lean`): the six one-child steps
`footprint.{hNeg,hNot,hOrTrue,hAndFalse,hOrFalse,hAndTrue}` are CLOSED from the
landed `eval<Arm>IHF` suppliers; the nine `IntCellF` cells are closed from
`bin<Op>CellF_of` + `ScaffoldRows.field_hI<Op>` (division's `INT64_MIN / -1`
subcase is the named premise `DivOverflowCellF`, the footprint twin of
`eval_binary_row`'s `hDivOv`); `eqCellF_of`/`neCellF_of`
(`Vsa/Sim/rows/EvalEqNeRowFootprint.lean`, over `eqBlockC_bridge_footprint` ≫
`blockC_eq/ne_footprint`) supply the two `EqCellF` cells from the landed
`BinEqCell` residuals; and `footprint{,NA}.hBinary_of_base` closes `hBinary` on
exactly `eval_binary_row`'s remaining hypotheses.
`BinaryHeadFootprintSupplyCov` is DISCHARGED (`binaryHeadFootprintSupplyCov`)
over the parametric head `blockB_binary_footprint_gen` (`EvalBinSim.lean`; the
landed `blockB_binary_footprint` is its projection at the trivial left-child
fact), so `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_clauses` need only
`StrCmpOwnedOperands` and the two closed clause recursions. The four
`BinStrCmpCellF` cells are CLOSED but for the shared operand residual: the
PRODUCT clause (footprint × payload coverage, `EvalIHFP noArenaFoot`) is declared
as the TSV line `FootprintCov` (`Vsa/Sim/rows/IHClause_FootprintCov.lean`,
generator kind `motive` — the `pred` column is the `EvalE` motive itself, since
the coverage half is indexed by the returned value), with the four leaves and the
six one-child arms wired from `IHClauseGeneric.footprintCov.<case>`
(payload-free results, plus the string literal's `evalStrPayloadIHF`) and the
same five steps open as `Footprint`. `Vsa/Sim/IHClauseGenericSupply.lean` states
the cell with its left child at the product clause (`BinStrCmpCellFP`), supplies
it from `StrCmpOperandsSupply` alone (`binStrCmpCellFP_cov`, over
`binRow_strcmpF_cov` and `binaryHeadFootprintSupplyCov`), and lowers it to the
plain `BinStrCmpCellF` through the closed product clause (`binStrCmpCellF_cov` at
`FootprintPayloadClause`); `binaryFootprintCells_of` and
`footprint{,NA}.hBinary_of_base` therefore take `StrCmpOperandsSupply` and
`FootprintPayloadClause` in place of the four cells. Left open in (b):
`hVar` at the `VarPinnedSim` shape (superseded: `Rows.evalVarIHF` over
`Rows.VarLeafResidF` lands the leaf; wire it in place of `footprint.hVar_of`),
and `hBinary`'s remaining `DivOverflowCellF` and equality pair; (c) declare `Call`/`ExecSeq` motives in the
`motives` column so `hCall` receives the callee's clause; (d) the allocating
family `allocFoot` over `MallocRun`/`HeapOwned.pushClosure`/`EnvNewContract`;
(e) DONE: `scripts/gen_footprint_row.py` + `scripts/footprint_rows.tsv` emit all
fifteen `*RowFootprint` modules (five family templates; `--check` in stage a3), and
`ExitFootprint.lean` carries the shared `intCellFoot`/`truthyArgCellFoot` whose
`_noArena` lemmas close the cell half of every `<arm>NodeFoot_noArena`. The per-op
`<op>CellFoot` stay stated beside their cells in the row files (definitionally the
shared predicate); folding them into aliases needs an edit of the landed row files.
`StrCmpOwnedOperands` (`Vsa/Sim/StrCmpCellClauses.lean`) is UNREACHABLE AS
STATED, and the verdict is stronger than "unproven": it quantifies an arbitrary
configuration constrained only by `TwoSubReturn`, which pins the operands solely
by `ValueRepr … (.str s)`, so the payload pointer may lie inside the stack,
inside the arena, or in the top eight bytes of the address space, and no shared
set satisfies `SharedGeom` for such a configuration. The derived-theorem
technique (keep the name, derive the content) was tried and does not fit. CLOSED
BY RETENTION instead: `blockB_binary_footprint_gen2` (`Vsa/Sim/EvalBinSim.lean`)
retains `BinaryOperandRetained` at the head's actual return, with the left
operand transported across the right child's footprint by
`ownedSlot_head_transport`; `binRow_strcmpF_owned`, `binStrCmpCell_of_owned` and
`ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned` consume it there. Every landed
name keeps its statement; the configuration-quantified definition survives as a
documented dead branch. The four string-comparison cells now take exactly a
shared-set choice (`OwnedIndex`, discharged at `stdShared` by `ownedIndex_std`),
the Layout premise `SharedTopSlackAll` (the pinned AST region and the arena end
far below `0x100000000`, so the `strcmp` word loop's eight-byte read stays in
RAM), and the two product-clause recursions.

The product clause is `FootprintCov` (`scripts/ih_clauses.tsv`, generated into
`rows/IHClause_FootprintCov.lean`), declared at the landed `EvalIHFP noArenaFoot`.
It needed a new clause KIND: `ValuePayloadCovered` is indexed by the RETURNED
VALUE, which an `EvalExtraM` cannot see, so `kind = motive` takes the `EvalE`
motive itself as the predicate. Ten steps are closed;
`binStrCmpCellF_cov`/`binStrCmpCellFP_cov` supply the four string cells, and
`hBinary`'s residual set shrank from seven to three.

After (a)–(d) the four string cells close from `StrCmpOwnedOperands` alone,
and `hEq`/`hNe` lose their `hVlSurv` conjunct the same way.

The two premises of `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of_owned` are supplied
by ONE recursion: the clause `FootprintPayloadOwned` (`scripts/ih_clauses.tsv`,
kind `motive`, guard `IHClauseGeneric.noAllocExpr e = true`, generated into
`rows/IHClause_FootprintPayloadOwned.lean`) at the landed `EvalIHFPO stdShared
noArenaFoot`; the right-operand premise `FootprintOwnedClause` is that clause
with the coverage conjunct dropped (`EvalIHFPO.forgetCov`). The three conjuncts
cannot be assembled from the landed `FootprintCov` and `OwnedPayload` clauses —
two `EvalIHWithM` recursions each quantify their own reached configuration — so
the steps are proved at the conjunction in `Vsa/Sim/IHClauseGenericProduct.lean`,
over the same rows the three landed families use: `EvalIHWithM.monoD` reads the
ownership and coverage halves off the child's OWN exit (`EvalExitD`'s
`ValueRepr`) for every payload-free result, `evalStrProductIHF` lands all three
conjuncts for the string literal at one run of `evalStrSimP_exact`, and
`IHClauseGenericProduct.hBinary` dispatches the binary arm with the four string
comparisons discharged by `binRow_strcmpF_owned` AT THE STEP'S OWN CHILD IHs
(the only place the left child's coverage and both operands' ownership exist
together). Thirteen of fifteen fields are wired; `hVar` (`VarProductStep`) and
`hBinary` (`DivOverflowCellF` + the two `BinEqCell`s) stay residual. The cells
close at `BinStrCmpCellNA` — the `BinDispatchRow` field restricted to operands
that do not allocate — because the guard is what makes `hAssign`/`hFn`/`hCall`
and `.add` vacuous; lifting it needs the `allocFoot` family of (d)/task 2.

OBSTRUCTION (the `SharedTopSlackAll` premise). `SharedTopSlackAll stdShared` is
FALSE, not merely unproven: `stdShared` is the envelope `k < 0x100000000`, which
contains the top eight bytes of the address space
(`not_sharedTopSlackAll_std`, `Vsa/Sim/IHClauseGenericProduct.lean`), so
`ScaffoldRows.field_hStr*_closed` (`Vsa/Sim/rows/StrCmpCellsOwnedClosed.lean`)
are vacuous as stated. And no index repairs it while
`AstRegionSpec.hi_ram` is `hi ≤ 0x100000000`: `OwnedIndex.ast` puts every byte of
every entry's AST region into the shared set, so the slack forces `hi + 7 ≤
0x100000000` on every AST region (`astRegionSlack_forced`), which the entry does
not carry. FIX: amend `AstRegionSpec.hi_ram` (`Vsa/Sim/InterpEntry.lean`) to
`hi + 8 ≤ 0x100000000` at its concrete Layout supplier. The landing pad is
already in place: the repaired index `stdSharedSlack` has `SharedTopSlackAll` as
a THEOREM (`sharedTopSlackAll_stdSlack`), `OwnedIndex stdSharedSlack` reduces to
the two named entry-layer premises `AstRegionSlack`/`ArenaSlack`
(`ownedIndex_stdSlack`), the clause is generated at it
(`FootprintPayloadOwnedSlack`), and `ScaffoldRows.field_hStr*_closedSlack` close
the four cells there with no false premise; the amendment discharges
`AstRegionSlack` outright.

#### The AST-region slack amendment

`AstRegionSpec.hi_ram` (`Vsa/Sim/InterpEntry.lean`) and its statement-side twin
`StmtRegionSpec.hi_ram` (`Vsa/Sim/ExecEntry.lean`) bounded the syntax region by
`hi ≤ 0x100000000`, the top of RAM. The `strcmp` word loop reads eight bytes at
a time and may read past a payload's final NUL, so that bound left the read
unjustified, and `IHClauseGenericProduct.astRegionSlack_forced` shows no choice
of shared index repairs it downstream: `OwnedIndex.ast` puts every syntax byte
into the shared set, so the set inherits exactly the region's bound. Both fields
are now `hi + 8 ≤ 0x100000000`. The two must move together, because a child
expression's region is derived from its statement's; that derivation
(`EntryGroundKit`) was the only site that broke.

The amendment strengthens an already-open assumption rather than adding a new
one: no proof constructs either field from concrete layout facts, every
occurrence propagates it from the entry bundles' assumption. What it does
discharge is `AstRegionSlack`, which is that field verbatim and is now the
theorem `astRegionSlack_holds` (`Vsa/Sim/IHClauseGenericProduct.lean`). The
field itself is true of the loaded image, whose syntax region sits in low RAM,
and it is discharged with the rest of `AstRegionSpec` when the entry-side region
assumptions are replaced by exact coverage (task 1). What it buys is that the
string-comparison closure is no longer vacuous: `SharedTopSlackAll stdShared` is
FALSE (`not_sharedTopSlackAll_std`, machine-checked, since `stdShared` is the
whole `k < 0x100000000` envelope and so contains the top eight bytes), and the
repaired index `stdSharedSlack` now derives its slack from these fields instead.

`ScaffoldRows.field_hStr*_closedSlack` and `strCmpCellsNA_slack`
(`Vsa/Sim/rows/StrCmpCellsOwnedClosed.lean`) therefore no longer carry
`AstRegionSlack`; `ownedIndex_stdSlack` is applied to `astRegionSlack_holds`.
The four cells at the repaired index rest on `ArenaSlack` (supplier: the
allocator ledger's concrete arena bounds, task 2), `VarProductStep`,
`DivOverflowCellF`, and the two `BinEqCell`s — each a named premise with a
supplier, none false. Slice-checked axiom-clean.

Two consumers needed weakening. `EvalChildArm.lean` and
`WhileCondDispatchClosed.lean` derive a child expression's region bound from
its statement's and wanted the old `hi ≤ 0x100000000`; they now compose
`Nat.le_add_right` with the strengthened field. The source audit found no other
direct use at the old bound. Other occurrences feed `omega` or rebuild the
amended twin spec.

#### Verification state of the amendment

| Step | State |
|---|---|
| Both `hi_ram` fields strengthened, both consumers weakened, `AstRegionSlack` discharged | Source complete |
| Integration build, all sources, `--resume` on the private cache | All 1,640 modules fingerprint-current, exit 0, including the executable and modules outside `Vsa`'s imports. The last run rebuilt exactly the three modules edited after the preceding build began (`rows/IHClause_FootprintPayloadOwnedSlack`, `rows/StrCmpCellsOwnedClosed`, `Vsa.lean`) and reused 1,637 |
| Generator checks (`gen_m4_term_row`, `gen_term_case_bundle`, `gen_ih_clause`, `gen_footprint_row` `--check`), `git diff --check` | PASS |
| `scripts/tests` | 257 run, 12 skipped, ONE error: `BoundaryInputTests` input fingerprint drift. Every other test passes |
| Boundary lock refresh | Refreshed for the amendment's four proof sources (ELF, fixture, case inventory and expectations all unchanged). It has since drifted again on five `EnvGetSpec` modules under concurrent edit; those are not part of the amendment, so the lock is left for whoever lands them. Boundary execution rerun pending |
| `check_all.sh` stage a4 (discipline) | FAIL, pre-existing: 56 findings across 27 files, none of them modified in the tree, so all present at HEAD. Recorded here per CLAUDE.md; the amendment adds none |
| `check_all.sh` stage b (forbidden tokens) | OK — 1,639 `.lean` files scanned, no `sorry`/`native_decide`/`bv_decide`/`axiom` |
| `check_all.sh` stage c (axioms) | OK — 1,086/1,086 theorems audited, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}. Stage a4's failure aborts the script, so b and c were run standalone against the same tree |
| `check_all.sh` stage a5 (IH clause status, informational) | 7 clauses, 105 residual fields. `FootprintPayloadOwnedSlack`: 12 WIRED, 3 MANUAL (`hStr`, `hVar`, `hBinary`) |

#### Residuals left open on the tower

The current selected check of `rows/StrCmpCellsOwnedClosed` passed: 950
modules, 889 reused and 61 rebuilt. Both requested declaration audits,
`astRegionSlack_holds` and `strCmpCellsNA_slack`, use only allowed axioms.
The driver checked selected source/object fingerprints before writing
`/private/tmp/vsa-slack-discharge/run-sky3uquq/receipt.json`.
`/private/tmp/vsa-closure-work/slack-slice-receipt.json` records that receipt,
the audit log, hashes, and counts. The external process is terminal; its exact
shell exit status was not directly observed. The all-source lookup integration
build remains live. This slice does not change the certified base-field count.

The amendment closes the string-comparison cells at
`ScaffoldRows.field_hStr*_closedSlack`. It closes nothing else. Still open:

- `VarProductStep` — `hVar` at the product clause. The current recursive
  lookup already retains its write set (`env_get_lookup_from_entry`);
  `varBridge_callee` drops it. The caller interfaces also need repair and
  store ownership must reach the clause entry. See the variable-lookup audit
  below; the older immediate-frame lookup is not the active supplier path.
- `DivOverflowCellF` — the footprint twin of `eval_binary_row`'s `hDivOv`, the
  `INT64_MIN / -1` subcase.
- The two `BinEqCell`s — `hEq`/`hNe`, which lose their `hVlSurv` conjunct by
  the same retention route the string cells took.
- Guard lifting: the cells close at `BinStrCmpCellNA`, operands that do not
  allocate, because the guard is what makes `hAssign`/`hFn`/`hCall` and `.add`
  vacuous. Lifting it needs the `allocFoot` family, step (d) over task 2's
  allocator ledger.

### 1. Finish recursive return and ownership contracts

- Migrate `TermSimAssembly.mEvalE` and the execution, sequence, and call
  producers to coherent returns. Wire `ReturnRepr.bind` into binary recursion
  so results, store representation, and ownership use one selected map pair.
- Supply `PreEpilogueOwned` at each actual producer endpoint. Fresh closures
  must retain their allocation map through `blockD_v_return`.
  `EqualityReturnMapObstruction` and `CoherentReturnObstruction` establish
  why independent witnesses and entry-prefix bounds cannot supply this.
- Replace legacy `EvalGround.ast`, `ExecGround.ast`, and `SeqArrayReadSafe`
  region assumptions with exact `ExprReprWithin`/`StmtReprWithin` coverage,
  indexed arrays, and `AstReadGeometry`. Keep the fixed AST domain inside the
  evolving `SharedReadDomain`; preserve its bytes through actual effects.
- Propagate `StoreArraysReady`, source store invariants, body/stack bounds,
  and distinct addresses for the three native functions through entries.
- Replace `VarCallLinkage.payloadDisj` and its unpinned `LeafWiden` premise
  with facts about the actual returned value and memory.
  The active field is `VarLeafResid`'s `LeafReturnWiden`: its `pres` and
  `surv` quantify over every `EvalExit`, which omits byte presence and permits
  arena changes. `VarLeafResidF` retains that same premise. `evalVarSimQ`
  discards the prologue's `_hpresM`; its final post retains agreement outside
  the result slot but no presence witness. Retain presence and the exact
  footprint through the actual prologue, lookup, and copy, then derive store
  survival from the entry at that returned memory.
  `/private/tmp/vsa-closure-work/return-repair/` stages
  `evalReturn_of_exit_facts`, which consumes presence and store survival at
  one return. The existing `evalReturn_of_exit_id` keeps its statement and
  projects the new lemma. `check-return-facts.sh` passed (exit 0): 142 selected
  modules, 141 reused, one rebuilt in 38.808 seconds. Both declaration audits
  report only `propext`, `Classical.choice`, and `Quot.sound`. Receipt:
  `return-repair/backend/run-yv1xs_o6/receipt.json`. The patch remains staged;
  actual variable-return presence and store-survival suppliers, consumer
  wiring, and full integration remain open.
- Obstruction (string and equality cells): `blockB_binary_data` takes the left
  value's survival across the right child as `hVlSurv`, quantified over ALL
  memory pairs that agree outside the right child's frame, the arena, and the
  right result slot. For a string payload inside the arena that statement is
  false (the pair may differ on the payload), so `StrLeftSurvivesSupply`
  (`StrCmpCell.lean`) and the first conjunct of `BinEqCellResid` are
  supplyable only for payloads outside the arena. Cure: restate the survival at
  the right child's actual exit — the recursive motive already retains the
  store's survival (`EvalReturn`); extend it to the left temporary through
  `ValueOwned` and thread that fact into `TwoSubReturn` in place of `hVlSurv`.
  Evidence: the hypothesis shape at `Vsa/Sim/EvalBinSim.lean`
  (`blockB_binary_data`, `hVlSurv`).

Reuse the implemented separation rules, `StableUnder`, `ReprDelta`,
`OutputDelta`, `CertifiedSegment`, and `RecursiveStepGeom` throughout.

### 2. Complete allocation and resource suppliers

**The allocator layer.** Allocator facts are RUN-GLOBAL, not per entry. One
`AllocLedger` (`Vsa/Sim/AllocLedger.lean`) carries the `malloc`/`free`/`realloc`
runs (`MallocRun`, the new `FreeRun`, `ReallocInstance`), the `strlen`/`memcpy`
runs, the private footprint's arena residence, the arena/stack/HTIF geometry, the
footprint discipline `ainv_private`, the request and headroom bounds, and one new
named clause `ainv_perm` (the abstract live list is a set, needed because
`MallocContract.freeSpec` pops the head). The three landed per-entry ledgers are
now projections of it: `EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc`,
`EnvDefineMissLedger.of_alloc`. `AInvAt` states the allocator invariant at a
memory with the pinned `gp`; `AllocLedger.ainv_stable` and `.ainvAt_transport`
replace every per-entry `ainv_stable` field.

- Ownership preservation through malloc, free, reuse, and realloc is ONE proof.
  `HeapOwned.ownedOff` (`Vsa/Sim/AllocOff.lean`) derives `OwnedOff` — every owned
  extent and shared byte is outside the stack region, the allocator-private set,
  and the fresh blocks — from the ledger, the caller's stack write footprint, and
  `MallocContract.privFoot_disjoint`; `HeapOwned.transport_off`/`.repr_off`
  consume it for ownership and representation. `HeapOwned.entryOff` is its
  entry-side (`fresh = []`) presentation, `EntryOff`, in the shape the landed
  lanes consume. Ledger movement is `HeapOwned.fresh` (a block enters
  unassigned), `HeapOwned.free` (an unassigned block leaves; `HeapArena.nodup`
  and `.freshErase` supply the list side), and the existing
  `Ledger.replace`/`.replaceArray` for realloc.
- The call adapters are `mallocReturn_of_parked` and `freeReturn_of_parked`: from
  a parked call carrying the caller's ownership to a named return that hands over
  the fresh block (`MallocBlock`), the advanced invariant, the memory frame, the
  footprint (`MallocReturnAt.allocFoot`, at the `allocFoot` family of
  `IHClauseGenericAlloc`), and the caller's `HeapOwned` and `StoreRepr` survived.
  A new allocating site adds no allocator fields and no separation derivation.
- Reseated so far: `envNewPushedRepr` (27 hand lines of separation → 7 on
  `HeapOwned.ownedOff`), and the `env_define` append and grow lanes (the four
  entry-side facts, derived twice by hand, → `HeapOwned.entryOff`). Remaining
  step is DONE. `Vsa/Sim/AllocRuns.lean` now holds the runs (`MallocRun`,
  `FreeRun`, `ReallocRun`/`ReallocInstance`, `StrlenRun`, `MemcpyRun`) and the
  `AllocLedger` record BELOW every per-entry ledger, which removes the import
  cycle that had forced each ledger to restate the allocator: `MallocRun` used
  to be declared in `rows/EnvNewContractSupply.lean` and the other three runs in
  `rows/EnvDefineMissLedger.lean`, above the record that bundles them. Each of
  the three per-entry ledgers now carries ONE `alloc : AllocLedger …` field, and
  36 consumer references across the four `env_define` lane files and
  `EnvNewContractSupply` project through it. The discipline gate falls from 68
  findings to 60 and R14 from 12 to 3.
  `ainv_stable` is gone too: each ledger now carries the arithmetic fact
  `stack_hi : esp.toNat ≤ SL.hi` (the entry's own `StackOK`) and DERIVES the
  footprint discipline as a theorem, `EnvNewLedger.ainv_stable` /
  `EnvDefineUpdateLedger.ainv_stable` / `EnvDefineUpdateOracles.ainv_stable`, so
  the five consumers are unchanged. `EnvDefineUpdateOracles.arena_htif` is
  derived the same way. R14 now reports 0 and the discipline gate is back to its
  56 inherited findings. `ainv_entry` stays a field and is not flagged: it
  mentions this entry's memory and extents, so it is the per-entry
  instantiation rather than a run-global fact.
- OPEN (unchanged, and outside this layer): relating `MallocContract.privFoot` to
  dlmalloc's actual indirect bin-link writes. That is the verified-allocator
  obligation behind `MallocContract` itself, not a fact any interpreter call site
  can supply; the proof consumes it only through `AllocLedger.ainv_private` and
  `MallocContract.privFoot_disjoint`, both named.
- `env_new` is supplied: `envNewContract_of_ledger`
  (`rows/EnvNewContractSupply.lean`) proves `EnvNewContract` from
  `EnvNewLedger` (one named ledger per entry: pinned `gp`, `s0` ghost
  presence, headroom and request bounds, `M.AInv` at entry and its stack-window
  stability, `MallocRun` — `MallocContract.spec` with the console-output and
  byte-presence clauses it omits —, the private footprint inside the arena,
  arena/HTIF/stack geometry, `StoreParents`, and `HeapOwned` with the stack
  region in the write footprint). The prologue is `envNewPrologueSeg` +
  `site_80002a10_env` (`envNewParked_of_entry`), the suffix
  `envNewSuccess_run`, the pushed store `storeRepr_allocFrame` after
  `StoreOwned.repr_transport` and the frame-map rebase `storeRepr_phif_mono`
  (`envNewPushedRepr`). `env_new_spec` stays unused (its `∀ p, EnvRegions … p`
  premise is false at `p = 0`).
- `HeapOwned.pushClosure` is DONE (`Vsa/Sim/AllocOff.lean`), over
  `StoreOwned.pushClosure`: old roles and bytes survive the build's memory through
  `OwnedOff`, the fresh record takes the `closure` role at the new index, captured
  environments stay allocated, and the pushed closure's AST is shared.
- `AllocBuildEntry.hOld` and `AllocBuildTailFacts.hOld` were UNINHABITABLE, and
  are FIXED. Each demanded `StoreRepr mpre …` for EVERY `mpre` agreeing with the
  post-malloc memory outside the stack window, the arena and the result slot.
  The arena was excluded from that agreement, so `mpre` could differ arbitrarily
  inside `[A.lo, A.hi)` — and `StoreRepr.frames` reads `FrameRepr` at `φf fa`,
  which `StoreRepr.frames_arena` places inside the arena. Perturbing one frame
  byte satisfied the hypothesis and refuted the conclusion, so anything built on
  these bundles was vacuous for a non-empty store. `hExprRepr` carried the same
  defect for the same reason: the `fn` AST node is arena-resident too.
  The cure is `BuildOff p sret` (`rows/AllocClosureInhab.lean`): the closure
  build's OWN write window, the fresh 16-byte record and the 24-byte result
  slot, which are the only bytes it stores to between the post-malloc and
  post-build memories. `hExprRepr`, `hOld` and `hCodeSurvive` now take agreement
  off that window, which is both weaker as a premise (so the fields are
  inhabitable) and true of the actual build; `hMpreFrame` states the same window,
  which is stronger and is what the reflected write log satisfies. The two
  consumers are rewired: the second composes through `A.contains p 16`, since a
  byte outside the arena is outside the fresh block. `allocClosureContract_of`
  and `storeRepr_pushClosure` audit at `propext`, `Classical.choice`,
  `Quot.sound`.
  Both repaired fields are now SUPPLIED, not merely inhabitable
  (`rows/ClosureBuildSupply.lean`): `closureBuildOld_of_owned` gives `hOld` and
  `closureBuildExpr_of_owned` gives `hExprRepr`, each from `HeapOwned.ownedOff`
  plus `buildOff_of_allocOff` (the result slot is a caller stack slot, so
  `AllocOff` refines `BuildOff`). The store side composes
  `StoreOwned.repr_transport` with `storeRepr_phic_mono`; the AST side is
  `exprRepr_agreeP` over the shared bytes. All three audit at `propext`,
  `Classical.choice`, `Quot.sound`, and `buildOff_of_allocOff` is axiom-free.
  REMAINING here: the bundle's ~28 machine-side fields (registers, spill
  readbacks, chain facts) are still open, and `closurePushed_of_mallocReturn`
  needs a bridge from the `fn` arm's own malloc plumbing (`mallocCallSpec`, the
  pruned `ExitP`) to `MallocReturnAt`, since that arm does not route through
  `mallocReturn_of_parked`.
- `EnvDefineContract` is proved by `envDefineContract_of_ledgers`
  (`rows/EnvDefineContractSupply.lean`) from the two ledgers per entry,
  `EnvDefineUpdateLedger` and `EnvDefineMissLedger`
  (`rows/EnvDefineMissLedger.lean`). The hit lane is
  `envDefineUpdateLane_ledger`. A miss on a non-empty frame runs
  `envDefineMissLane` to the cap dispatch, then `envDefineMissReady_run`
  (`rows/EnvDefineMissHead.lean`): the append arm is `envDefineAppendLane`
  (`rows/EnvDefineAppendLane.lean`: `strlen ≫ malloc ≫ memcpy ≫` the append
  store block `≫` epilogue over `StrlenRun`/`MallocRun`/`MemcpyRun`, the
  store side `frameRepr_append` + `storeDefineAdvance_of_append`); the grow
  arm is `envDefineGrowLane` (`rows/EnvDefineGrowLane.lean`: `cap' ≫
  realloc(names) ≫ realloc(values) ≫` rejoin over a `ReallocInstance`, one
  owned array per call through `reallocArray_run`, the ownership ledger
  re-seated by `Ledger/Immutable/Reserved.replaceArray` and
  `StoreOwned.replaceArrays`/`storeRepr_replaceArrays`
  (`RuntimeOwnershipArrays.lean`)) then the append lane. The empty frame is
  `envDefineEmptyLane` (`rows/EnvDefineEmptyLane.lean`): the CAP-INIT block
  as `#derive_case` segs run by `segRowKeepGhost`, then the append lane
  (`cap ≠ 0`) or the grow lane's `realloc(NULL,·)` entry
  (`EnvDefineGrowKind.init`, `cap = 0`); `envDefineCapInitGrow_unreachable`
  proves the `bnez` route's chain facts contradictory. Every call site is a
  `bridgeOfSegFull` parking (`rows/EnvDefineCallRuns.lean`), so
  `sailOutput` and byte presence reach `EnvDefineReturnState`;
  `bridgeMallocPre_at` states the malloc bridge at the actual memory.
  `EnvDefineMissLedger` names the external facts: `MallocRun`, the
  `ReallocInstance` (`ReallocOps` + `ReallocRun`), `StrlenRun`, `MemcpyRun`
  (each the landed spec plus its omitted `sailOutput`/presence clauses; the
  `memcpy` route hypothesis covers the byte route and the ≤ 64-byte word
  route), `ainv_private` (the allocator invariant reads only `gp` and its
  private footprint), the private footprint inside the arena, arena/stack
  disjointness, the queried name's arena residence, alignment and
  `StrRegions`, `copy_fit` (`8 * ((x.length + 1) / 8) ≤ 64`: identifiers of
  at most 71 bytes; the larger aligned `memcpy` route is outside every landed
  spec), and the request bounds. The ledger's ownership is runtime
  `HeapOwned` (`EnvDefineOwned`): the legacy `StoreHeapOwned` with `HeapArena`
  is uninhabitable for a fresh frame (`env_new` sets `cap = 0`, `names =
  vals = NULL`, and `FrameHeapOwned.arrays` demands `(NULL, 0) ∈ exts`).
- Physical accounting and arena capacity are `Vsa/Sim/AllocCapacity.lean`.
  `physSize n = 16 * ((n + 8 + 15) / 16)` is the chunk cost, header and
  16-byte alignment included, so `physSize_32 : physSize 32 = 48` is the plan's
  recorded figure as a checked theorem; `physTotal` sums it over a ledger.
  `extents_total_le` is the capacity theorem — pairwise-disjoint extents inside
  `[A.lo, A.hi)` have total size at most `A.hi - A.lo`, by strong induction on
  the ledger splitting each tail around its head extent into the part ending
  below it and the part starting above it. Nothing bounded the live set before
  this: `HeapArena` constrains each extent and their disjointness but never
  their total, so `MallocContract.nonNull_of_bounded` had no capacity content
  behind it. `ResourceBound` names the source-side obligation (the live
  ledger's physical cost leaves room for one more request at the static
  ceiling) and `arena_has_room` derives that the arena holds enough BYTES for the
  next bounded request. That is necessary, not sufficient: a byte total exhibits
  no contiguous PLACEMENT, so external fragmentation and the allocator's bin and
  coalescing behaviour stay behind `MallocContract`. `physSize` covers internal
  fragmentation only.
  `ResourceBudget A maxReq exts k` is the same statement indexed by how many
  further requests it still covers, which is what an induction along an
  execution needs. `.alloc` spends exactly one unit per request within the
  ceiling, whatever its size (`physSize_mono`); `.free` spends none and may
  recover some (`physTotal_erase_le`, over `physTotal_le_of_sublist`); `.mono`
  weakens the count; `.toBound` turns any budget with room to spare into the
  bound at that point.
  PARKED, NOT LANDED: the capacity precondition itself. `MallocContract.
  nonNull_of_bounded` currently quantifies over every machine state and every
  live list with no capacity condition anywhere in its statement, so read alone
  it says `malloc` never returns NULL for a bounded request however full the
  arena is. A future dlmalloc verification could not discharge that with
  dlmalloc's own heap invariant. It is inhabitable today only because `AInv` is
  a field of the same structure, so an inhabitant may define `AInv` to include
  "the arena has room" — which moves a CLIENT obligation inside the allocator's
  spec, hidden in an opaque predicate, and makes the contract unverifiable in
  isolation. The amendment adds `ArenaHasRoom A maxReq exts` (stated in
  `Vsa/Alloc.lean` beside `physSize`/`physTotal`) as an explicit precondition of
  `nonNull_of_bounded`, threaded through the eight call sites that prune OOM
  branches: as a ledger field on `EnvNewLedger` and `EnvDefineMissLedger`, and
  as a named premise on `prune_of_exit`, `concatOOM_prune`,
  `envDefMallocSuccessSaved_of_post`, `strdupMemcpy_prune_null` and
  `mallocReturn_of_parked`. The allocator side then reads "if there is room, it
  finds one", which is about dlmalloc alone; the client side is the caller's,
  discharged by `ResourceBudget`. UNVERIFIED: `Vsa/Alloc.lean` sits near the
  bottom of the graph, so the change invalidates ~1000 modules and 233 remain
  unbuilt. `Vsa.Alloc` and `Vsa.Sim.AllocCapacity` compile clean directly; that
  is no evidence of a proof error and no evidence of correctness for the rest.
  The diff is `capacity-precondition.patch` in the session scratchpad, checked
  to reverse-apply against the tree before it was parked.
  REMAINING: supply the COUNT. The carry lemmas reduce the obligation from
  "the live set is bounded at every point of every finite prefix" to "the source
  program makes at most `k` allocations", a static accounting over the
  interpreter's allocating constructs (environment records and their arrays,
  copied binding names, closure records, string payloads). That count then has
  to be connected to `Loaded` and the concrete arena bounds of the linker
  script.
  Discharging `nonNull_of_bounded` itself additionally needs the allocator's
  own placement argument, which is behind `MallocContract`.

### 3. Close sequence and for-loop recursion

- Close `hSeqSteps` for interpreter, closure-body, and block-body copies.
  Thread reached dispatch/resume carriers and whole-suffix invariants through
  empty, final, and continuing routes. Reuse `SeqSuffixGround` and the compiled
  closure return, normal-exit, and continuation lemmas. The block-body copy's
  child boundary demands `ExecSeqStackFrame .blockBody` (the parent's window
  `[esp+136, SL.hi)` outside the retslot and the arena); it follows from each
  child's `ExecExitD` by `blockBodyStackFrame_of_execExitD` with no geometry.
  Every sequence exit now also supplies `mem_extends` and `store_survives`
  (`ExecSeqExitI`), and every sequence entry `store_survives`
  (`ExecSeqEntryI`); the step suppliers take both from the child's `ExecExitD`.
- At closure child entry, derive `Exec_stmt` code, register presence
  (`x9`, `x20`, `x21`), header/array reads, and arena/stack geometry.
- Retain environment validity and machine geometry in `FEntryC`, `mForCond`,
  and `mExecStep`. `FlCondArmDispatchObstruction` refutes dispatch from the
  erased environment premise.
- Complete false-condition, body break/return, normal/continue, step, and
  next-iteration for-loop routes. Reuse the certified initializer and while
  suppliers after shared-contract integration.

### 4. Close the remaining terminating cases

| Family | Remaining work |
|---|---|
| Expressions | Variable lookup, assignment, constructor dispatch, equality/inequality, the two string concatenation cells, and `hDivOv`. Equality needs coherent operand maps, allocated bounds, payload coverage, and native identity. The four string comparison cells are on the `StrCmpCell` layer down to `StrCmpOperandsSupply` and `StrLeftSurvivesSupply` (below). |
| Arguments | Empty/nonempty loop assembly and `EvalArgsStep`; preserve spill slots `sp+24` and `sp+16`. Discharge the Lean supplier before removing SMT premise `argsLoopBoundAcrossCall`. |
| Calls and functions | `hCall`, `hCallClosure`, `hFn`; parameter bindings, depth bounds, allocation, and result marshalling. Complete the existing `CallClosureRow`/`CallClosureSplice` stage providers. |
| Native/output | Print, println, successful assert, `fprintf`/`_vfprintf_r`, `__swbuf_r`, `_putc_r`, and enclosing fputc folds. Preserve stdout/errno/HTIF state and output suffixes; reuse existing flush/write frames. |
| Statements | `hExecRouteCases`. The null declaration and the initialised declaration wait only for the named `env_define` contract (and, for the latter, the fresh-closure coherence and the payload window); the value return waits for the payload window; the for-start waits only for the named `env_new` contract; the block waits for `env_new` and the sequence-exit epilogue seam (below). All are on the layer. |
| Entry/exit | `hInitStore`: extend the owned initial execution to the full loop entry. `hEpilogueSpill`: retain code, saved slots, and runtime state through the reached sequence exit. The universal exit widener is refuted in `/private/tmp/vsa-epilogue-audit/EpilogueSpillObstruction.lean`. |

#### The parametric statement-arm layer

`Vsa/Sim/EvalChildArm.lean` states the `exec_stmt` arm → `eval_expr` child
seam once, over a descriptor (`kind`, `armPC`, reflected prefix, `jal` PC and
immediate, sub-result-slot immediate, child field offset) and two certificate
records: `Cert` (chain well-formedness, register fold, end PC, `jal` site; all
`decide`/`rfl`) and `Sem s e` (tag, child field, region projection, budget,
bodies bound, prefix chain facts). Generic theorems: `dispatch` (statement
entry → child `EvalEntry` plus the parent `Carrier`), `exitKit_at_exit`
(parent ground/AST/code/truthiness header at the child's widened exit),
`normalExitPre_of_exit` (a normal completion parked at the arm's `li a0,0`),
and `normalExitTail` (`ExecNormalExitTail.lean`: the parametric
`li a0,0; j 0x8000409c; epilogue`).

Instances (`rows/EvalChildArm{While,If,Expr,Ret,VarInit,ForCond}.lean`) are one
`#derive_case` prefix, one descriptor, and the certificates each.
`execWhileCondDispatch_closed_of_generic` re-derives the hand-closed
`WhileCondDispatchClosed` statement from the while instance. Measured on the
resumed private build:

| Arm | Hand-closed dispatch | Instance | Compile |
|---|---|---|---|
| while condition | 397 lines (`WhileCondPrefix` + `WhileCondDispatchClosed`), 3.2 s | 161 lines (reuses the seg) | 4.5 s incl. confirmation |
| if condition | none | 131 lines | 1.3 s |
| expression statement | none | 118 lines | 4.5 s |
| value return | none | 135 lines | 1.7 s |
| initialised declaration | none | 139 lines | 1.5 s |
| for-loop condition (in-frame) | none | 225 lines | 4.5 s |

The dispatch is split into `armState_of_entry` (prologue and jump table,
needs `EntryCert`) and `dispatch_of_armState` (the arm prefix and `jal`). The
for-loop condition enters the second half from the real loop head:
`EvalChildArm.ArmState.ofForLoopReady` and `forCond_dispatchFromLoopHead`.

`Vsa/Sim/TruthyCopy.lean` states the condition copy and `value_truthy` seam
once over a descriptor `TruthyCopy` (copy segment, `jal value_truthy` PC and
immediate) and `TruthyCopy.Cert D T` (register fold, the write log as three
`sd`s, the copy's chain facts, the generated call site). Generic theorems:
`copyReady_of_exitKit`, `truthyReturn_of_copyReady`, `route_of_truthyReturn`
(any reflected route from the return; routes may reload `s0`, so they are
framed by `abiButS0` rather than the full ABI set), and
`normalExitPre_of_route`. `rows/TruthyCopyWhile.lean` confirms
`ExecWhileCondCopyReady` from the generic parked state;
`rows/TruthyCopyIf.lean` carries the if copy and its three routes with their
chain facts. The `jal value_truthy` sites are generated from
`scripts/truthy_copy_sites.tsv`.

The generic layer is 996 + 178 + 696 lines and compiles in about 15 s; the
if copy seam with its three routes is 283 lines at 1.9 s, the closed
`hSIfNone` supplier is 110 lines at 1.6 s, the closed `hSIfTrue`/`hSIfFalse`
supplier (`rows/Field_hSIfBranchClosed.lean`, one shared `ifBranch_resume`)
is 340 lines, and the closed `hFlCondFalse` supplier
(`rows/Field_hFlCondFalseClosed.lean`, with `rows/TruthyCopyFor.lean`) is
120 + 150 lines. Rules R10 and R11
(`scripts/discipline_rules.tsv`) fail any new file that reflects an exec-arm
prefix (expression or statement child) by hand.

`Vsa/Sim/StmtChildArm.lean` states the in-frame call of a child statement
once, over a descriptor (`armPC`, reflected prefix, `jal` PC and immediate,
child field offset) with `Cert` and `Sem s sc`: `dispatch_of_armState` lands
the child's `ExecEntry` with the parent `Carrier`, `exitKit_of_exit`
recovers the parent at the child's `ExecExitD`, and the exit heads after a
status route are `normalExitPre_of_routeHead` and `retExit_of_routeHead`.
The same file carries the pieces every in-frame continuation shares:
`FrameFacts` (the parent frame at any in-frame point, with `transport`,
`afterExit`, and `EvalChildArm.frameFacts_at_exit`), `ArmState` generalised
over its PC with `ArmState.of_routeHead`, `TruthyCopy.RouteReady` and
`route_of_gholds`/`route_of_ready` (a reflected route from any parked
return, keyed by `a0`), and `LoopFrame` (memory bookkeeping across an
iteration for the final rebase). The `ForCond` and `ExecStep` motives now
carry the condition's and step's eval IHs (`ForCondIH`, `ExecStepIH` in
`TermSimAssembly.lean`; rows `hFcSome_row`/`hEsSome_row`).

The for-loop instances (`rows/ForLoopArms.lean`, 356 lines: the body call
`forBodyArm`, the in-frame step arm `forStepArm`, and seven reflected
routes) and the closed `hFlBodyBreak`/`hFlBodyRet`/`hFlLoop` suppliers
(`rows/Field_hFlBodyClosed.lean`, 418 lines) compile in under 10 s; the
generic layer file is 1,114 lines and the ret-arm resume
(`rows/RetSlotCopy.lean`) is 477 lines. The step arm and body call are entered
from arm states reached by routes, never through the prologue.

#### The helper-call layer

`Vsa/Sim/HelperCall.lean` states the in-frame call of a runtime helper once,
over a descriptor `HelperCall` (head PC, reflected prefix, `jal` PC and
immediate, callee entry) and a certificate `Cert` (link alignment, `jal`
target, ABI-avoiding prefix, the generated `jal` site from
`scripts/helper_call_sites.tsv`). `parked_of_gholds` runs the prefix and the
`jal` from any state whose pinned registers hold a list `L`
(`bridgeOfSegOut`) and lands `Parked` at the callee entry; `parked_of_armState`
enters from an `ArmState` (the five frame registers), `parked_of_ready` from
a `RouteReady` (the six call registers `callL`; the link register is
rewritten). The helper's return is `Return`: a `RouteReady` at the link PC
plus the memory footprint. Each callee has one adapter from its contract:
`nullReturn_of_parked` (`HelperCallNull.lean`, over `value_null_spec_full`)
and `envDefineReturn_of_parked` (`HelperCallEnvDefine.lean`, over the named
`EnvDefineContract`). The continuation reuses the existing kit
(`RouteHead.toRouteReady`, `ArmState.frameFacts`,
`FrameFacts.afterStackHelper`/`.afterExit`, `normalExitPre_of_routeHead`),
`armState_of_entry_kind` reaches any arm from the statement entry by its tag,
and the two shared tails are `retSlotResume` (`rows/RetSlotCopy.lean`: the
retslot copy and the status-3 epilogue from any route-ready state; the value
return is re-proved through it) and `envDefineTail_run`
(`rows/EnvDefineCall.lean`: `ld a1,8(s0)`, the copy to `esp+16`, the
`env_define` call, the normal exit). The three-word copy's byte facts
(`copy3_total`/`copy3_frame`) and the payload premise (`PayloadOffWindow`, the
former `RetPayloadOffSlot`) are shared. Rule R12 fails a hand-reflected helper
prefix.

Measured on the private overlay (warm imports):

| Leaf | Legacy (hand) | On the layer | Result |
|---|---|---|---|
| `ret;` (`hSRetNull`) | `ExecRetNull` 760 lines (`maxHeartbeats 8000000`) + `ExecRetNullGlue` 516 lines + `ExecRetNullGeom`; seam still open | `rows/Field_hSRetNullClosed` 167 lines, 3.7 s | closed |
| `var x;` (`hSVarNull`) | `ExecVarNull` 272 lines; `value_null`, the copy and `env_define` inside one open glue | `rows/Field_hSVarNullClosed` 168 lines, 3 s | `EnvDefineContract` only |
| `var x = e;` resume (`hSVarInit`) | `ExecVarInitGeom` glue oracle (child IH, copy, `env_define`) | `rows/Field_hSVarInitClosed` 112 lines, 2.4 s | `EnvDefineContract` + `VarInitPayloadOff` (the child's coherent exit is the motive `mEvalE := EvalReturnIH TrivialOwned`, not a premise) |
| shared | — | `HelperCall` 572, `HelperCallNull` 89, `HelperCallEnvDefine` 188, `rows/EnvDefineCall` 341 lines; 4–7 s each | — |

| `for` start (`hSForStart`) | `hArm` oracle in `ForStartGeom` | `rows/Field_hSForStartClosed` 205 lines, 3.5 s: `ExecInitReady` at the `env_new` return | `EnvNewContract` only |
| block (`hSBlock`) | `hArm`/`hEpi` oracles in `BlockGeom` | `rows/BlockArmEnvNew` 470 lines, 4.3 s: `ExecSeqEntryI .blockBody` at the loop head (nonempty) or the epilogue entry (empty) with the retained parent frame `Rows.BlockArmFrame`; `blockEpilogue_run` = sequence exit ≫ `epilogueTail` | `EnvNewContract` |

The `env_define` contract (`EnvDefineEntryState` → `EnvDefineReturnState`,
`HelperCallEnvDefine.lean`) is the one seam shared by `hSVarNull`,
`hSVarInit`, `hAssign`, and `hCallClosure`. The `env_new` contract
(`EnvNewEntryState` → `EnvNewReturnState` with `EnvNewFresh`: the returned
address, the extended frame map, and the pushed store represented under it;
`HelperCallEnvNew.lean`) is the seam shared by `hSBlock`, `hSForStart`, and
the closure call. Both are consumed through one adapter each
(`envDefineReturn_of_parked`, `envNewReturn_of_parked`).

Suppliers. `env_define`: the closed exact lanes (`rows/EnvDefinePrologueSaved`,
`rows/EnvDefineScanFramed.envDefineScanFiniteFramed`,
`rows/EnvDefineUpdateExact.envDefineUpdateClosed_of_heap_owned`,
`rows/EnvDefineDispatchExact.envDefineMissCapDispatch`,
`rows/EnvDefineAppendClosed`, `rows/EnvDefineGrowExact.envDefineGrowClosed`,
`rows/EnvDefineEpilogue`) composed under `MallocContract`, `ReallocOps`, the
ownership ledger (`StoreHeapOwned`/`ValueHeapOwned`), `FrameUnique`, and the
allocator-private footprint inside the arena; the per-lane geometry records
(`EnvDefRegions`, `EnvDefineUpdateGeom`, `AppendStoreFactsGeom`,
`EnvDefineGrowClosedGeom`) are the remaining caller data. `env_new`:
`env_new_spec` with `MallocContract`, `storeRepr_allocFrame`
(`rows/CallClosureEnvNewMarshal`) for the pushed store under `pushFrameMap`,
and the freshness of the returned block against every represented frame,
which needs the ledger relating `StoreRepr` images to the allocator's extents
(task 2; no such lemma exists).

`rows/EnvDefineContractUpdate.lean` (12 s) composes the `env_define` update
path from the statement arms' entry state: `envDefineUpdateLaneKeep` runs a
framed prologue (one `#derive_case` of the 13 instructions), the scan hit, the
keep-set-framed exact update and epilogue (`rows/EnvDefineTailFramed.lean`:
`segRowKeepGhost` instantiated for `updateStoreSeg` and
`envDefineEpilogueSeg`), and `envDefineUpdateLane_full` closes
`EnvDefineReturnState` with no residual hypothesis. The three former
`EnvDefineReturnResiduals` are discharged: `sailOutput` rides the scan frame
(`EnvDefineScanEntryFrame.out`/`EnvDefineScanFrame.out`, fed across the
`strcmp` seam by `rows/EnvDefineScanCallOut.envDefineScanCallRead64Out` over
`bridgeOfSegFull`), the untouched `x3`/`x4`/`x23–x27` come off the scan
frame's ABI ghost through `KeepGhost`, and `a0` is the hit's `strcmp` result
kept by both rows. `envDefineMissLane` runs the miss to `EnvDefineMissReady`
at the cap dispatch. The oracle record `EnvDefineUpdateOracles` is derived by
`EnvDefineUpdateOracles.of_entry` from `EnvDefineMem` (fixed-text projections
`FixedTextLoaded.Env_defineLoaded`/`.StrcmpLoaded`, `slot_in_stack`,
`value_words`, `arena_image`; the last three are new `EnvDefineMem` fields
supplied at the call site by `FrameFacts.geom`, `copy3_total`, and
`ExecGround.eval_call.image.arena`) and the external ledger
`EnvDefineUpdateLedger` (gp pin, saved-register presence, allocator headroom,
allocator invariant at entry and its footprint stability, `HeapArena`, arena
RAM/HTIF bounds, `StoreHeapOwned`/`ValueHeapOwned`, `FrameUnique`, the scan
string regions `ScanNames`, array alignment, and `define_survives` — the
defined store's survival, whose supplier is `StoreOwned.repr_transport` after
`HeapOwned.defineHit`). Not covered: the empty-frame path (`count = 0`
branches to `0x80002bf4`, no landed lane) and the append/grow lanes from
`EnvDefineMissReady` (`rows/EnvDefineAppendClosed`,
`rows/EnvDefineGrowExact.envDefineGrowClosed` under `ReallocOps`).

The block's epilogue seam is closed (`blockEpilogue_run`,
`rows/BlockArmEnvNew.lean`). The indexed sequence boundary carries what the
shared epilogue needs: `ExecSeqStackFrame .blockBody` keeps the parent's
window `[esp+136, SL.hi)` outside the retslot and the arena, and
`ExecSeqExitI` carries presence (`mem_extends`) and store survival
(`store_survives`) like `ExecExitD`. The arm retains the parent frame as
`Rows.BlockArmFrame` (spill slots, ghost tie, memory relation to the entry);
`EpilogueReady`/`epilogueTail` (`ExecNormalExitTail.lean`) run the epilogue
from any status over `execBlockDQR`, whose carried memory predicate supplies
the `ret` value. `normalExitTail` is the `li a0,0; j` prefix of the same
tail.

Residuals restated in the dispatch/resume shape (`Rows.RetCaseGeom`,
`Rows.VarInitCaseGeom`, `Rows.IfNoneCaseGeom`): the dispatch half is supplied
by `retResid_of_resume`, `varInitResid_of_resume`, and the closed
`field_hSIfNone`; the named resume seams still open are:

- `Rows.RetResumeResid` (`hSRet`): closed on the layer
  (`retSlotResume`) down to `PayloadOffWindow`: the returned string or native
  payload lies outside the retslot window. `retResumeResid_of_payload`
  supplies the residual from that premise. The premise is not derivable at
  `EvalExitD`: `ValueRepr` fixes no payload location, and the ground bundle
  relates the arena to the stack only below `sp` (`ExecGround.arena_stack`)
  while the retslot lies above `sp`. Suppliers: the ownership layer's payload
  location (`ValueOwned`, payload in the arena or the AST region) plus an
  arena/retslot separation fact in `ExecGround`.
- `Rows.VarInitResumeResid` (`hSVarInit`): closed on the layer
  (`varInit_resume`, through `envDefineTail_run`) down to two named premises:
  `EnvDefineContract` and `VarInitPayloadOff` (the `PayloadOffWindow` class at
  the call buffer `[esp+16, esp+40)`). The child's coherence is no premise:
  the recursor motive is `mEvalE := EvalReturnIH TrivialOwned` (`EvalReturn.lean`,
  `TermSimAssembly.lean`), so every child returns `EvalReturn` — the widened
  exit plus ONE selected map pair (`EvalReturn.repr`) representing its value,
  its store, and the store's survival across the stack region — and the resume
  consumes that pair directly. Producers: the four pinned leaves through
  `pinnedLeafReturn` (`eval*SimR`); the variable leaf through
  `evalReturn_of_exit_id` from the identity-map result `evalVarSim` now exposes
  (`blockC_var`'s post) and the identity-map widener `LeafReturnWiden`
  (`VarLeafResid`); the integer/boolean/string arms (unary, logical, binary)
  through `EvalIH.coherent_of_bounded` (`binOpSem_closuresBounded`); the
  allocating arms land the coherent epilogue themselves through
  `armReturn_of_facts` (= `blockD_v_return` from `EpilogueEntryFacts` at the
  arm's selected pair): `fn` in `fnResid_of_pipeline` (`FnArmGeom.hArm` at the
  widened `φc'`, the fresh index mapped to the allocated block; the bundle's
  former exit-level `EvalRecWiden` conjunct is replaced by the epilogue-entry
  facts at that pair), `call` in `callReturn_of_stages` (`CallArmHandoff` now
  carries the facts at the pair its children selected). `AssignArmSpec` is
  restated at the coherent motive. Consumers that need only the widened exit
  project `EvalReturnIH.forget`. Remaining split below the eval motive: the
  statement/call motives (`ExecExit.retval`, `CallExitI`) still select the
  returned value's map independently of the store's; the call arm's
  `callToEpilogue` stage is where that pair is currently selected.
- `Rows.ForStartPrefixResid` (`hSForStart`) is supplied by `forStart_run`
  from `EnvNewContract`; `Rows.BlockCaseResid` (`hSBlock`) by
  `field_hSBlock` from `EnvNewContract`.
- `Rows.VarNullResid` (`hSVarNull`) and `Rows.RetNullResid` (`hSRetNull`)
  are restated as the leaf simulation Triple (statement entry to widened
  exit); `field_hSRetNull` is closed and `field_hSVarNull` takes
  `EnvDefineContract`.

Three obstructions recorded by the layer were resolved in place:

- `ForLoopReady`, `ExecInitReady`, and `InitSomeStage` now carry
  `parentSp : g x2 = some sp`, `ra_align : r.toNat % 4 = 0`, and
  `mem_extends : MemExtends m0 ment`; `Field_hInitNone`, `Field_hInitSome`,
  and `InitSomeReturnReady` supply them from the actual initializer run.
  `forCond_dispatchFromLoopHead` takes only the record.
- `ExecDispatchReady` keeps its strong memory frame. The if-branch residuals
  (`Rows.IfBranchCaseGeom`, `IfTrueCaseResid`/`IfFalseCaseResid`) instantiate
  its ghost memory as the reached memory and rebase the branch's `ExecExitD`
  to the entry memory with `Rows.execExitD_rebaseMem` (memory extension plus
  the arena/retslot-excepted frame). `exec_ifTrue_row`/`exec_ifFalse_row`
  are re-proved by composition. `Field_hSIfBranchClosed` closes both fields;
  the `auipc a4; addi a4` table base is read back from the reflected route
  by unfolding the register fold (`if_route_a4`), not by `rfl`.
- `SubExecReturnR`'s payload clause is conditioned on the returned value's
  actual string (`Vsa.Sim.ValuePayload v s`, `ReprCopy.lean`): it is vacuous
  for integer, boolean, and null payloads and names the string or native
  payload otherwise. `valueRepr_copy` and `valueRepr_copy_of_writeWindow`
  take the same guard; `ExecRet`, `ExecRetNull`, `EvalCallNative2`,
  `FrameCalc`, `EnvGetSpec6`, and `EvalVarBridge` consume it.

#### The string-comparison cell layer

`Vsa/Sim/StrCmpCell.lean` states the four string-comparison cells once over a
descriptor `StrCmpOp` (operator, result function, token, jump-table index and
slot, the landed slot predicate, the sign-tail seg, the `jal value_bool` /
`ld s3` / `j` PCs and immediates) and a certificate `StrCmpOp.Cert` (the token
and slot arithmetic, the sign tail's `ChainOK`/facts/end PC/readbacks, the
three generated box sites, the box wiring, the `binOpSem` closure, and the
proved `StrCmpOrderBridge`). Generic theorems:

- `strCmpKindEntry_of_twoSubReturn` — the shared operator dispatch
  (`evalBinopChain_run`) from the actual return of both children, reading both
  kind tags and payload pointers back from the represented operand boxes
  (`strOperandsStaged_of_twoSubReturn`, `BinaryReturnLoads`);
- `strCmpTailReady_of_kindEntry` (`Vsa/Sim/StrCmpSeam.lean`) — the
  operator-independent middle: the landed kind check `strKindCheck`, the seam
  seg `strSeamSeg` (`mv a1,a7; mv a0,s3; sd a2,0(sp)`) with the generated
  `site_80003b18_sc` through `bridgeOfSegOut`, `strcmp_full_spec`, and the
  landed rejoin `strRejoin` with the token read back through the write log; the
  exit `StrCmpTailReady` ties the `strcmp` word to the operand strings for every
  proved order bridge; `FixedRodataLoaded.maskPinned` supplies the word mask
  from the fixed image;
- `blockC_strcmp` — dispatch ≫ seam ≫ the operator's sign tail (a framed
  `segEval_sound` run over the certificate) ≫ the `jal value_bool` site ≫
  `boolBoxEpilogue`, landing the integer rows' `PreEpilogueVD` post;
- `evalStrCmpSim`, `binRow_strcmp`, `binStrCmpCell_of` — the recursive case
  from the arm entry (`blockB_binary_data ≫ blockC_strcmp ≫ blockD_v_rec`), from
  the node entry (`blockA_binaryArm_budgeted`), and the field supplier. The
  reached data `StrCmpResid` is supplied by `EvalEntry.binaryPostGeom` and
  `EvalEntry.binaryReturnImage`; the operand regions are the named residual.

Instances (`rows/StrCmpCellInstances.lean`) are one descriptor and one
certificate each; `ScaffoldRows.field_hStr{Lt,Le,Gt,Ge}_of` take the two shared
residuals. Measured on the private overlay (warm imports, `proof_slice`):

| Layer or cell | Lines | Compile |
|---|---|---|
| `StrCmpSeam` (op-independent middle) | 471 | 2.8 s |
| `StrCmpCell` (dispatch, block C, sim, row, supplier) | 868 | 4.6 s |
| `StrCmpSeamSites` (generated) | 52 | — |
| all four instances (`StrCmpCellInstances`) | 237 (≈55 per cell) | 4.7 s |
| one INTEGER comparison cell for comparison (`rows/EvalLtRow` + `EvalLtChain`, hand-rolled, `maxHeartbeats 8000000`) | 1,912 | — |

Every declaration of the three new files depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The superseded hand scaffolding
(`StrArmFrontData`, `strArmFront`, `StrArmPrologue`, `StrArmMachineResid`,
`StrSeamSpan2`, `StrArmToStrcmp`, `StrArmStageSpan`) is removed; the residual
bundle field `TermGuards.strArmProlog` is replaced by `strCmpOperands` and
`strLeftSurvives`. Rule R13 (`scripts/discipline_rules.tsv`) fails any new file
that reflects the seam by hand.

The residual `StrCmpOperandsSupply` is true and derivable: string payloads live
in the arena (`value_str`, concatenation) or in the AST region (literals), both
inside RAM, 8-aligned, and disjoint from the `strcmp` code, the HTIF window,
and the callee's spill slot; the supplier is the ownership layer's payload
location (`ValueOwned`) plus `EvalGround`'s arena/stack geometry. The residual
`StrLeftSurvivesSupply` is the `hVlSurv` obstruction recorded in task 1.

Footprint-carrying exit (IH tower, Level 1; contract in the session scratchpad
`ih-tower/L1-interface.md`). `Vsa/Sim/ExitFootprint.lean` states `MemFootprint`
(named field `agree`), the standard windows (`stackWin`, `resultSlot`,
`arenaWin`, `word8`) and families (`FootFam`, `noArenaFoot`, `exitFoot`,
`binaryHeadFoot`), and the exit siblings `EvalExitF F` / `EvalIHF F` over
`EvalIHWithM`: an `EvalExtra` cannot see `sp` or the entry memory `m0`, and a
footprint is relative to `m0`, so the footprint contract is the `sp`/`m0`-aware
`EvalIHWithM`, with `EvalIHWith.toM`, `EvalIHF.forget`, `EvalIHF.mono`, and
`EvalIH.exitFoot` (the weak exit is the footprint `exitFoot`). Glue, all
statement-preserving: `armTail_rec_gen` (`EvalRecCommon`; `armTail_rec_with` is
its corollary), `armTail_rec_withM`/`armTail_rec_footprint`
(`ArmTailFootprint`), `blockD_v_rec_footprint`, `boolBoxEpilogue_footprint`,
`blockC_strcmp_footprint`, `blockC_lt_footprint`, and `blockB_binary_footprint`
(`EvalBinSim`; `blockB_binary_data` is its projection at `exitFoot`).
`BinaryHeadFootprintSupply` (`BinaryHeadFootprint.lean`) is discharged by
`binaryHeadFootprintSupply`. Pilots: `StrCmpCellFootprint.lean`
(`evalStrCmpSimF`, `binRow_strcmpF`, `binStrCmpCellF_of` at
`EvalIHF noArenaFoot`, from the two `StrCmpCell` residuals) and
`rows/EvalLtRowFootprint.lean` (`evalLtSimF`, `binRow_ltF`). A generated
`Footprint` clause must be an `EvalExtraM` motive (`EvalIHF F`), not an
`EvalExtra`; the recursion glue at a child call is `armTail_rec_gen`.
Integer cells (Level 1B, all eight, `ih-tower/L1B-int.md`): `blockC_<op>_footprint`
(`.add .sub .mul .div .mod .le .gt .ge`; each landed `blockC_<op>` is its
projection) with the cell footprint `<op>CellFoot` = the three dispatch-ladder
temporaries `sp-848/840/832` ∪ the result slot — identical for all nine integer
cells; the libgcc callees (`muldi3_post`, `divdi3_post`, `moddi3_post`) state
memory unchanged, so no scratch window enters. `.div`/`.mod` write through a
reflected `writeLog`: `evalBlocks_store_offsets_exact` +
`divDispatch_footprint`/`modDispatch_footprint` (`rows/EvalDivRow.lean`,
`rows/EvalModRow.lean`) refine the landed `[v2, v2+0x108)` window to the exact
`{0xf0, 0xf8, 0x100}` stores. `intBoxEpilogue_footprint` (`BinopTailGen`) is the
int twin of `boolBoxEpilogue_footprint`. `rows/Eval<Op>RowFootprint.lean`:
`eval<Op>SimF`, `binRow_<op>F` (residual at the entry config as
`BinIntCellResid`), `Bin<Op>CellF` + `bin<Op>CellF_of` discharged by the landed
`BinIntCell .<op>` suppliers (`ScaffoldRows.field_hI<Op>`); no new residual.
Duplication signal: eight per-op copies of one template — a generator + one
shared `intCellFoot` is the next step.

Clauses as metatheorems over footprints (IH tower, Level 2; contract in the
session scratchpad `ih-tower/L2-clauses.md`). `Vsa/Sim/IHClauseFootprintMeta.lean`
derives the two clause shapes once over `MemFootprint` (region preservation:
`agreeP_of_disjoint`/`region`/`EvalIHF.regionPreserved`; payload survival:
`cstring`/`valueRepr`/`sharedCString`/`valueOwned`/`EvalIHF.cstringSurvives`) and
`strLeftSurvives_of_footprint`, the left temporary's survival at the ACTUAL
memories from the right child's `noArenaFoot` footprint and the left payload's
whole-stack coverage. `Vsa/Sim/IHClauseGeneric.lean` holds the `Footprint`
clause's generic steps at the generator's field types (`EvalIHF noArenaFoot`
motive): `hInt`/`hStr`/`hBool`/`hNull` CLOSED (`leafExitF_of_pinned`: the pinned
leaf exit IS the `noArenaFoot` footprint); `hVar` from `Rows.VarLeafResidF` (`Rows.evalVarIHF`;
`VarPinnedSim` is uninhabitable as stated — see the variable-leaf paragraph); `hNeg`/`hNot`/the four logical cases from the
arms' footprint row contracts `NegRowF`/`NotRowF`/`LogicalShortRowF`/
`LogicalFallRowF` (Level 1B: the `F` siblings of the closed fields); `hBinary`
from `BinaryFootprintCells` (`.lt` supplied by `intCellF_lt` over pilot B, the
four string comparisons by `binStrCmpCellF_of`). OBSTRUCTION: at `noArenaFoot`
the clause is uninhabited — `hAssign`, `hFn`, `hCall`, and `hBinary` at `.add`
with a string operand write the arena (`StrAddLCellF`/`StrAddRCellF` are
unsatisfiable). The closable shape is the guarded motive
`noAllocExpr e = true → EvalIHF noArenaFoot …` (`IHClauseGeneric.footprintNA`,
all 15 steps; needs a generator `guard` column), or the allocating family
`allocFoot` (`Vsa/Sim/IHClauseGenericAlloc.lean`: `EvalIHAlloc priv`, named
premises `FnArmFootprint M`, `CallArmFootprint M`, `StrAddFootprint M` from
`MallocRun`, `HeapOwned.pushClosure`, `EnvNewContract`, `Reserved.outsideFresh`;
`value_str` does not allocate). String cells (`Vsa/Sim/StrCmpCellClauses.lean`):
`strCmpOperandsAt_of_owned` derives `StrCmpOperandsAt` from both returned values
being owned (`ValueOwned`, the `Owned` index of `EvalReturn`) under
`SharedGeom shared SL`; `StrCmpOperandsSupply` reduces to `StrCmpOwnedOperands`.
The alignment defect is fixed: `strcmp_full_spec_cond` (`StrcmpSpecCond.lean`)
derives the word-path alignment from the entry test (`align8_of_test`) and
`StrCmpRegion.wordRegion` is the alignment-free `StrcmpWSlack`. `StrLeftSurvivesSupply`
is replaced by the head premise `BinaryHeadFootprintSupplyCov` (Level 1B:
`blockB_binary_footprint` with the left child at the product clause `EvalIHFP`
and `strLeftSurvives_of_footprint` at `hvalL_R`); the exact `BinDispatchRow`
fields follow (`field_hStr{Lt,Le,Gt,Ge}_of_clauses`) from it, `StrCmpOwnedOperands`,
and the closed clause recursions `FootprintPayloadClause`/`FootprintClause`.

One-child arms and leaves at the footprint exit (L1B-una). Heads:
`blockB_unary_gen` (`EvalNegSim`; `blockB_unary_with`/`blockB_unary` are its
projections) and `blockB_logical_gen` (`EvalAndSim`; `blockB_logical` is its
projection) take the child at any retained fact `Q mcall`;
`blockB_unary_footprint` (`UnaryHeadFootprint.lean`, `unaryHeadFoot F`) and
`blockB_logical_footprint` (`LogicalHeadFootprint.lean`, `logicalHeadFoot F`,
`logShortNodeFoot`, `logFallNodeFoot`) are their `EvalIHF F` instances. Cells,
each with the landed theorem as projection: `blockC_neg_footprint`
(`negCellFoot`: `sp-848/840/832` + the box), `blockC_not_footprint`,
`blockC_andFalse_footprint`, `blockC_orTrue_footprint`, `blockC_logTail_footprint`
(all `truthyCellFoot`: the `value_truthy` argument copy `[sp-1024, sp-1000)` + the
box), `blockC_andTrue_footprint Fr`/`blockC_orFalse_footprint Fr`
(`logFallCellFoot Fr 848`/`944`, the RIGHT child through `armTail_rec_footprint`).
Rows `rows/Eval{Neg,Not,OrTrue,AndFalse,AndTrue,OrFalse}RowFootprint.lean` land
`eval<Arm>SimF`, `<arm>RowF`, and the unconditional `EvalIHF noArenaFoot` supplier
`eval<Arm>IHF`. Leaves (`LeafFootprint.lean`): `pinnedLeafExitF` turns the pinned
exit (`LeafMemPin.agree` = `noArenaFoot`) into `EvalExitF noArenaFoot`; `evalIntIHF`
is unconditional, `evalNullIHF`/`evalBoolIHF`/`evalStrIHF` take the named
`EvalEntry → Eval*Entry` bridges (`NullEntryBridge`/`BoolEntryBridge`, supplied
inline by `rows/TermRouting.lean`'s `eval_null_row`/`eval_bool_row`; `StrEntryBridge`
open on `EvalEntryStrAstRegion`). Variable leaf
(`rows/EvalVarRowFootprint.lean`): LANDED at `EvalIHF noArenaFoot` — the SAME
family as the literal leaves — down to ONE named conjunct. `evalVarSimQ`
(`EvalVarSim.lean`; `evalVarSim` is its `Q := True` projection) threads any fact
`Q` about the `env_get` call-return memory through `blockC_var_gen` (`blockC_var`
is ITS projection), which retains the arm's own write window `[sret, sret+24)`.
`Rows.VarLeafResidF` is `Rows.VarLeafResid` with the `env_get_found` oracle's post
strengthened by `Rows.VarPostCallPin SL sp m0 mpc`
(`∀ a ∉ [SL.lo, sp), mpc[a]? = m0[a]?` — no arena drift); `varLeafResid_of_F`
projects it back onto the landed residual, and `evalVarIHF`/`eval_var_rowF` land
the leaf at the generator's `hVar` field type. The conjunct has a proved supplier:
`env_get`'s write set is `[out, out+24) ∪ [sp0-64, sp0)` with
`out = (sp-1088)+0xf0`, `sp0 = sp-1088`, both inside `[SL.lo, sp)` under the entry's
`StackOK SL sp 2176`; `EnvGetSpec10.env_get_found_framed` already carries that frame
and `envGetFramedPost_pin` (`rows/EvalVarBridgeCallee.lean`) converts it to
`VarPostCallPin`, with `varCallLinkage_calleeF` composing it through an assumed
memory-transparent repack. The active recursive path already carries the same
write windows in `env_get_lookup_from_entry`; retain them through
`varBridge_callee` instead of changing `VarCallLinkage.finalMemFrame`.
The existing arena-carved post cannot recover this discarded information.
Consequently
`IHClauseGeneric.VarPinnedSim` is NOT provable as stated (from `EvalVarEntry` alone
nothing constrains the arena on the call-return memory); the `Footprint` clause's
`hVar` step should take `Rows.VarLeafResidF` (→ `Rows.evalVarIHF`) instead of
`Rows.VarLeafResid` + `VarPinnedSim`.

#### Variable-lookup supplier audit

The active supplier is `env_get_lookup_from_entry`
(`Vsa/Sim/EnvGetRecursive.lean`), which covers parent-chain lookup. Its return
retains the prologue spill agreement and `EnvGetValuePost.mem` retains the
output-buffer agreement. `varBridge_callee` obtains both and discards them
while constructing `VarPostCall`. Retaining their composition at that actual
return supplies the footprint; strengthening `finalMemFrame` is unnecessary.
The immediate-hit adapter in `rows/EvalVarBridgeCallee.lean` still assumes its
repackaging and cannot supply the general parent-chain path.

The source audit identified additional contract gaps:

- `VarRowResid` (`rows/EvalVarBridge.lean`) quantifies over arbitrary ghosts
  and arbitrary `ment/v8/v9/v18`. Choosing the everywhere-`none` ghost makes
  the demanded `VarCallLinkage.g8` read `none = some 0`. Its replacement must
  receive both the actual `EvalEntry` and actual `ArmEntryK` witnesses.
  Consumers: `varLeafResid_of_rowResid`, `eval_var_row_closed`.
- `VarCallLinkage.payloadDisj`, `EnvGetHitGeom.payDisj`,
  `HitTailSt.payDisj`, `FoundSt.pvVals`, `EnvGetCallerGeom.pvVals`, and
  `FrameStackDisj.valstr`
  quantify over unrelated strings. The downstream copy theorem already
  requires `ValuePayload v s`, but these callers discard that guard.
  The unguarded proposition forces every payload word above the destination,
  excluding integer zero and valid lower-addressed strings. Use the actual
  value's `ValuePayload` guard throughout the lookup/copy chain; ownership
  supplies its equivalent `ValuePayloadCovered` predicate. The spill-frame
  transport needs the same guard on each binding's actual value.
- `VarCallLinkage.finalFrame` quantifies over arbitrary `EnvGetValuePost`
  witnesses. That post omits the full saved-register frame. Retain it through
  the recursive execution and scan seams. `finalMinstret` is already supplied
  by `EnvGetValuePost.good.minstret`; it needs no additional retention.
  The post already restores `x19`–`x21`; with the linkage's ghost pins,
  only `x3`, `x4`, and `x22`–`x27` remain. `gen_fn.py --fn env_get
  --entry 0x80002c10 --cfg-only` identifies 51 instructions, twelve blocks,
  two loop back-edges, and one `strcmp` call. Its generated block draft is
  `/private/tmp/vsa-closure-work/FnEnvGet.lean`; use those segments with
  `segRowFramed`/`segRowKeepGhost` to retain the eight registers. The generic
  generator does not supply a fold for these loops. The draft is uncompiled.
  `EnvGetSegments.lean` extracts its seventeen generated branch/block variants
  and pin lists, then applies `segEval_selected_framed` through one wrapper.
  `check-env-get-segments.sh` passed (exit 0): all seventeen variants avoid
  `x3`, `x4`, and `x22`–`x27`. Its 783-module dependency slice reused every
  module. The three segment declarations have only allowed axioms.
  `EnvGetSegments.receipt.json` records source/object/log hashes and the
  dependency receipt; `extract-env-get-segments.py` and
  `EnvGetSegments.sources.json` retain extraction provenance. This verifies
  the blocks and frame wrapper; call and loop composition remain pending.
  `EnvGetCallFrame.lean` now stages the call seam: `call_framed` uses
  `bridgeOfSegFull` and `site_80002c68_eg2` to retain the generated argument
  block's computed result, output, and eight-register frame at the actual
  `strcmp` entry. It takes the block's `ChainFacts`; it does not yet assemble
  the string inputs or compose the comparison and recursive loop.
  `check-env-get-call.sh` passed (exit 0), with all 788 dependency modules
  reused. `call_framed` reports only the allowed axioms. Frozen sources and
  logs are in `/private/tmp/vsa-closure-work/call-source/`; provenance and
  object hashes are in `EnvGetCallFrame.receipt.json`. The comparison and
  recursive loop remain outside that check.
  `EnvGetCompareFrame.lean` stages the subsequent `strcmp` composition.
  A generated `strcmp_post.destruct` exposes the legacy post by name;
  `CallResult.compare` combines its full saved-register frame with the call's
  retained frame at the same endpoint. `EnvGetReflected.scan_compare` in
  `EnvGetScanCompare.lean` stages the caller: from `ScanSt`, it selects the binding pointer, obtains
  reflected load facts through `wordLoadFacts_of_read64`, and assembles
  `StrcmpEntryCond` at the actual call endpoint. `check-env-get-scan.sh` failed in `EnvGetCompareFrame`: its unbounded
  register proposition lacked a `Decidable` instance, and the destructurer
  was generated under the wrong namespace. Its 824-module dependency slice
  passed (819 reused, five rebuilt); both dependency audits use only allowed
  axioms. The segment and call modules also compiled. The comparison caller
  was not reached. `scan-repair-source/` contains a fresh seven-module snapshot
  with a bounded register proof and the destructurer invoked at root scope.
  `check-env-get-scan-repair.sh` used the verified dependency slice;
  it checks comparison, scan transport, branching, and semantic decision.
  The corrected 824-module slice passed with all modules reused.
  `EnvGetCompareFrame` then compiled, and all six declaration audits use
  only allowed axioms. `EnvGetCompareFrame.receipt.json` records the source,
  object, log, and dependency receipt. `EnvGetScanCompare` and
  `EnvGetScanState` also compiled, with four further allowed-axiom audits.
  `EnvGetScanState.receipt.json` records both modules. The result branch also
  passed its two audits (`EnvGetScanBranch.receipt.json`). The check then failed
  in `CompareResult.value`: its local zero-sign equivalence left one integer
  sign case open. `scan-advance-source/` replaces the ambiguous `split` with
  an explicit sign case split. The decision theorem remains unverified.
  No loop frame is yet proved.
  `EnvGetScanState.lean` adds the shared `ScanSt.transport` adapter;
  `CompareResult.scan` uses it at the actual `0x80002c6c` return.
  `scan_compare_state` keeps the semantic comparison and scan carrier at
  one endpoint. `EnvGetScanBranch.lean` instantiates the generated result
  branch for both polarities through `segEval_selected_framed`, retaining
  the scan carrier, output, and caller frame. The obsolete queued
  `check-env-get-scan-branch.sh` was retired before starting because it used
  the same failed comparison source. Its snapshot remains preserved in
  `scan-branch-source/`. The corrected check covers these additions.
  `EnvGetScanDecision.lean` stages the semantic composition:
  `CompareResult.value` exposes the actual `a0` with its name-equality
  equivalence; `scan_decision` composes the slot load, call, and branch while
  retaining the scan, output, and caller frame at one endpoint. Its source
  and dependency-manifest hashes are in `EnvGetScanDecision.sources.json`.
  This draft is included in the corrected scan check and has not been compiled.
  `scan-advance-source/` stages the generated `c54` back-edge for both
  count-branch polarities. `ScanSt.reseat` centralises carrier construction;
  `ScanSt.transport` projects it for unchanged indices. `scan_advance` selects
  the incremented index and cursor from the same reflected result, retains
  the caller frame, and relates the exit branch to semantic exhaustion.
  The snapshot records source and reused-object hashes. Its four unchanged
  prefix modules are verified; `check-env-get-scan-advance.sh` is queued to
  check the factored carrier, branch, repaired semantic decision, and back-edge.
  The factored scan carrier, result branch, and repaired semantic decision
  have now compiled with eight allowed-axiom audits. Their source/object/log
  hashes are in `EnvGetScanDecision.receipt.json`. The back-edge then failed:
  `sign_extend` needed the `LeanRV64DExecutable.Functions` namespace, and
  `gholds_lookup` needed its register-list argument before the held-register
  proof. `scan-loop-source/` fixes those references and reuses the seven
  verified prefix modules. The corrected back-edge compiled and passed its
  three allowed-axiom audits. `EnvGetScanAdvance.receipt.json` records source,
  object, log, and dependencies.
  `EnvGetScanLoop.lean` stages the fold through
  `loopFromBody`: named scan points retain the first-match invariant, a typed
  position distinguishes head/hit/exhaustion, and the loop invariant retains
  the actual caller frame and output. Its measure is remaining names at the
  generated `c60` load head and zero at either exit. Source and dependency
  hashes are in `EnvGetScanLoop.sources.json`. The frozen nine-module snapshot
  is in `scan-loop-source/`. `check-env-get-scan-loop.sh` is queued to include
  the missing `DeriveLoop` dependency, check the corrected back-edge, and then
  check this fold. Its complete 825-module slice passed (29 reused from the
  loop cache and 796 from the scan cache). The back-edge passed; compilation
  reached the loop fold, which failed only at `scanLoopMeasure_head`: its
  simplifier left `if True` unreduced. `scan-loop-repair-source/` rewrites the
  known guard before simplifying the index read. `check-env-get-scan-loop-repair.sh`
  reuses all eight verified dependency modules and checks only the corrected
  loop module. The corrected fold passed (exit 0), with six declaration audits
  using only allowed axioms. `EnvGetScanLoop.receipt.json` records its frozen
  source, object, log, dependencies, and the compiler-overlap incident below.
  A post-check hash audit matched all 825 selected dependency objects.
  This closes the inner scan loop with its actual caller frame and output.
  The whole lookup still needs prologue, parent traversal, hit copy, and return
  composition. `EnvGetScanOutcome.lean` stages the semantic exit adapter through
  `lookup_first_match` and `lookup_scan_miss`. `EnvGetParentBranch.lean` stages
  the generated parent load/branch with its actual loaded pointer and frame.
  The parent check failed before elaboration because its unnecessary
  `EnvGetSpec5` import was absent from the selected backend. The frozen
  `parent-outcome-repair-source/` snapshot imports `Code.Env_get` directly and
  reuses the verified loop objects. Both adapters await compilation.
  `EnvGetScanStart.lean` stages the generated `c48` pointer/index
  initialisation and its composition with the loop. `ScanStartReady` names
  the reached positive-count state, header read, and ownership-derived scan
  names. `scan_frame` retains the source lookup outcome and actual caller
  frame through initialisation and scanning. The frozen `scan-entry-source/`
  snapshot contains all three candidates and nine verified dependency objects.
  `check-env-get-scan-entry.sh` checks the independent parent branch, then the
  outcome and initialisation consumers. Its shell syntax check passed.
  `wait-for-lookup-checks.py` is now live with process visibility, waiting for
  the two existing build drivers, their wrappers, and project compiler children
  before entering the compiler lock. It aborts on permission failure and never
  reclaims a lock while waiting. Log: `scan-entry-wait.log`; session `44848`.
  No additional compiler has started. The positive-count
  branch must still supply `ScanStartReady` from the reached outer-loop state.
  `EnvGetCountHead.lean` now stages that generated `c40` load/test, retaining
  the loaded count, branch destination, unchanged memory, output, and saved
  registers. It reuses `wordLds4`, `bytesVal_lw_wordLds4`, and the `blez_guard`
  lemmas in `HelperCall`. Its signed count bound comes from
  `FrameOwned.length_signed`. The frozen `count-head-source/` snapshot awaits
  the additional `HelperCall` dependency and compilation. The dependency
  preview selected 906 modules, with 880 reusable and 26 pending rebuilds in
  the then-current full backend (`count-head-dependencies-plan.log`).
  `check-env-get-count-head.sh` will re-evaluate that plan, check dependencies,
  and compile the count test. `wait-for-count-check.py` is live with process
  visibility behind the builds and scan waiter; session `26008`, log
  `count-head-wait.log`. The script's syntax check passed. The count result
  has an uncompiled composition in `EnvGetFrameScan.lean`. `FrameState` retains
  frame data before scan registers are initialised; its `after_count` and
  `scan_ready` adapters supply the positive branch from the actual count result.
  `frame_scan` composes the generated count test, initialisation, and inner
  scan. `FrameOutcome.miss` unifies empty and exhausted frames at the parent
  entry, while `.hit` retains the source lookup's first binding. Source and
  pending-dependency hashes are in `EnvGetFrameScan.sources.json`. This candidate
  awaits the queued count/scan checks before compilation. Prologue and parent
  traversal must still supply `FrameState` from actual owned-store entries.
  `EnvGetOwnedFrameState.lean` stages that data supplier. `owned_frame_state`
  combines reached `FrameRegisters` with `StoreOwned`, `StoreRepr`,
  `StoreArraysReady`, `Ledger`, query ownership, and comparison geometry. It
  selects the actual names pointer and reuses the verified `scanNames` and
  `length_signed` suppliers. `FrameRegisters.after_parent` preserves the
  reached pins through `ParentResult`. Hashes and pending dependencies are in
  `EnvGetOwnedFrameState.sources.json`. These adapters are uncompiled; prologue
  execution and ownership transport to reached memory remain obligations.
  The queued `VarRowResidObstruction.lean` now also contains
  `EnvGetValuePost.with_gp` and `envGetPost_gp_not_determined`: replacing `x3`
  preserves `GoodState` by `insert_nonpinned` and every recorded post field,
  so an inhabited post cannot determine `gp`. These candidates still await
  compilation; they concern arbitrary post witnesses, not the actual run.
- `VarProductStep` needs the source store's ownership at entry. `EvalEntry`
  currently carries `StoreRepr`, not `StoreOwned`. The suppliers are
  `StoreOwned.frames`, `FrameOwned.values`, `ValueOwned.covered`, and
  `ValueOwned.copy_total`; their ownership input remains unsupplied.
- `ScanNames.nameRegW` and `bindRegW` in both `EnvGetSpec3` and
  `EnvSetScanCore` require `StrcmpWRegion` unconditionally. Together with
  `nameCStr`, the query clause forces `name.toNat % 8 = 0`, including calls
  that take the byte path. `VarRowResidObstruction.lean` now stages
  `ScanNames.name_aligned` and `scanNames_unaligned_false`; compilation is
  pending. Use the existing `StrcmpWSlack` and `strcmp_full_spec_cond`, which
  derives word alignment from the executed branch test. Keep names-array
  slot alignment separate from string-pointer alignment.

The applied alignment repair was checked in
`/private/tmp/vsa-closure-work/alignment-repair/`, over the payload-repair
snapshot. Seven files replace the two scan carriers' word regions and migrate
five comparison call sites in lookup, update, and definition scans to
`StrcmpEntryCond`. `EnvSetScan.scanMiss_to_chain` remains a direct carrier
conversion. `check-scan-alignment.sh` passed (exit 0): 860 selected modules,
833 reused and 27 rebuilt; summed module build time 2,232.6 seconds. Its four
declaration audits (`env_get_lookup_from_entry`, `scanMiss_to_chain`,
`envDefineScanCompare`, `envDefineScanCompareFramed`) report only `propext`,
`Classical.choice`, and `Quot.sound`. Receipt, source fingerprints, object
hashes, and audit log are in
`/private/tmp/vsa-closure-work/alignment-repair/backend/run-s2icy46k/`.
The module log `alignment-repair/backend/logs/Vsa_Sim_EnvGetSpec6.log` also
audits `env_get_hit_tail` and `env_get_found_spec` with the same allowed axioms.
This checks the selected dependency closure. The combined check below
also covers the marshalling consumer. Full integration remains pending.

The combined payload/alignment patch and twelve-file hash manifest are
`combined-lookup-repair.patch` and `combined-lookup-repair.sources.json`
under `/private/tmp/vsa-closure-work/`. `git apply --check` passed against
the recorded root hashes. `check-combined-lookup.sh` passed (exit 0): 862 selected modules,
860 reused, two rebuilt, and thirteen declaration audits with only allowed
axioms. This includes `EnvGetMarshal` and the lookup, update, and definition
consumers. Receipt: `combined-lookup-backend/run-6m_zxu3l/receipt.json`.
The twelve-file patch is now applied to the worktree. Full integration remains
pending in `check-lookup-integration.sh`, queued under the compiler lock.

Candidate counterexamples and recursive footprint adapters are in
`/private/tmp/vsa-closure-work/`. `check.sh` passed its 364-module dependency
slice (all reused) and the lookup audit, then failed in the obstruction file:
`St` resolved to the wrong declaration, and `insert_nonpinned` lacked its
explicit register argument. The footprint file was not reached.
`footprint-repair-source/` fixes both elaboration errors and preserves source
hashes and the dependency receipt. `check-footprint-repair.sh` checks the
footprint file first and then the obstruction file, retaining both results.
The footprint file passed all six declaration audits with allowed axioms;
`EnvGetFootprint.receipt.json` records source, object, log, and dependencies.
The obstruction file still failed because `SpecSt` is not an exported alias;
`obstruction-repair-source/` now uses the exact semantic type `Vsa.While.St`.
Its corrected check passed (exit 0), with seven allowed-axiom audits against
the preserved pre-amendment contracts. `VarRowResidObstruction.receipt.json`
records the source, object, log, and dependency snapshot. The word-alignment
obstruction concerns the old carrier, already amended in the worktree.
The arbitrary-post `gp` obstruction confirms that `VarCallLinkage.finalFrame`
must be replaced in the actual-run path by retained execution frame facts.
The variable residual remains open.
`EnvGetFootprint.lean` also contains `EnvGetEntryPost` and
`env_get_lookup_from_entry_framed`: a named adapter retaining the prologue
frame and value post at one return configuration. Its `.footprint` composes
the spill and result windows. The queued check covers these additions.
Its `.callerFootprint` composes that result with the arm-entry frame.
`ArmEntryK.destruct.memFrame` already supplies agreement outside the caller's
stack, including arena bytes; no stronger arm-memory premise is needed.
The caller still supplies `SL.lo + 1152 ≤ sp.toNat` from the actual eval entry.
`/private/tmp/vsa-closure-work/bridge-repair/` stages the consumer change over
the alignment snapshot. `varBridge_calleeQ` retains an extra memory fact at
the actual lookup return; the old `varBridge_callee` projects it.
`varBridgeF` composes the existing argument prefix and arm-entry frame with
the recursive lookup footprint. It retains `VarCallLinkage`'s outstanding
register-frame premise. This draft awaits the helper and alignment checks;
it has not been compiled or counted as a closed residual.

`EnvGetOwnedSource.lean` in that directory adds the candidate
`StoreOwned.lookupSource`: `get?_terminal_first`, `FirstMatch.index`, and
`frame_slot_valueRepr` select the same source slot that `FrameOwned.values`
owns. `EnvGetOwnedSource.copy_owned` transports its payload through the actual
total copy via `ValueOwned.copy_total`. This covers terminal frames reached
through parents. It still requires the entry's store ownership and the
copy's shared-byte agreement. `check-owned.sh` stopped before elaborating the candidate because its
dependency slice omitted the imported `RuntimeOwnershipInitial` module.
`check-owned-repair.sh` passed the complete 236-module dependency slice
(all reused), then failed because `Frame` resolved to the machine-frame
predicate. `owned-frame-repair-source/` qualifies all semantic frame types
as `Vsa.While.Frame` and records source hashes and the verified dependency
receipt. `check-owned-frame-repair.sh` passed (exit 0), with all eight
candidate audits using only allowed axioms. `EnvGetOwnedSource.receipt.json`
records the source, object, log, and dependency receipt. Entry ownership
remains unsupplied; this does not close the variable residual.
The same candidate now derives the guarded copy premise through
`ValueOwned.payload_disjoint`, and the source slot's arena bounds through
`ArrayOwned.slot_in_arena` and `FrameOwned.value_slot_in_arena`. The latter
uses the actual values-pointer read and the live allocation ledger. These
facts supply payload and source-slot geometry; they do not supply the
entry's ownership, array readiness, or scan-register facts.
`EnvGetOwnedSource.access` additionally selects all three copied words from
`StoreArraysReady`, derives source alignment, and uses
`FrameOwned.length_signed` to bound the semantic scan index by `2^31`.
These additions passed with the ownership candidate above.

`EnvGetOwnedNames.lean` stages the next consumer against the alignment repair.
`SharedCString.strcmpSlack` derives comparison geometry from the actual string
and `SharedGeom`; `FrameOwned.bindingString` selects the owned key through its
actual names-array read. `FrameOwned.scanNames` combines those facts with
`Ledger`, names-array alignment, query ownership, and mask bytes to construct
the repaired `ScanNames` carrier for every occupied slot. Its array bounds use
`ArrayOwned.slot_in_arena`. `owned-names-source/` now qualifies the semantic
frame types and imports `SharedGeometry` directly. The staged
`shared-geometry-repair/repair.patch` moves the unchanged `SharedGeom` record
out of `StrCmpCellClauses`, avoiding a dependency on the recursive cell proofs
from the entry/lookup geometry layer. `git apply --check` passed; the patch
is now applied to the worktree. `check-owned-names.sh` is queued against that frozen source
snapshot, reusing ownership and alignment dependencies before checking both
ownership modules. Its 238-module dependency slice passed (22 reused from
the ownership cache, 215 from alignment, one new geometry module built).
The ownership helper then recompiled with eight allowed-axiom audits. The name
carrier failed on its missing `EnvGetSpec9` import for `cstr_unique_eg9`.
`owned-names-repair-source/` adds that import and reuses the verified ownership
object; `check-owned-names-repair.sh` is queued to check the additional dependency
and name carrier. The corrected check passed (exit 0): 242 selected modules,
238 reused from the output cache and four from the alignment backend, with
no rebuilds. All four name-carrier declaration audits use only allowed axioms.
`EnvGetOwnedNames.receipt.json` records source, object, log, dependencies, and
the compiler-overlap incident. A post-check hash audit matched all 242 selected
dependency objects. The existing cell consumer still requires integration.
Entry ownership, shared geometry, and the fixed mask supplier remain obligations.

The payload-guard repair is staged in
`/private/tmp/vsa-closure-work/payload-repair/repair.patch`, with source hashes
in `sources.json`. It guards all six affected contracts by the actual
binding's `ValuePayload` and preserves that guard at the copy and spill
transport consumers. Its isolated source snapshot needs eleven modules
rebuilt in a 364-module dependency closure; 353 match the private backend.
The unstarted `check-payload.sh` was retired after the combined repair check
passed both of its imports and all ten declaration audits. The combined patch
supersedes this isolated candidate and is now applied to the worktree.

### 5. Close divergence, errors, and final assembly

- Construct `DivWork`: loop-head representation, `Loaded` entry drive,
  iteration/re-entry, and the 29-arm approximate recursive dispatch.
- Construct `ErrWork`: loaded-program-indexed leaves, recursive error
  propagation, formatted error/exit tail, and top-level abrupt completion.
  Complete auxiliary `hCallTooMany` with its indexed child and signed count
  bridge; reuse the bad-closure impossibility proof.
- Construct all 63 `TermResidualsBase` fields, then `RemainingWork`, then the
  final refinement theorem. Remove the 56 inherited discipline findings and the
  12 per-entry allocator ledger fields R14 reports (supplied by `of_alloc`).

### Verification hygiene: an overlay is not the backend

`rows/ClosureBuildSupply.lean` was committed (`fef1ec8`) and imported from
`Vsa.lean`, but only ever compiled into a private `proof_slice` overlay. Its
object was therefore absent from the shared backend, and the next full
`build_private` run failed at `Vsa.lean` with a missing-object error for it.
The module itself is fine; the mistake was treating "verified in my overlay" as
"verified", when the two differ exactly on whether the rest of the tree can see
the result.

The rule this implies: a slice verifies a change, but only a full build verifies
that the change is INTEGRATED. Any commit that adds a module and imports it from
a root has to be followed by a build that compiles the root against the shared
backend, or it breaks the next person's gate rather than your own. Overlays stay
the right tool for iteration — the shared backend must not be written by hand —
but the integration build is not optional, and the gap between them is a commit
that looks green and is not.

## Validation and automation still to finish

Repository artifact cleanup removed twelve tracked `.olean` files under
`experiments/`; their Lean sources remain. The active build imports none of
those experiment modules. `difftest.sh` and `smt_check.py` compile their
experiment dependencies into private directories. Backups and hashes are in
`/private/tmp/vsa-closure-work/tracked-olean-backup/removed.json`.
The source-tree scan, including ignored files and excluding dependency/Lake
directories, now finds no `.olean` or `.ilean` files. `.gitignore` excludes
both extensions. `houdini_summary_remote.sh` now requires a fingerprint-current
private backend and recompiles both experiment modules into a fresh temporary
directory before emission. Its five refusal tests and shell syntax check pass;
no remote campaign was run.
Project compiler objects also remain under `.lake/build`; they were not
removed during the live integration build.
This cleanup does not close the remaining hygiene or validation gates.

- Export typed Lean authority for each query, field, span, stop, semantic
  relation, effect, dependency, and source hash. Replace duplicated Python
  allowlists for migrated contracts. Reject missing, duplicate, stale, or
  mismatched certificates.
- Connect certified effects to SMT rewriting and post-dependent slicing.
  Parse terms before rewriting. Retain preserved inputs as dependencies;
  memory framing alone does not establish noninterference between executions.
- Project summaries onto live registers, memory, output, status, store, and
  environment. Match recursive summaries to the typed induction hypotheses.
- Finish contract-driven Houdini mining, shared summaries, incremental Z3,
  and exact-fingerprint result caching. Require convergence before validation;
  report query sizes, symbols, solve times, and unsat cores.
- For each helper family, connect a finite SMT relation, independent Python
  oracle, and Lean semantic bridge. Cover environment operations, equality,
  truthiness, strings, allocation, boxing, and output.
- Compare actual ELF/Sail traces, SMT reflection, and the independent oracle.
  Check claimed register, memory-footprint, and output effects, including
  composition. Cover zero/one/many iterations, every status, argument and
  parameter boundaries, shadowing/update/miss, parent chains, and output
  prefixes/suffixes. Kill branch, boundary, effect, and semantic mutants.
- Complete the coverage ledger for 63 base fields, `DivWork`, `ErrWork`, and
  `hCallTooMany`. Record execution, SMT, oracle, mutation, Lean-bridge, and
  full-residual evidence independently, with explicit finite/composite/
  Lean-only/nonfinite capabilities.
- Rerun the full supplier search at exact inherited types and the complete
  library census. Preserve all four initial-boundary regression cases.
- Allocator-layer checks: rule R14 (`scripts/discipline_rules.tsv`) fires on any
  hand-rolled allocator ledger field outside `AllocLedger`; the census must find
  `EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc` and
  `EnvDefineMissLedger.of_alloc` at their inherited types, and `FreeRun` and
  `AllocLedger.ainv_perm` are new named premises needing SMT/oracle evidence
  rows in the coverage ledger.
- Induction-hypothesis clauses (`scripts/ih_clauses.tsv`, `gen_ih_clause.py`,
  `Vsa/Sim/IHClauseSupport.lean`): a clause is an `EvalExtraM` (or an
  `EvalExtra` embedded through `EvalIHWith.toM`) recursed as the `EvalIHWithM`
  motive beside the old motive (product recursor); each recursor case is a
  named `Residuals` field (`Vsa.Sim.IHClause.<Name>.Residuals.<case>`).
  `Trivial` is closed (`closed`, axiom-clean). `Footprint` is
  `footExtra noArenaFoot` (`Vsa/Sim/ExitFootprint.lean`): its 15 `EvalE`
  fields (children `EvalIHF noArenaFoot` → parent `EvalIHF noArenaFoot`) are
  the generic `footprint` hooks. Motives
  of the other eight relations default to `True`, so a clause step at `hCall`
  receives nothing from the callee: a footprint-style clause needs the `Call`
  and `ExecSeq` motives declared in the `motives` column before its `hCall`
  field is inhabited.
- Clause-field automation (`scripts/ih_clause_status.py`, `ih_clause_fuzz.py`,
  `ih_clause_ledger.py`, `proof_slice --structure`; TOOLING.md "Validation"):
  per field WIRED/HOOK/MANUAL/STALE, hook-lemma probes, census re-check of the
  wirings, drafted candidates checked in Lean, refutation verdicts, and an
  evidence ledger. Measured on the overlay: `Trivial` 15/15 WIRED (census
  FOUND); `Footprint` (`footExtra noArenaFoot`) 15/15 HOOK,
  `Vsa.Sim.IHClauseGeneric.footprint.*` missing, every drafted candidate
  (hook lemma, `trivialStep_of_old`, `withMaps_of_old` bare/`.toM`) rejected
  by Lean (FAILED ×15). Unwired steps are outside the statement_fuzz/smt_check
  fragment (motive conclusions); the bounded engines report ENCODE-GAP. No
  trace query targets a clause step (execution evidence 0/30).

The current checkpoint's four actual Sail boundary regressions passed against
matching source hashes. The three unsafe snapshots are excluded by the current
boundary; the admitted stable control matches source output and termination.
`/private/tmp/vsa-closure-work/integration-boundary-receipt.json` records the
summary hash, all 1,254 verified input hashes, eight artifact hashes, and all
four case results. The checkpoint then passed all 260 Python tests in 80.211
seconds without skips and the four generator checks. It stopped at stage a4
with 56 discipline findings; later stages did not run. Exact log hash and
findings: `integration-checkpoint-receipt.json` in the same directory.
The separate declaration audit passed all 1,086 entries with allowed axioms.
`integration-axiom-receipt.json` retains its script/log hashes and the preceding
backend manifest. These checkpoint results predate the lookup integration batch.

The worktree now contains the twelve lookup amendments,
`Vsa/Sim/SharedGeometry.lean` with the unchanged geometry record, and
`Vsa/Sim/RuntimeOwnershipLookup.lean` with the verified ownership suppliers.
`Vsa.lean` imports the ownership module. `lookup-integration-sources.json`
records the sixteen affected source hashes. `check-lookup-integration.sh` has
completed the all-source private compilation (exit 0). Backend verification
failed (exit 2): `Vsa.Sim.rows.IHClause_FootprintPayloadOwnedSlack`,
`Vsa.Sim.rows.StrCmpCellsOwnedClosed`, and `Vsa` were stale.
`lookup-integration-receipt.json` retains the exit codes and log hashes.
This does not establish a fingerprint-current integration checkpoint.
The queued scan-entry check also finished: `EnvGetScanOutcome` passed;
`EnvGetParentBranch` and `EnvGetScanStart` failed on unreduced bitvector
numerals in address arithmetic. Failed declarations are not accepted proof
evidence. `EnvGetScanEntry.receipt.json` records the aggregate failure.
The count-head check passed (exit 0), recorded in
`EnvGetCountHead.receipt.json`. Frame-scan and owned-frame-state composition
remain uncompiled private drafts.
Fresh boundary validation and the complete supplier search remain required.
The final residual construction remains open.

## Completion gates

Run against one frozen source snapshot. Partial checks do not close these gates.

| Gate | Required evidence |
|---|---|
| A — Emission | Fresh, complete emission of all 72 finite queries with typed capabilities and provenance. |
| B — SMT | Every executable semantic projection decided; no unknown, timeout, malformed query, inconsistent premise, or assumed validity. |
| C — Certificates | Query, field, span, theorem, footprint, and provenance mutations all rejected. |
| D — Fuzzing | Every claimed executable leaf covered; clean findings and all required mutants killed. |
| E — Semantic seams | Exact Lean theorem coverage for every non-SMT seam. |
| F — Termination | Compiled, hypothesis-free constructor for all 63 base fields. |
| G — Divergence/errors | Compiled `DivWork` and `ErrWork` for the concrete layout and loaded-program index. |
| H — Assembly | `remainingWork_closed : RemainingWork interpRunLayout`. |
| I — Refinement | `endToEnd_refinement remainingWork_closed` compiles; axioms limited to `propext`, `Classical.choice`, and `Quot.sound`. |
| J — Hygiene | Discipline and generator checks pass; unchanged ELF; no admitted proofs, extra axioms, `native_decide`, `bv_decide`, raised limits, stale objects, or repository-generated `.olean` files. |

## Execution rules

Follow [CLAUDE.md](../../CLAUDE.md) for proof discipline and
[TOOLING.md](../../TOOLING.md) for commands. Run the abstraction inventory
before proof work. Record each new contract gap beside its task, with the
affected declaration, missing supplier, obstruction evidence, and import
dependents. Update this plan in place; keep build transcripts in receipts.

Use one compiler or full solver/fuzzer campaign at a time. Preserve the private
cache `/private/tmp/vsa-full-build.sQd0gM` and resume it with `--resume`.
Check changed dependencies before consumers; run the all-source gate at a
completed residual or shared-interface checkpoint. Record fingerprints,
built/reused counts, exit status, log, and timing. Documentation edits need
no Lean rebuild.

The latest parent-branch launch exposed a lock-wrapper failure: `kill -0`
reported live owners as unavailable, and the wrapper reclaimed their locks.
Process inspection confirmed overlapping external, integration, name-carrier,
and loop checks. Preserve those running jobs and their snapshots. Launch no
further compiler until they finish. Future lock acquisition must have process
visibility; permission failure is not evidence that an owner is dead.
`lock-visibility-receipt.json` records the confirming probe: sandboxed
`kill -0 58547` failed with `operation not permitted`; the same probe with
process visibility succeeded. Launch future compiler wrappers with
`require_escalated`; do not modify the running wrapper or reclaim its lock.
