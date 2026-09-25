# Interpreter-level design: `eval_expr`, `exec_stmt`, `interp_run` in the Iris logic

Status: built. The statements live in `Interp/SpecEval.lean`,
`Interp/SpecExecDisp.lean`, `Interp/SpecLoop.lean` and the helper `Spec*.lean`
files; the assumptions in `Interp/Holes.lean`; the assembly in
`Interp/TermSim.lean`, `Interp/StuckSim.lean`, `Interp/TopRun*.lean` and
`Interp/EndToEnd.lean`. This page fixes the representation predicates, the
function specs, the assembly of `InterpSim`, and the fan-out. MachCSL's own rule applies here (paper §9.1, xv6iris
`claude-notes/durable-notes.md` "Orchestration"): the top level owns the specs,
and a proof that fights its interface is evidence the interface is wrong.

Rocq citations are to xv6iris at `8438e55` (`iris/…`, `claude-notes/…`).

## Decisions (user, 2026-09-23)

- **Q1 accepted.** `Loaded` gains a `StackAdmissible` field shaped like `capacity`. The top-level statement narrows honestly; no unprovable stack claim remains. (S1)
- **Q2: `IrisHoles` replaces `RemainingWork`.** Do not keep both. Package A deletes `RemainingWork`, `TermResidualsBase`, `DivWork`, `ErrWork` and their suppliers once `endToEnd_refinement` is re-proved from `IrisHoles`; the name `endToEnd_refinement` is kept.
- **Q3: two WPs** (`mTWP` total, `mWP` partial) behind `MachWP`.
- **Q4: newlib `snprintf`/`fprintf` safety specs stay as named holes for now,** scheduled after E1–E6. They must not be forgotten: every hole lives as a field of `IrisHoles` (so it appears in the final theorem's hypothesis) AND has an entry in `VsaIris/HOLES.md` with owner package, satisfiability evidence and discharge plan. `scripts/check_iris_holes.py` fails if the two disagree.
- **A0's `BootGap` moves into `Loaded` (2026-09-24).** The boundary heap facts become `InterpRunReadyFacts` fields, as Q1 did with `stack_admissible`; `world_of_boundary` no longer takes them as a premise. (lane BG; see the next STATEMENT CHANGE)

- **Two more boundary facts in `Loaded` (2026-09-24, integration).** H1's frame invariant (`FrameLayout`/`FrameBridge`: canonical capacity, `SharedWin` for string reads) needs them at the global frame; `Loaded` did not state them. (see the next STATEMENT CHANGE)

- **Q8 decided (2026-09-24): the semantics cuts.** `Value.catDisplay` renders a named closure as `fnCatRender n = "<fn " ++ n ++ ">"` cut to 63 characters (strings are byte lists, so 63 bytes), exactly `stringify`'s `snprintf(buf, 64, "<fn %s>", n)` (`Newlib.fnRender_eq`, `strRender_eq`). `Loaded` is unchanged.
- **Boundary facts (standing, 2026-09-24).** A fact a proof needs at the boundary that `Loaded` does not state becomes a `BootHeapFacts` field with a control witness.

## STATEMENT CHANGE (lane A): the general registers and `main`'s `s0` in `Loaded`

`InterpRunReadyFacts` (`Vsa/Sim/LayoutInstance.lean`) gains two fields, as
the standing decision on boundary facts (2026-09-24) prescribes:

```lean
gprs      : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome
s0_impure : c.σ.regs.get? Register.x8 = some 0x8001b970#64
```

- **Why.** Adequacy needs the global invariant at the loaded configuration,
  and `VsaOk.gpr` states every general register present; `Loaded` named only
  the argument and callee-saved ones. `interp_run` spills `s0`, and its error
  line and the `longjmp` landing reload it as `&_impure_ptr`
  (`interpRun_partial_boot`'s `R0 8 = 0x8001b970`); `main` sets it at
  `0x80004590` (`addi s0,gp,1120`) before `jal interp_run`.
- **What narrowed.** `interpRunLayout.atInterpRun`, hence `Loaded
  interpRunLayout p c` and the hypothesis of `endToEnd_refinement`.
  `Refinement.lean` is unchanged. `InterpRunPhysicalFacts` and the historical
  boundaries (`BeforeRuntimeOwnership` etc.) are unchanged.
- **Not vacuous.** The control's snapshot now has `s0 = 0x8001b970`
  (`OutputAliasPhysical.physicalConfigS0`: `physicalRegs` with `x8`
  replaced; `Control.heapConfig` uses it). `physicalS0_gprs` and
  `physicalRegsS0_x8` supply the fields in `Control.readyFacts`; the other
  physical facts transport through `PhysicalCarrier.of_regs_s0`. The
  output-alias witness keeps `physicalConfig` (`s0 = 0`); its trace is
  unchanged.
- **Consumer.** `TopBoundary.vsaOk_of_ready` (no `hgpr` premise);
  `TopEntryBoot.topRegs_ready`/`topRegs_carve` (the entry registers from
  adequacy's register points-to), `codeRes_of_boundary` (`gp ↦ᵣ gpV ∗ binImg
  ⊢ |==> codeRes`), `interpRun_total_top`/`interpRun_partial_top`.

## STATEMENT CHANGE (lane A): the landing core stops at `interp_run`'s frame

`StackGeom s n` (`SpecEval.lean`) gains `top : s.toNat ≤ spEntry - interpRunFrame`:
every `eval_expr`/`exec_stmt` site (and every helper whose `stackAt` carries
`StackGeom`) runs at or below `interp_run`'s lowered `sp`. `CoreOK`
(`SpecErr.lean`) widens only regions with `sc.toNat ≤ spEntry - interpRunFrame`,
and `evalCore := abortCore N L Room inp runSp (runSp.toNat - 0x87800000)`
(`LeafErr.lean`; `runSp = BitVec.ofNat 64 (spEntry - interpRunFrame)`), no longer
the whole segment.

- **Why.** H5's `wp_abort` accepts `abortRes … (sM - 176) n` only: an
  out-of-memory `exit` over the whole segment could run on bytes the top owns
  (`struct Interp`, `main`'s frame).
- **Producers.** The top's `topStackGeom`; children derive `top` from the
  parent (`narrow`, `lower`, `lowerE`, `evalCallGeom`, `callGeomF`,
  `stackGeom_evalSP`); the helper contexts (`SgCtx`, `NpCtx`, `NplCtx`,
  `NaCtx`) carry it from their entry `StackGeom`.
- **Consequence.** `TopRunP.evalCore_top`: the partial specs' core is the top's
  abort core; `interpRun_partial` has no `hcore` premise.

## STATEMENT CHANGE (lane A): the `interp_run` loop keeps the node and the frame image

`interpSeqP_body` (`SeqLoopInterp.lean`) now returns, at a `ret`/`brk`/`cont`
exit, `ReadOK (R' 9).toNat` (`s1` is still the statement node, `ReadOK` from
`InterpData.geo` at the node's tag), and its abort branch hands the frame back
as `ownSet (interpS s) (fun a => a ↦ₘ imgM Mt a)` instead of `byteAny` (the
`longjmp` landing reloads `in`, the link and `main`'s `s0` from it). The abort
image comes from `Arm.ms_callExecPM` (the exec call threading one continuation
`K` whose abort branch takes the frame at `Mt`); `ms_callExecP` is its
instance. `interpRun_partial` uses `interpSeqP_all` directly (the former
premise `interpSeqPX_body` is gone).

## STATEMENT CHANGE (lane A): one rule for the top-level abrupt statuses

H5's `TopAbrupt.wp_topAbrupt` (the `line` word as `roImg`, which no AST
representation supplies: the statement's `+4` word is not in its read set) and
lane A's `wp_topAbrH` are folded into `Interp.wp_topAbrupt` (`TopRunP.lean`),
over H5's descriptor `TopSite` (now `head`, `fmt`, `fmtBytes`, `jal`) and
certificates `topRet_ok`/`topBrk_ok` (`jal` and format facts), with the
staging and tail as `interp_run`'s symbolic runs (`TopRuns`, `line` read by
havoc from a `ReadOK` node).

## STATEMENT CHANGE (lane A): closure geometry in `closOwn`

`closOwn ca cd` (`Repr.lean`) carries `ClosObj img p q e` (nonnull, the
`fn_expr`/`env` words, and `ReadOK` on the object's 16 bytes) and the `EX_FN`
node as `astEG` (view with `ReadOK` geometry) instead of `astE`. `ReadOK` and
`astEG` moved from `SpecEval.lean` to `Repr.lean` (names kept).

- **Why.** The closure call and `value_print` load the object and the node;
  `CloSupply`/`DispSupply` were named premises because `closOwn` lacked the
  geometry.
- **Producer.** The `fn` arm (`fnLit_{T,P}` templates) passes the fresh heap
  block's placement and the node's `astEG` to `storeRepr_allocClosure`.
  The boundary store has no closures (`storeRepr_empty`).
- **Consequence.** `cloSupply : CloSupply N` and `dispSupply : DispSupply N`
  (`CallClosure.lean`) hold for every `N`; `SharedWin` follows from `ReadOK`.
## STATEMENT CHANGE (lane A): `_impure_ptr` is read-only

`Stdio.stdioAt P` owns the 8 bytes of `_impure_ptr` (`0x8001b970`, never
written; it holds `&_impure_data`) as the persistent `Stdio.impureRO`
(`roImg impureW impureByte`, `VsaIris/Vsa/ImpureRO.lean`) and every other
byte of `stdioFoot` (`stdioExcl`) exclusively; its image agrees with
`_impure_ptr` (`ImpureImg`). `StdioOK` is unchanged.

- **Why.** `envText` and `allocText` list `_impure_ptr` as `↦ₘ□`, and full
  and discarded ownership of one byte cannot coexist, so `textOwn allocText`
  could not be produced next to `world`'s `stdioOwn`.
- **Consequence.** `textOwn_envText`/`textOwn_allocText` (`binImg ∗
  impureRO ⊢ textOwn …`, `VsaIris/Vsa/ImpureText.lean`); `stdioAt_impure`
  projects `impureRO`. The boundary discards the 8 bytes with a ghost update.
  Readers of `_impure_ptr` (`main`'s error line, the out-of-memory block,
  `native_print`/`native_println`) read it with a discarded fraction
  (`imgFootD`, the data view `impMem`).
- **Holes.** The `IrisHoles` newlib statements keep their text; newlib never
  writes `_impure_ptr`, so they remain satisfiable.

## STATEMENT CHANGE (lane A): helper specs carry their code context; memcpy/strcpy destinations above HTIF

Every helper spec a case lemma takes as a closed hypothesis carries, in its
precondition, the persistent code context its proof runs from:

| spec | added to the precondition |
|---|---|
| `envNewSpec`, `envDefineSpec` | `codeX` (beside `gp ↦ᵣ□ gpV`) |
| `envGetSpec`, `envSetSpec` | `gp ↦ᵣ□ gpV ∗ codeX` |
| `strcmpSpecV`, `strcmpOrdSpec`, `strlenHeapSpec`, `strcpyHeapSpec` | `binImg` |
| `memcpySpecOwned` | `binImg` |
| `valueEqualSpec` | `binImg` (its `strcmp` call's) |

`codeX := binImg ∗ impureRO` (`VsaIris/Vsa/ImpureText.lean`) gives
`textOwn envText`/`textOwn allocText`; `world_codeX`/`world_allocText`/
`world_binImg` frame it out of `world`, `codeRes_gpM` gives `gp`.

- **Destinations above HTIF.** `memcpySpec`, `memcpySpecOwned`, `strcpySpec`
  and `strcpyHeapSpec` require `htifLo + 16 ≤ dst.toNat` (VSA's store facts
  hold only above the HTIF words). The `…H` copies and the `gapRO` premise are
  deleted; `memcpy_spec_env`/`memcpy_spec_owned`/`StrLeaf.strcpy_spec`/
  `StrLeaf.strcpy_heap_spec` prove the real specs. Every caller's destination
  is a heap block or a stack buffer (env_define's name copy, `stringify`'s
  buffers, the concatenation block).
- **`stringifySpec`'s abort** is `⌜ρ = .uncounted⌝ ∗ abortRes … ∗ slot24 p`:
  only an uncounted `malloc` fails, and the out-of-memory path hands back the
  value's slot, so `stringifySpecT` (counted) and `stringifySpecP` are both
  consequences (`stringifyT_closed`, `stringifyP_closed`).
- **Leaf specs inside helper proofs** (`strcmpSpec`, `strlenSpec`,
  `memcpySpec`, `strcpySpec`) stay code-free resources; the proofs that use
  them own `binImg` and take them as `binImg ⊢ …` (`stringify_spec`) or
  receive them from it (`envDefine_closed`).
- **The cases.** `caseT_FnLit`/`caseP_FnLit`/`caseT_BinaryConcat`/
  `caseP_BinaryAdd` are closed statements: they take `binImg` and
  `textOwn allocText` from `world` in their precondition. `TermSupply`/
  `StuckSupply` lose `fnLit`/`concat`/`add` and gain `alloc`,
  `stringifyT`/`stringifyP`, `strlenHeap`, `memcpyOwned`, `strcpyHeap`.
- **`topLive`** adds `_impure_ptr`'s 8 bytes (in `envText`/`allocText`) and the
  stack segment (`stringify`'s `strlen` of its stack buffer), present in a
  loaded configuration by `InterpRunPhysicalFacts.statics`/`.stack_bytes`.
- **Suppliers.** `VsaIris/Interp/Supply.lean`: the generic
  `fnSpecW_close`/`fnSpecAbort_close`/`helperSpec_close` (a spec proved under
  a persistent context its precondition carries is closed), one `*_closed`
  theorem per spec, and `supplies_of : IrisHoles → Supplies`.

## STATEMENT CHANGE (lane A, Q7 decided 2026-09-25): the helpers' stack headroom

`Vsa.Sim.LayoutInstance.helperHeadroom = 2048` is added to
`ProgramStackFits.need` (a narrowing of `Loaded`, as Q1) and to the Iris
budget `stackBudget need d = need + (maxCallDepth - d) * perCallBudget +
evalFrame + helperHeadroom`.

- **Why.** At call depth `maxCallDepth` the budget left `evalFrame = 1088`
  bytes below a leaf arm's frame, but `runtime_error` needs `rtErrNeed = 1248`
  (so `ErrRoom (.var x) maxCallDepth` was false), and a native call's
  `fprintf` chain needs `nativePrintlnNeed = 4224` below a call node that
  left 2176 (E4's `hroom`). The constant is the larger shortfall.
- **Consequence.** `ErrRoom e d` holds at every depth (`errRoom`); E4's
  `hroom` holds at every depth.
- **Not vacuous.** The control program and every `c/tests/*.wl` witness
  (`StackAdmissibleWitness.lean`) still decide `programStackFits` (about
  2.24 MB of slack).

## STATEMENT CHANGE (lane A): `newlib.exitHandlers` is exact from `StdioOK`

`exitHandlersSpec` takes `quiet : Bool`: with `quiet = true` it starts from
`StdioOK` only and the continuation's output extension is empty. `term_sim`
needs `Halts c st'.out 0` exactly; the old field allowed `exit(0)` to print.
It holds of the binary: `main` makes `stdout` unbuffered, so the close path
flushes nothing. `wp_exitCall` takes `quiet`; H5's error exits pass `false`.

## STATEMENT CHANGE (integration): the global frame's capacity and the shared bytes' geometry

`BootFrameChunks` gains `cap_canon : F.cap = 8` (the capacity `env_define`
reaches for `interp_init`'s three natives, `capFor 3`), and `BootHeapFacts`
gains `shared_geom : SharedGeom shared stackSL` (every shared byte is RAM with
8 bytes of slack, off the HTIF words and the stack; VSA's own `SharedGeom`).

- **Why.** H1 made the frame invariant exact: `FrameLayout.cap_canon`
  (`cap = capFor n`, which the counted regime's growth charges follow) and
  `frameBody_of_frameRepr`'s `SharedWin P` (the string routines' read
  window). Neither follows from the ownership data: `FrameArraysOwned.bound`
  only gives `3 ≤ cap`, and `Immutable.readable` only `k < 2^32`.
- **What narrowed.** `Loaded interpRunLayout p c`, as in lane BG.
- **Not vacuous.** The control has `cap = 8` (`rfl`) and shared bytes at
  `0x81000200…` and in the AST page (`Control.sharedGeom`, `omega`).
- **Consumer.** `World.lean`: `BootGap.sharedWin` (`sharedWin_of_geom`),
  `FrameChunks.cap_canon`. The array blocks are the chunk payloads cut to
  `8 cap`/`24 cap` bytes (`trimArrays`, H1's exact `FrameLayout.arrays`); the
  boundary heap's live list `Boot.H` trims them the same way
  (`BlockHeapAt.shrink`), so the store's blocks stay live-list members.

## STATEMENT CHANGE (lane BG): `Loaded interpRunLayout` now carries the boundary heap facts

`Vsa/Sim/LayoutInstance.lean` `InterpRunReadyFacts` replaced the field
`ownership : ∃ D, InitialOwned … D` by

```lean
boot : ∃ D top brkv chunks bins F,
  BootHeap c.σ.mem A φf φc stmts count D top brkv chunks bins F
structure BootHeap … : Prop where
  owned : InitialOwned m A stackSL φf φc stmts count D
  alloc : InitialAllocatorAt m D.exts (ReallocExtent D.allocations) stmts count top brkv chunks bins
  facts : BootHeapFacts m D.shared (φf 0) top brkv chunks F
structure BootHeapFacts … : Prop where
  top_room  : top + 16 ≤ brkv                    -- dlmalloc's MINSIZE top
  brk_page  : brkv % 4096 = 0                    -- Q5
  binblocks : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32   -- Q5b
  frame     : BootFrameChunks m chunks shared e F  -- global frame: 3 distinct whole unshared chunk payloads, cap 8
  stderr    : read64 m impureStderrAddr = some exitStderr            -- Q6
  shared_geom : SharedGeom shared stackSL                            -- (integration)
```

- **What narrowed.** `interpRunLayout.atInterpRun`, hence `Loaded
  interpRunLayout p c` and the hypothesis of `endToEnd_refinement`.
  `Refinement.lean` is unchanged. `InterpRunReadyFacts.ownership` is now a
  theorem projecting `boot`, with the old field's type, so its consumers are
  unchanged.
- **Why these witnesses together.** The facts are about the ownership
  data's `shared` set and one allocator walk (`top`, `brkv`, `chunks`), which
  `ownership` and `InitialOwned.allocator` bound existentially. Stating them
  as separate fields would let the gap talk about different witnesses.
- **Consumer.** `VsaIris/Interp/World.lean`: `boot_of_loaded` fills
  `Boot.frame`/`Boot.heapFacts` from `boot`; `Boot.G` is the frame geometry
  and `Boot.gap : BootGap b b.G` projects the old premise.
  `world_of_boundary b ρ hρ` has no gap argument and carves `b.bytes b.G`.
- **Not vacuous.** The control: `Vsa/Sim/NativeNameAudit/ControlBootHeap.lean`
  (`Control.bootHeap`: kernel `decide`s over the chunk list and reads through
  the heap log), consumed by `Control.readyFacts`, hence `Control.loaded`.
  No field mentions the program, so unlike `ProgramStackFits` there is no
  per-program predicate to decide at `c/tests/*.wl`. No checked `Loaded`
  configuration has been built for those programs, for any field.

## STATEMENT CHANGE (S1, Q1 landed): `Loaded interpRunLayout` now carries stack admissibility

`Vsa/Sim/LayoutInstance.lean` `InterpRunReadyFacts` gained the field

```lean
stack_admissible : StackAdmissible c.σ.mem stmts count
-- StackAdmissible m stmts count :=
--   ∀ p, ProgramRepr m stmts count p → ProgramStackFits p
structure ProgramStackFits (p : Program) : Prop where
  need   : stackSL.lo + Stmt.stackNeedList p + maxCallDepth * perCallBudget
             + evalFrame + interpRunFrame ≤ spEntry
  bodies : Stmt.bodiesBoundList perCallBudget p = true
```

- **What narrowed.** `interpRunLayout.atInterpRun`, hence
  `Loaded interpRunLayout p c`, hence the hypothesis of `endToEnd_refinement`
  (and of `endToEnd_refinement_iris`). `Refinement.lean` is unchanged:
  `Loaded` is generic in `Layout`, and the field sits in the concrete layout's
  ready facts, beside `ownership`, which carries
  `DlHeap.InitialAllocatorAt.capacity` (same ∀-over-`ProgramRepr` shape).
- **So `interpRunLayout' = interpRunLayout`.** §5.4 and `Specs.lean` need no
  separate layout. The skeleton's `StackAdmissible` is superseded by the
  landed one.
- **Why.** §10.4: without it, an AST deeper than the 8 MiB stack overflows
  into the heap (`heapEnd = stackSL.lo = 0x87800000`), and `InterpSim` is
  unprovable.
- **The bound's arithmetic.** `interp_run` spills 176 bytes
  (`interpRunFrame`), then calls `exec_stmt` at `spEntry - 176` with depth 0.
  Each top-level statement needs ItemZero's `execNeed s 0 = s.stackNeed +
  maxCallDepth * perCallBudget + evalFrame` below that. The consumer is
  `ProgramStackFits.execBudget`, which gives the `StackOK` at the first call.
- **Not vacuous.**
  - The control program: `NativeNameAudit.Control.readyFacts` (so
    `Control.loaded` still inhabits `Loaded interpRunLayout`).
  - Every `c/tests/*.wl` program and `Validation.recursionSmall`:
    `Vsa/Sim/StackAdmissibleWitness.lean`, one kernel `decide` of
    `programStackFits` each.
  - Needs range from 3440 to 5232 bytes, against about 2.24 MB of slack.

## 0. The design in five sentences

1. Every block of machine code (a reflected segment, a helper call, a loop) is
   proved ONCE, against an abstract WP `W` that both the total WP (`mTWP`) and a
   new partial WP (`mWP`) instantiate (§1).
2. `term_sim` uses TOTAL, derivation-indexed specs, proved by the existing
   mutual recursor over the cost companions (`EvalECost` …), exactly the motive
   pattern `TermSimAssembly` already uses. It needs no determinism lemma and has
   no error arms.
3. `stuck_sim` uses PARTIAL, outcome-quantified specs, proved by Löb. Their
   continuation is an additive pair: return with a derivation, or abort (runtime
   error or out-of-memory exit). This one Löb proof replaces `ErrWork` and
   `DivWork` together.
4. The runtime is owned by representation predicates. Strings, AST and closures
   are persistent. Frames are exclusive inside one `storeRepr`. The allocator is
   `isHeap`/`isHeapRoom` in MachCSL's counted and uncounted regimes. Output is a
   console ghost cell.
5. The final theorem is `Vsa.Refine.refinement` applied to
   `interpSim_iris (h : IrisHoles)`. `Refinement.lean` is unchanged, and
   `IrisHoles` names the allocator machine runs and the newlib safety specs,
   nothing else.

## 1. Two directions, one set of blocks

### Why two WPs

`term_sim` needs termination, so it needs a total WP, and total WPs forbid Löb.
`stuck_sim` needs a statement about programs with *no* derivation, including
divergent ones: "the machine never halts with exit 0". That is a safety
statement, and it needs a partial WP and Löb (partial adequacy: never stuck,
and every halt satisfies `Φ`).

The rejected alternative is one partial WP plus a step-credit resource for
termination (time credits). It would demand an exact step budget per
derivation: string lengths, bin scans in `_malloc_r`, the `strlen` word loop.
That is the brittle counting VSA's `TripleN` already pays for. Two WPs cost one
extra piece of glue per case (the generator emits both, §6). The blocks are
shared, and blocks are where the proof mass lives.

### The shared interface (work package F1, landed)

```lean
structure MachWP (M : MachineModel) where          -- VsaIris/MachWP.lean
  W       : (Nat × String → IProp GF) → IProp GF
  lat     : IProp GF → IProp GF                    -- step modality: id (total), ▷ (partial)
  lat_intro : ∀ P, P ⊢ lat P
  lagRun  : LagFoot M Fp Fp' Pre Post K →          -- the lag kernel (Lag.lean) at W level
            Fp ∗ (∀ σ σf, ⌜Post σ σf⌝ -∗ Fp' σf -∗ lat (W Φ)) ⊢ W Φ
  halt    : …                                      -- VsaIris.wp_exec_halt, abstracted
  fupd    : (|={⊤}=> W Φ) ⊢ W Φ
  -- console (F2): MachWP.runOut and MachWP.haltConsole are derived theorems
```

- `twpW M := ⟨mTWP M, id, …⟩` and `wpW M := ⟨mWP M, ▷, …⟩`.
  `mWP M Φ := cpuTok -∗ WP Loop @ NotStuck; ⊤ {{ Φ }}` (iris-lean
  `ProgramLogic/WeakestPre.lean`) with the same lagging state interpretation
  (`Ptsto.fullInterp`).
- Why `lagRun` rather than a `run` field: a `RunFact` segment and a
  `LocalRun` segment are both instances of one lagged run (`LagFoot`). Both
  WPs prove the kernel once (`Lag.lag_run`, from a single-step rule
  `StepRule lat L`), and `MachWP.run` (= `wp_run`), `MachWP.runL` and
  `wp_localRunW` derive from it for every `Wp`. The earlier draft's `run`
  field could not give the loop rule, whose segments end in a predicate, not
  in exact values.
- `lat` records the later that one step of the partial WP pays for. Blocks use
  the later-free `Wp.run`; `(wpW M).runL` (`wp_run_later`) gives the
  continuation `▷ mWP`, which Löb consumes (`wp_call_later` for a recursive
  `jal`).
- `twp_wp : mTWP M Φ ⊢ mWP M Φ` (iris-lean `twp.to_wp`) is not
  needed by any block, because blocks are generic. The assembly uses it only
  where a partial proof calls something proved only totally (§5.3).
- Partial adequacy: `mach_adequacyP` (`Adequacy.lean`) and, at the VSA
  instance, `Inst.vsa_adequacyP_nonzero`:
  `AdequacyHypP GF (vsaModel live) mr mm (fun v => v.1 ≠ 0) →
   Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0`, `stuck_sim`'s conclusion.

Every lemma below `eval_expr` is stated `∀ (Wp : MachWP M)`. Helper loops are
proved by **fuel induction, not Löb**, which is sound for both WPs and is also
MachCSL's idiom for bounded loops (`ProofMemset.v:1-9` "bounded loop, not
iLöb"; `ProofMemmove.v:350` `mm_loop`, induction on `rem`). Only the three
recursive entry points (`eval_expr`, `exec_stmt`, and the `interp_run` loop) are
mode-specific.

### The mode-generic function spec

`fnSpec` (`Call.lean`) is `fnSpecW Wp` at `Wp := twpW`. `fnSpecW Wp` takes the
WP as a parameter; the body is unchanged. The partial recursive specs need a
second exit, `fnSpecAbort` (§4.2):

```lean
def fnSpecAbort (Wp) (entry) (P Q : BitVec 64 → IProp GF) (A : IProp GF) :=
  □ ∀ r Φ, PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
    ((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ)) -∗ Wp.W Φ
```

The `∧` is xv6iris's rule (`durable-notes.md`, "Contracts and resources": two
continuations of which exactly one fires are an ADDITIVE pair). The return
branch and the abort branch are proved from the SAME resources, so a caller's
frame, and the abort continuation it inherited, are available to both.

## 2. Foundations the specs need (work packages F1–F3)

- **F1, the partial WP (landed).** `mWP` (`PartialWP.lean`); the segment rule
  with a later for it (`wp_run_later`); the halt rule (`wpP_exec_halt`); and
  partial adequacy at the VSA instance (`Inst.vsa_adequacyP`):

  `AdequacyHypP … φ → Diverges c ∨ ∃ out e, Halts c out e ∧ φ (e, out)`

  The loop is deterministic with one non-value expression, so never stuck
  plus no reachable exit gives `Diverges` (`diverges_or_halts_of_adequate`,
  classical case split on exit reachability). It reuses `wp_adequacy_gen`,
  as the total route does.
- **F2, the console (built: `Ptsto.lean`, `Step.lean`, `Vsa/Console.lean`).**
  - `MachineModel` has `out : State → String` (VSA: `Vsa.Machine.output`).
  - The console cell `consoleOwn s` is a ghost map on `MachGS.conName`, key 0.
    Its authority `conInterp` is part of `mstateInterp` and lags with the
    register and memory maps (`lagInterp`, `ConAgree`). MachCSL's console
    authority sits in the state interpretation the same way (paper §7.5,
    Figure 28 `cons_auth`). `consoleOwn_excl`: there is one console.
  - Every run fact frames the output. `RunFactO … o` carries the run's console
    effect `OutStep` (`none` silent, `some o` prints `o`), and `RunFact` is the
    silent case. `SegFrom`, `RetExec` and `JalExec` carry the same conjunct.
    VSA's `segEval_sound` already proves it (`σ'.sailOutput = σ.sailOutput`);
    `jalExec_of_site` takes `StepConFrame` from the jal's observation. A run
    that does not own the console cannot print, so a missing putchar is an
    unprovable goal.
  - The lag kernel carries the console authority: `LagFoot.look`/`commit`
    see all three authorities (`mauths`). `LagFoot.ofRM` builds a silent
    run's instance from register/memory lookup and commit plus its output
    frame; `RunFact.lagFoot` and `SegFrom.lagFoot` use it.
  - `MachWP.runOut` (the `putc` rule), for either WP: a printing run
    (`RunFactO.lagFootPrint`) consumes `consoleOwn s` and returns
    `consoleOwn (s ++ o)`. VSA instance `Inst.wp_putcW` over
    `stepObs_tohost_putchar`, at `_write`'s store `0x8000005c` (`putcSite`).
  - `MachWP.haltConsole` with `HaltFact` (halt/console agreement), for either
    WP, from the `halt` field: at an exit step, `Φ (e, s)` with `s` the
    console cell. VSA instance `Inst.wp_exitW` over `stepOnce_tohost_G`, at
    `_exit`'s store `0x80000190` (`exitSite`). `Inst.vsa_adequacy_exit`
    turns the total WP into `Halts c out e ∧ φ (e, out)`; `vsa_adequacyP`
    does the same for the partial WP.
  - Adequacy allocates the cell at the initial output: `AdequacyHyp` and
    `AdequacyHypP` take the initial output `o` and hand the client
    `consoleOwn o`.
  - Change from the draft: the console rules are derived theorems, not
    `MachWP` fields. `putc` is `lagRun` at a printing footprint, and the halt
    rule is the `halt` field read against `mstateInterp`, which carries the
    console authority.
  - Change from the draft: the console does not own `tohost` bytes. In the
    Sail model a `tohost` store is MMIO: memory is unchanged and the HTIF
    registers decide the effect (`Vsa/Sim/Htif.lean`). What every console
    store needs is an idle mailbox (`htif_payload_writes = 0`); it is a global
    invariant, `VsaOk.htifIdle`, which segments frame and the putchar store
    re-establishes. The binary has no narrow `tohost` store.
  - Change from the draft: `γo` lives in `MachGS`, not `InterpGS`, because
    its authority is in the machine's state interpretation.
- **F3, calling conventions and stack (built: `CallAbort.lean`, `Stack.lean`,
  `Loop.lean`, `Interp/Need.lean`).**
  - `fnSpecAbort Wp entry P Q A` with `wp_callAbort` and the Löb twin
    `wp_callAbort_later`, both mode-generic. `fnSpecAbort_of_fnSpecW` lets a
    partial-mode proof call a helper proved only with `fnSpecW` (H1-H4);
    `fnSpecAbort_mono` is the consequence rule, and `fnSpecAbort_rebase`
    carries the abort-resource difference as an extra precondition.
  - `stackScratch s n` split and join (`blockOwn` arithmetic):
    `blockOwn_split`/`blockOwn_join` state the successor address and the
    lengths as EQUATIONS, so no call site rewrites under `blockOwn`;
    `stackScratch_narrow`/`_widen` and the carve/join pair
    `stackScratch_carve`/`stackScratch_join`, whose side condition
    `nc + f ≤ n` is `Vsa.Alloc.StackOK.child`'s.
  - The ItemZero need `evalNeed e d = e.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame`,
    verbatim from `EvalEntry.stackBudget` (`Vsa/Sim/InterpEntry.lean:630`).
  - xv6iris spells a budget as the sum, never a round number (`durable-notes.md`
    "A stack-budget premise is arithmetic").
  - Change from the draft: `evalNeed`/`execNeed` are both `stackBudget need d`,
    and the whole kit rests on TWO arithmetic lemmas — `stackBudget_child`
    (the Iris route's `StackOK.child`: a child's budget plus the parent's
    spilled frame fits the parent's, at the same depth) and `stackBudget_call`
    (a closure body at depth `d + 1`, inside one `perCallBudget`). Each arm of
    the two recursors is one line over them (`evalNeed_binary_left`,
    `execNeed_block`, `execNeed_callBody`, ...). The boundary bridge to S1 is
    `execNeed_of_stackFits` (arithmetic) and `stackScratch_boundary` (the Iris
    carve) over `ProgramStackFits`.
  - Change from the draft: the abort resource is `abortAt Core s need :=
    Core ∗ stackScratch s need`, generic in the site-independent `Core`
    (§4.2's `abortRes` is this at `abortCore`, the landing registers and SOME
    world). The skeleton wrote the `stackScratch` INSIDE the existential; it
    binds neither `s` nor `need`, so the two are equivalent, and hoisting it
    is what lets `abort_rebase` move the stack part on its own.
  - Change from the draft: the call step itself is ONE rule, not a per-site
    carve. `wp_callArmW` (ordinary) and `wp_callArmAbort` (partial) lend the
    callee a narrower part of the caller's owned region, keep the slack, and
    on the partial side re-base BOTH continuations: the return branch gets the
    caller's region and frame back, and the abort branch joins the very same
    frame and slack into the caller's `abortAt Core s n`. That the two
    branches use the same bytes is what the `∧` of `fnSpecAbort` buys, and it
    is the step every one of E1-E6's call sites takes.
  - STATEMENT CHANGE (F3): `abort_rebase` needs two more side conditions,
    `np ≤ sp_.toNat` and `nc ≤ sc.toNat`. `Nat` subtraction truncates, so
    without them `stackScratch s n` is `blockOwn 0 n` and the three intervals
    `[s_p - n_p, s_c - n_c)`, `[s_c - n_c, s_c)`, `[s_c, s_p)` do not join.
  - **The bounded-loop rule** (`Loop.lean`, §4.3): `MachWP.loop I K body fin n`
    by fuel induction, for either WP (xv6iris `ProofMemset.v:1-9` "bounded
    loop, not iLöb"; `ProofMemmove.v:350` `mm_loop`, induction on `rem`).
    Change from the draft: the body's two continuations — the next iteration's
    `I k` and the loop's inherited exit `K` — are an ADDITIVE pair, the same
    fix as §10.1. With a separating pair the body consumes `K` and the second
    iteration has none, which is exactly the bug §10.1 records for `while`.
    `MachWP.loopI` is the variant with no separate exit resource, and
    `MachWP.loopSeg` the one whose body is ONE reflected `RunFact` segment
    (an invariant opener/closer around the segment footprint, with a frame
    `F k` across it) — the shape `strlen`, `memcpy`, `strcmp` and the
    `args[32]` fill use (H3).

## 3. Representation predicates (work package R)

The ghost state is a new class `InterpGS GF` with two names, plus the
console from F2:

- `γf : ghost_map Nat Nat`: spec frame address to machine `Env*`.
- `γc : ghost_map Nat Nat`: spec closure address to machine `Closure*`.
- `γo`: the console, `MachGS.conName` (F2), used through `consoleOwn`.

`φf` and `φc` stop being arguments threaded through every lemma (the
`φf φc : Addr → Nat` pairs in `StoreRepr`). They become ghost maps whose
fragments are PERSISTENT: `frameAt fa e := fa ↪[γf]□ e`. A frame's `Env*`
never moves, since only its arrays are reallocated. A closure never moves or
changes.

| predicate | owns | kind | VSA counterpart |
|---|---|---|---|
| `strAt p s` | the bytes of `s` and its NUL at `p`, `↦ₘ□` | persistent | `CString` |
| `astE a e`, `astS a s`, `astSs a n ss` | every AST byte, `↦ₘ□` | persistent | `ExprRepr`/`StmtRepr`/`StmtArrayRepr` |
| `valOf v w0 w1 w2` | the meaning of three words: tag, payload, native address | persistent | `ValueRepr` |
| `valAt a v` | the 24 bytes at `a` (exclusive) with `valOf` | exclusive | `ValueWordRepr` |
| `closAt ca p` / `closOwn ca cd` | the closure's 16 bytes `↦ₘ□`, `fn_expr` AST, `env` link | persistent | `ClosureRepr` |
| `frameOwn fa f` | the `Env` struct, the names/vals arrays with spare capacity (whole heap blocks), each name `strAt`, each slot `valAt` | exclusive | `FrameRepr` |
| `storeRepr s B` | `γf`/`γc` auths over the allocated prefixes, every `frameOwn`, every `closOwn`, and `⌜StoreBodiesBound s perCallBudget⌝`. `B` lists the heap blocks it owns | exclusive | `StoreRepr` + `HeapOwned` + `StoreOwned` |
| `consoleOwn s` | the console cell | exclusive | `OutRepr` |
| `interpCtx d` | `Interp`: `call_depth = d` (exclusive), `globals` (persistent), `on_error` (persistent after `setjmp`), `err_msg` (exclusive) | mixed | `CallEntryI` fields |
| `heapRes ρ H` | `isHeapRoom L Room H k` if `ρ = counted k`; `isHeap L H` if `ρ = uncounted` | exclusive | `AllocLedger` |
| `world ρ st d` | `∃ H B, heapRes ρ H ∗ storeRepr st.store B ∗ consoleOwn st.out ∗ interpCtx d ∗ ⌜B ⊆ H⌝` | exclusive | the whole `EvalEntry` bundle |

Decisions and why:

- **Persistent immutable data** (MachCSL: text as `↦ₓ□`, `claude-notes/design/execution-model.md`).
  - C never writes a string, an AST node or a closure after building it, and
    never frees one. Persistence retires `ReprSurvival`, `store_survives`,
    `shared_agree`, `Reserved`/`BindingShared` and every "survives the child"
    obligation at once.
  - The persistent bytes sit in live heap blocks, which `heapFoot` excludes,
    so the allocator never needs them. xv6iris's warning ("a persistent
    points-to at a WRITABLE image byte is an inconsistent premise",
    `durable-notes.md`) does not bite, because nothing ever writes them.
- **One monolithic `storeRepr`.**
  - BigStep's frames are shared by closures and mutated through parent chains
    (`Store.set`). Every `eval_expr` call can reach any frame, so splitting
    frames across callers buys nothing.
  - `env_get`/`env_set`/`env_define` open ONE frame out of `storeRepr` with a
    single opener/closer (xv6iris `spec-modules.md`: "Simultaneous borrows of a
    sealed bundle need ONE opener").
- **Live blocks are whole chunk payloads** (the user's ruling). Strings carved
    out of a concat or stringify buffer sit inside their block. `B ⊆ H` makes
    `free`/`realloc` of a frame array find its block in `H`.
- **Heap regimes are MachCSL's `kalloc_env (Some n)` / `kalloc_env None`**
  (`KvmSpec.v:123`, paper §6.5). The counted regime (total mode) cannot fail and
  its credits come from the boundary's `capacity` (`DlHeap.InitialAllocatorAt`).
  The uncounted regime (partial mode) lets `malloc` return NULL, and `xmalloc`'s
  arm then takes the out-of-memory exit.

## 4. Function specs (§4.1 total, §4.2 partial)

All three recursive entries are MachCSL `Spec<F>`-shaped (`spec-modules.md`):
the statement lives in ONE `…_body` definition, and callers take it as a
hypothesis, never as a proof import.

Shared entry resources for `eval_expr` (entry `0x80003164`; ABI from
`EvalEntry`: `a0 = sret`, `a1 = env`, `a2 = e`; `in` is not an argument, gcc
dropped it):

```
evalPre ρ st d env e sret aE s :=
  a0 ↦ᵣ sret ∗ a1 ↦ᵣ aE ∗ a2 ↦ᵣ aX ∗ □ astE aX e ∗ □ frameAt env aE ∗
  sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗ clobbered clobE ∗
  slot24 sret ∗ ⌜e.bodiesBound perCallBudget ∧ SpOK s⌝ ∗ world ρ st d ∗ □ codeImage
evalPost ρ st' d v sret s :=
  sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗ clobbered clobE ∗
  valAt sret v ∗ world ρ st' d
```

`exec_stmt` (entry `0x80003fe0`; `a0 = in`, `a1 = s`, `a2 = env`, `a3 = ret`)
has the same shape. It carries `execNeed` and an exclusive `slot24 ret` that
holds `valAt ret v` exactly when the status is `.ret v` (`statusRet`). The
status comes back in `a0` as `StatusCode`.

### 4.1 Total (`term_sim`)

```lean
def evalSpecT_body (st d env e st' v n) (D : EvalECost st d env e st' v n) :=
  ∀ k sret aE s saved, fnSpecW twpW evalEntry
    (fun r => ⌜r.toNat % 4 = 0⌝ ∗ evalPre (.counted (k + n)) st d env e sret aE s saved)
    (fun _ => evalPost (.counted k) st' d v sret s saved)
```

- **Derivation-indexed.** The continuation receives exactly `D`'s outcome, and
  the credits drop by `D`'s cost.
- **No determinism lemma.** The right child of `binary` starts at `D`'s
  intermediate state, because the left child's continuation was indexed by `D`.
- **No error arms.** Each machine test resolves against `D`'s pure premise: the
  operand kinds, `binOpSem … = some v`, `get? = some`, arity, depth, and
  `truthy` for `assert`.
- `execSpecT_body` is the same shape over `ExecSCost`. The sequence loops,
  `EvalArgs` and `ForLoop` are block lemmas, not specs (§4.3).
- Proof: the mutual recursor over the nine cost companions, with motives
  `m_R … D := evalSpecT_body … D`. This is `TermSimAssembly`'s motive
  mechanism, and the 49 recursor rows become 49 Iris case lemmas.

### 4.2 Partial (`stuck_sim`)

```lean
def evalSpecP_body (st d env e) :=
  ∀ sret aE s saved, fnSpecAbort wpW evalEntry
    (fun r => ⌜r.toNat % 4 = 0⌝ ∗ evalPre .uncounted st d env e sret aE s saved)
    (fun _ => ∃ st' v, ⌜EvalE st d env e st' v⌝ ∗ evalPost .uncounted st' d v sret s saved)
    (abortRes s (evalNeed e d))
```

- **Outcome-quantified.** The return branch builds the derivation from the
  children's, rule by rule, as the machine runs.
- **Error arms go to the abort branch.** A runtime error calls `runtime_error`
  (its spec is H5: `snprintf` into `err_msg`, then `longjmp`), which lands at
  `interp_run`'s `setjmp` return with `a0 = 1`. An out-of-memory NULL goes
  `fprintf`, then `exit(1)`.
- **What the abort branch receives.** `abortRes s n := ∃ kind, landingRegs kind
  ∗ ∃ ρ st d, world ρ st d ∗ stackScratch s n`. It hands back the WHOLE owned
  stack below the site's `sp`.
- **Re-basing at every call.** Callers do not own the abort continuation for
  the child's region. At each call the caller builds the child's
  `abortRes s_c n_c -∗ W Φ` from its own `abortRes s_p n_p -∗ W Φ`, joining its
  frame bytes `[s_c, s_p)` back in (lemma `abort_rebase`, F3). Because of the
  `∧`, those same frame bytes also serve the return branch.
- **Proof: Löb over `evalSpecP_body ∧ execSpecP_body`.** Each recursive `jal`
  follows at least one step, which pays the `▷`. Divergence costs nothing: the
  partial WP allows it.

### 4.3 Sequences and loops are block lemmas

gcc inlined `call_value` and `eval_binary` into `eval_expr`, and there is no
`exec_seq` function. The statement sequence exists three times: the block arm,
the closure body inside the call arm, and `interp_run`'s loop. Following
xv6iris ("A block gcc emitted twice is one lemma, parameterized by its PCs as
literals", `durable-notes.md` "Seams and block lemmas"), it is ONE lemma
`seqLoop (site : SeqSite)`. `SeqSite` records the loop-head PC, where the index
and count live, the `jal exec_stmt` site and the exits. Instantiations:
`blockSite`, `closureSite`, `interpSite`. The lemma is mode-generic.

- Total mode: induction on the `ExecSeqCost` derivation.
- Partial mode: fuel induction on the remaining count, which is bounded by
  `count`. Each statement uses the Löb hypothesis for `exec_stmt`.

The fuel-induction rule itself is F3's `MachWP.loop` (`VsaIris/Loop.lean`),
with `MachWP.loopSeg` for a body that is one reflected `RunFact` segment. Its
body takes the next iteration's invariant and the loop's inherited exit as an
ADDITIVE pair, which is what keeps an abort continuation alive across
iterations (§10.1).

`EvalArgs` (the `args[32]` fill), `while`, and `for` are loop lemmas of the same
kind.

- Total mode: induction on the derivation.
- Partial mode: `while` and `for` loop forever when the program does, so they
  need Löb, not fuel. The loop lemma takes the Löb hypothesis for its own head
  as a premise, `▷ loopSpec`, and the recursive entry discharges it inside the
  one global Löb.

### 4.4 `interp_run` (entry `0x800043ec`)

`interpRunSpecT p D` and `interpRunSpecP p` are ordinary `fnSpecW` specs from
the boundary state. The loop is `seqLoop interpSite`. The partial abort branch
is closed INSIDE `interp_run`'s own proof:

- `setjmp` returns 1, `interp_run` returns 1, `run_source` calls `fprintf` and
  returns 70, then `main`, then `exit`.
- A top-level `ret`/`brk`/`cont` status returns 1, giving exit 70.
- Out of memory gives `exit(1)`.

So the external partial spec's postcondition is `∃ e, ⌜e ≠ 0⌝`-style unless
the program completed normally, and then its continuation receives `ExecSeq
initSt 0 0 p st' .normal`, which is `BigStep p st'.out`.

## 5. Assembly (work package A)

### 5.1 The boundary (A0, landed)

`VsaIris/Interp/World.lean`:

```lean
theorem world_of_boundary (b : Boot c p) (ρ : Regime) (hρ : RegimeOK b.top ρ) :
    ([∗map] k ↦ v ∈ b.bytes b.G, k ↦ₘ v) ∗ consoleOwn (output c.σ) ⊢
      |==> ∃ γf γc, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes b ρ)
```

- `Boot c p` names every witness of `Loaded interpRunLayout p c`
  (`boot_of_loaded`). `b.bytes b.G` is the byte map adequacy hands the client
  (`Boot.bytes_agree`: it agrees with the configuration). Its address list is
  sealed behind `Classical.choose` so the kernel never unfolds the
  `2 ^ 32`-element range it is cut from.
- `bootRes b ρ`: `worldPre` (the allocator `heapRes vsaLayoutP vsaRoomB ρ`,
  the store `initSt.store` in one frame, the console, `Stdio.stdioOwn`, and
  `interpCtxPre`: `world` with the `jmp_buf` still exclusive), frame 0's
  address, `astSs`, `roOn CodeByte` (text and rodata; `textOwn_of_roOn`
  projects any `textOwn`), `roOn shared`, the stack below `interp_run`'s entry
  (F3's `stackScratch_boundary` carves from it), `main`'s frame outside
  `struct Interp` (480 bytes), and the writable statics outside the allocator
  and newlib.
- The heap is `vsaLayoutP`/`vsaRoomB`, the layout and room of
  `IrisHoles.alloc` (H4), not S1's `vsaLayout`/`costRoom`.
  `RegimeOK top (.counted k)` is `2k + extendSlack ≤ heapEnd - top`;
  `Boot.regime_of_bigStep` gives it at the derivation's cost from
  `InitialAllocatorAt.capacity`.
- `Boot.gap : BootGap b b.G` supplies the boundary heap facts (the three
  frame chunks, `top_room`, Q5, Q5b, Q6) from `InterpRunReadyFacts.boot`
  (see "STATEMENT CHANGE (lane BG)").
- `WorldStdio.stdioOK_of_mem`: `StdioOK (memImg m)` from `ConsoleStream m`,
  `ExitRuntimeData m` and the `stderr` word.

Vacuity (`VsaIris/Interp/WorldVacuity.lean`): `ctlBoot`, `ctl_bootGap`, and
`ctl_world_counted`/`ctl_world_uncounted` instantiate `world_of_boundary` at
the control program in both regimes.

### 5.1b The heap credits: Room ↔ Cost (S1, landed)

`VsaIris/Vsa/CostRoom.lean`. The counted regime's index is COST BYTES, so
`heapRes (.counted k) := isHeapRoom vsaLayout costRoom H k`. It is NOT
`vsaRoom`: VSA's `AllocationReserve` is unsatisfiable after `malloc(24)`
(`split24_vsa_reserve_false`), and it counts requests of a uniform `maxReq`,
not bytes.

- **`costRoom img H k`** holds when `av->top + 2k + extendSlack ≤ heapEnd`.
  - It reads only the top word, an allocator global (`roomLocal_cost`), and is
    monotone (`isHeapRoom_cost_mono`).
  - It has no live-extent clause: freshness is `Shape`'s job.
- **Charges cover chunks (2n + slack).** Each C allocation site's request `n`
  sits under its modeled charge `c`, with `16 ≤ c` (`Covers`: `covers_envNew`,
  `covers_closure`, `covers_nameCopy`, `covers_stringify`,
  `covers_concatBuffer`, and `arrayRealloc_split` for the two array
  `realloc`s). Hence `physSize n ≤ 2c` (`physSize_le_two_charge`).
- **Per allocation.** `CostTop.spend`/`.split`: advancing top by at most `2c`
  turns `c + k` credit bytes into `k`. A bin hit, or a free merging into top,
  only helps.
- **Iris malloc at charge `c`.** `mallocCostSpec` is `mallocRoomSpec` at
  `costRoomAt c k` (unit credit = `c` bytes). `isHeapRoom_costAt_one`/`_zero`
  rewrite it to `isHeapRoom costRoom H (c + k) → isHeapRoom costRoom _ k`.
  Its first-order obligation is `MallocCostRun` (H4, the `alloc.mallocRoomRun`
  row of HOLES.md).
- **Boundary (A0).** `costRoom_of_bigStep`: `BigStep` gives a costed
  derivation of cost `n` (`BigStep.cost`), and `InitialAllocatorAt.capacity`
  gives `costRoom` at `n` (`costReserve_of_initial`). Non-vacuous:
  `Control.costReserve` has 2^20 credit bytes at the control heap.
- **Cost existence/soundness** for the recursor: `Vsa/While/CostExists.lean`
  (`EvalECost.exists` … `ExecSeqCost.exists`, and `EvalECost.sound` …, which
  give the `EvalE`-level invariants to a case lemma holding only `D`).

### 5.2 `term_sim`

```lean
theorem term_sim_iris (h : IrisHoles) :
    ∀ p c out, Loaded interpRunLayout' p c → BigStep p out → Halts c out 0
```

1. `BigStep` gives `ExecSeq initSt 0 0 p st' .normal`.
2. `ExecSeqCost.exists` gives the cost `n`. It is proved in S1 if absent.
3. `interpRunSpecT` with `Φ := fun v => ⌜v = (0, st'.out)⌝`.
4. After `interp_run` returns 0: `main`'s epilogue, then `exit(0)`, then the
   halt rule. The console gives `out = st'.out`.
5. `vsa_adequacy` (exists).

### 5.3 `stuck_sim`

```lean
theorem stuck_sim_iris (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout' p c → (¬ ∃ out, BigStep p out) →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0
```

1. Use `interpRunSpecP` with `Φ := fun v => ⌜v.1 ≠ 0⌝`.
2. Normal completion hands a `BigStep` derivation, which contradicts the
   hypothesis.
3. Every abort and every non-normal top status ends in `exit(70)` or `exit(1)`.
4. Partial adequacy (F1) finishes it.
5. Where a total-only proof is reused (the `snprintf` `%lld` path inside
   `value_print`, if it stays total), `twp_wp` bridges.

### 5.4 The final theorem

```lean
theorem interpSim_iris (h : IrisHoles) : InterpSim interpRunLayout' :=
  ⟨term_sim_iris h, stuck_sim_iris h⟩

theorem endToEnd_refinement_iris (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout' p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement (interpSim_iris h)
```

`interpRunLayout'` is `interpRunLayout`: Q1's stack-admissibility field landed
in `InterpRunReadyFacts` (see "STATEMENT CHANGE" at the top).

## 6. The exponentiating layer on Iris (work package G)

The producers do not change. `#derive_case`, `segEval_sound`, `gen_fn.py`,
`gen_sites.py`, `gen_fixed_image.py` and the decode tables keep emitting exec
facts. `seg_runFact` and `segFrom_of_runFact` turn them into `RunFact`s.
`wp_seg` consumes a segment in one application, with its named register pins,
written bytes and read-only bytes.

Two changes:

1. **The row generators emit Iris case lemmas instead of Triples.**
   `gen_m4_term_row.py`, `gen_exec_row.py`, `gen_bin_dispatch_row.py`,
   `gen_allocator_cases.py`, `gen_m5_error_routing.py` and the `*_sites.tsv`
   tables are retargeted. ONE row table (`arms.tsv`) gives each machine arm:
   - its entry PC and dispatch path;
   - its segments;
   - its child calls (which AST field, which slot, which spec);
   - its helper calls;
   - its semantic rule (total), or its rule plus error arms (partial).

   From it the generator writes `Case/<Arm>T.lean` and `Case/<Arm>P.lean`.
   Hand edits go in the table, never in the output (xv6iris
   `code-organization.md`: "no hand-written duplicate beside a generated
   layer").
2. **One file set per function, xv6iris-style** (`spec-modules.md`):
   `Interp/Spec<F>.lean` (the statement only, no code import),
   `Interp/Proof<F>.lean` (takes callee specs as hypotheses) and one assembly
   file. A proof never imports another proof, so the build parallelises.

### Worked case: `binary .add` on two ints, total mode

C path: `eval_expr` then `EX_BINARY` then (inlined `eval_binary`) left child,
right child, operator jump table (`0x80019f58`), the `T_PLUS` int/int arm,
`value_int(a+b)`, epilogue.

```lean
theorem case_binary_add_intT (hl : evalSpecT_body st d env l st₁ (.int a) nₗ Dₗ)
    (hr : evalSpecT_body st₁ d env r st₂ (.int b) nᵣ Dᵣ) :
    evalSpecT_body st d env (.binary .add l r) st₂ (.int (wrap64 (a + b))) (nₗ + nᵣ)
      (.binary … Dₗ Dᵣ rfl) := by
  intro k sret aE s saved; iintro !> %r %Φ Hpc Hra Hpre Hk
  -- (1) prologue + kind dispatch to the binary arm: one reflected segment
  iapply (Wp := twpW) wp_seg evalPrologueBinSeg …;  iframe …;  iintro Hseg
  -- (2) left child into the frame's L slot; everything else framed by the wand
  iapply wp_callW (hl (k + nᵣ) slotL aE (s - 1088) savedL);  iframe …
  iintro Hpc Hra ⟨Hsp, Hstk, Hsv, Hclob, HvL, Hworld⟩
  -- (3) stage the right child: one segment; (4) right child
  iapply wp_seg stageRightSeg …;  iapply wp_callW (hr k slotR aE (s - 1088) savedR);  …
  -- (5) operator dispatch + int/int add + store into sret: one segment whose
  --     branch conditions are pinned by `valOf (.int a)` / `valOf (.int b)`
  iapply wp_seg addIntTailSeg (tagL := 2) (tagR := 2) …
  -- (6) epilogue (one segment) and the continuation
  iapply wp_seg evalEpilogueSeg …;  iapply Hk …
```

- It uses five segment applications and two child calls. The frame rule
  handles the frame bytes, the other slot, the caller's `ra`/`s`-regs and the
  whole `world`. There is no transport, survival or widening lemma.
- The partial twin differs in two places. (2) and (4) use `wp_callAbort` with a
  re-based abort continuation. At (5) the kind test is read off the ACTUAL
  values: int/int continues, str goes to the concat arm (a different row), and
  anything else calls `runtime_error` through the H5 spec.

## 7. What is reused, what is retired

| kept (fact producers) | retired (framing and plumbing) |
|---|---|
| Decode tables, `#derive_case`, `segEval_sound`, `bblocks_sound*`, `gen_fn.py` + `FnSummary`, `StepObs`/`JalStep` (via `jalExec_of_site`) | `WidenMeta`/`LeafWiden`/`ExecRecWiden`/`EvalRecWiden`/`blockD_v_phic` |
| `Vsa/While/*` (semantics, `Cost`, `StackNeed`, `Derive`, `Validation`) | `ReprSurvival`, `store_survives`, `Reserved`/`BindingShared`, `shared_agree*` |
| `MemRepr` (the persistent lift `astE_of_exprRepr` reads it) and `RuntimeRepr` (as the spec of `valOf`/`frameOwn`) | `AllocLedger`, `OwnedOff`/`EntryOff`, `MallocContract`, `privFoot`, the per-entry ledger fields (R14) |
| The helper *segments*: `StrlenSegments`, the memcpy word loop, the `value_equal` jump table, env_* scans (block lemmas re-wrapped as `Wp`-generic) | `EvalEntry`/`ExecEntry`/`CallEntryI` field towers, `EvalReturnIH`/`ReturnRepr` index machinery, the IH clause tower (`IHClause_*`) |
| `LayoutInstance` geometry, `ImageDischarge`, `InitialOwned` (boundary inputs to A0) | `TermResidualsBase` (63 fields), `DivWork`, `ErrWork`, `RemainingWork`: replaced by `IrisHoles` |
| `Refinement.lean` (unchanged) | `SeparationLogic*.lean` (VSA's own, subsumed) |

The discipline gate (`check_discipline.py`) gets rules for the new layer:
- no `sorry` in `VsaIris/Interp`;
- `Spec*` files import no `Proof*` or `Case*` file;
- generated `Case/*` files are not hand-edited (hash check, as the stage-a3
  drift gate does now).

## 8. Case inventory and estimates

Estimates are Lean lines. The basis is the env_new pilot (`EnvNewPilot.lean`,
443 lines against VSA's 2,747 for the same cone) and the generated
`Case/*` shape above.

| family | total rules (T) | partial arms incl. errors (P) | lines (T+P) |
|---|---|---|---|
| leaves: int, str, bool, null, fn | 5 | 5 | 0.8k |
| var (hit / miss), assign (ok / unbound) | 2 | 4 | 0.9k |
| binary: add int, add concat ×2 kinds, sub, mul, div, mod, eq, ne, 4 cmp × {int, str}, type/zero errors | 16 | 22 | 4.5k |
| logical: or ×2, and ×2; unary: neg, not, neg type error | 6 | 7 | 1.4k |
| call: closure (ok), natives print / println / assert-ok; arity, depth, not-callable, too-many-args, assert-fail, brk/cont-escape errors | 4 | 10 | 3.5k |
| exec: expr, varInit, varNull, block, if ×3, while ×4, for (+ForLoop 4, ForCond 2, ExecInit 2, ExecStep 2), ret ×2, brk, cont | 25 | 16 | 5.0k |
| loop lemmas: `seqLoop` (3 sites), `EvalArgs`, while, for | shared | shared | 1.5k |
| helpers (H1–H5), mode-generic | | | 7–9k |
| foundations F1–F3, R, A0, A | | | 5–6k |
| **total** | | | **≈ 30k** |

The generator (G) carries about 60% of the case lines. Hand work concentrates
in F, R, the helpers, and the three loop lemmas.

## 9. Fan-out plan

```
F1 partial WP ──┐
F2 console ─────┼─> F3 fnSpecW/abort/stack ─> R repr ─┬─> H1..H5 helpers ─┐
S1 cost/admiss. ┘                                      └─> G generator ────┼─> E cases (T,P) ─> A assembly
                                                          A0 boundary ─────┘
```

| package | content | depends on | parallel with |
|---|---|---|---|
| **F1** | `mWP`, `MachWP`, `twpW`/`wpW`, `run_later`, partial adequacy at the VSA instance | none | F2, S1 |
| **F2** | console ghost, `out` projection, `putc` rule, halt/console agreement | none | F1, S1 |
| **S1** | `ExecSeqCost.exists`; stack-admissibility predicate (Q1); `Room` ↔ `Cost` bridge (2n + slack against `vsaRoom` credits) | none | F1, F2 |
| **F3** (landed) | `fnSpecAbort`, `wp_callAbort`, `wp_callAbort_later`, `abort_rebase`, `blockOwn`/`stackScratch` carve-join, `evalNeed`/`execNeed` arithmetic and the `ProgramStackFits` bridge, `MachWP.loop`/`loopSeg` | F1 | R (after F1) |
| **R** | `InterpGS`, all §3 predicates, openers (one frame out of `storeRepr`), `astE_of_exprRepr`, the two-owner sanity lemmas | F1, F2 | F3 |
| **A0** | `world_of_boundary`, vacuity check at the control program | R, S1 | H* |
| **H1** | `env_new`, `env_define` (append / grow / hit), `env_get`, `env_set` over `storeRepr` openers | R | H2–H5 |
| **H2** | `value_truthy`, `value_equal`, `value_print`, `stringify`, natives `print`/`println`/`assert` | R, H3 | H1, H4, H5 |
| **H3** | `strlen` (pilot in flight), `memcpy`, `strcmp`, `snprintf` `%lld` | F1 | all |
| **H4** | `_malloc_r`/`_free_r`/`_realloc_r` runs (discharges `IrisHoles.alloc`), regime lemmas, the `xmalloc` site lemma | F1 (iris-heap work continues here) | all |
| **H5** | `runtime_error` + `longjmp`/`setjmp` (landing), `exit`, the abort landing to exit(70) path, the out-of-memory arm | F3, R | H1–H4 |
| **G** | `arms.tsv`, retargeted generators, `Case/*T`/`*P` emitters, drift gate | F3, R (interfaces only) | H* |
| **E1–E6** | the six case families of §8, each T and P | G, H* | each other |
| **A** | recursor assembly (T), Löb assembly (P), `interp_run`, `term_sim_iris`, `stuck_sim_iris`, final theorem, axiom audit | E*, A0 | none |

Parallel width: F1, F2 and S1 together; then R and F3; then H1–H5 and G (six
lanes); then E1–E6 (six lanes).

**Named holes** at the end, in `structure IrisHoles`, each checked satisfiable
(§10):
- `alloc`: `MallocRoomRun`, `MallocLocalRun`, `FreeLocalRun`, `ReallocLocalRun`,
  unless H4 discharges them;
- `newlib`: safety specs of `snprintf` (`%s`/`%d` error messages) and `fprintf`
  on the error/out-of-memory paths. These are only needed for partial mode's
  "never stuck". The `%lld` success path is proved (VSA M3).

## 10. Adversarial review (paper §9.3): what broke, and the fix

1. **Linear abort continuation across a loop.** The first draft put `abortK` in
   the precondition as a plain wand, and the return branch then lost it: the
   while loop's second iteration had no abort. Fix: an additive pair `(return ∧
   abort)`. Both branches are proved from one context, so the loop's return
   branch still holds the inherited `abortK`.
2. **Abort loses the callers' stack frames.** An error at depth k handed the
   top only its own scratch, while the frames between it and `interp_run` sat
   in the callers' return closures, and `fprintf` after the landing needs that
   stack. Fix: `abortRes s n` carries the stack below `s`, and every call
   re-bases the child's abort continuation, joining the caller's frame
   (`abort_rebase`).
3. **Total mode and determinism.** An outcome-quantified total spec would need
   `EvalE` determinism to start the right child at the left child's actual
   state. Fix: derivation-indexed total specs over the recursor. The motives
   supply the children at exactly `D`'s states, and no determinism lemma is
   needed.
4. **The stack budget at the boundary does not bound the program (possible
   falsity of `InterpSim` as stated).**
   - `InterpRunPhysicalFacts.stack_ok` is the constant `176 + 1088`
     (`LayoutInstance.lean:214`), and nothing at the boundary bounds
     `p.stackNeed` or `bodiesBound`.
   - The AST comes from `Loaded`, not from the parser, so any depth is
     admissible.
   - An 8,000-deep `-(-(…))` overflows the 8 MiB stack into the heap directly
     below it (`heapEnd = stack lo = 0x87800000`). After that, nothing
     constrains the machine, and both `term_sim` and `stuck_sim` are
     unprovable.
   - Fix (approved as Q1, landed by S1): `InterpRunReadyFacts.stack_admissible`
     (`ProgramStackFits`, see "STATEMENT CHANGE" at the top), beside
     `capacity`.
5. **The out-of-memory path in partial mode.** The capacity bound only covers
   terminating derivations, so a divergent program can exhaust the heap. That
   is correct behaviour, `exit(1) ≠ 0`, but only if the uncounted regime's
   NULL arm is in the spec. Fix: `heapRes .uncounted` is `isHeap` with
   `mallocSpec`, which has the NULL arm, and the site lemma routes NULL to the
   out-of-memory abort.
6. **Satisfiability of the persistent string bytes.** `stringify` and concat
   write their buffer AFTER `malloc`, so the bytes are exclusive while they
   are written and only then discarded to `↦ₘ□`. The site lemmas must state
   the discard AFTER the copy, never at allocation. A premise `strAt p s`
   before the write is refutable. This is recorded as a rule for H2.
7. **Two owners of the frame arrays.** `storeRepr` owns the array blocks and
   `isHeap` must not also own them: `B ⊆ H` and `heapFoot` excludes `H`.
   Scratch check for R: `storeRepr s B ∗ heapRes ρ H ∗ ⌜B ⊆ H⌝ ⊬ False`,
   proved by exhibiting the boundary world (xv6iris's "two owners of one
   address space" diagnostic, `durable-notes.md`).
8. **A 32-bit `argc`/`paramc` read as a 64-bit word** (xv6iris "A 32-bit
   argument's register premise is the ABI's word"): the arity and too-many-args
   tests are `lw` plus signed compare. The spec pins `sign_extend 64
   (argc : BitVec 32)`. `ExprRepr.call`'s `argc < 2^31` already matches this.
9. **Console versus `tohost` writes inside helpers.** A helper segment that
   does not own `tohost` provably cannot print (F2), so a missing putchar in a
   print path shows up as an unprovable goal, not as a silent output mismatch.

### STATEMENT CHANGES (R, landed)

The §3 predicates are built in
`VsaIris/Interp/{Repr,Store,Bridge,Boundary,Vacuity}.lean`. Four statements
differ from the skeleton, each because the skeleton's shape does not compose
with what the proofs consume:

- **The AST is `*ReprWithin` over a read-only VIEW.** `astE a e` is
  `∃ P m, ⌜ExprReprWithin m P a e⌝ ∗ roOn P m` (`roOn P m := □ ∀ k b, ⌜P k⌝ →
  ⌜m[k]? = some b⌝ → k ↦ₘ□ b`), not an enumerated byte list. The hereditary
  read set `P` of `ExprReprWithin` IS the set `roOn` needs, so child
  projections (`MemReprReadFields`/`ReadChildren`/`ReadArrays`) apply
  unchanged, and `InterpRunReadyFacts.ast_owned` hands A0 exactly this `P`
  (`astSs_of_programRepr`).
- **Mutable data is an owned byte IMAGE plus pure layout facts**, not a chain
  of per-word `word64`s: `ownImg S img := ownSet S (fun a => a ↦ₘ img a)`
  with `imgLE`/`imgW` reading the words. This is the form `wp_seg`/`LocalRun`
  consume (a segment's write log is a function on addresses), and it keeps
  one `decide` per fact instead of one per byte.
- **`frameOwn` carries a named `FrameGeom` + `FrameLayout`** (CLAUDE.md law 6)
  instead of the skeleton's existential-and-conjunction tower; `env_define`'s
  `realloc` needs the block extents by name. VSA's `FrameRepr` conjunction is
  consumed through ONE named destructurer, `FrameReads`.
- **`interpCtx` splits.** `interpCore` holds the fields every mode shares;
  `interpCtx` adds the read-only `jmp_buf` (after `setjmp`), `interpCtxPre`
  the exclusive one (at `interp_run`'s entry, what A0 has).

§10.7's scratch check is discharged concretely rather than abstractly:
`storeRepr_blocks_off_heap` / `world_blocks_off_heap` prove no store byte is
in `heapFoot`, and `VsaIris/Interp/Vacuity.lean`'s `ctl_predicates_inhabited`
exhibits all the predicates together at the control program's real initial
memory. `heapRes`/`world` inhabitation at that memory needs `isHeap` for the
interpreter control's dlmalloc heap and stays with H4/A0.

### STATEMENT CHANGES (H5)

- **`struct Interp` layout.** `interpJmpLen = 208`, `interpErrOff = 224`
  (were 112 and 128). newlib's riscv `jmp_buf` is 26 words (14 integer + 12
  FP slots; `setjmp` fills the first 14), so `err_msg` starts at `in+224`:
  `runtime_error` passes `addi a0,s0,224` to `snprintf`, and `main` passes
  `addi a2,sp,496` with `in = sp+272`. VSA's `ObjGeom (inp, 384)` undercounts
  the object (480 bytes) but is only a geometry bound.
- **`err_msg` is a parameter of the context.** `interpCoreE`/`interpCtxE`/
  `worldE` take the `err_msg` resource `E`; `interpCore`/`interpCtx`/`world`
  are the instances at `errAny` (any bytes). The landing's `world` has
  `errStr` (a NUL within the 256 bytes), which `runtime_error`'s second
  `snprintf` establishes and `main`'s `fprintf("%s\n", in->err_msg)` needs.
- **`world` owns newlib's runtime data.** `Stdio.stdioOwn`: every
  `.data`/`.bss` byte from `__sglue` to `__bss_end` outside the allocator's
  globals, at an image satisfying VSA's `ConsoleStream` and
  `ExitRuntimeData` (`Stdio.StdioOK`). `value_print` (H2), the error line and
  `exit` all need it; `InterpRunPhysicalFacts.console`/`.exit_runtime` give it
  at the boundary. `Newlib.stdioFoot_off_alloc`: the two owners are disjoint.
- **`IrisHoles.newlib` is exact** (`VsaIris/Vsa/Newlib.lean`):
  `snprintf`/`fprintf` with `%s`/`%d` formats (`FmtArgsOK`), `fwrite` (gcc's
  form of the out-of-memory `fprintf`), and `exit`'s newlib interior
  (`__call_exitprocs`, `__stdio_exit_handler`). A write to `stderr` leaves
  newlib's data in a state `Ierr` outside `ExitRuntimeData` (the `FILE`
  gains `__SWR` and a buffer), so `NewlibHoles := ∃ Ierr, NewlibHolesAt Ierr`.
- **`stderr` output is console output.** `_write` ignores its descriptor and
  stores every byte to `tohost`, so the error line is printed. VSA's
  `FprintfStderrNeutral` (`Vsa/Sim/ExitPath.lean`: the output is unchanged
  across `fprintf`) is false; nothing in the Iris route uses it.
- **Out of memory is `fwrite` + `exit(1)`**, not `fprintf`: every inlined
  `xmalloc` NULL arm is `fwrite(msg, 1, 14, stderr); exit(1)`.
- **`abortCore` depends on the site's region** (`VsaIris/Interp/Abort.lean`).
  `abortRes s n = abortAt (abortCore s n) s n` with `abortCore s n :=
  landingCore ∨ oomCore s n`. `landingCore` is the `longjmp` landing: some
  `worldE (errStr inp)`, the `jmp_buf` read-only at `jb`, and `landingRegs jb`
  (`ra`, `s0`–`s11`, `sp` read off `jb`, `a0 = 1`, PC at the restored `ra`).
  `oomCore s n` is `exit`'s entry with `a0 = 1` after the out-of-memory
  `fwrite`, and its stack pointer `s'` leaves room for `exit` inside `[s - n,
  s)` (`OomSp`). That fact is about the site's region, so the core is not
  site-independent as F3's `abortAt Core` assumed; it is monotone in the region
  (`abortCore_mono`), and `abortRes_widen` turns a callee's `abortRes` into
  `abortAt (abortCore s n) (s - f) nc`, which is what F3's `wp_callArmAbort`
  (at `Core := abortCore s n`) consumes through `fnSpecAbort_mono`. The
  alternative, `exit(1)` run by the site itself, needs `Φ (1, _)`, which only
  the top's continuation can supply.
- **The abort continuation is closed** (`wp_abort`): at `interp_run`'s `jal
  exec_stmt` (`sp = sM - 176`), `abortRes` plus what `interp_run`'s proof keeps
  (`TopLanding`: the `jmp_buf` it wrote, its frame, `main`'s saved pair) ends in
  `exit(70)` (`wp_abortLanding` → `Landing.wp_landing` → `MainErr.wp_mainErrTail`
  → `Exit.wp_exitCall`) or `exit(1)` (`wp_abortOom`), for either WP.

### STATEMENT CHANGES (G, landed)

`eval_expr`'s specs are stated in `VsaIris/Interp/SpecEval.lean` (it
supersedes §D of `Specs.lean` for `eval_expr`). Each change is forced by the
binary or by what the proofs consume:

- **ABI: `a0 = sret`, `a1 = in`, `a2 = e`, `a3 = env`**, not `a1 = env,
  a2 = e`. The C signature is `eval_expr(Interp *in, Expr *e, Env *env)` with
  an `sret` result. Evidence: the prologue keeps `a1` in `s2` and passes it
  unchanged to both children and to `runtime_error` (`0x80003184 mv s2,a1`,
  `0x8000350c mv a1,s2`, `0x80003b2c mv a0,s2`); the binary arm spills `a3`
  for the right child (`0x800034f4 sd a3,0(sp)`, `0x80003500 ld a3,0(sp)`);
  the var arm passes `a3` to `env_get` (`0x80003438 mv a0,a3`).
- **Registers are one valuation.** The skeleton quantified over arbitrary
  `saved`/`clobE` lists; no body meets that (it spills `s0`-`s3` whatever the
  caller passed). The pre owns every register but `PC`/`ra` (which `fnSpecW`
  handles) and `gp`/`tp` as `regFile rv`, with named argument pins
  `EvalRegs`; the post returns some `rv'` with `KeepRegs calleeSaved rv rv'`.
  This is also exactly the shape a symbolic run (`SWP`) consumes.
- **`codeRes`** (the code, the jump tables, `gp`, persistent) is in the pre:
  every segment fetches its instructions from it.
- **`astEG`** = `astE` plus the read set's address facts (`ReadOK`: RAM, off
  the HTIF words), which every load side condition needs. A0 supplies them
  from `ast_readable`; `astEG_astE` forgets them.
- **`StackGeom`/`SlotGeom`** name the stack and result-slot geometry.
- **The line field is not read-owned.** `0x80003524 lw s0,4(s0)` reads the
  node's line number, outside `ExprReprWithin`'s read set; the step is a
  havoc load (`swp_havocD`): the run continues for every loaded value.
- Helpers are stated with `helperSpec` (registers kept but a clobber list);
  `valueIntSpec` is the stub for `value_int` (H2).
- **The partial spec's abort also hands back the result slot**:
  `evalSpecP_body Core …`'s abort resource is `abortAt Core s (evalNeed e d) ∗
  slot24 sret`, not `abortRes s (evalNeed e d)` alone. The caller lends its
  child a result slot inside the caller's own frame; to rebase its abort
  (`abort_rebase`, §10.2) it must rebuild that whole frame, slot included
  (`ms_callEvalP`). The landing core is a parameter `Core` (H5 fixes it).
- **`seqLoop` is three loop motives, not one lemma.** The three sites differ in
  more than PCs: the block arm indexes with `a6` (spilled at `sp+8`) and passes
  its own `ret` slot through; the closure body indexes with the callee-saved
  `s0` inside `eval_expr`'s frame and lends the slot `sp+144`; `interp_run`
  walks a cursor to a bound, calls `value_null` before each statement, reads
  the global frame from `in->globals`, and routes `ret`/`brk`/`cont` to two
  runtime errors. Each site is the recursor motive of `ExecSeqCost` in total
  mode (`blockSeqT_body`, `closureSeqT_body`, `interpSeqT_body`: cases
  `consNormal`/`consAbrupt`/`nil`) and a structural motive in partial mode
  (`*SeqP_body`, `*SeqP_all`), over a named loop-head invariant; the exits are
  continuations indexed by status (`closureExit`, `interpExit`).
- **`interp_run`'s loop assumes `repl = 0`** (`InterpFrame.flag`): `main`
  passes `li a3,0` (`0x800045e0`), and the REPL path (evaluate and print
  expression statements) has no source counterpart. The loop reads the
  statement array and `in->globals` through one merged view (`InterpData`);
  their disjointness and the view's construction from `astSs` and
  `interpCore`'s `wordRO` are A's.
- **Partial cases split on the children's actual values.** A row's partial
  case runs the shared prefix (children through the Löb hypothesis
  `evalSpecsP`), then case-splits on the returned values: the row's kinds
  finish (with the derivation), the others are exported by `#ix_chain` as
  hypotheses of the case, which the rows they belong to discharge
  (`#ix_piece … from <piece> at k`). Machine kind tests are then decided by
  facts (`valOf_tag`), never by case analysis inside a run.

### STATEMENT CHANGES (H2)

- **`helperSpec` hands the callee an aligned return address.** Lane G's
  `SpecEval.helperSpec` had no `⌜r.toNat % 4 = 0⌝` in its precondition, so no
  helper could run its `ret` (the step needs the target word-aligned), and
  G's stub `valueIntSpec` was unprovable. The fact is now in the
  precondition, and `ms_callHelper` takes it at the call site (`by decide` on
  the literal return address); G's `binInt` template passes it.
- **The helpers' code is the interpreter's.** `gen_interp_steps.py`'s code
  (`interpText`, `codeRes`) covers the value helpers, the natives and
  `stringify`, so a helper spec needs no second code resource and lane G's
  `helperSpec` shape is used as is. `sltu`/`sltiu` get `itO_<pc>` step lemmas
  (`SymObs.swp_alu`, over H4's `swp_aluRR`), which `ix_run` tries.
- **`IrisHoles.out`** (`VsaIris/Vsa/NewlibOut.lean`): newlib's stdout calls
  (`fputs`, `fputc`, `fwrite`, `fprintf` on `stdout`) exact about what they
  print, and `stringify`'s `snprintf(buf, 64, "<fn %s>", name)`. VSA assumed
  the same (`CallIOContracts`).
- **`nativeAssertSpec` is a `fnSpecAbort`** (`SpecValue.lean`). Its return
  branch hands back `Call.assertOk`'s premise
  (`∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy`). Its abort branch hands
  back H5's `abortRes s nativeAssertNeed`, the result slot and the arguments.
  `runtime_error` needs the `jmp_buf` read-only at a named image `jb` with its
  `ra` word aligned (`rtErr_spec`'s `hjb`). `world` only gives `∃ jb`, so the
  spec takes `jb`, `jmpRO inp jb` and the alignment as premises. The caller's
  error arms need the same facts for their own `runtime_error` calls.
- **`stringifySpec` is a `fnSpecAbort`** (`SpecStringify.lean`). Its return
  branch hands back a fresh heap block (`strOwn`, `FreshBlock`, the regime's
  `heapRes` with the block pushed) holding `strRender st v`: `catDisplay`,
  except that a named closure renders as `Newlib.fnRender` (Q8). Its abort
  branch is H5's `abortRes s stringifyNeed` (partial-mode `malloc` NULL,
  `oom80003140`). The closure arm needs `dispRes st v` (read geometry of the
  closure object and its `EX_FN` node), as `value_print` does.
  `stringify_spec` takes as premises: `textOwn allocText` (as H1's
  `malloc`/`realloc` specs), `AllocSpecs`, H5's `NewlibHoles`,
  `IrisHoles.out`, H1's `strlenSpec`/`memcpySpec`, and two callee specs for
  the stack buffer, `memcpySpecOwned` (owned source) and `strcpySpec`, whose
  supplier is the string-function lane (H3). It also takes
  `hstk : ∀ a ∈ [0x87800000, 0x88000000), live a`: H3's `strlen` reads the
  stack buffer, and its step lemmas need `live` on those bytes.
- **`ix_run1`** (`ITac.lean`) is `ix_run` stopping at a branch it cannot
  decide, leaving `cond → …` for each side. Lane G's `ix_run` explores both
  sides. H2's scripts resolve each side themselves. The two share
  `ixRunCore`.

### STATEMENT CHANGES (E4)

- **`world` owns the binary's image `Newlib.binImg`** (persistent: `.text`
  and `.rodata` of the fixed ELF, `worldE`'s last conjunct; projection
  `worldE_binImg`). Every native (`nativePrintSpec`, `nativePrintlnSpec`,
  `nativeAssertSpec`), `stringifySpec`, `runtime_error` (`rtErr_spec`) and the
  abort landing take `binImg` (newlib's code), but no recursive spec carried
  it: `evalPre`/`execPre` have only `codeRes` (the interpreter's own code), so
  no call arm could call a native and no error arm could call `runtime_error`.
  Precedent: H5 put `Stdio.stdioOwn` into `world` for the same callees. The
  definitions of its domain moved below `Repr` (`Vsa/BinDom.lean`) so `worldE`
  can name it; `binImg` itself is defined in `Repr.lean` (namespace
  `VsaIris.Newlib`, name unchanged). Consumers adjusted: `world_heapStore`
  (the image on the right), `world_blocks_off_heap`, `rtErr_spec` (rebuilds
  the landing's world with its own `binImg`), `wp_abortLanding`, E1's
  `var`/`assign`/`fnLit` templates and E2's `catRest` (it keeps the image for
  `world_of_catRest`). A supplies it
  at `setjmp` from the boundary's `roOn CodeByte` (`bootRes`).
- **`interpCtxE` carries the `jmp_buf`'s aligned `ra` word**
  (`∃ jb, jmpRO inp jb ∗ ⌜(imgW jb (inp + interpJmpOff)).toNat % 4 = 0⌝`).
  `runtime_error` (`rtErr_spec`'s `hjb`) and `nativeAssertSpec` need it; E2's
  `errCtx` supplied it as a partial-mode premise, which a total-mode `assert`
  call cannot have. With it in the world, `world_errCtx` derives `errCtx` in
  either mode. Supplier: A, after `setjmp` (the saved `ra` is `0x80004428`).
- **`interpCoreE` carries `d ≤ maxCallDepth`.** The closure call's depth
  test is a signed 32-bit compare (`addiw`, `blt 1000`); for a counter of
  `2^31` or more it passes, while `Call.closure` needs `d < maxCallDepth`, so
  the partial spec (quantified over every `d`) was unprovable at such worlds.
  The machine keeps the bound (the check before every body, the reset on the
  error, the decrement after); A0 establishes it at `d = 0`. Consumers adjusted:
  `rtErr_spec` (rebuilds the landing's context with the same `d`),
  `wp_abortLanding`, `world_of_boundary` (`World.lean`), `ctl_interpCtxPre`.
- **`nativeAssertSpec`'s abort carries its reason**, `⌜¬ AssertOk vs⌝`
  (`AssertOk vs := ∃ v m, (vs = [v] ∨ vs = [v, m]) ∧ v.truthy`): total mode
  must prove the abort continuation of the `∧`, and refutes it with
  `Call.assertOk`'s premise. H2's abort paths (`na_badPath`, `na_falsy*`)
  supply it (`not_assertOk_len`, `not_assertOk_falsy`).
- **The call arm's partial case takes `execDispsP`.** A closure call runs
  its body with `exec_stmt` inside `eval_expr`'s arm, so `caseP_CallArm`'s
  Löb hypotheses are `evalSpecsP ∗ errCtx ∗ execDispsP` (E5's statement form
  of the exec Löb hypothesis). `execSpecsP_of_disps` gives `CallCloP` the
  entry specs G's closure loop takes. The recursor's partial case supplies both
  hypotheses; the other eval arms keep `evalSpecsP ∗ errCtx`.

### STATEMENT CHANGES (E2)

- **An eval error arm carries `errCtx inp` and `ErrEnv`** (`SpecErr.lean`).
  `runtime_error` needs `binImg` (its `callFrame`, the format strings) and
  the `jmp_buf`'s aligned `ra` word (`rtErr_spec`'s `hjb`); `evalPre` has
  neither, and `world` has the `jmp_buf` without the alignment. The partial
  cases are `evalSpecsP … Core ∗ errCtx inp ⊢ evalSpecP_body …` with
  `ErrEnv` (NewlibHoles, CodeLive, `InpGeom`, `inp < 2^64`, `CoreOK Core`) a
  Lean premise. `CoreOK Core`: the landing core absorbs H5's `abortCore` at
  any region inside the stack segment (`coreOK_top`).
- **String comparisons take `strcmpOrdSpec`**, the sign class of `strcmp`'s
  result (`StrcmpSign`). H1's `strcmpSpecV` only says zero iff equal, which
  does not decide `<`. Supplier: H3's `strcmp` run.
- **String `+` takes its callee specs over OWNED heap strings**
  (`SpecConcat.lean`). The two renderings are fresh blocks the arm frees, so
  `strlen`/`strcpy` cannot read them through the persistent `strAt`:
  `strlenHeapSpec`/`strcpyHeapSpec` own the string and lend `heapRes` (the
  word loads read up to seven bytes past the NUL, inside the chunk, which
  `heapFoot` owns). `stringifySpecT` is `stringifySpec`'s return branch in the
  counted regime (a total-mode caller cannot discharge `fnSpecAbort`'s abort
  branch); `stringifySpecP` is `stringifySpec` whose abort also returns the
  value's slot (an eval arm's abort rebuilds its whole stack). Both cases
  take `binImg`/`textOwn allocText` (the allocator's code for `malloc`/`free`)
  and fix `L = vsaLayoutP`, `Room = vsaRoomB` (the layout `stringifySpec` is
  stated at). `CatDispSupply` is lane E4's `DispSupply`.
- **The concatenation's cost** is `binOpCost` = `concatCost` = two
  `stringifyCost` + `catBufCost` (`binOpCost_concat`); `free` keeps the
  credits (`freeRoomSpec`).

## 11. Open questions for the user

- **Q5 (lane H4; resolved 2026-09-24: `BootHeapFacts.brk_page`): a page-aligned break at the boundary.** `malloc_extend_top`
  grows the top in place only when the old heap end is page-aligned (`0x80004f70`). Otherwise it
  returns NULL when the old top is under 32 bytes (`0x80004f94`), or it fenceposts and frees the
  old top, which `ChunkWalk` cannot describe. `InitialAllocatorAt` does not rule this out, so its
  `capacity` does not imply allocation success. The Iris heap shape therefore adds
  `brkv % 4096 = 0`. Every allocator path preserves it (extension by page-rounded sizes, trim by
  whole pages). A0 needs it at the boundary, which means a new `Loaded` field beside `capacity`,
  or a proof from the loader. Recorded in `PROOF_CLOSURE_PLAN.md` §2.

- **Q5b (lane H4; resolved 2026-09-24: `BootHeapFacts.binblocks`): a 32-bit `binblocks` word at the boundary.** `_malloc_r`'s
  block search shifts a mask up to the next set bit of `binblocks` and advances the bin index by
  four each shift (`0x80004994`-`0x800049a0`). `HeapAt.binblocks` bounds only the bits of nonempty
  blocks, and dlmalloc clears the bitmap lazily, so a bit at 32 or above would walk the index past
  bin 127. The Iris heap shape therefore adds `bb < 2 ^ 32` (`PHeapAt.bb_lt`); every path preserves
  it, since the bits written are `1 << (i / 4)` for `i < 128`. Same supplier as Q5. Recorded in
  `PROOF_CLOSURE_PLAN.md` §2.

- **Q1 (hard to change later): stack admissibility at the boundary** (§10.4).
  Approve a `stack_admissible` field in `InterpRunReady`, shaped like
  `capacity`? Without it, `InterpSim interpRunLayout` looks false for very deep
  ASTs.
- **Q2: the top-level hypothesis.** `RemainingWork` (63 + Div + Err fields) is
  replaced by `IrisHoles` (the allocator runs plus the newlib safety specs).
  `Refinement.lean` and `InterpSim` are unchanged, and the new theorem is
  `endToEnd_refinement_iris`. Keep `endToEnd_refinement`'s name by redefining
  it over `IrisHoles`, or keep both during migration?
- **Q3: two WPs.** Total derivation-indexed plus partial Löb, with shared
  blocks, is recommended. The alternative is a single partial WP with step
  credits for termination: it avoids the duplicate case glue but needs exact
  step budgets.
- **Q4: newlib safety holes.** `snprintf`/`fprintf` on the error paths are
  needed only so that partial mode is "never stuck". Leave them as named
  holes, or schedule proofs? (`vfprintf` is large.)
- **Q6 (lane H5; resolved 2026-09-24: `BootHeapFacts.stderr`): `_impure_data._stderr` at the boundary.**
  `main`'s error line (`0x80004600`) loads its stream with `ld a5,0(s0);
  ld a0,24(a5)`, i.e. from the reentrancy record's `_stderr` field
  (`0x8001b550`). `InterpRunPhysicalFacts` pins stdout (`ConsoleStream`) and
  the idle `stderr` `FILE` (`ExitRuntimeData.stderr`) but not this pointer, so
  from the boundary alone `fprintf` may be handed any stream and the error
  path's safety is unprovable. `Stdio.StdioOK` requires it
  (`read64 m stderrPtrAddr = some exitStderr`); the supplier is one more
  `ExitRuntimeData` field, read off the same snapshot
  (`Vsa/Sim/OutputAliasSnapshot.lean`). A0: the ELF's `.data` holds it
  (`_impure_data` initializes `_stdin`/`_stdout`/`_stderr` to `&__sf[0..2]`).
  The control snapshot had zeroed `_stdin` and `_stderr`; it now carries the
  two ELF words. Resolved: `Loaded` states the pointer
  (`BootHeapFacts.stderr`, lane BG), and `Boot.gap` hands it to
  `world_of_boundary` as `BootGap.stderr`.
- **Q7 (lane H5, needs the user): the error path's stack at the deepest call.**
  `runtime_error` needs 224 bytes plus `snprintf`'s chain (272 + 592 + 64 =
  928, `IrisHoles.newlib.snprintf` claims 1024). The budget's leaf headroom is
  `evalFrame = 1088` (`EvalEntry.stackBudget`, `ProgramStackFits.need`), so an
  error raised at call depth `maxCallDepth` from the deepest `eval_expr` has
  no owned stack for `runtime_error`: 1152 > 1088 even at the measured need.
  Either the boundary reserves an error headroom `rtErrNeed ≥ 224 + 1024`
  below the program's need, or `perCallBudget` accounting leaves it at depth
  `maxCallDepth`. H5 states `runtime_error`'s spec with its real need; E1–E6
  must supply it at each error site.
- **Q8 (lane H2; decided 2026-09-24: the semantics cuts, see Decisions): `stringify` cuts a named closure's rendering
  at 63 characters.** `stringify` renders a closure with
  `snprintf(buf, 64, "<fn %s>", name)` and copies the buffer, so the string
  `+` of a closure whose name is longer than 58 characters yields
  `("<fn " ++ name ++ ">")` cut to 63 characters, while `Value.catDisplay`
  (and so `EvalE`'s concat rule) renders it uncut: `InterpSim` is false for
  such programs. Either the semantics cuts (`catDisplay` of `.closure` is
  `Newlib.fnRender name`), or `Loaded` bounds name lengths. H2 states
  `stringify` against the machine (`Newlib.fnRender`); evidence in
  `PROOF_CLOSURE_PLAN.md` ("`stringify` cuts a closure's rendering").

### STATEMENT CHANGES (H1)

Two changes to R's predicates, both because an `env_*` spec cannot be proved
without the fact and no other resource carries it:

- **`storeRepr` carries `Vsa.Sim.StoreInvariant`** (unique names per frame,
  parents point to older frames), in the named pure part `StorePure`
  (`maps`, `blocks`, `bodies`, `inv`). `env_get`/`env_set` walk the parent
  chain: `parents` makes the walk terminate (the total WP needs it) and
  bounds its length by `frames.size` (so the machine's answer is
  `Store.get?`'s). `env_define` updates the FIRST matching slot, which is
  `Store.define`'s update only when names are unique. VSA carried the same
  pair in `HeapRepr` (`Vsa/Sim/HeapOps.lean`). Consequences: the generic
  closer of `storeRepr_open` takes `StoreInvariant s'`;
  `storeRepr_open_define` takes `StoreInvariant s` and re-establishes it
  (`StoreInvariant.define`); `storeRepr_allocFrame` takes `StoreInvariant s'`
  (from `StoreInvariant.allocFrame`, the parent being an allocated frame).
- **`strAt p s` carries `StrWin p s.length`**: `[p, p + len + 8)` is RAM and
  off the HTIF words. `strcmp` and `strlen` load whole aligned words and read
  up to 7 bytes past the NUL (`0x80006eb8`, `strlen`'s word scan), so every
  caller of either needs the window, and the window is a property of where
  the string lives, not of the call. Producers: `strAt_of_owned` takes it
  (heap strings: arena geometry); `strAt_of_cstringWithin` and the
  `valOf`/`bindings`/`frameBody` bridges take `SharedWin P` — every byte of
  the shared read view has its 8-byte window — which A0 establishes once at
  the boundary (`ctl_sharedWin` at the control program). The over-read bytes
  themselves are NOT owned by the string: their values never decide the
  result, so the H3 runs read them as total reads (`readByte = getD 0`).
- **`FrameLayout` gains `win`, `e_align`, `cap_canon`.** `win`: every block
  of a frame is RAM above the HTIF words and 16-aligned (`BlockWin`), which
  every `env_*` load and store into the struct and arrays needs (`LdOK`,
  `StOK`), and which only the frame knows (`env_get`/`env_set` hold the store,
  not the heap). `cap_canon`: `cap = capFor count` (`0, 8, 16, 32, …`,
  `env.c`'s growth policy). The counted regime charges `defineCost`, which
  pays for array growth exactly when the count sits on a canonical cap; a
  frame with `count = cap` off that sequence would grow without credits.
  `capForAux` mirrors `arrayCostAux`'s fuel recursion. `FrameBridge` carries
  the three facts at the boundary (`ctl_frameBridge`: cap 8 for 3 natives).
- **`FrameLayout.arrays` states the arrays' exact extents**: with `cap > 0`,
  `nblk = (pn, 8 * cap)` and `vblk = (pv, 24 * cap)` (was: lower bounds).
  `env_define`'s growth `realloc`s each array from its live extent
  (`realloc(names, 16 * cap)`), and `realloc`'s spec takes the live block
  `(p, nOld)` at its heap entry with `nOld < nNew`; the heap's entries are the
  exact requests (`env_define` allocates `8 * cap` and `24 * cap`), so only
  the equality gives `nOld = 8 * cap < 16 * cap`. `FrameLayout.arrays_le`
  recovers the componentwise bounds; `FrameBridge.arrays` carries the same
  equality (`ctl_frameBridge`: 64 and 192 bytes at cap 8).

### STATEMENT CHANGES (E1)

- **`ReadOK` carries the string window** (`SpecEval.lean`, field `win`: the
  byte plus 8 is RAM and off the HTIF words). `astEG` gave the AST's read
  set only `ReadOK` (RAM, off HTIF), but a string field of the AST (`str`'s
  literal, `var`'s and `assign`'s name) becomes `strAt` only with H1's
  `SharedWin P` (`strAt_of_cstringWithin`), and `strlen`/`strcmp` need that
  window. `SharedWin P` follows from the strengthened `ReadOK`
  (`sharedWin_of_readOK`, `LeafArm.lean`). The supplier is A0, which already
  establishes `SharedWin` at the boundary (`ctl_sharedWin`); no existing
  construction of `ReadOK` changed (all consumers project fields).
- **The error context of the partial cases (E1, no statement change to
  `evalPre`).** An error arm's `runtime_error` needs the binary image
  (`binImg`), the `jmp_buf` read-only at an image whose `ra` word is aligned,
  and `in`'s placement; `world` has the `jmp_buf` only existentially and no
  alignment. The partial cases with error arms therefore take the persistent
  `errCtx inp` (`LeafErr.lean`) beside the Löb hypothesis:
  `errCtx inp ∗ evalSpecsP … ⊢ evalSpecP_body …`. A holds all three at
  `interp_run`'s `jal exec_stmt` (`TopLanding`).
- **One landing core.** Each abort site's `abortCore s n` depends on its
  region; every region inside the stack segment widens to
  `evalCore := abortCore 0x88000000 0x800000` (`evalCore_of`), so the
  partial cases with error arms are stated at `Core := evalCore`; G's
  generic-`Core` cases instantiate at it.
- **Q7 as a named premise.** `ErrRoom e d` (`rtErrNeed + evalFrame ≤
  evalNeed e d`) is the `var`/`assign` partial cases' premise; it holds for
  `d < maxCallDepth` (`errRoom_of_lt`) and is exactly Q7 at the deepest level.
- **`fn` is stated at `vsaLayoutP`/`vsaRoomB`**, `malloc`'s heap, with
  `AllocSpecs live` and `textOwn allocText` (H4's `allocSpecs` supplies the
  former).


### STATEMENT CHANGES (E5)

- **`exec_stmt`'s specs are stated at its dispatch point** (`Interp/SpecExecDisp.lean`).
  gcc compiled the `if` arm's `return exec_stmt(in, branch, env, ret)` as a tail
  call inside the frame: after `li a6,8; auipc a4` it jumps back to the kind
  dispatch (`0x8000422c ld s0,16(s0); j 0x80004014`, `0x800042cc ld s0,24(s0);
  bnez s0,0x80004014`). The branch never runs from `exec_stmt`'s entry, so the
  entry spec `execSpecT_body` of the branch cannot discharge the arm, and no
  entry-shaped motive can.
  - `execDispT_body … D` (total) and `execDispP_body Core …` (partial) state the
    arm from `0x80004014` with the 176-byte frame spilled (`DispFacts`:
    `DispRegs` — `sp = s-176`, `s0` the statement, `s1` `in`, `s2` the `ret`
    slot, `s3` the frame, `a6 = 8`, `a4` the jump table; `ExecSaved` — the
    spills), the frame bytes as the tracking memory of `ms`, the stack below the
    frame. The continuation (`execDispK`) receives the state after the
    epilogue's `ret` (`ExecRet`).
  - **The recursor motive of `ExecSCost` is `execDispT_body`** (A); the partial
    Löb hypothesis is `execDispsP`. `ExecDisp.lean` recovers the entry specs by
    running the prologue: `execSpecT_of_disp`, `execSpecP_of_disp`,
    `execSpecsP_of_disps` (every `jal exec_stmt` caller: block/while/for bodies,
    closure bodies, `interp_run`).
  - The partial `if` re-dispatch is a jump, not a `jal`, so the Löb later is paid
    by the route's run (`SymLater.lean`: `wp_swpF_later`, a symbolic run that
    takes a step strips a `▷` from a hypothesis).
- **Out-of-memory arms follow E2's core convention**: the partial cases of the
  allocating arms (block, `for`: `env_new`; `var`: `env_define`) take
  `CoreOK N L Room inp Core` and `errCtx inp`; out of memory, H5's
  `wp_oomBlock` (`oom80002a38`, `oom80002bd0`) runs over the arm's lowered
  stack and the resulting `abortRes` enters `Core` (`ms_callEnvNewP`,
  `ms_callEnvDefineP`, `ExecOom.lean`). The arms fix `L`/`Room` to
  `vsaLayoutP`/`vsaRoomB` (the `env_*` specs' heap).

### STATEMENT CHANGES (N2)

- **`StdioOK` pins the C locale** (`Vsa/Sim/LocaleData.lean`: `LocaleData`,
  the fourth conjunct of `Stdio.StdioOK`). `_svfprintf_r`, behind every
  `snprintf`/`fprintf` hole, reads three words of `__global_locale` (`.data`,
  inside `stdioFoot`): the `mbtowc` hook it calls through `jalr s4`
  (`0x80007740`, `__global_locale + 232 = 0x8001b880`), `__mb_cur_max`
  (`0x8001b8f8`, via `__locale_mb_cur_max`), and the lconv `decimal_point`
  (`0x8001b898`, via `_localeconv_r`, then `strlen`). `StdioOK` pinned none of
  them, so the `snprintf` holes quantified over locale data that sends the
  indirect call anywhere: unprovable as written.
  - **What narrowed.** `LayoutInstance.BootHeapFacts` gains `locale :
    LocaleData m` (so `Loaded interpRunLayout`, the hypothesis of
    `endToEnd_refinement`, narrows); `World.BootGap` gains `locale`, and
    `stdioOK_of_mem` takes it. `StdioOK`'s consumers are unchanged except
    `StdioOK.stderr` (the tower's third conjunct is now a pair).
  - **Not vacuous.** The control's snapshot carries the ELF values
    (`NativeNameAudit.Control.locale_mem`, three reads through the heap log,
    each one `decide`): `__ascii_mbtowc`, `1`, `"."` at `0x80019770`.
  - **Every hole that returns `stdioOwn` must now also restore the locale**;
    nothing writes it (`setlocale` is not linked into any path).
- **The `out.snprintf*` holes take an aligned return address and a stack and
  buffer above newlib's data.** `snprintfIntSpec`/`snprintfFnSpec` carry
  `⌜r.toNat % 4 = 0⌝` in their precondition: `snprintf` returns through
  `jalr zero, 0(ra)`, a successful step only to a 4-aligned target (lane N1's
  change to `outSpec`, same reason). `OutHoles.snprintfFn` (and the proved
  `Sym.snprintfInt_out`, `Vsa/SnpHoles.lean`) take `0x8001c168 ≤ s - 1024`,
  `0x8001c168 ≤ buf` and `buf + 64 ≤ 2^32` besides `SpIn`: `SpIn` bounds the
  stack only below by the HTIF words, so the 1024-byte frame may lie over
  `.data`/`.bss` (whose bytes the run reads: the locale words, `_impure_ptr`),
  and nothing places `buf` off the HTIF words or in 32-bit RAM. `stringify`'s
  callers (`sg_intArm`, `sg_fnArm`) derive all three from `SgCtx.hs1` (the
  stack region starts at `0x87800000`) and pass the alignment through
  `ms_callNewlibA`.
- **Not a statement change: the conversion table is data.** `_svfprintf_r`
  dispatches through a jump table in `.rodata` (`0x8001a0fc`). The holes'
  `CodeLive` makes only `.text` live, so `snpText` holds the code alone and the
  table is read through the run's data view (`SnpSvfConv.TabAt`, from
  `binImg`), like the format string.
