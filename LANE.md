# Lane A: the final assembly (`endToEnd_refinement` from `IrisHoles`)

Branch `lane-a`, from `hub/iris-main` (`05874b5`), fast-forwarded to `hub/lane-e4`
(`f9d805d`, E4 final; it had already merged `iris-main`). Design:
`VsaIris/INTERP_DESIGN.md` §4, §5, §9 package A.

## User decisions taken in this lane

- **Q7 (2026-09-25): boundary reserve.** `ProgramStackFits.need` and the Iris
  `stackBudget` gain one constant headroom, so `runtime_error` (and, per E4's
  finding, the natives' `fprintf` chain) fit below the deepest `eval_expr`
  frame. See "Foundations" below for the constant.

## Plan

### Foundations (one rebuild each; done by me, in order)

| # | change | why |
|---|---|---|
| F1 | `helperHeadroom` in `ProgramStackFits.need` and `stackBudget` | Q7: `ErrRoom e maxCallDepth` is false (1248 > 1088); E4's native `hroom` at depth `maxCallDepth` needs 4224 > 2176 |
| F2 | `newlib.exitHandlers` exact from `StdioOK` (no output) | `term_sim` needs `Halts c st'.out 0` exactly; the hole allowed `∃ o'` |
| F3 | `_impure_ptr` read-only (discarded) inside `stdioAt` | `textOwn allocText`/`textOwn envText` hold it persistently while `stdioOwn` owned it exclusively: the two could not coexist, so no `malloc` spec was ever usable beside `world` |
| F4 | helper specs valid: code context in their precondition | cases take `⊢ envNewSpec …`, but H1's proofs need `textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ …`; `binImg` is in `world` (E4) |

### Supplier ledger (every premise of the case lemmas, and who supplies it)

| premise | supplier | status |
|---|---|---|
| `valueInt/Bool/Null/StrSpec`, `valueKindNameSpec`, `valueTruthySpec`, `valueEqualSpec` | H2 (`⊢`) | proved |
| `envNew/Define/Get/SetSpec` | H1 + F4 (`env*_closed`, `Supply.lean`) | proved |
| `strcmpSpec`, `strcmpSpecV`, `strcmpOrdSpec` | strcmp run (`ProofStrcmp.lean`) | proved |
| `memcpySpec`, `memcpySpecOwned` | memcpy run (`ProofMemcpy.lean`), destination above HTIF | proved |
| `strcpySpec`, `strcpyHeapSpec` | strcpy run (`ProofStrcpyH.lean`), destination above HTIF | proved |
| `strlenSpec`, `strlenHeapSpec` | `ProofStrlen.lean`, `ProofStrHeap.lean` | proved |
| `stringifySpecT/P` | `stringifyT_closed`/`stringifyP_closed` (`Supply.lean`) | proved |
| `AllocSpecs` | H4 `allocSpecs` | proved |
| `CatDispSupply`, `CloSupply`, `NativeInj` | boundary/store facts | open |
| `ErrRoom`, native `hroom` | F1 | open (F1) |
| `ErrEnv`, `CoreOK`, `errCtx`, `leafErrCtx`, `InpGeom` | top (`interp_run`'s `setjmp`) | open |
| `CloArityP` | `rtErr_spec` returning the readable bytes | open |
| `NewlibHoles`, `OutHoles` | `IrisHoles` | holes (10) |

### Assembly

1. `interp_run` spec, both modes: prologue + `setjmp`, loop entry, G's
   `interpSeqT/P`, exits (normal → `main` → `exit(0)`; `ret`/`brk`/`cont` →
   `wp_topAbrupt`; landing → `wp_abort`).
2. `term_sim_iris`: mutual recursor over the nine cost companions.
3. `stuck_sim_iris`: Löb over `evalSpecP_body ∧ execDispP_body`.
4. `interpSim_iris`, `endToEnd_refinement` from `IrisHoles`; delete
   `RemainingWork`/`TermResidualsBase`/`DivWork`/`ErrWork` and their feeders.
5. Audit.

## Done

- F4 (helper specs carry their code context; memcpy/strcpy destinations above HTIF; `topLive` adds `_impure_ptr` and the stack): `Supply.lean`, `supplies_of : IrisHoles → Supplies`.

- F1 (Q7 headroom, `helperHeadroom = 2048`, `errRoom` at every depth) and F2 (`exitHandlers` quiet from `StdioOK`), `327fe89`.
- `TermSim.lean`: the total recursion (nine motives, fifty cases; `binaryT` dispatches `binOpSem`), `interpSeqT_all`, `execDispT_all`, over `TermSupply`.
- `StuckSim.lean`: the Löb (`specsP_all : errCtx inp ⊢ □ (eval ∧ exec partial specs)`), over `StuckSupply`.
- `TopBoundary.lean`: `topLive`, `vsaOk_of_ready`, the register map.
- `Loaded` fields `gprs` and `s0_impure` (control: `physicalConfigS0`); `TopEntryBoot.lean`: `codeRes_of_boundary`, `topRegs_carve`, `interpRun_total_top`/`interpRun_partial_top` from `bootRes` and adequacy's registers.

## In flight (sub-agents)

| item | where | status |
|---|---|---|
| strcmp (`strcmpSpec`, `strcmpSpecV`, `strcmpOrdSpec`) | main tree, new files | running |
| memcpy (`memcpySpec`, `memcpySpecOwned`) | main tree | obstruction found: the specs allow a destination below the HTIF words; fix = add `htifLo + 16 ≤ dst` (F4); proving the fixed form |
| strcpy, strlen (`strlenSpec`), heap forms | main tree | running |
| `interp_run` whole run, both modes | main tree | running |
| F3 `_impure_ptr` read-only in `stdioAt` | worktree wt1 | running |
| F5 closure geometry in `closOwn` (`CloSupply`) | worktree wt2 | running |
| F6 `runtime_error` returns its readable bytes (`CloArityP`) | worktree wt3 | running |

## Foundations still to do (me, after F3)


## Holes

None added.
