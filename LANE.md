# Lane H2: value functions and natives

Branch `lane-h2` (from `hub/iris-main`), merged `hub/lane-g` (its step-table
generator and arm layer) and `hub/lane-h1` (`mallocRho_spec`, `memcpySpec`,
`strlenSpec`; `strAt` carries `StrWin`). Design: `VsaIris/INTERP_DESIGN.md` §9 H2; statement
changes in §10 "STATEMENT CHANGES (H2)"; open question Q8.

## Done
- **Statements** (`VsaIris/Interp/SpecValue.lean`), in lane G's register-file
  form (`helperSpec`): `valueNullSpec`, `valueBoolSpec`, `valueStrSpec`
  (+ G's `valueIntSpec`), `valueTruthySpec`, `valueEqualSpec`,
  `valuePrintSpec`, `nativePrintSpec`, `nativePrintlnSpec`; callee spec
  `strcmpSpecV` (H3), `nativeAssertSpec` (`fnSpecAbort`). `stringify`: in
  flight.
- **Proved, for either WP** (axioms ⊆ {propext, Classical.choice, Quot.sound},
  `VsaIris/Audit.lean`):
  - `valueNull_spec`, `valueBool_spec`, `valueInt_spec` (discharges G's stub),
    `valueStr_spec` (`ProofValueCons.lean`): `helper_leaf` (`HelperRun.lean`,
    a helper as one symbolic run) plus one `ix_run` each;
  - `valueTruthy_spec` (`ProofValueTruthy.lean`);
  - `valueEqual_spec` (`ProofValueEqual.lean`): every kind; strings through
    `strcmpSpecV` (H3) at `jal 0x800028d4`, closures by the store's address
    map (`storeRepr_clos_inj`), natives by `NativeInj`; one lemma per arm;
  - `valuePrint_spec` (`ProofValuePrint.lean`), given `IrisHoles.out`: every
    arm tail-calls newlib (`ms_tailNewlib`, `NewlibCall.lean`); the closure
    arm reads the closure object and the `EX_FN` name field through a data
    view (`roOwn_clod`);
  - `nativePrint_spec` (`ProofNativePrint.lean`), given `IrisHoles.out`: six
    `#ix_seg` runs; the loop is a Lean induction over the arguments left
    (`np_loop`: `np_A` = head, copy, `value_print`; `np_B_more`/`np_B_last`);
    newlib's two stdio words enter a run through `ms_ioOpen`/`ms_ioClose`;
  - `nativePrintln_spec` (`ProofNativePrintln.lean`): `native_print` into its
    own frame slot (by `nativePrint_spec`), `fputc('\n')`, `value_null`;
  - `nativeAssert_spec` (`ProofNativeAssert.lean`), given H5's `NewlibHoles`:
    a `fnSpecAbort`. Seven `#ix_seg` runs. `runtime_error` is called through
    `ms_callNewlibAbort` (`NewlibCall.lean`) against `rtErr_spec`. The abort
    rebuilds `abortRes s nativeAssertNeed` (`na_rtErr`). The messages are
    `FmtArgsOK` over `.rodata` or the second argument's string
    (`readable_str`). The first argument's copy uses `ms_carveVal`/
    `ms_uncarveVal`.
- **Generator** (`scripts/gen_interp_steps.py`, shared with G): the step table
  covers the value helpers, the natives and `stringify` (their kind tables and
  `stringify`'s `.rodata` constant as table words); `sltu`/`sltiu` get
  `itO_<pc>` (`VsaIris/Vsa/SymObs.lean`: `aluStep_of_obs`, `swp_alu`), which
  `ix_run` tries. eval_expr's `seqz` sites get them too.
- **Statement fix in G's layer**: `helperSpec` hands the callee an aligned
  return address (without it no helper can `ret`); `ms_callHelper` takes
  `(by decide)` at the call site; G's template and cases regenerated.

- **Shared layers**: `LocalRun.promote` and `strlen_specOwnedW`
  (`Vsa/StrlenOwned.lean`: H3's `strlen` on an owned buffer, the bytes handed
  back unchanged); `ms_callRegs` (`Interp/CallRegs.lean`: a call from a run by
  the callee's register list, `regFile_cut`/`regFile_uncut`).

## In flight
- `stringify`: statement done (`SpecStringify.lean`: `fnSpecAbort`, both
  regimes, `strRender` = `catDisplay` with `fnRender`; callee specs
  `memcpySpecOwned`, `strcpySpec`, H1's `strlenSpec`/`memcpySpec`; hole
  `out.snprintfInt`). Runs done (`ProofStringify.lean`, fifteen `#ix_seg`).
  Glue in progress: shared tail (`strlen`, `malloc`, OOM/`memcpy`,
  epilogue), then the arms.

## Holes (`VsaIris/HOLES.md`, `IrisHoles.out`, `VsaIris/Vsa/NewlibOut.lean`)
- `out.fputs`, `out.fputc`, `out.fwrite`, `out.fprintf`: newlib's stdout
  calls, exact about what they print (VSA assumed the same:
  `CallIOContracts`). `out.snprintfFn`: `snprintf(buf, 64, "<fn %s>", name)`;
  `out.snprintfInt`: `snprintf(buf, 64, "%lld", i)`.

## Findings
- `closOwn`/`astE` carry no read geometry (`ReadOK`), so no run can load a
  closure object or its `EX_FN` node from them. `dispRes` (what `value_print`
  needs of a closure) carries it; its supplier is the `EX_FN` arm (heap block,
  program AST) or a geometry field on `closOwn`. The `call` arm needs the same.
- **Q8**: `stringify` cuts a named closure's rendering at 63 characters
  (`snprintf` into `char buf[64]`); `Value.catDisplay` does not, so the
  concat rule disagrees with the machine for names longer than 58 characters
  (`PROOF_CLOSURE_PLAN.md`).
- G's `helperSpec` lacked the return-address alignment (fixed, above).
- `runtime_error` needs the `jmp_buf` at a named image with an aligned `ra`
  word; `world` gives only `∃ jb` (INTERP_DESIGN.md §10, H2).
- H3's `strlen` needs `live` on the bytes it reads (`Ctx.codeLive`); for a
  stack buffer that is the stack region, a condition on the top-level `live`
  like `CodeLive` (`stringify` takes it as `StackLive live`).
- Tooling: after merging G, `ix_run` explores undecided branches; H2's scripts
  use `ix_run1` (the stopping variant). `simpa`/`omega` over `k % 2^64` with a
  variable `k` can produce kernel deep recursion; explicit `Nat.mod_eq_of_lt`
  rewrites avoid it.

## Interface for other lanes
- E lanes call the helpers with `ms_callHelper` (G) against the specs above.
- H3: `strcmpSpecV` is the register-file form of H1's `strcmpSpec`.
- H1: `HelperRun.helper_leaf` is the register-file twin of H1's `wp_ew`
  (a span as one run); `SymObs.swp_alu` gives `snez`/`seqz` steps to any
  `SWP` table.
