# Lane H2: value functions and natives

Branch `lane-h2` (from `hub/iris-main`), merged `hub/lane-g` (its step-table
generator and arm layer). Design: `VsaIris/INTERP_DESIGN.md` §9 H2; statement
changes in §10 "STATEMENT CHANGES (H2)"; open question Q8.

## Done
- **Statements** (`VsaIris/Interp/SpecValue.lean`), in lane G's register-file
  form (`helperSpec`): `valueNullSpec`, `valueBoolSpec`, `valueStrSpec`
  (+ G's `valueIntSpec`), `valueTruthySpec`, `valueEqualSpec`,
  `valuePrintSpec`, `nativePrintSpec`, `nativePrintlnSpec`; callee spec
  `strcmpSpecV` (H3). `native_assert` and `stringify` statements: in flight.
- **Proved, for either WP** (`ProofValueCons.lean`): `valueNull_spec`,
  `valueBool_spec`, `valueInt_spec` (discharges G's stub), `valueStr_spec`.
  Each is `helper_leaf` (`HelperRun.lean`: a helper as one symbolic run) plus
  one `ix_run`.
- **Generator** (`scripts/gen_interp_steps.py`, shared with G): the step table
  covers the value helpers, the natives and `stringify` (their kind tables and
  `stringify`'s `.rodata` constant as table words); `sltu`/`sltiu` get
  `itO_<pc>` (`VsaIris/Vsa/SymObs.lean`: `aluStep_of_obs`, `swp_alu`), which
  `ix_run` tries. eval_expr's `seqz` sites get them too.
- **Statement fix in G's layer**: `helperSpec` hands the callee an aligned
  return address (without it no helper can `ret`); `ms_callHelper` takes
  `(by decide)` at the call site; G's template and cases regenerated.

## In flight
- `value_truthy`, `value_equal` (strcmp call), `value_print` (tail calls
  into `IrisHoles.out`), natives, `stringify` (strlen/malloc/memcpy/snprintf,
  OOM through H5's `wp_oomBlock`; `strcpy` is run symbolically inline).

## Holes (`VsaIris/HOLES.md`, `IrisHoles.out`, `VsaIris/Vsa/NewlibOut.lean`)
- `out.fputs`, `out.fputc`, `out.fwrite`, `out.fprintf`: newlib's stdout
  calls, exact about what they print (VSA assumed the same:
  `CallIOContracts`). `out.snprintfFn`: `snprintf(buf, 64, "<fn %s>", name)`.

## Findings
- **Q8**: `stringify` cuts a named closure's rendering at 63 characters
  (`snprintf` into `char buf[64]`); `Value.catDisplay` does not, so the
  concat rule disagrees with the machine for names longer than 58 characters
  (`PROOF_CLOSURE_PLAN.md`).
- G's `helperSpec` lacked the return-address alignment (fixed, above).

## Interface for other lanes
- E lanes call the helpers with `ms_callHelper` (G) against the specs above.
- H3: `strcmpSpecV` is the register-file form of H1's `strcmpSpec`.
- H1: `HelperRun.helper_leaf` is the register-file twin of H1's `wp_ew`
  (a span as one run); `SymObs.swp_alu` gives `snez`/`seqz` steps to any
  `SWP` table.
