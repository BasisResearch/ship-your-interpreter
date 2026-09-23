# Lane G: the exponentiating layer on Iris (generators)

Branch `lane-g` (from `hub/iris-main`), pushed to `hub`. Design:
`VsaIris/INTERP_DESIGN.md` §6 and §9 G. E1-E6 build on the row format and the
emitter below; both are stable from this commit on (additions only).

## Row format (`scripts/iris_arms/arms.tsv`)

One row per machine arm, tab-separated, `#` comments. Hand edits go in the
table, never in the generated `VsaIris/Interp/Case/*.lean`.

| column | meaning | example (`BinaryAddInt`) |
|---|---|---|
| `arm` | case name; files `Case/<arm>T.lean`, `Case/<arm>P.lean` | `BinaryAddInt` |
| `fn` | `eval` (`eval_expr`, `0x80003164`) or `exec` (`exec_stmt`, `0x80003fe0`) | `eval` |
| `tag` | AST kind tag the prologue's jump table dispatches on | `6` |
| `ctor` | the source term, children as variables | `.binary .add l r` |
| `children` | `var:E\|S:outcome:slot`, `;`-separated; `slot` = frame offset of the child's `sret`/`ret` slot | `l:E:.int a:120; r:E:.int b:144` |
| `result` | the arm's outcome (value for `eval`, status for `exec`) | `.int (wrap64 (a + b))` |
| `steps` | the arm's code, in order (step language below) | see the table |
| `errors` | partial mode only: `family:branchPC:target` for each branch whose other polarity leaves this row (to `runtime_error` or another row) | `kind:0x800038ac:0x80003df8` |

### Step language (`;`-separated)

| step | Lean it becomes | total | partial |
|---|---|---|---|
| `run <from> <to>` | one first-order stretch of straight-line/branching code from PC `from` to the `jal` at `to` (or `ret`), run symbolically | `wp_localRunW` | same |
| `child <var> <jalPC>` | the recursive call on child `var` into its frame slot | `wp_callArmW` + the child's `evalSpecT_body`/`execSpecT_body` | `wp_callArmAbort` + the Löb hypothesis |
| `helper <Spec> <jalPC>` | a runtime helper call (`value_int`, `env_get`, …) against its `fnSpecW` statement, taken as a hypothesis | `wp_callW` | `fnSpecAbort_of_fnSpecW` + `wp_callAbort` |

The first step must be a `run` from the function entry (the shared prologue
and the kind dispatch are inside it) and the last a `run … ret` (the shared
epilogue). The generator validates every row against `experiments/disasm.txt`:
PCs are instructions, `child` sites are `jal` into the recursive entry, `helper`
sites are linking `jal`s.

## Emitter interface (`scripts/gen_iris_cases.py`)

```
rows = load_rows()          # list[Arm], validated against the disassembly
text = emit(arm, "T"|"P")   # Lean source of one case
write_all(check=False)      # regenerate; check=True is the drift gate
```

`python3 -B scripts/gen_iris_cases.py [--check|--list]`. The `--check` mode is
the stage-a3 drift gate for `VsaIris/Interp/Case/*`.

## Findings so far

- **`eval_expr`'s ABI is `a0 = sret, a1 = in, a2 = e, a3 = env`**, not the
  `a1 = env, a2 = e` of `Specs.lean` §D. Evidence: the prologue keeps `a1` in
  `s2` and passes it back unchanged to both children and to `runtime_error`
  (`0x80003184 mv s2,a1`, `0x8000350c mv a1,s2`, `0x80003b2c mv a0,s2`), and the
  binary arm spills `a3` and reloads it for the right child
  (`0x800034f4 sd a3,0(sp)`, `0x80003500 ld a3,0(sp)`); the var arm passes `a3`
  to `env_get` (`0x80003438 mv a0,a3`). C source: `eval_expr(Interp *in, Expr
  *e, Env *env)` returning a `Value` through `sret`. `exec_stmt`'s ABI in §D is
  right.
- **`evalPre` needs the code bytes and fixed register sets.** §D quantifies over
  arbitrary `saved`/`clobE` lists, which no real body meets (it spills `s0-s3`
  whatever the caller passed), and omits the persistent code image a segment
  fetches from. Both are being fixed in `Interp/SpecEval.lean` (in flight).
- **The binary arm reads the node's line field** (`0x80003524 lw s0,4(s0)`),
  which `ExprReprWithin`'s read set `P` does not cover.

## Done (all in `lake build VsaIris`, no holes)
- Row format, step language, emitter interface (above); `gen_iris_cases.py`
  parses and validates rows (`--list`, `--check`); `emit` is still a stub.
- Symbolic-run layer: `SWP` (H4) over the interpreter as `IW` (`IRun.lean`);
  generated step table `Steps/Part00-10.lean` (`scripts/gen_interp_steps.py`,
  one lemma per instruction: `it_`/`itD_`/`itT_`/`itH_`/`jalx_`), the jump
  tables' values (`interpRO_lw_<addr>`, macro `ix_tab`), havoc loads of
  unowned bytes (`swp_havocD`, `fuel_unif`, `SymData.lean`).
- `ix_run h [using [facts]] [at pc…]` (`ITac.lean`) runs `eval_expr`'s binary
  arm end to end: prologue, kind dispatch, operator table, int/int checks.
  `#ix_seg name binders : goal by ix_run …` turns ONE run into ONE lemma whose
  statement ends in the computed end state (own declaration, own elaboration
  budget, small context; the `?`-hole / `have` approach does not work and a
  whole arm in one declaration exceeds the default heartbeats).
- `Interp/SpecEval.lean`: `eval_expr`'s statement (see INTERP_DESIGN.md §10
  "STATEMENT CHANGES (G)"): `regFile rv` + `EvalRegs`/`KeepRegs`, `codeRes`,
  `astEG`, `StackGeom`/`SlotGeom`, `evalPre`/`evalPost`, `evalSpecT_body`,
  `helperSpec`, `valueIntSpec` (stub for H2).
- `Interp/Arm.lean`, the arm layer: `ms pc R S Mt` (machine state of an arm),
  `wp_swpF`/`swp_closeF` (a run in continuation form; the frame is `let`-bound
  so the run's `simp … at *` cannot rewrite it), `ms_callEvalT` (child call,
  slot carved/joined, result as `slotWrite` + `□ valOf`), `ms_callHelper`,
  `ms_intro`/`ms_exit`, `roOwn_data` (AST view), `BinNode`/`binNode_of_repr`,
  `evalCallGeom`, the `ldvf_*_imgLE` load calculus, `ix_mem` forwarding.

## In flight
Hand-written `BinaryAddInt` total case (scratch draft; runs 1 and the left
call done in IPM glue). Next: runs 2-4 as `#ix_seg` lemmas with facts as
binders, the right call, the `value_int` call, the exit into `evalPost`;
then the partial twin, then `emit_total`/`emit_partial` and the drift gate.

## Pitfalls found
- `omega` on goals containing `2^64 - c` (`BitVec.toNat_sub` of a literal)
  produces a proof the kernel rejects after 2 min ("deep recursion"); use
  `toNat_sub_frame` / `evalSP_eq`.
- `simp … at *` inside a run rewrites everything in the goal, including an
  Iris frame carried in the post (`ra` became `1`): keep frames opaque.

## Next (exact plan for the resuming session)
1. **Exercise `ix_run`** on run 1 of `BinaryAddInt` (0x80003164 → jal
   0x800034f8): state `IW` with `S = InExt (s-1088, 1088)` (the frame),
   `Dt`/`DA` = the AST view `m` of `astE aX e` on the node's covered bytes;
   facts to feed `sx_side` via `macro_rules`: `ldv .lw m aX = 6`,
   `ldv .ld m (aX+16) = pl` (from `ExprReprWithin.binary`, `ldv_ld`).
2. **Havoc load** (`swp_havoc`, SymData): `0x80003524 lw s0,4(s0)` reads the
   node's line field, which `P` does not cover. Prove a SegFrom step directly
   (choose `lds` from the state's own bytes; `seg_runFact` then gives the step);
   continuation `∀ v, SWP … (upd R 8 v)`, uniform fuel via a finite-sup lemma
   over `BitVec 64` (no Mathlib: induction on `toNat` bound). Generate
   `itH_<pc>` for loads; driver tries it last.
3. **`VsaIris/Interp/SpecEval.lean`** (statement only; `Specs.lean` imports
   it and keeps its sorries). Changes vs `Specs.lean` §D, to record in
   INTERP_DESIGN.md §10: ABI `a0=sret a1=in a2=e a3=env`; registers as one
   valuation `regFile rv` (all GPRs but PC/ra/gp/tp) with pure pins, post
   `∃ rv'` agreeing on s-regs+sp; `□ sepL interpText (↦ₘ□)` + `InterpLive
   live` in the pre; AST predicate `astEG` = `astE` plus `∀ k, P k → RAM ∧ off
   tohost` (a projection to `astE`, A0 supplies it from `ast_readable`);
   stack/slot geometry as named structures; `M := vsaModel live`.
4. **Arm layer** `VsaIris/Interp/Arm.lean`: `wp_swpW` (run an `IW` goal whose
   Q is `Matches pcf Rf Mtf`, symbolic in and out, over `wp_localRunW`);
   `toMem`/`patch` images with `imgM` lemmas; slot carve/join between the
   frame `ownImg` and `slot24`/`valAt`; `ldvf .lw/.ld` ↔ `imgW` bridges for
   `valOf`; child-call step over `wp_callArmW`/`wp_callArmAbort`; helper-call
   step over `wp_callW` + `fnSpecAbort_of_fnSpecW`.
5. **Hand-write `BinaryAddInt` total** (runs: 0x80003164→0x800034f8,
   0x800034fc→0x80003518, 0x8000351c→0x800038d4 (jump table op 11 →
   0x80003888), 0x800038d8→ret via `j 0x800033ec`; helper `value_int`
   0x8000280c: `sw 2,0(a0); sd a1,8(a0)`, clobbers a5 — state its stub
   `fnSpecW` in a spec file), then the partial twin; then turn both into
   `emit_total`/`emit_partial` in `gen_iris_cases.py`, regenerate, add the
   `--check` drift gate to `scripts/check_all.sh` stage a3 (and
   `gen_interp_steps.py --check`).
6. `seqLoop (site)` for the block arm / closure body / `interp_run` loop.

## Holes
None added. `python3 scripts/check_iris_holes.py` passes.
