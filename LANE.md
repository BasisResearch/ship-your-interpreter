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
| `family` | the case template `scripts/iris_arms/templates/<family>_<T\|P>.lean` and its `key=value` parameters (addition, optional) | `binInt op=.add mop=+ wrap=toInt_add_wrap tok=11` |

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
text = emit(arm, "T"|"P")   # Lean source of one case: the family template, filled
write_all(check=False)      # regenerate; check=True is the drift gate
FAMILIES[name] = subst_fn   # a family: row -> {PLACEHOLDER: text}
```

A family is a template (a proved case with `{PLACEHOLDER}`s, e.g.
`templates/binInt_T.lean`, extracted from the hand-proved worked example) and a
substitution function in `gen_iris_cases.py` that reads the row. A new arm
shape is a new family: prove one instance by hand with the tools below, turn
it into a template, register it. Rows of an existing family are one TSV line.

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
- **The worked example in both modes, from generated output** (family
  `binInt`, rows `BinaryAddInt` and `BinarySubInt` of `arms.tsv`):
  `Case/BinaryAddIntT.lean` (`caseT_BinaryAddInt`: total, derivation-indexed,
  children's `evalSpecT_body` and `valueIntSpec` as hypotheses) and
  `Case/BinaryAddIntP.lean` (`caseP_BinaryAddInt`: partial, from the Löb
  hypothesis `evalSpecsP`; the other-kinds branch exported as `hx_1`), and the
  same two for `-`. Axioms ⊆ {propext, Classical.choice, Quot.sound}. Drift
  gate: `check_all.sh` stage a3 runs `gen_interp_steps.py --check` and
  `gen_iris_cases.py --check`.
- Partial-mode layer: `evalSpecP_body`/`evalSpecsP` (SpecEval), `ms_callEvalP`
  (Löb call; abort rebased by rebuilding the frame, the child's slot handed
  back), `valOf_tag`, `#ix_piece` with several leftovers, `#ix_chain` exports,
  `#ix_piece … from p at k` (continue an exported branch).
- Symbolic runs: `IW`/`SWP` over the generated step table (`Steps/*`,
  `it_`/`itD_`/`itT_`/`itH_`/`jalx_` per instruction), jump-table values,
  havoc loads (`swp_havocD`); driver `ix_run h [using [facts]] [at pc…]`.
- Proof steps as declarations (`ITac.lean`): `#ix_seg` (one run → one lemma
  ending in the computed end state), `#ix_piece … [from prev]` (any proof step;
  its one leftover goal, with every local, becomes the lemma's hypothesis),
  `#ix_chain` (assemble). A whole arm in one declaration exceeds the default
  heartbeats; pieces keep each step within budget without writing any
  intermediate state by hand.
- `Interp/SpecEval.lean` (statement; INTERP_DESIGN.md §10 "STATEMENT CHANGES
  (G)"), `Interp/Arm.lean` (the arm layer): `ms`, `wp_swpF`/`swp_closeF`/
  `swp_closeM`, `ms_callEvalT`, `ms_callHelper`, `ms_intro`/`ms_exit`,
  `evalFrame_join`, `roOwn_data`, `BinNode`, `evalCallGeom`, `evalSP_off`,
  the seam invariant `EvalSaved` (+ `ix_saved`), `ix_reg`/`ix_keep`/`ix_fwd`.

## Recipe for a new family (E lanes)
1. Write the runs as `#ix_seg` lemmas with the facts they need as binders
   (register pins, data-view reads from the node facts, frame reads); iterate
   on the error `#ix_seg` prints (the stuck goals).
2. Write the glue as `#ix_piece`s split at calls: `wp_swpF` + the run lemma
   (`refine … ?_` then prove the facts: `ix_keep [keeps…]`, `ix_fwd`,
   `EvalSaved` fields) + `swp_closeM` + the call step; `#ix_chain` at the end.
3. Replace the row-specific literals by `{PLACEHOLDER}`s, save as
   `templates/<family>_T.lean`, add `FAMILIES[<family>]`, add the rows.

## Next
- The exported other-kinds branch of the binary arms is the concat and
  type-error rows' starting point (`#ix_piece … from BinaryAddIntP_p2 at 2`);
  their families (and `*` through `__muldi3`, `/`, `%`) are E-lane work on
  this layer. `runtime_error`'s spec is H5's; a stub is not in the tree.
- `exec_stmt`'s spec statement (`execSpecT/P_body`) beside `evalSpec*` in
  SpecEval, and `seqLoop` for the three statement-sequence sites.

## Holes
None added. `python3 scripts/check_iris_holes.py` passes.
