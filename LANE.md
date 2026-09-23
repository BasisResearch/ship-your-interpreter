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

## In flight
- `VsaIris/Interp/SpecEval.lean`: the statement-only spec module (xv6iris
  `Spec<F>` shape), with the ABI fix.
- The arm layer (frame, prologue/epilogue, child/helper call steps).
- The symbolic step table for `eval_expr`/`exec_stmt` (reusing lane H4's
  `SWP` layer).
- Emitters, the `BinaryAddInt` worked example in both modes, `seqLoop`.

## Holes
None added.
