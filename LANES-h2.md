# Lane E2: the binary operators

Branch `lane-e2` (from `wave4-base`), pushed to `hub`. Design:
`VsaIris/INTERP_DESIGN.md` §4, §6, §8 (family E2); statement changes in §10
"STATEMENT CHANGES (E2)" (to be written with the P family). Rows:
`scripts/iris_arms/arms.d/e2-binary.tsv`; families:
`scripts/iris_arms/families/e2_binary.py`; templates `scripts/iris_arms/templates/`.

## Done

- **Total cases, integer comparisons** (`<`, `<=`, `>`, `>=`): `caseT_BinaryLtInt`,
  `caseT_BinaryLeInt`, `caseT_BinaryGtInt`, `caseT_BinaryGeInt`
  (`Case/Binary{Lt,Le,Gt,Ge}IntT.lean`, family `binOne`, generated). They reuse lane G's
  prologue runs (`BinaryAddIntT_run1`/`_run2`). The comparison tail's bit is read as the
  source's `decide` by `cmp_*_bit` (`BinArm.lean`).
- **`value_kind_name`** (`0x800029c8`): `valueKindNameSpec` (`SpecErr.lean`) and
  `valueKindName_spec` (`ProofValueKindName.lean`). The slot is lent at its tracked bytes;
  only the kind word is read.
- **The error-arm layer for `eval_expr`** (`SpecErr.lean`, `ErrArm.lean`), for all E lanes:
  - `errCtx inp` (persistent: `binImg` + the `jmp_buf` read-only with its `ra` word
    aligned) and `ErrEnv` (pure: `NewlibHoles`, `CodeLive`, `InpGeom`, `inp < 2^64`,
    `CoreOK Core`). `coreOK_top`: the whole stack's `abortCore` is a valid `Core`.
  - `ms_rtErrEval`: `jal runtime_error` from an eval arm at `sp = s - 1088` ends in the
    arm's `abortAt Core s n`.
  - `ms_callKindName`: `value_kind_name` on the slot a run stored.
  - Messages: `operand_fmt` (`"operand of '%s' must be an int, got %s"`), `kindName_cstr`,
    `rodata_cstr`/`rodata_cstrV`, `readable_rodata_fmt`; `evalNeed_binary_rtErr`.
- **Generator additions** (additions only; G's arms regenerate identically):
  - `gen_interp_steps.py`: `value_kind_name`, libgcc `__muldi3`/`__divdi3`/`__moddi3`
    (+ `__hidden___udivdi3`, `__umoddi3`) and the kind-name / comparison-name tables
    (`CSWTCH.18`, `CSWTCH.25`); one membership lemma per loaded table word
    (`interpRO_acc{w}_{addr}`, used by `ix_ro`).
  - `gen_iris_cases.py`: per-lane family modules `scripts/iris_arms/families/*.py`
    (`FAMILIES_EXT`), so lanes do not edit the shared file.
  - Run split points: `run <from> <to> @pc …` (family `binOne`): the run is a chain of
    `#ix_seg`/`#ix_piece`s joined by `#ix_tree`, each within the elaboration budget.
- **`#ix_tree`** (`ITacTree.lean`): a proof from a TREE of pieces (the binary arm's rows
  after one shared prefix); `#ix_chain` is the linear case.
- **`ix_run` side conditions** (`BinArm.lean`): `ix_ro` (table membership by the generated
  lemma, no list walk), `ix_absurd` (a branch on a value's kind decided by the row's kind
  fact `kL ≠ 2#64` in the context; no decision procedure runs).

## In flight

- Partial cases per operator, closed (no exported branches): `caseP_BinarySub` is proved in
  scratch (int row + both type-error rows through `runtime_error`), being turned into the
  `binP` family (templates + generator) for `-`, `*`, `/`, `%`, the comparisons, `+`.
- libgcc `__muldi3`/`__divdi3`/`__moddi3` helper specs (loops, fuel induction).
- `==`/`!=` (`value_equal` + `value_bool`), string comparisons (`strcmp`), concatenation.

## Findings (for the other E lanes)

- **An eval error arm needs `errCtx inp` and `ErrEnv`**, not in `evalPre`: `binImg` (for
  `runtime_error`'s `callFrame` and the format strings) and the `jmp_buf`'s aligned `ra`
  (`rtErr_spec`'s `hjb`); `world` has the `jmp_buf` but not the alignment. The partial
  cases take `evalSpecsP … Core ∗ errCtx inp ⊢ evalSpecP_body …`; package A supplies
  `errCtx` after `interp_run`'s `setjmp`. Q7 does not bite the binary arm: below its frame
  there are at least 2176 bytes (`evalNeed_binary_rtErr`).
- **Heartbeat hazards in `ix_run`/`ix_fwd`**: the `.rodata` table membership `decide` walks
  the whole list (fixed by `ix_ro`); `ix_fwd using […]` simps with every hypothesis (`*`),
  and `sx_addr` simps `at *`: clear the big memory equations (`hMt*`) before forwarding.
  An `exact` inside an `sx_side` rule can "succeed" by error recovery: use tactics that
  fail cleanly.

## Holes

None added. `python3 scripts/check_iris_holes.py` passes.

## Line counts (generated vs hand)

| file | lines | kind |
|---|---|---|
| `Case/Binary{Lt,Le,Gt,Ge}IntT.lean` | 4 × 283 | generated |
| `BinArm.lean`, `ITacTree.lean`, `SpecErr.lean`, `ErrArm.lean`, `ProofValueKindName.lean` | see `wc -l` | hand |
