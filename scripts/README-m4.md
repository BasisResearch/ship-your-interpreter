# M4 case-emitter scaffolding (`gen_m4_case.py` + `m4_cases.tsv`)

Milestone M4 is the mutual induction over the ~40 big-step `EvalE`/`ExecS`
constructors. Five leaf cases are PROVEN end-to-end
(`EvalIntSim*.lean`, `EvalNullSim.lean`, `EvalBoolSim.lean`, `EvalStrSim.lean`,
`EvalVarSim.lean`), all built from the shared machinery in
`EvalSimCommon.lean` (`blockA_k` prologue+dispatch, `ArmEntryK`, `armTail_v`,
`PreEpilogueV`, `blockD_v`, `KindSlotPinned`, jump table @ `0x80019f58`).
This directory holds the ground-truth parameter table for those cases and an
emitter that generates the fixed scaffolding of a new case file.

## The common shape (reverse-engineered from EvalNullSim vs EvalBoolSim)

Every leaf case file has the same section skeleton:

1. **Arm sites** — `jal <value_*>` and `j 0x800033ec` step lemmas
   (`site_<pc>_ee`), plus an optional payload-load site (`ld`/`lw a1,8(a2)`).
   *Fully mechanical*: pc, 32-bit word, LE bytes, imm, `decode_<word>`,
   `eval_expr_at_<pc>` are the only parameters.
2. **`loaded_<case>_writeMap8`** — callee-code survival under a stack spill.
   Statement mechanical (code range); body unfolds the per-callee chunk defs.
3. **`value_<case>_spec_full`** — the strengthened callee spec (base
   `ValueSpec` post + console-output invariance + sret memory frame).
   Statement mechanical; body re-runs the callee's instructions (3 for null,
   5 for bool, 4 for str) — the dominant per-case proof work.
4. **`blockC_<case>`** — `ArmEntryK → PreEpilogueV`. Three styles:
   * `armTail` (null): no payload; the whole block is one `armTail_v`
     instantiation — *fully mechanical*.
   * `payload_then_armTail` (str): payload `ld`, then `armTail_v` from the jal
     PC; the payload-value bridge is per-case.
   * `inline_tail` (int, bool): payload load + hand-inlined jal/callee/j
     (~150 lines, historical — new cases should prefer `armTail_v`).
   * `custom_inlined_epilogue` (var): own 18-instruction arm incl. inlined
     epilogue, reaches `EvalExit` directly (no `blockD_v`).
5. **`<Case>SlotPinned` + `<case>_slot_kindPinned`** — jump-table slot pin at
   `jumpTableBase + 4k`. *Fully mechanical* given the 4 slot bytes.
6. **`Eval<Case>Entry`** — the entry structure: ~30 fields shared verbatim,
   3 fields per-case (the `ExprRepr` payload, the slot pin, the callee-code
   predicate + its two disjointness ranges).
7. **`exprRepr_<case>_kind`** — kind-tag inversion (per-case constructor names).
8. **`Eval<Case>SimGoal` + `eval<Case>Sim`** — the ∀-goal and the
   `blockA_k ≫ blockC ≫ blockD_v` composition. Mechanical except two lambdas:
   `hcalleeSurv` (discharged by `loaded_<case>_writeMap8`) and `hexprSurv`
   (kind-word survival is a fixed template; payload/CString survival per-case).

## `m4_cases.tsv` columns

One row per proven case (`int`, `str`, `bool`, `null`, `var`); future cases
extend the table. Columns:

| column | meaning |
|---|---|
| `case` | short name (`null`, …) |
| `evale_ctor` | big-step constructor (`EvalE.null`) |
| `value_binders` | extra ∀-bound value vars (`b:Bool`, `-` if none) |
| `value_expr` | produced `Value` term (`.bool b`) |
| `tag` | `ExprKind` jump-table tag (int 0, str 1, bool 2, null 3, var 4) |
| `arm_pc` | jump-table landing PC of the arm |
| `payload_insn`/`payload_word`/`payload_site` | payload load (`ld`/`lw`/`-`), its encoding, its site lemma |
| `jal_pc`/`jal_word`/`jal_imm` | the `jal <callee>` site |
| `j_pc`/`j_word`/`j_imm` | the `j 0x800033ec` site (`-` for var) |
| `callee`/`callee_entry`/`callee_code_lo`/`callee_code_hi` | callee symbol, entry PC, code range |
| `callee_loaded` | callee code-pin predicate (`Value_nullLoaded`) |
| `slot_bytes` | 4 LE bytes of the jump-table slot (`d4:94:fe:ff`) |
| `slot_def`/`slot_thm` | slot-pin def + `KindSlotPinned` bridge |
| `entry_struct`/`spec_full`/`blockC`/`blockC_style`/`epilogue` | per-case decl names + block-C/epilogue style |
| `goal_def`/`theorem`/`spec_file` | goal def, gate theorem, source file |
| `base_import`/`decode_imports` | the file's import row |

## Acceptance: emitted `null` skeleton vs the real `EvalNullSim.lean`

```
python3 scripts/gen_m4_case.py null -o /tmp/EvalNullSim.gen.lean
```

Diff (whitespace-normalized exact line matches, `difflib`):

* real file: **394 lines** (370 non-empty); emitted skeleton: **323 lines**,
  6 `PER-CASE` holes.
* **250/394 = 63.5%** of the real file's lines are reproduced exactly by the
  scaffold (61.9% of non-empty lines). The two arm sites, `blockC_null`
  (the full `armTail_v` instantiation, including all five target-arithmetic
  side goals and the ArmEntryK repack), `NullSlotPinned` + its bridge, the
  entry structure, the goal, and the whole `evalNullSim` composition (except
  one lambda) are emitted byte-for-byte.
* The non-matching 144 lines decompose as:
  * **~65 lines** — `value_null_spec_full`'s body (the callee re-run):
    genuinely per-case, emitted as a described hole.
  * **~10 lines** — the `hexprSurv` lambda body in `evalNullSim` (kind-word
    survival; the template is given in the hole comment).
  * **~3 lines** — `exprRepr_null_kind`'s `cases` body.
  * **~45 lines** — docstring prose + deliberate genericizations: the emitter
    names the per-case entry fields uniformly (`callee_code`,
    `sret_vcalleecode_disjoint`, `vcalleecode_stack_disjoint`, hypothesis
    `hsret_vcallee`) where the real files use per-case names
    (`value_null_code`, `sret_vnullcode_disjoint`, …), and the emitter also
    emits a `loaded_null_writeMap8` statement that the real null file inherits
    from elsewhere. These lines are equivalent in content, not in text.

So in content terms: **~78% of the null case is scaffolding** (everything but
the callee re-run, the ExprRepr survival/inversion, and the writeMap8 chunk
unfold), and the emitter generates all of it from one TSV row. Sanity runs on
the other styles: `bool` → 326 lines / 8 holes (payload site + inlined tail
holes), `var` → 282 lines / 8 holes (custom arm; slot/entry/goal scaffolding
still emitted).

## Residual per-case work (what a human/agent fills per new case)

1. **TSV row data** — decode the arm from the ELF: arm PC, instruction words,
   jal/j immediates, callee entry + code range, jump-table slot bytes
   (`gen_decode_index.py` + the byte pins in `Vsa/Sim/Code/`), and the needed
   `DecodeTable.Batch*` imports; add `eval_expr_at_<pc>` pin lemmas if the arm
   PCs are new.
2. **`value_<case>_spec_full` body** — re-run the callee instruction-by-
   instruction over its site battery (the per-site lemmas must exist in
   `ValueSites`/`ValueSpec`, as for the four `value_*` callees). Dominant cost;
   scales with callee length.
3. **`loaded_<case>_writeMap8` body** — mechanical chunk unfold + one
   `refine ⟨?_,…⟩ <;> rw [getElem_writeMap8_disjoint …]` (arity = pinned bytes).
4. **Payload handling** (if the arm has a payload load): the payload site body
   (`exec_ld`/`exec_lw` instantiation), the payload-value bridge
   (e.g. `sext32_ne_zero` for bool, `exprRepr_str_pay64`/CString for str), the
   payload-survival part of `hexprSurv`, and any extra entry fields
   (str/var-style `*_stack_disjoint` geometry for pointer payloads).
5. **`exprRepr_<case>_kind`** — one-to-three-line constructor inversion.
6. **Non-leaf cases** (the actual M4 frontier): the recursive premises enter
   through the arm as sub-calls to `eval_expr` itself — the `blockC` hole then
   composes the induction hypothesis instead of a `value_*_spec_full`; the
   scaffold's site/slot/entry/goal sections still apply unchanged, but the
   `armTail_v` shape does not (the callee is `eval_expr`, whose post is
   `EvalExit`, not the `value_*` post). Expect `blockC` to stay hand-written
   for recursive cases until an `armTail`-analogue for `EvalExit`-shaped
   callees is proven.

Note: the emitted skeletons contain `sorry` holes by design and MUST NOT be
landed in `Vsa/` (repo rule: no `sorry` in landed files). The emitter and this
table are the deliverable; the skeleton is the starting point per case.
