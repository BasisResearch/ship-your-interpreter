# Wave 43 — layoutgen: jump-table slot-pin generator + fn arm-site supplier

Plan queue item 5, two legs. HEAD 73864f7 (wave 42).

## Leg 1 — EXPONENTIATING: gen_layout.py emits ALL 11 dispatch slot pins

Extended `scripts/gen_layout.py` to read the `eval_expr` `.rodata` jump table
(base `0x80019f58`) out of the ELF (`objdump -s --section=.rodata`) and emit ONE
`EvalSimCommon.KindSlotPinned k armPC m` theorem per `ExprKind` tag (`c/src/ast.h`
enum = 11 tags, 0..10) into a NEW generated file
`Vsa/Sim/rows/LayoutJumpTableGen.lean` (`groundSlot_0 … groundSlot_10`).

Slot table read from the fixed ELF (tag, name, slot addr, LE bytes, arm PC):

```
 0 EX_INT     0x80019f58  b0 94 fe ff  0x80003408
 1 EX_STR     0x80019f5c  bc 94 fe ff  0x80003414
 2 EX_BOOL    0x80019f60  c8 94 fe ff  0x80003420
 3 EX_NULL    0x80019f64  d4 94 fe ff  0x8000342c
 4 EX_VAR     0x80019f68  dc 94 fe ff  0x80003434
 5 EX_ASSIGN  0x80019f6c  24 95 fe ff  0x8000347c
 6 EX_BINARY  0x80019f70  90 95 fe ff  0x800034e8
 7 EX_LOGICAL 0x80019f74  04 96 fe ff  0x8000355c
 8 EX_UNARY   0x80019f78  88 96 fe ff  0x800035e0
 9 EX_CALL    0x80019f7c  58 92 fe ff  0x800031b0
10 EX_FN      0x80019f80  6c 94 fe ff  0x800033c4   <- the leg-2 target
```

Each `groundSlot_k` takes 4 byte pins as premises and produces
`KindSlotPinned k armPC m` with the sign-extended reassembly
`0x80019f58 + (Int32)offset = armPC` closed by `decide` (the `int_slot_kindPinned`
idiom). Two previously-UNPINNED tags now covered: slot 5 (EX_ASSIGN→0x8000347c)
and slot 6 (EX_BINARY→0x800034e8).

SELF-VERIFYING (both known generator bug classes hard-error):
- refactored the mandatory self-verify into `self_verify(path, content)`, run on
  BOTH generated files (LayoutGround + LayoutJumpTableGen): `lake env lean` +
  `sorryAx` grep (false-decide class) + axiom-audit count match + axiom ⊆
  {propext, Classical.choice, Quot.sound}.
- `read_jump_table` hard-aborts on an ABSENT slot byte (zero-pinned-lds class).
- CROSS-CHECK: the 9 arm PCs already pinned in the proof
  (int/str/bool/null/var/logical/unary/call/fn = `EXPECTED_ARM_PC`) are re-derived
  from the freshly-read bytes and compared; a drift (ELF change or bad read)
  hard-aborts. VERIFIED the abort fires (corrupted anchor → SystemExit).

Run output: both files self-verify OK (10 + 11 axiom audits, no sorryAx),
idempotent (unchanged on re-run).

## Leg 2 — fn arm-site supplier: NEW `Vsa/Sim/rows/FnArmSeamSupply.lean`

The three FnArm seam bundles (`AllocBuildStagingLink`/`AllocBuildTailFacts`/
`AllocBuildReloadPost`) are ALREADY landed in `rows/FnArmSeams.lean` (wave 39) as
named-field structures, with `staging_of_link`/`allocBuildEntry_tail`/
`fnArmSeamRun_of_seams` closing the seams MODULO them. Per the wave-40 analysis
they are the IRREDUCIBLE off-path machine residuals (arm-front `a3 := φf env`
decode; the `AllocBuildEntry` ~30-field marshalling transported across `malloc`
via `CallSpec.memOut`) — the exact analog of strdup's `StrdupMemcpyContent`
caller-content bundle, which is likewise a NAMED premise (see
`StrdupTailContractClose.lean`), never a theorem. So "the fn bundle suppliers" is
NOT about eliminating those three — it is the arm-site assembly that CONSUMES leg-1
(the slot pin) and threads the seam through, closing `FnResidBundle`/`FnResid`.

Landed (all green + axiom-clean {propext, Classical.choice, Quot.sound}, ~2s):
- `FnSlotBytes m` — named-field predicate = the 4 concrete `EX_FN` slot bytes.
- `fnSlot_grounded : FnSlotBytes m → KindSlotPinned 10 0x800033c4 m` — CONSUMES
  leg-1's `LayoutJumpTableGen.groundSlot_10`. (This is the tag-10 analog of
  `int_slot_kindPinned`, but the bytes come from the ELF via the generator, not
  from `EvalEntry`'s carried `IntSlotPinned`.)
- `FnDispatchLayout` — named-field bundle of the tag-10 dispatch/layout facts
  (`hbytes`/`hkind`/`hexprSurv`/`htableStk`), the EX_FN clone of the leaf-arm
  dispatch shape, with the slot pin GROUNDED.
- `fnResidBundle_of_parts` — assembles `FnResidBundle` from `hAlloc` + `hWF`
  (StoreClosuresBounded) + a per-ghost provider `hSeamPer` (widened map φc',
  ghosts, `calleeLoaded`, PhiExtends/hout, `FnDispatchLayout`, the `FnArmSeamRun`
  seam, `EvalRecWiden`). The 4 `decide`-able perGhost fields (hkle/hklt/hslot/
  harmAl) are discharged here; hslot via `fnSlot_grounded`.
- `fnResid_of_parts` — `FnResid` directly, composing `fnResidBundle_of_parts` with
  `fnResid_from_bundle` (`FnResidSupply`).

### Named residuals (precisely, per Law 2)
Everything reduces into `hSeamPer`'s `FnArmSeamRun` field, which is closed
upstream by EITHER `fnArmSeamRun_of_seams` (modulo the two irreducible seam
bundles `AllocBuildStagingLink` + `AllocBuildTailFacts`, `rows/FnArmSeams`) OR
`fnArmSeamRun_of_allocClosure` (modulo `AllocClosureContract`,
`rows/FnArmSeamReduce`). Those two seam bundles are the irreducible off-path
machine (arm-front decode + AllocBuildEntry marshalling); NOT supplied here by
design (strdup-`StrdupMemcpyContent` precedent), they enter through `hSeamPer`.
`EvalRecWiden` and `StoreClosuresBounded` are the other carried residuals, same
class as every arm.

## FILES
- EDIT: `scripts/gen_layout.py` (+jump-table reader/emitter/cross-check, refactored
  self-verify into `self_verify`; both files self-verify).
- NEW (generated): `Vsa/Sim/rows/LayoutJumpTableGen.lean` (11 `groundSlot_k`).
- NEW: `Vsa/Sim/rows/FnArmSeamSupply.lean` (fn arm-site supplier, 5 defs/thms).
- Discipline: OK on both new .lean files.

## WIRING (report-only, coordinator-owned — NOT applied)
- `Vsa.lean`: add (in dependency order)
  `import Vsa.Sim.rows.LayoutJumpTableGen`
  `import Vsa.Sim.rows.FnArmSeamSupply`  (imports LayoutJumpTableGen + FnResidSupply).
  Then regen the top olean (`lake env lean -o .lake/build/lib/lean/Vsa.olean Vsa.lean`).
- `scripts/check_all.sh` THEOREMS: add
  `Vsa.Sim.LayoutJumpTableGen.groundSlot_0` … `groundSlot_10` (11),
  `Vsa.Sim.fnSlot_grounded`, `Vsa.Sim.fnResidBundle_of_parts`,
  `Vsa.Sim.fnResid_of_parts`.

## OBSERVATIONS / BLOCKERS
- No falsity found. No new lemma-gap: the two seam bundles are genuinely
  irreducible (strdup precedent), correctly kept as named premises inside the
  seam provider.
- Abstraction-table candidate: `gen_layout.py` now also emits the dispatch slot
  pins — add it to CLAUDE.md's "Motive tables / generators" note.
