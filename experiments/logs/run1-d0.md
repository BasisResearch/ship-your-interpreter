# run1-d0 — io-DAG residue MKinds

### 2026-09-01 xor/sll/sllw/srlw/sraw LANDED (5 kinds, mail-merge clone)

Extended the block-reflection MKind decoder with the io-DAG residue
mnemonics. Task asked for `.xor` + `.sllw` mandatory, `sll`/`srlw`/`sraw`
optional-if-identical — they were identical (all five ExecuteAlu
characterizations already existed: `execute_rtype_xor_char`,
`execute_rtype_sll_char`, `execute_rtypew_sllw_char`,
`execute_rtypew_srlw_char`, `execute_rtypew_sraw_char`), so all five landed.

Clone sources: `.xor` ← `.or` (RTYPE), `.sll` ← `.srl` (RTYPE shift),
`.sllw`/`.srlw`/`.sraw` ← `.subw` (RTYPEW, sign_extend of 32-bit op; word
shifts take the extra inner `extractLsb (extractLsb v2 31 0) 4 0` shamt from
the char lemma statements). All ALU rd-writers — no store widths touched, so
the `wentry-width-set-hardcoded` obstruction (observations.md) is NOT
triggered; no files beyond the standard 4-file chain needed edits.

Files touched (the standard MKind 4-file chain, same site list as wave-45
mkind-lwu / the D0 part-1/2 passes):

- `Vsa/Sim/BlockMem.lean` — MKind constructors (5), astOfM arms
  (RTYPE XOR/SLL, RTYPEW SLLW/SRLW/SRAW), wvalM arms, MemFacts True-arm
  patterns, KindOK 3-conjunct group line, instDecKindOK (5), and five
  template-generated `block_mem_run` arms (appended after `lhu`).
- `Vsa/Sim/BlockDecode.lean` — decodeM: opcode 0x33 funct3=4 (xor) /
  funct3=1 (sll), both funct7-guarded on 0x00; opcode 0x3b funct3=1 (sllw,
  funct7 0x00) and funct3=5 (srlw 0x00 / sraw 0x20). Five real-word
  `mkLine` rfl smoke examples from the proof binary
  (xor@0x80006bc8 0x00a5c7b3, sll@0x80004948 0x00661633,
  sllw@0x80007138 0x008a973b, srlw@0x80010c70 0x00fad53b,
  sraw@0x80013a40 0x40f757bb).
- `Vsa/Sim/BlockTerm.lean` — one arm each in `domRun_keys_bt`,
  `keysOK_runGM_bt`, `writeLog_wlog_low_bt`.
- `Vsa/Sim/LoopStep.lean` — one arm each in `wlogM_width`.

Verification:
- `lake env lean` green on all four files: BlockMem 4.7s, BlockTerm 1.5s,
  BlockDecode 0.9s (incl. the 5 rfl smoke examples), LoopStep 1.4s.
- olean regen in dependency order via `lake env lean -o`:
  BlockMem → BlockTerm → BlockDecode → LoopStep
  (intermediates like SegEval/BlockAdapter unchanged — additive
  interface-compatible constructors, same as prior D0 passes).
- Axiom probe (scratch /tmp): `block_mem_run`/`block_mem_sound`/
  `domRun_keys_bt`/`keysOK_runGM_bt`/`writeLog_wlog_low_bt` all ⊆
  {propext, Classical.choice, Quot.sound}. Scratch decodeM probes for all
  five real words + astOfM RTYPE-XOR AST check, all `rfl`.
- Downstream consumers green against regenerated oleans:
  `Vsa/Sim/EnvDefSeg.lean` (the #derive_case canary, 1.7s, axiom-clean) and
  `Vsa/Sim/rows/FnWriteFold.lean` (whole-function fold layer, 1.6s,
  `write_summary` axiom-clean).
- `scripts/check_discipline.py`: OK (9 rules).

No heartbeat/timeout bumps, no sorry/axiom, no surprises → no new
observations.md entry.
