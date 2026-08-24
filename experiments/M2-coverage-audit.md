# M2 coverage audit (2026-08-23)

Scope check of the Layer-0 instruction battery against the fixed binary
`while-riscv-htif.elf`, per PLAN-InterpSim.md M2: decode table + instruction
classes + HTIF lemmas.

## Decode table — COMPLETE, exact

- Reachable instruction words (from `interp_run` call-graph closure,
  `experiments/reachable_words.txt`): **8,187**.
- Decode lemmas in `Vsa/Sim/DecodeTable/Batch01–16.lean`: **8,187**,
  set-equal to the reachable words (no gaps, no extras; verified by
  name extraction `decode_<word>` vs the word list).
- The census total (10,399 unique words, `disasm_census.json`) counts all
  257 functions in the binary; the 2,212-word difference is code
  unreachable from `interp_run` (lexer/parser/libc startup), which
  PLAN-InterpSim.md explicitly places outside the proof scope.
- All 16 batches build kernel-clean (`/tmp/interpsim_batches.log`,
  `ALL_BATCHES_DONE`).

## Mnemonic classes over the reachable words (65 mnemonics, 5 classes)

| Class | words | execute lemmas | step lemmas |
|---|---|---|---|
| ALU | 3,019 | `ExecuteAlu.lean`: ITYPE ×6, RTYPE ×10, RTYPEW ×5, SHIFTIOP ×3, SHIFTIWOP ×3, ADDIW, LUI, AUIPC — all present | `StepAlu.lean` generic `try_step_alu`/`step_alu_{notick,tick}` over abstract `hexec` (single-rd-insert shape) |
| BRANCH | 1,787 | `ExecuteBranch.lean`: beq/bne/blt/bge/bltu taken+nottaken; **bgeu taken+nottaken in `StepBeq.lean`** (pilot file) | `StepBranch.lean` generic over op: taken/nottaken × notick/tick at try_step/stepOnce/Step levels |
| JUMP | 1,496 | `ExecuteJump.lean`: jal/jalr + x0 pseudo forms (j/jr/ret) | `StepJump.lean`: all forms × notick/tick |
| LOAD | 943 | `ExecuteLoad.lean`: width-generic `vmem_read_addr_data_w` + `execute_load_char` (+signed/unsigned corollaries) — covers lbu/lh/lhu/lw/lwu/ld | reuses `StepAlu` generics (single-rd-insert shape); `DemoLoad.lean` = the StepLoad stand-in |
| STORE | 942 | `MemStore.lean` generic `vmem_write_addr_w` + `ExecuteStore.lean` single width-generic `execute_STORE_char` — covers sb/sh/sw/sd | `StepStore.lean` generic `try_step_store`/`step_store_{notick,tick}` over abstract mem post-state |

Pseudo-instructions in the census (li, mv, neg(w), not, seqz/snez/sgtz,
sext.w, zext.b, beqz/bnez/bgez/bgtz/blez/bltz, j/jr/ret) all decode to the
underlying covered ops; the decode table works per concrete word, so no
separate treatment is needed.

No csr/fence/ecall/ebreak/amo/M-extension words are reachable (soft
mul/div via libgcc `__muldi3`/`__divdi3` are ordinary ALU/branch loops).

## HTIF — COMPLETE

`Htif.lean`: `htif_store_putchar` (console write appends one char to
`sailOutput`) and `htif_store_exit` (`(e <<< 1) ||| 1` sets
`htif_done`/exit code) + payload lemmas, verified.

## M2 gate — PASSED (2026-08-23)

All classes verified kernel-clean, plus two end-to-end composability
demos proving the whole stack composes per class:

- `DemoStore.lean`: `step_store_sd_x11_x2_notick` for word `0x00b13423`
  (`sd x11, 8(x2)`) — decode table → `execute_STORE_char` →
  `vmem_write_addr_8` → `try_step_store` → `Machine.Step` + `GoodState`.
- `DemoLoad.lean`: `step_load_ld_x11_x2_notick` for word `0x00813583`
  (`ld x11, 8(x2)`) — decode table → `execute_load_signed_char` →
  `vmem_read_data_eight` → generic `step_alu_notick` (no LOAD-specific
  step lemmas exist or are needed).

CI gates: no `sorry`/`axiom`/`native_decide`/`bv_decide` anywhere under
`Vsa/` (comment mentions only); aggregate `lake build Vsa` passes
(190 jobs); `#print axioms` on the demo theorems, the Triple loop rule,
and a decode lemma shows only `propext`/`Classical.choice`/`Quot.sound`
(`experiments/M2_axiom_audit.lean`).
