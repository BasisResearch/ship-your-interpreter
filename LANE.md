# Lane V2: final non-vacuity audit of `endToEnd_refinement`

Branch `lane-v2` (from `hub/iris-main` `905e3735`). Brief: `~/lane-v2-aws.md`.
Report: `REVIEW2.md` (verdict at the top). Tooling: `experiments/review-v2/`.

## Status: done — verdict NOT VACUOUS; two findings (F1 synthetic CSR file in the witness, F2 native ELF/trace links), proposals P8–P11, nothing fixed

## Done

- Task 1: `example : IrisHoles := ⟨⟩`; `ReviewV2.endToEnd_unconditional` with no hypotheses; `#print axioms` on it, all ten `Gen.*.loaded`, the six `*_halts`, `initializeMemory_eq`, `endToEnd_refinement`, `interpSim_iris`: `[propext, Classical.choice, Quot.sound]` (`Audit.lean`); `check_final_axioms.sh` 24/24.
- Task 2: `Replay.lean` — the theorem's own `setupElf`/`stepOnce` from the embedded ELF reproduces the witness memory/registers exactly and halts identically from both states, for all 10 witnesses (proof: 382,730 steps, `55 2500 36`, exit 0; `err_divzero`: exit 70). Kernel corollaries: `Halts cProof "55\n2500\n36\n" 0`, `¬ Halts cProof "" 0`, `¬ Diverges cProof`, clean-halt uniqueness; `err_divzero`/`err_undefined`: no `BigStep`, no clean halt, diverges-or-nonzero. `Halts`/`Diverges`/`output`/`BigStep`/`bootMem` re-stated by `rfl`. `elf_xcheck.py`: `elfHex` = the ELF file; generated image pages = the file's bytes.
- Task 3: every field of `InterpRunPhysicalFacts` (47), `InterpRunReadyFacts` (+4), `BootHeap`/`InitialOwned`/`InitialAllocatorAt`/`HeapAt`/`BootHeapFacts`/`BootFrameChunks`, `GoodState`, `ConsoleBoot`, `ExitRuntimeData`, `LocaleData`, `StderrStream`, `SharedReadWin` tabulated with its generated-proof supplier (REVIEW2.md §3). Synthetic: `GoodState` (F1). By construction: `stack_bytes` (P3). Program-dependent: `capacity`, `stack_admissible` (M1).
- Task 4: 30/35 corpus programs agree between the emulator (rebuilt from this tree, sha-identical to B3's) and the Lean semantics on the AST decoded from the binary's own parser output (Q8 cases included); `err_parse` outside; `recursion`/`adv_big_ok`/`adv_oom_*` not evaluated in Lean.
- Task 5: `lake build Vsa VsaIris VsaIris.Audit VsaBoot` green (2,807 jobs); `check_all.sh --static-only` OK; `check_iris_holes.py` 0 holes; no raised limits in `VsaIris/`/`Vsa/Sim/Boot/`; no forbidden tokens.

## In flight

- Uncapped emulator runs of `adv_oom_term`/`adv_oom_div` (lane V: `out of memory`, exit 1); reported in REVIEW2.md §4 when they finish.

## Holes

None added; `IrisHoles` is empty.

## Next

User decision on P8 (generalise the witness over the reached register file), P9 (re-check the native links per build), P10 (restore `LANES-b1.md`), P11 (docs).
