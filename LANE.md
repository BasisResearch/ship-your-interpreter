# Lane V2: final non-vacuity audit of `endToEnd_refinement`

Branch `lane-v2` (from `hub/iris-main` `905e3735`). Brief: `~/lane-v2-aws.md`.
Report: `REVIEW2.md` (verdict at the top). Tooling: `experiments/review-v2/`.

## Status: done — verdict NOT VACUOUS; follow-ups P8 (witness at any entry configuration), P9 (replay in check_all stage c3, axiom audit extended, README), P10 (LANES-b1.md) landed on the user's approval; build green, axioms standard, IrisHoles empty

## Done

- Task 1: `example : IrisHoles := ⟨⟩`; `ReviewV2.endToEnd_unconditional` with no hypotheses; `#print axioms` on it, all ten `Gen.*.loaded`, the six `*_halts`, `initializeMemory_eq`, `endToEnd_refinement`, `interpSim_iris`: `[propext, Classical.choice, Quot.sound]` (`Audit.lean`); `check_final_axioms.sh` 24/24.
- Task 2: `Replay.lean` — the theorem's own `setupElf`/`stepOnce` from the embedded ELF reproduces the witness memory/registers exactly and halts identically from both states, for all 10 witnesses (proof: 382,730 steps, `55 2500 36`, exit 0; `err_divzero`: exit 70). Kernel corollaries: `Halts cProof "55\n2500\n36\n" 0`, `¬ Halts cProof "" 0`, `¬ Diverges cProof`, clean-halt uniqueness; `err_divzero`/`err_undefined`: no `BigStep`, no clean halt, diverges-or-nonzero. `Halts`/`Diverges`/`output`/`BigStep`/`bootMem` re-stated by `rfl`. `elf_xcheck.py`: `elfHex` = the ELF file; generated image pages = the file's bytes.
- Task 3: every field of `InterpRunPhysicalFacts` (46), `InterpRunReadyFacts` (+4), `BootHeap`/`InitialOwned`/`InitialAllocatorAt`/`HeapAt`/`BootHeapFacts`/`BootFrameChunks`, `GoodState`, `ConsoleBoot`, `ExitRuntimeData`, `LocaleData`, `StderrStream`, `SharedReadWin` tabulated with its generated-proof supplier (REVIEW2.md §3). Synthetic: `GoodState` (F1). By construction: `stack_bytes` (P3). Program-dependent: `capacity`, `stack_admissible` (M1).
- Task 4: 30/35 corpus programs agree between the emulator (rebuilt from this tree, sha-identical to B3's) and the Lean semantics on the AST decoded from the binary's own parser output (Q8 cases included); `err_parse` outside; `recursion`/`adv_big_ok`/`adv_oom_*` not evaluated in Lean.
- Task 5: `lake build Vsa VsaIris VsaIris.Audit VsaBoot` green (2,807 jobs); `check_all.sh --static-only` OK; `check_iris_holes.py` 0 holes; no raised limits in `VsaIris/`/`Vsa/Sim/Boot/`; no forbidden tokens.

## Follow-ups landed (REVIEW2.md §8)

- `Vsa/Sim/Boot/Entry.lean` (`EntryRegs`), `Physical.lean` (`readyFacts_at`/`loaded_at`), generator + regenerated `Gen/*.lean` (`loadedEntry`, `loadedEntry_fill`), `Vsa/Sim/Boot/Audit.lean` (`*_halts_entry`), `check_all.sh` stage c3, `check_final_axioms.sh` (53 theorems), README, `LANES-b1.md`.

## In flight

- Uncapped emulator runs of `adv_oom_term`/`adv_oom_div` (lane V: `out of memory`, exit 1); reported in REVIEW2.md §4 when they finish.

## Holes

None added; `IrisHoles` is empty.

## Next

Nothing open on this lane. P11 (docs) is folded into P9's README paragraph.
