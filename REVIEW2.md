# Lane V2: final non-vacuity audit of `endToEnd_refinement`

Reviewed: `hub/iris-main` at `905e3735` (branch `lane-v2`, a copy of that commit with `experiments/review-v2/` added; nothing else changed). The claim under review:

```lean
theorem Vsa.Sim.EndToEnd.endToEnd_refinement (h : VsaIris.Interp.IrisHoles) :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out)
```

with `structure IrisHoles : Prop where` (no fields) and the ten loader-derived witnesses `Vsa.Sim.Boot.Gen.<Prog>.loaded` (library `VsaBoot`).

## Verdict: NOT VACUOUS

**Strongest single piece of evidence.** Running the theorem's own step function (`Vsa.setupElf` then `Vsa.stepOnce`, the functions `Halts` is defined over) on the ELF parsed from the embedded `Vsa.elfHex` for exactly `Gen.Proof.entrySteps = 85,483` steps yields a Sail state whose memory is *equal* to the witness memory `bootMem Gen.Proof.script Gen.Proof.log` (same size, 127,071 present bytes, pointwise equal), whose `x1…x31` and `PC` equal the witness registers, whose console is empty, and which halts after 382,730 steps with exit 0 and output `"55\n2500\n36\n"`; the witness configuration halts identically. The kernel-checked, hypothesis-free theorem `ReviewV2.proofElf_halts_unconditional : Halts cProof "55\n2500\n36\n" 0` (`Vsa/Sim/Boot/Audit.lean`, axioms `[propext, Classical.choice, Quot.sound]`) is therefore a statement about the state the binary reaches, and `Halts` is not trivially true there (`¬ Halts cProof "" 0`, `¬ Diverges cProof`, both kernel-checked). The same replay agrees for all ten witnesses, including the two runtime-error programs (exit 70, kernel-proved to have no `BigStep` and no clean halt).

The audit found no vacuity. It found one gap between "the witness state" and "the reached state" (F1: the witness's control-register file is synthetic; `Loaded` pins only the registers that agree) and one trust boundary that is native, not kernel (F2: the ELF bytes and the store log enter the kernel as generated data; the ELF parse and the emulator's trace are checked natively). Both are proposals for statement/tooling changes, not soundness problems.

## 0. Findings, ranked

| # | severity | finding | evidence | proposal |
|---|---|---|---|---|
| F1 | **medium (witness is a model of the reached state, not the reached state) — landed as P8 (§8)** | `Gen.<Prog>.loaded` is stated at `bootConfig (bootMem script log) regs entrySteps`, whose register file `bootRegs` (`Vsa/Sim/Boot/Config.lean`) is `physicalAssignments.take 32` (32 control registers at the model's *setup* values: `mtime = mcycle = minstret = mip = htif_tohost = 0`) plus `x1…x31` from the trace, with `cycleCount = 0`. The state the binary reaches has `mtime = mcycle = 0xa6f5`, `minstret = 0x14deb`, `mip = 0x80` (MTIP pending, masked by `mie = 0`), `htif_tohost = 0x8001ad00`, `cycleCount = 1`, and every CSR of `init_model` present. `Loaded` inspects only `GoodState`'s 20 pinned CSRs (`Vsa/Sim/GoodState.lean`), and every one of them was checked equal in the reached state (§2.1), so the reached state is `Loaded` too and `endToEnd_refinement` applies to it by `∀ c` — but that last step is checked natively, not by the kernel: no theorem states `Loaded` for the reached register file, and none can without reducing `init_model`. Behaviourally the two states are indistinguishable (identical `Halts` results for all ten witnesses, §2.1). | `experiments/review-v2/Replay.lean` (10 runs, §2.1); `bootRegs`/`csrAssignments` (`Config.lean:31–49`); `physicalAssignments` (`OutputAliasPhysical.lean:14`) | **P8** (§6): state `Gen.<Prog>.loadedAt` over any configuration `⟨σ, entrySteps % 2, entrySteps⟩` with `GoodState σ`, the traced `x1…x31`/`PC`/`htif_payload_writes`, and a memory extending the entry view; the current `bootConfig` instance becomes a corollary. Then only `GoodState` of the reached state is a native check, like `ElfLoads`. |
| F2 | **low (native trust boundary, documented) — landed as P9 (§8)** | The kernel never connects `Vsa.elfHex` (the 138,880-byte ELF) to `bootMem`: `initializeMemory_eq` takes `ElfLoads elf script` as a premise (the ELFSage parse of a concrete file, evaluated natively by `gen_boot_witness.py check-elf`), and the store log `Gen.<Prog>.log` is the emulator's `--trace-all` store operands, decoded *syntactically* (`memOpOf` in `riscv-lean/lean_emulator/LeanRiscv.lean`: opcodes `0x03`/`0x23` only). `LogOk` is the kernel's check that `runs` is the log's effect, not that the log is the machine's. Both links hold: (i) this lane's Python cross-check — `elfHex` = `c/while-riscv-htif.elf` (sha256 `b146c6ed…`), `fixedText`/`fixedRodata`/`bootData`/`bootLow` pages = the file's `.text`/`.rodata`/`.data`+`.tohost`+`.init_array`/attributes bytes, `bootPieces` = the PT_LOAD segment (113,040 `p_filesz` bytes) plus ELFSage's three unattributed regions; (ii) the replay (§2.1): `initializeMemory` + 85,483 `stepOnce`s = `bootMem` exactly, for all ten programs. The syntactic capture is complete for this binary: it is `-march=rv64i` (`c/Makefile`), `e_flags = 0` (no RVC), no A/F/D, `satp = 0` (no page walks), and lean-sail's only memory write is `writeByte` (`riscv-lean/lean-sail/Sail/ConcurrencyInterfaceV1.lean:196`). | `experiments/review-v2/elf_xcheck.py`, `Replay.lean` | add the replay (or the `ElfLoads` check) to `check_all.sh`'s compiled stage so the native links are re-checked per build; document the two native links beside `IrisHoles` in README |
| F3 | low (coverage) | The ∀-program theorem is witnessed at 10 real entry states (`proof`, `while`, `arithmetic`, `for`, `scope`, `strings`, `functions1/2`, `err_divzero`, `err_undefined`). `recursion.wl` has every trace fact but no `loaded` (`capOk` for `fib(20)` is out of kernel reach); `err_parse.wl` never reaches `interp_run`. M1 stands: `capacity` and `stack_admissible` make `Loaded` execution-dependent (`adv_oom_term` has a `BigStep` but is not `Loaded`). | `Gen/Recursion.lean` (no `loadedAt`); `LANES-b3.md` | none (documented) |
| F4 | low (hygiene) — landed as P10 (§8) | (a) `LANES-b1.md` is byte-identical to `LANES-b3.md`: lane B1's report (`hub/lane-b1:LANE.md`, P1/P2) was overwritten in the INT2 merge `79ea46fb`. (b) `scripts/check_final_axioms.sh` audits only `Gen.Proof.loaded` and `proofElf_halts` of the boot library; the other nine witnesses and five `*_halts` are audited by `Vsa/Sim/Boot/EndToEnd.lean`'s two `#print axioms` and this lane's `Audit.lean` only. (c) `Vsa/While/Validation.lean:25` sets `maxRecDepth 4000000` and is in the capstone's import cone (`whileWl_valid`); no limit is raised in `VsaIris/` or `Vsa/Sim/Boot/` (REVIEW.md L3: 1,011 files under `Vsa/` raise limits). (d) The design doc's `LANES-b1.md`/README are otherwise current. | `diff LANES-b1.md LANES-b3.md`; `git show hub/lane-b1:LANE.md` | restore `LANES-b1.md` from `hub/lane-b1:LANE.md`; extend `check_final_axioms.sh` |
| F5 | info (semantics corpus) | 30/35 corpus programs: the Lean semantics (cost evaluator on the AST decoded from the binary's *own* parser output at the traced entry) agrees with the emulator's output and exit code, including Q8's `catDisplay` cut (`adv_longname`, `adv_name58/59`, `adv_native`) and the abrupt-status programs (`adv_break`: `TopAbrupt`, exit 70). `err_parse` is outside the theorem; `recursion` (`fib(20)`) did not finish in the interpreter within the session; `adv_big_ok`/`adv_oom_*` were skipped in Lean (megabyte strings as `List Char`). `adv_oom_term`/`adv_oom_div` did not finish under the emulator within 60 M steps either (lane V reported `out of memory`, exit 1 at a higher cap); uncapped runs are in §4. | §4 | none |

Nothing in `Halts`, `Diverges`, `output`, `BigStep`, `bootMem`, `loadedMem` is redefined: their definitions are re-stated as `rfl` examples in `Audit.lean` (§2.3).

## 1. Unconditional (task 1)

`VsaIris/Interp/Holes.lean`:

```lean
structure IrisHoles : Prop where          -- no fields
theorem IrisHoles.proved : IrisHoles := ⟨⟩
```

`VsaIris/HOLES.md` has 0 rows and `python3 scripts/check_iris_holes.py` prints `ok: 0 ledgered holes`. `Vsa/Sim/Boot/Audit.lean` (kernel-checked, `lake env lean` in 37 s) contains

```lean
example : VsaIris.Interp.IrisHoles := ⟨⟩
theorem ReviewV2.endToEnd_unconditional :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Sim.EndToEnd.endToEnd_refinement ⟨⟩
```

`#print axioms` on it, on every `Gen.<Prog>.loaded` (10), on `proofElf_halts`, `while_halts`, `arithmetic_halts`, `for_halts`, `scope_halts`, `strings_halts`, `initializeMemory_eq`, `endToEnd_refinement`, `interpSim_iris` and on every `ReviewV2.*` corollary below reports exactly `[propext, Classical.choice, Quot.sound]`; `IrisHoles.proved` depends on no axiom. No `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` anywhere. `scripts/check_final_axioms.sh` after a fresh build: `24/24 theorems audited`.

## 2. Non-vacuity, concretely (task 2)

### 2.1 The witness configuration is the machine's (task 2a)

`experiments/review-v2/Replay.lean` (native; `lake env lean --run experiments/review-v2/Replay.lean <name>|all`) does, for each witness `Gen.<Name>`:

1. parses the ELF (`Vsa.whileElf?` from the embedded `elfHex` for `proof`; B3's corpus ELF for the others, which this lane re-verified byte-identical to the proof ELF outside the 453-byte script blob, with the blob equal to the `.wl` source padded with newlines — `elf_xcheck.py`);
2. checks `decide (elfPieces elf = imagePieces script)` (the `ElfLoads` premise of `initializeMemory_eq`);
3. runs `Vsa.setupElf` and then `Vsa.stepOnce` (the definitions `Step`/`Halted`/`Halts` are the graph of) for exactly `entrySteps` steps from `Vsa.initState elf` (`initializeMemory .B64 elf`);
4. compares the reached state with `bootConfig (bootMem script log) regs entrySteps`: memory size and every byte on the witness's key set (`bootPieces` ∪ the run tree; equal sizes plus pointwise agreement is map equality), `x1…x31`, `PC`, tick counter `i = entrySteps % 2` (`plat_insns_per_tick = 2`), `sailOutput = #[]`, and each `GoodState`-pinned CSR (`cur_privilege`, `misa`, `mstatus`, `mie`, `mseccfg`, `satp`, `mtvec`, `mideleg`, `medeleg`, `hart_state`, `htif_done`, `htif_tohost_base`, `elp`, `pmpcfg_n`, `pmpaddr_n`, `pma_regions`, `menvcfg`, `mcountinhibit`, `mcyclecfg`, `minstretcfg`, `htif_payload_writes`);
5. runs BOTH states to halt with `Vsa.runSteps` and compares (exit, output) with the emulator's.

| witness | entry steps | traced stores | present bytes (reached = witness) | halt steps | exit | output | GoodState CSRs | differs from witness only in |
|---|---|---|---|---|---|---|---|---|
| proof (`while.wl`, embedded ELF) | 85,483 | 8,837 | 127,071 | 382,730 | 0 | `55 2500 36` | all equal | `htif_tohost` (`0x8001ad00` vs `0`), counters, `mip`, `cycleCount` |
| while (padded build) | 86,320 | 9,005 | 127,071 | 383,567 | 0 | `55 2500 36` | all equal | same |
| arithmetic | 106,390 | 9,680 | 127,917 | 136,423 | 0 | `= arithmetic.expected` | all equal | same |
| for | 120,300 | 12,637 | 130,307 | 351,097 | 0 | `= for.expected` | all equal | same |
| scope | 75,486 | 8,002 | 127,008 | 100,119 | 0 | `= scope.expected` | all equal | same |
| strings | 36,228 | 5,031 | 124,416 | 50,716 | 0 | `= strings.expected` | all equal | same |
| functions1 | 72,465 | 8,441 | 128,691 | 99,347 | 0 | `15 11 81 3 1` | all equal | same |
| functions2 | 62,110 | 7,318 | 127,901 | 78,109 | 0 | `true <fn make_adder> <fn> 21` | all equal | same |
| err_divzero | 18,184 | 2,263 | 122,523 | 23,113 | 70 | `runtime error [line 1]: division by zero` | all equal | same |
| err_undefined | 12,365 | 1,761 | 121,182 | 17,131 | 70 | `runtime error [line 1]: undefined variable 'nope'` | all equal | same |

Every check passed for every witness except the one the harness labelled `htif_tohost`, which `GoodState` does not pin (`htif_tohost : ∃ v, …`): the model's `initializeRegisters` sets it to the `tohost` address, the witness to `0`. The reached and witness states halt after the same number of steps with the same output and exit code in all ten cases; the emulator (rebuilt from this tree, sha256 identical to B3's binary) prints the same.

So `bootMem script log` is `initializeMemory .B64 elf` plus the traced stores, byte for byte, and the trace is complete (no untraced write: `writeByte` is lean-sail's only memory write; the binary has no compressed, atomic, floating-point or CSR-side memory writes; the HTIF store path writes a register). The loader image itself is generated data (`ImageData.lean`, `FixedImageData.lean`) that this lane re-derived from the ELF file in Python: every page equals the file's bytes; `bootPieces = [(0x0, 28), (0x80000000, 113040), (0x0, 0), (0xe8, 3864), (0x21b7d, 3)]` is the PT_LOAD `p_filesz` segment plus the `.riscv.attributes` PT segment at vaddr 0 and ELFSage's two unattributed file regions (all below RAM, never read). `.bss` (2,008 bytes) is not loaded; the run to entry writes it (`check_loaded.py`: 2008/2008 present).

### 2.2 The instantiated theorem is non-trivial (task 2b)

Kernel-checked in `Vsa/Sim/Boot/Audit.lean` (all axioms ⊆ {propext, Classical.choice, Quot.sound}):

```lean
theorem proofElf_halts_unconditional : Halts cProof "55\n2500\n36\n" 0        -- cProof := bootConfig (bootMem Gen.Proof.script Gen.Proof.log) Gen.Proof.regs 85483
theorem proofElf_not_halts_empty     : ¬ Halts cProof "" 0                      -- Halts.deterministic
theorem proofElf_not_halts_exit1     : ¬ Halts cProof "55\n2500\n36\n" 1
theorem proofElf_clean_halt_unique   : ∀ out, Halts cProof out 0 → out = "55\n2500\n36\n"
theorem proofElf_not_diverges        : ¬ Diverges cProof                        -- Diverges.not_halts
theorem arithmetic_halts_unconditional / for_halts_unconditional / strings_halts_unconditional / scope_halts_unconditional
-- runtime errors
theorem errDivzero_noBigStep   : ¬ ∃ out, BigStep Gen.ErrDivzero.prog out        -- execSeqEval 1000 … = .stuck (decide +kernel) + execSeq_cost_exists + execSeqCost_none_of_stuck
theorem errDivzero_never_clean : ∀ out, ¬ Halts cDiv out 0                        -- from endToEnd_unconditional at Gen.ErrDivzero.loaded
theorem errDivzero_stuck       : Diverges cDiv ∨ ∃ out e, Halts cDiv out e ∧ e ≠ 0  -- (interpSim_iris ⟨⟩).stuck_sim + halts_fillZero/diverges_fillZero
-- and the same three for err_undefined
```

`Gen.Proof.prog = Programs.whileWl` (`prog_eq`, by `stmtsBeq_sound`), so the instantiated theorem is `BigStep whileWl out ↔ Halts cProof out 0`; `BigStep whileWl "55\n2500\n36\n"` is `Validation.whileWl_valid` (a kernel-checked derivation). For the error programs the theorem yields "no clean halt" and "diverges or exits nonzero"; it does not by itself exclude divergence (that is the intended shape of `stuck_sim`). The replay and the emulator show the halt: exit 70 after 23,113 / 17,131 steps.

### 2.3 The notions are the real ones (task 2, last clause)

`Audit.lean` re-states these by `rfl` (so any redefinition would fail to elaborate):

- `Halts c out e = ∃ c' σf, Steps c c' ∧ Halted c' e σf ∧ output σf = out`, `Diverges c = ∀ n, ∃ c', StepsN n c c'`, `output σ = String.join σ.sailOutput.toList` (`Vsa/Machine.lean:36–69`); `Step`/`Halted` are the graph of `Vsa.stepOnce` (`Vsa/Elf.lean:47`, frozen interface), which mirrors the emulator's loop (`riscv-lean/lean_emulator/LeanRiscv.lean`, `traceLoop`); the exit code is the HTIF `htif_exit_code` (`tohost >> 1`), so `exit(70)`/`exit(1)`/`exit(65)` are all `≠ 0`. `output` is the HTIF console; `stderr` and `stdout` are the same console (`_write` ignores `fd`), so an error diagnostic is part of `out`.
- `BigStep p out = ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out` (`Vsa/While/Semantics.lean:574`), the relation `Vsa/While/Validation.lean` validates (`whileWl_valid`, `arithmetic_valid`, `for_valid`, `functions_valid`, `scope_valid`, `strings_valid`, `recursionSmall_valid`) and §4 re-validates on 30 programs.
- `bootMem script L = writeLog (loadedMem script) L.log`, `loadedMem script = loaderMem bootPieces (imageByte script)` (`Vsa/Sim/Boot/Image.lean`); `fillZero c` changes only the memory (`fillZero_bootConfig`).

## 3. Hidden assumptions (task 3): every field, as it is now

`Loaded interpRunLayout p c` (`Vsa/Refinement.lean:60`) is `∃ a n, ProgramRepr c.σ.mem a n p ∧ InterpRunReady c a n`, and `InterpRunReady c a n` (`Vsa/Sim/LayoutInstance.lean:575`) is `∃ inp N A φf φc aLeft, InterpRunReadyFacts c a n inp N A φf φc aLeft`. The generated proof `Gen.<Prog>.loadedAt` (via `loaded_of`, `Vsa/Sim/Boot/Physical.lean:184`) chooses `a = stmts = a1`, `n = count = a2`, `inp = 0x87fffe10`, `N = bootNatives`, `A = bootArena = [_end, __heap_end) = [0x8001c170, 0x87800000)`, `φf = const env`, `φc = const 0`, `aLeft = 0`; `ProgramRepr` comes from the decoder (`decodesTo_sound`) and `ProgramRepr.unique`. "Witnessed" below means: proved by the generated Lean proof at the real entry memory (a `decide +kernel` over the byte view `bootView script runs`), for all ten programs; the Python checker is not cited.

| structure / field | statement | witnessed by (generated proof) | verdict |
|---|---|---|---|
| **InterpRunPhysicalFacts** (46 fields, `LayoutInstance.lean:176`) | | | |
| `good : GoodState c.σ` (20 pinned CSRs, 11 present-only: `htif_tohost`, `mip`, `sig_meip/seip`, `mtime`, `mtimecmp`, `minstret`, `minstret_increment`, `mcycle`, `nextPC`, `PC`) | machine mode, `misa/mstatus` init values, `mie = mtvec = satp = … = 0`, `htif_done = false`, `htif_tohost_base = tohost`, PMP/PMA init, counters present | `bootState_good`: the witness's CSR file *is* `physicalAssignments.take 32` | **synthetic** (F1); every pinned value verified equal in the reached state natively (§2.1) |
| `tick : c.tick < 2` | | `entrySteps % 2` | true of real boots (`plat_insns_per_tick = 2`; replay: `i = 1` at step 85,483) |
| `pc`, `htif_payload` | `PC = 0x800043ec`, `htif_payload_writes = 0` | CSR list | replay: equal |
| `interp_arg`, `interp_local`, `stmts_arg`, `count_arg`, `repl_arg`, `ra`, `sp`, `gp`, `s0 … s11` | `a0 = &Interp = 0x87fffe10`, `a1 = stmts`, `a2 = count`, `a3 = 0`, `ra = 0x800045ec`, `sp = 0x87fffd00`, `gp = 0x8001b510`, `s*` present | `BootRegs` (decided on the trace's entry GPR row), `bootRegs_gpr` | replay: `x1…x31` equal |
| `main_ra` | `[0x87fffff8] = 0x80000038` | `BootMemFacts.mainRa` | real (traced stack) |
| `text_image` | `.text` bytes `[0x80000000, 0x80018be0)` | `PartialView.text`: no traced store below `0x80018be0` (`RunTree.above`) | real |
| `rodata_image` | `.rodata` bytes after the script blob `[0x80018da6, 0x8001acf0)` | `PartialView.rodata`: no store below `0x8001acf0` | real; **script bytes** unpinned (P2) — every build's own blob is in `imageByte script` |
| `statics` (8 pins: `%lld`, `"."`, parse slots, `__mb_cur_max`, `_impure_ptr`, …) | | decided through the view | real (`.data` after CRT) |
| `console : ConsoleBoot` (18) | `_flags = 0x000a`, `_p = _bf._base = &buf` (1 byte), `_w = _r = 0`, `_write = __swrite`, `_cookie`, lock words, `_impure_ptr` | decided | real (P1); **console flags** at the boundary are the real `0x000a` |
| `exit_runtime : ExitRuntimeData` (11 + 2 idle FILEs) | `_atexit = 0`, `__sglue = {0, 3, __sf}`, stdin/stderr idle, `__sclose`, `_ub._base = 0`, `_lb._base = 0` | decided | real |
| `arena_protected` | no `ProtectedInitialByte` in `[_end, __heap_end)` | `bootArena_protected` (constant geometry) | real, all boots |
| `out : OutRepr c.σ initSt` | console output so far = `""` | `rfl` (witness `sailOutput := #[]`) | replay: real state has no output at entry |
| `globals`, `call_depth` | `Interp.globals = env`, `Interp.call_depth = 0` | decided | real |
| `interp_geom`, `setjmp_geom`, `stack_ok`, `stmts_align/ram/win/stack` | constant arithmetic; `stmts` bounds | `decide`, `BootRegs` | real |
| `stack_bytes` | every byte of `[0x87800000, 0x88000000)` present | `fillZeroMem_stack` | **holds of `fillZero c` by construction, never of the sparse state** (P3; the loader inserts `p_filesz` bytes, the run to entry a few KB of stack). Sound because `halts_fillZero`/`diverges_fillZero` (a `Resp` proof over the model, `Vsa/Densify/`). **RAM bound**: `fillZero` fills exactly `[0x80000000, 0x88000000)`; every loader/traced byte lies there or below `0x22000` (unaffected) |
| `store`, `store_survives`, `native_addrs` | `initSt.store` = `{print, println, assert}` at `0x80002ed4/0x80002f7c/0x80002df4`, capacity `cap`, surviving the prologue footprint | `frameCheck` over the prologue-masked view (`store_of_check`) | real |
| `arena_budget : A.lo + aLeft ≤ A.hi` | | `aLeft = 0` | trivially satisfiable; `aLeft` is an existential the Iris route does not need (`world_of_boundary` takes it as given) |
| **InterpRunReadyFacts** (+4, `:432`) | | | |
| `boot : ∃ D top brkv chunks bins F, BootHeap …` | ownership + one allocator walk + heap facts, all about the same witnesses | `initialOwned_of`, `heapAt_of_check`, `capacity_of_capOk`, `bootHeapFacts_of` | real (below) |
| `stack_admissible : StackAdmissible` | every represented program satisfies `ProgramStackFits` (`stackNeedList + maxCallDepth·perCallBudget + evalFrame + helperHeadroom(2048) + 176 ≤ sp − stack.lo`, bodies bounded) | `programStackFits prog` decided + `ProgramRepr.unique` | real for the 10 programs; **program-dependent** (M1). **Error headroom** `helperHeadroom = 2048` (Q7) is part of this decidable check |
| `gprs` | `x1…x31` present | `bootState_gprs` | real |
| `s0_impure` | `x8 = 0x8001b970` (`&_impure_ptr`) | `BootRegs.s0` | real (replay) |
| **BootHeap.owned : InitialOwned** (7) | | | |
| `heapLower`, `heapUpper`, `arenaHeap` | `A = [0x8001c170, 0x87800000)` | `rfl` | constant |
| `heap : HeapOwned` (= `Ledger`, `Immutable`, `Reserved`, `StoreOwned`) | live extents = frame record + the two arrays + three key copies + the AST extents (in-use payloads); **shared bytes** = the keys, the three native names (`.rodata` literals `0x80019538/40/48`) and the AST extents | `OwnOk` (ranges, decided), `FrameOk` (reads, decided), `ledger/immutable/reserved/storeOwned` | real; the shared set is the generator's choice (existential `D`), so no hidden constraint on the binary |
| `arrays : StoreArraysReady` | arrays 8-aligned, value words present | `FrameOk` | real |
| `program` | every represented program reads only shared bytes | decoder coverage `own.sharedB` + uniqueness | real |
| `allocator : InitialAllocator` | `∃ top brkv chunks bins, InitialAllocatorAt …` | below | |
| **InitialAllocatorAt** | | | |
| `heap : HeapAt` (23: `sbrk_base`, `brk` page bounds, `top_ptr/top_size/top_header/top_pad = 0`, `max_sbrked`, `mallinfo` present, first-chunk `prev_inuse`, chunk walk `_end → top`, coalescing, free footers, bin rings, `bin_free`/`free_binned`, `remainder ≤ 1`, `binblocks` bits, `live`, `exact`) | dlmalloc's state at entry | `heapCheck` decided (proof ELF: 154 chunks, 0 free, no bins) | real |
| `capacity` | `∀ p, ProgramRepr → ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n → 2n + 8256 ≤ heapEnd − top` | `capOk 1000 prog top` (cost evaluator; complete for the relations) | real for the 10 programs; **program-dependent** (M1); vacuous for the `err_*` programs (evaluator `stuck`); **`recursion.wl` not witnessed** |
| **BootHeapFacts** (8) | | | |
| `top_room`, `brk_page`, `binblocks < 2^32` | | decided | real |
| `frame : BootFrameChunks` (9: `cap = 8`, arrays' pointers, `sblk/nblk/vblk` whole in-use payloads, distinct, unshared) | | `HeapFactsOk` decided | real (**capacity 8** is what `interp_init` leaves) |
| `stderr` | `_impure_data._stderr = &__sf[2]` | decided | real |
| `locale : LocaleData` (3) | `_mbtowc_r` hook = `__ascii_mbtowc`, `__mb_cur_max = 1`, decimal point `"."` | decided | real (**locale**) |
| `stderrStream : StderrStream` (2) | stderr `_bf._base = 0`, `_write = __swrite` | decided | real |
| `shared_geom : SharedReadWin` (3) | shared bytes in `[0x80000000, 0x88000000 − 8)`, 8-byte window off the 16 HTIF bytes, off the stack | `OwnOk.readWin` | real (P7); **shared bytes** in `.rodata` admitted |

Nothing in this table is false of the real boots or true only of a hand-made snapshot, with the two qualifications above: `stack_bytes` is true only of the fill (by the P3 design), and `GoodState` is proved at a synthetic CSR file whose pinned entries the reached state matches (F1). The control snapshot (`Control.loaded`) is no longer the only witness; it is still in `check_final_axioms.sh`.

## 4. Semantics sanity (task 4)

Method: for each of the 35 corpus ELFs (`experiments/review-v/wl/*.wl`, built by B3's `gen_boot_witness.py corpus`; re-verified identical to the proof ELF outside the blob), the AST was decoded from the **binary's own parser output** at the traced `interp_run` entry (`gen_corpus.py`, reusing the witness generator's decoder on B3's traces), and the Lean semantics was run on it with the cost evaluator `execSeqEval` (`Vsa/While/CostEval.lean`, complete for `ExecSeq`); the emulator rebuilt from this tree ran every ELF (`run_corpus.sh`, 60 M-step cap, then uncapped for the two out-of-memory programs). `compare.py` matches: `done/normal` ⇔ exit 0 and equal output; `stuck` or abrupt status ⇔ exit ≠ 0.

| result | programs |
|---|---|
| **agree** (30) | `BigStep` = emulator, exit 0: `adv_depth999`, `adv_empty`, `adv_intmin` (INT64_MIN, `/(-1)`, `%`, `10^24` wrap, `tdiv`/`tmod`), `adv_longname` (Q8: `""+f` cut to 63 bytes without `>`, `println(f)` full), `adv_loopvar`, `adv_name58` (63 chars with `>`), `adv_name59` (cut), `adv_native` (`<native fn>` vs `<native fn println>`, `<fn>`), `adv_nest` (440 nested `-`), `adv_nest_odd`, `adv_nonascii` (equal as Lean strings; outside the theorem by `CStr`, L1), `adv_strcmp`, `adv_truthy`, `arithmetic`, `for`, `functions1`, `functions2`, `proof`, `scope`, `strings`, `while`; no `BigStep` and exit 70: `adv_arity`, `adv_assert2`, `adv_break` (`TopAbrupt`, status `brk`), `adv_depth1000` (`d < 1000`), `adv_modzero`, `adv_notcallable`, `adv_toomany`, `err_divzero`, `err_undefined` |
| outside the theorem | `err_parse` (exit 65, never reaches `interp_run`) |
| not evaluated in Lean | `recursion` (`fib(20)`: the evaluator did not finish in the interpreter within the session; emulator = `recursion.expected`, exit 0), `adv_big_ok` (emulator `2`, exit 0), `adv_oom_term`, `adv_oom_div` (megabyte strings as `List Char`) |

`adv_oom_term`/`adv_oom_div` under the emulator: uncapped runs still in progress at this commit (see `LANE.md`; updated below when they finish). (Lane V reported `out of memory`, exit 1, matching M1: `adv_oom_term` has a `BigStep` yet is not `Loaded` because `capacity` fails.)

The cost evaluator is exponential in the fuel argument for loops (`oracle f` nests `f` oracles): fuel 100,000 made `while.wl` take > 15 min and one run 70 GB; fuel 3,000–5,000 answers in seconds. This is a property of the evaluator, not of the semantics.

## 5. Hygiene (task 5)

- `lake build Vsa VsaIris VsaIris.Audit VsaBoot` at `905e3735`: **green, 2,807 jobs** (the checkout's `VsaIris` oleans predated the last commits; the rebuild took 35 min under the shared lock).
- `scripts/check_all.sh --static-only`: stage a3 (generator drift), a4 (discipline), a5, b (2,502 files scanned for `sorry`/`native_decide`/`bv_decide`/`axiom`) all **OK**. `scripts/check_final_axioms.sh`: **24/24**. `python3 scripts/check_iris_holes.py`: `ok: 0 ledgered holes`.
- Raised limits: none in `VsaIris/` (the two `maxHeartbeats` mentions in `Interp/ITac.lean`/`Vsa/Stdout/Tac.lean` read the budget; they do not set it) and none in `Vsa/Sim/Boot/` or `Vsa/Densify/`. `Vsa/While/Validation.lean:25` (`maxRecDepth 4000000`, for `bigstep_derive`) is in the capstone's cone; 1,011 files under `Vsa/` raise limits (L3, unchanged).
- Forbidden tokens: no `native_decide`, `bv_decide`, `ofReduceBool`, `trustCompiler` outside comments in `Vsa/`, `VsaIris/`, `VsaBoot.lean`, `VsaRun.lean`, or the emulator; every audited theorem's axioms are the three standard ones (§1).
- The emulator was rebuilt from this tree (`lake build lean_riscv_emulator`, 250 jobs); the binary is sha256-identical to B3's `vsa-b3-work/bin/lean_riscv_emulator`; `riscv-lean/` is identical to lane V's checkout.
- Working tree: clean at `905e3735`; this lane adds only `experiments/review-v2/` and this file (plus `LANE.md`, the plan entry).

## 6. Proposals (statement/tooling changes; the user's call; nothing applied)

- **P8 (F1): witness the reached configuration's shape, not a synthetic register file.** Generalise `Gen.<Prog>.loadedAt` (via `readyFacts_of`/`loaded_of`) to `∀ σ, GoodState σ → (σ.regs.get? PC = some 0x800043ec) → (htif_payload_writes = 0) → (∀ i, gprGet σ (i+1) = some (regs (i+1))) → PartialView σ.mem (bootView script runs) → (∀ k ∈ stack, present) → Loaded interpRunLayout prog ⟨σ, entrySteps % 2, entrySteps⟩`. `bootState_good`/`bootState_pc`/`bootState_htif_payload`/`bootState_gprs` are exactly the four facts used, so the current `loaded` is the instance at `bootState`. Then "the binary's reached state is `Loaded`" reduces to `GoodState` of that state — a native check in the same class as `ElfLoads` (both could be emitted by `gen_boot_witness.py check-elf`). Cost: `Physical.lean` only; no proof of the tower changes.
- **P9 (F2): re-check the native links per build.** Add `experiments/review-v2/Replay.lean all` (≈ 10 min interpreted) or at least the `ElfLoads` evaluation to `check_all.sh`'s compiled stage, and list the ten `Gen.*.loaded` and six `*_halts` in `check_final_axioms.sh`. Document in README that two facts are native, not kernel: the ELFSage parse of `elfHex` (`ElfLoads`) and the emulator's store log being the machine's (`LogOk` checks the log's *effect*).
- **P10 (F4): restore `LANES-b1.md`** from `hub/lane-b1:LANE.md`.
- **P11 (docs):** state in README/INTERP_DESIGN that the capstone theorems (`proofElf_halts`, …) hold at `bootConfig`, a configuration equal to the reached one on memory, GPRs, PC and every `Loaded`-inspected register, with the counters at their setup values.

## 7. Reproduction

```
lake build Vsa VsaIris VsaIris.Audit VsaBoot lean_riscv_emulator
lake env lean Vsa/Sim/Boot/Audit.lean                                # §1, §2.2, §2.3 (kernel; built by `lake build VsaBoot`)
lake env lean --run experiments/review-v2/Replay.lean all             # §2.1 (native; needs B3's corpus ELFs, VSA_BOOT_WORK)
python3 experiments/review-v2/elf_xcheck.py                           # §2.1 image provenance (pure Python)
python3 experiments/review-v2/gen_corpus.py /tmp/Corpus.lean && lake env lean --run /tmp/Corpus.lean [name] [fuel=N]   # §4
REVIEW_V2_WORK=/tmp/review-v2-work experiments/review-v2/run_corpus.sh && python3 experiments/review-v2/compare.py    # §4
scripts/check_all.sh --static-only; scripts/check_final_axioms.sh; python3 scripts/check_iris_holes.py               # §5
```

Outputs of this lane's runs are outside the repository (scratch), summarised above.

## 8. Follow-ups landed (approved by the user, 2026-09-25)

- **P8 (F1).** `Vsa/Sim/Boot/Entry.lean`: `EntryRegs σ g` names the four
  register facts `Loaded` reads (`GoodState`, `PC = interp_run`,
  `htif_payload_writes = 0`, the traced `x1 … x31`), with `EntryRegs.gprs`
  (presence), `EntryRegs.setMem`/`GoodState.setMem` (transport across the zero
  fill) and `bootState_entryRegs` (the witness register file is an instance).
  `Physical.lean`: `readyFacts_at`/`loaded_at` assemble the boundary at ANY
  configuration `⟨σ, tick, steps⟩` with `EntryRegs σ g`, an empty console and a
  memory the entry view is a partial view of; `readyFacts_of`/`loaded_of` are
  their instances at `bootState`. The generator emits, per program,
  `loadedEntry` and `loadedEntry_fill` (the form `endToEnd_refinement` takes;
  the fill supplies the stack bytes), with `loadedAt`/`loaded` as corollaries;
  the ten `Gen/*.lean` were regenerated from B3's traces (the diff is exactly
  that block). `Vsa/Sim/Boot/Audit.lean` (the lane's audit, moved into the
  library) adds `proofElf_halts_entry`, `arithmetic_halts_entry`,
  `errDivzero_never_clean_entry`: the capstones at any entry configuration.
  What remains native is exactly the three hypotheses at the reached state,
  which `Replay.lean` checks field by field (`EntryRegs` = the 20 pinned
  `GoodState` CSRs + PC + payload + GPRs; empty console; memory equality ⇒
  partial view). The full reached register file (every CSR `init_model`
  defines) cannot be kernel-covered without reducing `init_model`; the
  witness now ranges over all of them.
- **P9 (F2).** `scripts/check_all.sh` stage c3 runs `Replay.lean proof`
  (embedded ELF: `ElfLoads` + replay + halt) whenever the VsaBoot build is
  present, and `all` when `VSA_BOOT_WORK` points at the corpus;
  `scripts/check_final_axioms.sh` audits every `Gen.*.loaded`,
  `Gen.Proof.loadedEntry_fill`, the six `*_halts` and the `ReviewV2.*`
  theorems (24 → 53). README: the witnesses and the two native links beside
  `IrisHoles`.
- **P10 (F4).** `LANES-b1.md` restored from `hub/lane-b1:LANE.md`.
- **`IrisHoles` removed (user request, 2026-09-25).** The empty record, its
  ledger and checker are deleted; `interpSim_iris`, `supplies_of`,
  `endToEnd_refinement(_loaded)`, the six capstones and the `ReviewV2.*`
  theorems take no hypothesis. `endToEnd_refinement : ∀ p c, Loaded
  interpRunLayout p (fillZero c) → …`. §1 above describes the state before
  the removal (`example : IrisHoles := ⟨⟩` is gone with the structure).
- Build: `lake build Vsa VsaIris VsaIris.Audit VsaBoot` green (2,809 jobs);
  `check_final_axioms.sh` 53/53 standard; `IrisHoles` unchanged (empty);
  `check_all.sh --static-only` (a3, a4, a5, b), `check_discipline.py`,
  `check_iris_holes.py` (0 holes) pass; stage c3's command
  (`Replay.lean proof`: `ElfLoads`, 85,483-step replay, memory/`EntryRegs`/
  console equality, both halts) exits 0 in 4 m 27 s interpreted.
