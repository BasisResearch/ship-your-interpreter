# Ship your interpreter

This Lean 4 project verifies `c/while-riscv-htif.elf`, a WHILE-language
interpreter written in C and compiled to bare-metal RV64. The proof relates an
inductive big-step semantics of WHILE to the binary's execution in the
Sail-generated RISC-V model.

![endToEnd_refinement](docs/theorem.png)

```lean
theorem endToEnd_refinement :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)
```

`BigStep` is in `Vsa/While/Semantics.lean`; `Halts` and `Diverges` are in
`Vsa/Machine.lean`. Every theorem below depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

This repository holds only what these theorems need. It has no comments, no
scripts and no generators; generated Lean files are committed as they were
produced.

## What is proved

| Theorem | File | Statement |
| --- | --- | --- |
| `endToEnd_refinement`, `endToEnd_refinement_loaded` | `VsaIris/Interp/EndToEnd.lean` | the binary halts cleanly with output `out` exactly when `BigStep p out`; if it diverges, the program has no derivation |
| `endToEnd_trichotomy` | `VsaIris/Interp/EndToEndTrichotomy.lean` | every nonzero exit is `70` (runtime error) or `1` (out of memory); the binary exits nonzero or diverges exactly when the program errs or diverges |
| `bigStep_not_err`, `bigStep_not_diverges`, `err_not_diverges` | `Vsa/While/Exclusive.lean` | the three source behaviours are mutually exclusive |
| `proofElf_halts` and the other `*_halts` | `Vsa/Sim/Boot/EndToEnd.lean` | the ELF, run from its traced `interp_run` entry state, prints the expected output and exits 0 |
| `Gen.<Prog>.loaded*` | `Vsa/Sim/Boot/Gen/` | `Loaded` holds at the traced entry states of ten programs |
| `*_halts_entry`, the runtime-error programs | `Vsa/Sim/Boot/Audit.lean` | the same results at any configuration matching the traced entry registers |
| `preservation`, `type_soundness` | `Vsa/While/TypePreservation.lean`, `TypeProgress.lean` | a well-typed program terminates, diverges, or fails by division by zero, a failed `assert` or the call-depth cap |
| `typeCheck_iff`, `infer_sound`, `infer_complete`, `whileTyped_iff` | `Vsa/While/TypeCheck.lean`, `TypeInfer.lean` | the type checker decides `WellTyped`; inference finds a typing exactly when one exists |
| `wellTyped_machine`, `whileTyped_machine` | `VsaIris/Interp/TypeSafety.lean` | type safety stated for the loaded binary |
| `adequacy_bigStep`, `adequacy_machine` | `VsaIris/WhileLogic/` | a weakest-precondition proof of a WHILE program gives a `BigStep` derivation and a clean machine halt |
| `analyze_sound`, `progCost_sound` | `Vsa/AbsInt/` | the abstract interpreter over-approximates every run; `progCost` bounds allocation cost |
| `whileWl_machine` | `VsaIris/AbsInt/Machine.lean` | the analysis result for `while.wl`, stated for the loaded binary |
| `wellTyped_trichotomy`, `noAlarm_machine`, `noAlarm_terminating`, `adequacy_exact` | `VsaIris/Interp/TrichotomyCorollaries.lean` | the type system, the analyser and the program logic combined with the trichotomy |
| `compile_correct`, `compileG_correct`, `compileChecked_correct` | `Vsa/Compiler/Correct.lean`, `CorrectG.lean`, `Checked.lean` | the WHILE-to-RV64 compilers (a subset compiler, the full compiler, and the checked compiler with no heap premise) produce code with the same refinement property |
| `loaded_of_checked`, `endToEnd_checked` | `Vsa/Sim/CheckedBoundary.lean`, `VsaIris/Interp/EndToEndChecked.lean` | `endToEnd_refinement` with the two program assumptions replaced by checkers |

## What is assumed

`Loaded interpRunLayout p (fillZero c)` is the only hypothesis of
`endToEnd_refinement`. It says that configuration `c` is at the entry of
`interp_run` with the ELF's code and data in memory, the C runtime and
allocator in their initial state, and the AST of `p` laid out as the C structs
of `c/src/ast.h`. It contains two assumptions about the program:

- `capacity`: the heap has room for every terminating run of `p`;
- `stack_admissible`: the statically computed stack need of `p` fits the stack.

`fillZero c` fills absent RAM bytes with zero, which is how the Sail model
reads them.

The kernel checks `Loaded` at ten traced entry states. Two links between those
witnesses and the ELF file are not checked by the kernel: that loading the ELF
gives the witness's initial memory, and that the traced boot is the machine's.
The scripts that checked them, and the generator that produced the witness
files, are not in this repository.

## Layout

| Path | Content |
| --- | --- |
| `c/` | the C interpreter, its Makefile, linker script and `crt0`, the test programs `c/tests/*.wl`, and the verified ELF |
| `riscv-lean/` | vendored Sail-generated RISC-V models, a Lean emulator and `lean-sail` |
| `Vsa/Machine.lean` | the ISA as a transition relation; `Halts`, `Diverges` |
| `Vsa/While/` | the WHILE AST, the big-step semantics, error and cost semantics, the type system, checker, inference and parser |
| `Vsa/MemRepr.lean`, `Vsa/Refinement.lean` | the memory representation of ASTs; the refinement theorem from a forward simulation |
| `Vsa/Sim/` | decoding, runtime representations, function contracts and the simulation; `Vsa/Sim/Boot/` holds the boot witnesses |
| `Vsa/AbsInt/` | the abstract interpreter, its domains and the allocation-cost analysis |
| `Vsa/Compiler/` | the verified compilers |
| `VsaIris/` | the Iris-based machine logic and the interpreter proof; `VsaIris/WhileLogic/` is the source-level program logic |
| `Vsa.lean`, `VsaIris.lean`, `VsaBoot.lean` | library roots importing the modules above |
| `VsaRun.lean`, `WhileC.lean`, `WhileCheck.lean` | the executables |

## Building

```sh
lake build
```

This uses the Lean version in `lean-toolchain` and builds the three libraries
and the three executables. It is a long build.

```sh
.lake/build/bin/vsa_run                          # run the ELF on the executable Sail model
.lake/build/bin/whilecheck c/tests/functions.wl  # type-check a WHILE program
.lake/build/bin/whilecheck --selftest c/tests    # compare the parser with Vsa/While/Programs.lean
.lake/build/bin/whilec prog.wl -o prog.elf       # compile a WHILE program to an RV64 ELF
.lake/build/bin/whilec prog.wl --run             # compile, then run on the Sail model
```

The parsers and the ELF writer of `whilec` and `whilecheck` are not verified.

To rebuild the interpreter ELF (needs a RISC-V cross compiler with newlib):

```sh
make -C c riscv-htif                             # embeds c/tests/while.wl
make -C c riscv-htif HTIF_SCRIPT=tests/for.wl
```

The proofs are about the committed `c/while-riscv-htif.elf`; a rebuild with a
different toolchain can produce different bytes.
