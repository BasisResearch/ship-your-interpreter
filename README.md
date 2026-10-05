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
| `bigStep_iff_L` | `Vsa/CT/Agree.lean` | a leakage semantics `BigStepL` (branch taken, division operands, printed values) agrees with `BigStep` on every program |
| `ct_sound` | `Vsa/CT/Prog.lean` | a program accepted by the constant-time checker `ctSeq`, run on two inputs that agree on public variables, has leakage of the same shape, and equal leakage when the printed values agree |
| `sim_mulT`, `sim_divT`, `sim_modT` | `Vsa/Compiler/LibT.lean` | the libgcc multiply, divide and remainder routines take a Sail PC sequence fixed by their operands |
| `am_ct`, `ct_machine` | `Vsa/CT/TProg.lean`, `Vsa/CT/Machine.lean` | the compiled binaries of a `ctSeq` program for two such inputs halt after the same Sail PC sequence, hence the same number of steps, whenever the printed values agree |
| `sel_machine`, `eq_machine`, `lad_machine` | `Vsa/CT/Examples.lean` | `ct_machine` for constant-time select, a byte-distance check and a Montgomery ladder |

## Constant-time WHILE

`ct_machine` is stated for the subset compiler `compile`. Comparisons and `!` compile to
branch-free `slt` sequences and `*` to a fixed 64-iteration shift-add loop. `/` and `%` call
libgcc and leak their operands, so the checker requires both to be public. Secret inputs are
literals of an input prefix written in a fixed shape (`encLit`), so the code layout does not
depend on them. Printed values are declassified: the machine traces of the two runs agree
whenever the two runs print the same values. The theorem covers terminating runs. `compileG`
and `compileChecked` are not covered; their runtimes branch on data by construction.

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
| `Vsa/CT/` | the leakage semantics, the constant-time checker and its soundness, the traced compiler simulation and `ct_machine` |
| `VsaIris/` | the Iris-based machine logic and the interpreter proof; `VsaIris/WhileLogic/` is the source-level program logic |
| `Vsa.lean`, `VsaIris.lean`, `VsaBoot.lean` | library roots importing the modules above |
| `VsaRun.lean`, `WhileC.lean`, `WhileCheck.lean` | the executables |

## Proof structure

The machine-code proof is organised around a few abstractions, each proved once:

| Abstraction | Where | Replaces |
| --- | --- | --- |
| `#simp_nf`, `decodeW` | `Vsa/Meta/SimpNF.lean`, `Vsa/Sim/DecodeNF.lean` | per-word decode lemmas: the Sail decoder is simplified once, and each decode fact is one `rfl` |
| `TextPiece` | `Vsa/Sim/TextImage.lean` | per-address code-byte lemmas: code residency is a range of the ELF image |
| `StepRules`, `StepGen.driverLemma?` | `VsaIris/Vsa/StepRules.lean`, `StepGen.lean` | per-address step lemmas: one rule per instruction class; a step lemma is built on demand from the image |
| `SymExec`, `sym_run` | `VsaIris/Vsa/SymExec.lean`, `VsaIris/Interp/SymInterp.lean` | stepping in interpreter machine runs: a symbolic executor proved sound once |
| `Region`, `HeapPermit`, `Win` | `VsaIris/Vsa/` | address, frame and heap-edit reasoning in allocator and newlib paths |
| `boot_witness` | `Vsa/Sim/Boot/` | per-program boot data: derived data is computed, and the kernel checks every value |
| descriptor and mode arms | `VsaIris/Interp/ArmCore.lean`, `ArmEval.lean` | total/partial twins and sibling operators among the big-step rules |
| `Vsa/Lang`, `VsaIris/Lang` | | the refinement argument, shared by any interpreter proved on this machine |

`abstractions/ROUND-*.md` records how each layer was chosen and measured.
[`docs/PORTING.md`](docs/PORTING.md) explains how another interpreter on this machine layer uses them.

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
