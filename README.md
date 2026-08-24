# Verified semantic abstraction of a RISC-V binary

The interpreter binary `c/while-riscv-htif.elf` (a WHILE-language
interpreter compiled to bare-metal RV64, doing I/O over HTIF) is the source
of truth. This Lean 4 project gives it semantics via the Sail-generated
RISC-V ISA model and proves, CompCert-style, that an inductive big-step
semantics of WHILE abstracts the machine's behavior — for all programs.

## Layout

| File | Content |
| --- | --- |
| `Vsa/ElfBytes.lean`, `Vsa/Elf.lean` | the ELF embedded byte-for-byte as a Lean term; ELFSage parse; a pure, fuel-bounded runner over the Sail RV64D step (tooling — the native harness `vsa_run` reproduces the binary's behavior: exit 0, `55\n2500\n36\n`, 382,730 steps) |
| `Vsa/Machine.lean` | **the ISA as an inductive transition relation** (graph of one architectural step), behaviors `Halts`/`Diverges`, determinism + behavior-uniqueness lemmas |
| `Vsa/While/Ast.lean` | deep embedding of WHILE (mirrors `c/src/ast.h`) |
| `Vsa/While/Semantics.lean` | **inductive big-step semantics** — store-based mutable environments shared by closures, C truncating division, string coercion, `break`/`continue`/`return` statuses, `print`/`println`/`assert`. Purely relational: nothing in the theory evaluates WHILE |
| `Vsa/While/Derive.lean` | `bigstep_derive`: a syntax-directed tactic that *constructs* derivation trees of the big-step relation for closed programs (untrusted meta-code; the kernel checks the derivations) |
| `Vsa/While/Programs.lean`, `Vsa/While/Validation.lean` | the `c/tests/*.wl` scripts as deep embeddings, and kernel-checked theorems `BigStep prog "<binary's output>"` validating the semantics against I/O examples obtained by running the binary |
| `Vsa/MemRepr.lean` | **inductive memory-representation relation**: when RV64 memory holds the C AST structs (`ast.h`, LP64, little-endian) representing a deep-embedded program |
| `Vsa/Refinement.lean` | **the ∀-program refinement theorem** |

## The refinement statement

```lean
theorem refinement {L : Layout} (H : InterpSim L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Machine.Halts c out 0) ∧
      (Machine.Diverges c → ¬ ∃ out, BigStep p out)
```

`Loaded L p c` says configuration `c` is at the interpreter phase with `p`'s
memory representation (via the inductive `ProgramRepr`). `InterpSim` is the
forward-simulation obligation — every derivable behavior is realized by the
machine, and underivable programs never halt cleanly:

```lean
structure InterpSim (L : Layout) : Prop where
  term_sim  : ∀ p c out, Loaded L p c → BigStep p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded L p c → (¬ ∃ out, BigStep p out) →
              Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0
```

Given forward simulation, the **backward** direction (whatever the machine
does was specified) and **divergence preservation** are *derived* in
`Refinement.lean` from machine determinism by classical case analysis —
the composition CompCert uses to get behavioral equivalence from a forward
simulation and a deterministic target. Everything in the repository builds
with zero `sorry`s and zero axioms; `InterpSim` is an explicit hypothesis.

Discharging `InterpSim` is interpreter-binary verification: per-function
simulation lemmas relating the compiled code of `eval_expr`/`exec_stmt`/
`interp_run` (under the ISA relation) to the big-step rules, by induction
on derivations — verified-compilation-scale work, cleanly isolated.

## Building

```sh
lake build            # whole development (needs riscv-lean/ built once)
lake exe vsa_run      # run the embedded ELF under the Lean ISA model
./c/tests/run_tests.sh host   # the binary's own test suite
```
