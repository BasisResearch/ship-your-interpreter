# Ship your interpreter: the result

Language implementations are trusted software. Every program we write passes through one, and we believe its output only because we believe the implementation agrees with the language's semantics. Verified compilers prove that agreement for compilers. Interpreters, the implementations most languages actually ship, rarely get the same treatment, and when they do the proof stops at the source code of the interpreter rather than the binary people run.

We closed that gap for one small language. The artefact is a WHILE interpreter written in C, with a lexer, a parser and a tree-walking evaluator supporting closures, strings, integer arithmetic and runtime errors. It is compiled to a bare-metal RV64 ELF, links against dlmalloc and newlib, and prints through the HTIF console. The proof relates that exact binary, byte for byte, to an inductive big-step semantics of WHILE.

The machine is the Sail RISC-V model, so every instruction the binary executes is accounted for, including the allocator's chunk surgery and the formatted printing inside newlib. The theorem, in Lean 4, is

```lean
theorem endToEnd_refinement (h : IrisHoles) :
    ∀ p c, Loaded interpRunLayout p (fillZero c) →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)
```

and `IrisHoles` has no fields, so the result is unconditional. For every program the binary loads, the program derives output `out` exactly when the machine halts printing `out` with exit code 0, and a diverging machine means no derivation exists. The only axioms are Lean's standard three.

For months the proof stalled on framing. Each time the proof needed a new fact about memory, that fact had to be carried through every case of the evaluator and re-proved to survive every write. The allocator was worse, since dlmalloc writes its chunk headers at addresses that depend on the heap's state, so no fixed footprint could even state what malloc touches. Porting MachCSL's approach (Kaashoek and Zeldovich's concurrent separation logic over Sail) to iris-lean removed that whole class of work. Once the allocator owns its own free bytes, the frame rule keeps a caller's data safe across a call. We then proved the real `_malloc_r`, `_free_r` and `_realloc_r` instead of assuming a contract for them. The remaining cases fell in about three days of agent-driven proof, run as parallel lanes over a shared design.

The hypothesis `Loaded` deserves as much scrutiny as the conclusion, because a theorem about configurations that never occur says nothing. An adversarial review found exactly that, since the original boundary pinned a console flag, some script bytes and a fully present stack that no real boot state satisfies. After those were repaired, we built `Loaded` for ten programs from real boot traces of the binary. A second review replayed the machine from the ELF and reached a memory pointwise equal to the witness, and a hypothesis-free theorem shows the proof ELF halts printing `55 2500 36`.

Two assumptions remain, and both are about the program rather than the proof. Its heap use must fit the arena, and its recursion depth must fit the stack, which is simply what it means for a bounded machine to run a program to completion. The links from the ELF file to the embedded bytes and from the emulator's trace to the boot state are checked natively rather than in the kernel, and both are cross-checked by exact replay.
