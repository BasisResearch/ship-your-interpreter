# Ship your interpreter

This Lean 4 project verifies `c/while-riscv-htif.elf`, a WHILE-language
interpreter compiled to bare-metal RV64 with HTIF I/O. The proof relates an
inductive big-step semantics of WHILE to the binary's execution in the
Sail-generated RISC-V model.

The full Lean source build passes. The end-to-end theorem
`Vsa.Sim.EndToEnd.endToEnd_refinement` (`VsaIris/Interp/EndToEnd.lean`) is
proved from the named newlib holes `VsaIris.Interp.IrisHoles`
(`VsaIris/HOLES.md`). The
[proof closure plan](experiments/smt/PROOF_CLOSURE_PLAN.md) records completed
proofs, remaining obligations, and validation results. Permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. `REVIEW.md` is the
adversarial soundness review of the final theorem's hypotheses.

The tooling that makes this tractable is documented separately in
[`TOOLING.md`](TOOLING.md): proof generators, validation commands, and
incremental builds.

## Layout

| File | Content |
| --- | --- |
| `c/` | the C interpreter (lexer → parser → AST → evaluator), its host build, the cross-compiled RISC-V ELF under verification, and its test suite |
| `riscv-lean/` | vendored Sail-generated RISC-V models (`Lean_RV64D`, executable variant), a Lean emulator, and `lean-sail` at rems-project@0794631 patched so unmapped addresses read as zero (zero-initialised RAM) |
| `Vsa/ElfBytes.lean`, `Vsa/Elf.lean` | the ELF embedded byte-for-byte as a Lean term; ELFSage parse; a pure fuel-bounded runner over the Sail RV64D step. The native harness `vsa_run` reproduces the binary's behaviour: exit 0, `55\n2500\n36\n`, 382,730 steps |
| `Vsa/Machine.lean` | **the ISA as an inductive transition relation** (the graph of one architectural step), the behaviours `Halts`/`Diverges`, and determinism plus behaviour-uniqueness lemmas |
| `Vsa/While/Ast.lean` | deep embedding of WHILE, mirroring `c/src/ast.h` |
| `Vsa/While/Semantics.lean` | **the inductive big-step semantics**. Store-based mutable environments shared by closures, C truncating division, string coercion, `break`/`continue`/`return` statuses, `print`/`println`/`assert`. Purely relational: nothing in the theory evaluates WHILE |
| `Vsa/While/Derive.lean` | `bigstep_derive`, a syntax-directed tactic that *constructs* derivation trees of the big-step relation for closed programs. Untrusted meta-code; the kernel checks the derivations |
| `Vsa/While/Programs.lean`, `Vsa/While/Validation.lean` | the `c/tests/*.wl` scripts as deep embeddings, plus kernel-checked theorems `BigStep prog "<binary's output>"` that validate the semantics against I/O examples obtained by running the binary |
| `Vsa/MemRepr.lean` | **the inductive memory-representation relation**: when RV64 memory holds the C AST structs (`ast.h`, LP64, little-endian) that represent a deep-embedded program |
| `Vsa/Refinement.lean` | **the ∀-program refinement theorem** |
| `Vsa/Triple.lean` | **the Layer 1 program logic**: total-correctness Hoare triples over the ISA relation, model-independent, with step-counting (`TripleN`) for divergence simulation |
| `Vsa/Sim/` | Instruction decoding, runtime representations, function contracts, recursive simulation, and residual suppliers |
| `experiments/` | Lean proof probes, SMT and fuzz validation, and coverage data |
| `experiments/smt/PROOF_CLOSURE_PLAN.md` | Current proof status, remaining work, and incremental-build rules |

## The refinement statement

```lean
theorem refinement {L : Layout} (H : InterpSim L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Machine.Halts c out 0) ∧
      (Machine.Diverges c → ¬ ∃ out, BigStep p out)
```

`Loaded L p c` says configuration `c` sits at the interpreter phase with `p`'s
memory representation, via the inductive `ProgramRepr`. `InterpSim` is the
forward-simulation obligation. Every derivable behaviour is realised by the
machine, and underivable programs never halt cleanly.

The theorem is instantiated at `L := Vsa.Sim.LayoutInstance.interpRunLayout`
(`Vsa/Sim/LayoutInstance.lean`), whose `Loaded` is
`∃ a n, ProgramRepr c.σ.mem a n p ∧ InterpRunReady c a n`. It is the
theorem's whole hypothesis, so read it as the contract with the loaded
binary. `InterpRunReadyFacts` requires, at `interp_run`'s entry:

- **Machine state.** `pc = 0x800043ec`; the ABI arguments `a0 = &interp`
  (`0x87fffe10`), `a1 = stmts`, `a2 = count`, `a3 = 0` (script mode);
  `ra`, `sp = 0x87fffd00`, `gp`, `s0 = &_impure_ptr`; every general register
  present; `GoodState` (machine mode, `misa`/`mstatus` at their reset
  values, traps undelegated, HTIF idle); `main`'s saved return address.
- **Image and runtime data.** The exact `.text` and `.rodata` bytes of
  `c/while-riscv-htif.elf` (`FixedTextLoaded`, `FixedRodataLoaded`), the
  static pins `snprintf`/`vfprintf` read, newlib's stdout `FILE`
  (`ConsoleStream`: unbuffered, one-byte buffer, `__swrite`), the idle
  `stdin`/`stderr` `FILE`s and empty `atexit` list (`ExitRuntimeData`),
  `_impure_data._stderr`, and no console output yet (`OutRepr`).
- **The interpreter object.** `Interp.globals` and `call_depth = 0`, the
  object and its `jmp_buf` inside RAM above the HTIF words, and 8 MiB of
  stack below `sp` with every stack byte present in the memory map.
- **The AST.** `stmts` is an 8-aligned array of `count` `Stmt*` in RAM,
  `ProgramRepr` holds for `p`, and the AST's bytes are immutable shared
  bytes: outside the writable ELF sections, the stack, the global frame's
  header and arrays, and every allocation the interpreter may write
  (`InitialOwned`). Strings are ASCII (`CStr` requires bytes below 128).
- **The initial store.** The global frame holds exactly `print`, `println`,
  `assert` (`StoreRepr initSt.store` with their entry addresses), with
  capacity 8, in three whole in-use dlmalloc chunks (`BootFrameChunks`).
- **The allocator.** dlmalloc's heap `[_end, __heap_end)` in its canonical
  shape (`DlHeap.HeapAt`: a chunk walk from `_end` to the top chunk, free
  chunks on exactly one well-formed bin, page-aligned break, 32-bit
  `binblocks`, the top chunk at least 16 bytes below the break).
- **Two program-dependent assumptions**, both universally quantified over
  the program the memory represents:
  - `InitialAllocatorAt.capacity` — for every terminating derivation of
    `p` with modeled allocation cost `n` (`Vsa/While/Cost.lean`),
    `2 * n + 8256 ≤ __heap_end − top`: the heap has room for the run. A
    terminating program that allocates more than the free heap is *not*
    `Loaded`; the binary prints `out of memory` and exits 1, and the
    theorem says nothing about it.
  - `stack_admissible` — `ProgramStackFits p`: the statically computed
    stack need of `p` (nesting depth of its statements and expressions,
    the 1000-deep call budget, the evaluator frame, the helpers'
    headroom, `interp_run`'s frame) fits below `sp`, and every function
    body fits one call level.

`REVIEW.md` audits this hypothesis against the binary's real entry state;
the fields that no real run satisfies are listed there with proposals.

```lean
structure InterpSim (L : Layout) : Prop where
  term_sim  : ∀ p c out, Loaded L p c → BigStep p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded L p c → (¬ ∃ out, BigStep p out) →
              Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0
```

Given forward simulation, `Refinement.lean` *derives* the backward direction
(whatever the machine does was specified) and divergence preservation from
machine determinism by classical case analysis. This is the composition
CompCert uses to get behavioural equivalence out of a forward simulation over
a deterministic target. `InterpSim` stays an explicit hypothesis.

The simulation lemmas in `Vsa/Sim/` relate compiled
`eval_expr`/`exec_stmt`/`interp_run` code to the big-step rules by induction on
derivations.

## Building

```sh
python3 scripts/build_private.py \
  --output-root /private/tmp/vsa-full-build.sQd0gM \
  --include-executable --resume
```

Reuse the private build cache above. On a new checkout, create one external
directory with `mktemp -d` and retain it for subsequent runs. Dependencies in
`riscv-lean/` must already be built. This command typechecks all project Lean
sources, including `VsaRun.lean`.

Use the Lean version in `lean-toolchain`. Follow [CLAUDE.md](CLAUDE.md) for
proof discipline and [TOOLING.md](TOOLING.md) for focused verification.
Preserve the proof ELF; build interpreter variants in a temporary copy of `c/`.
