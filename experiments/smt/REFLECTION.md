# Steps reflection → Z3 validity (ReflectSpan.lean)

The encode-gap in every simulation residual is `Steps c c'` — the RISC-V machine
step relation inside `Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'`. This
tool reflects `Steps` into an EXACT, gap-free, Z3-checkable first-order formula,
with no approximation anywhere.

## What it does

Reads the proof ELF (`c/while-riscv-htif.elf`), decodes each span word with the
proof's own `mkLine`, and reflects the machine effect over one datatype

    MState = (mm : Array Int (BitVec 8), rr : Array Int Int)

threaded through the whole control-flow graph:

* **memory** — each store writes bytes (`int2bv`) into `mm` at the exact address;
* **registers** — each instruction updates `rr` with its exact symbolic value;
* **loads** — `ld1/ld4/ld8` = byte-assembly (`bv2int`) over `mm`, exact;
* **bitwise** — `bvor_i/bvand_i/bvxor_i` via `int2bv`/`bv2int`, exact;
* **branches** — `ite` on the exact register/memory comparison (`branchCondSt`);
* **calls** — `callee_t : MState → MState`, axiom = the callee's OWN body
  reflection (every register + memory outcome reflected — NO ABI clobber/return
  conventions);
* **loops** — `define-fun-rec loop_t(S) = ite(loopcond_t S, S, loop_t body)`,
  the exact recursive memory+register effect.

`#reflect_exact "<path>" <lo> <hi>` writes the complete SMT; `emitExactAxioms`
recursively closes the callee/loop summaries.

## Verified

* auto-decode matches `WlogExtract`'s hand-written `brkContProlog` exactly;
* the eval-expr call span reflects to `callee_exec_stmt` as a `(MState) MState`
  function defined by its body's `ite` over exact register selects — 0 ABI
  symbols;
* Z3 parses the exact SMT clean; loads/bitwise are byte-assembly, not
  uninterpreted;
* **validity**: on the exact prologue reflection, Z3 proves frame preservation —
  `(not (= (select mem_exit A) (select (mm s0) A)))` for `A` below the spill
  frame is UNSAT. Reflect `Steps` exactly → Z3 checks validity, end to end, for
  straight-line spans.
* **all 52 encodable**: `ReflectResiduals.lean` maps every open residual to its
  concrete span (`KindTablePins` eval arms, exec_stmt dispatch statement arms,
  `seqLoopImage` seq loops) — 53/53 reflect exactly, gap-free, DAG-sized (largest
  15KB, no blowup). Rests on complete MKind coverage (every instruction exact:
  immediates from the word, shifts via BV, U-type corrected) + the let-DAG.
* **per-residual validity**: frame preservation on the reflected UNARY arm
  `Steps` is UNSAT (proved) — the end-to-end pipeline (reflect a real residual's
  span → Z3 proves a Post conjunct) works, not just the prologue.

## Remaining

1. **Loop invariants** for Z3 *termination* on the `define-fun-rec` loops — the
   encoding is exact and gap-free, but deciding a loop-bearing residual needs the
   loop invariant as the recursion's decidability lemma (autoprove/Houdini mines
   it, emitted as the `loopcond_t`/`loop_t` lemma).
2. **Per-residual span wiring** — each residual class pins its concrete spans in
   a ground table (`seqLoopImage` and analogues); wire those into the encoder so
   a residual's `Steps` is the reflected `mem_exit`, and encode its pre/post
   (`SegEntry`/`SegExit`) over the same `MState`.

Files: `experiments/smt/ReflectSpan.lean`, `experiments/smt/WlogExtract.lean`.
