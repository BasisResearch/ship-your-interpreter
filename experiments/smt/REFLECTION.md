# Steps reflection → Z3 validity (ReflectSpan.lean)

The encode-gap in every simulation residual is `Steps c c'` — the RISC-V machine
step relation inside `Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'`. This
tool reflects `Steps` into a first-order, Z3-checkable formula over one datatype

    MState = (mm : Array Int (BitVec 8), rr : Array Int Int)

and reports, per span, whether that reflection is EXACT or merely bounded.

## The encoder: bounded symbolic execution with merging

`reflectBmc` symbolically executes the span with the **PC concrete**, so every
dispatch is resolved here in Lean rather than handed to the solver. Each live
arrival carries a guard term and a state term; arrivals at the same PC in the
same round are **merged** (guard = disjunction, state = `ite` chain). Merging is
what keeps it linear: a diamond does not double and a loop does not branch, it
re-arrives at its header.

* **memory** — each store writes bytes (`int2bv`) at the exact address;
* **registers** — each instruction updates `rr` with its exact symbolic value,
  bound per instruction so a block is linear rather than quadratic;
* **loads** — `ld1/ld2/ld4/ld8` = byte assembly (`bv2int`) over `mm`;
* **bitwise/shifts** — through the bitvector theory;
* **branches** — `ite` on the exact register comparison;
* **computed gotos** — resolved against the three pinned AST-kind jump tables
  (`0x800031ac` eval kinds, `0x80003558` binary ops, `0x80004030` stmt kinds),
  read out of the ELF; the arms this resolves to are exactly the proof's
  `evalArm*`/`execArm*` constants;
* **calls** — `callee_<t>` summary, one round, no inlining;
* **loops** — a re-arrival at a header applies `loop_<h>` once and resumes at
  **every exit edge of the whole natural loop** (backward reachability), so the
  post-loop code is reflected instead of dropped.

`complete = true` for a span means the frontier emptied inside the bound: the
encoding is EXACT for that span. `complete = false` would mean arrivals were
still live and the result is bounded. Nothing is reported VALID on a span that
is not complete.

## Where it stands

* **52/52 spans complete**, at 60 rounds, average 93 KB, whole campaign emitted
  in 5 seconds (`#emit_bmc`, `spans.tsv`).
* **Two opaque symbols in the entire campaign** — the indirect calls through a
  register at `0x800039f4` and `0x80004784` (the native function pointers).
  They are listed in `opaque.tsv`, and the driver EMPTIES their clause sets
  rather than assuming them: an assumed-but-unproved clause would be an axiom
  smuggled into every query that mentions it.
* Every callee and loop summary has an obligation file — its one-step body under
  a `<sym>_ih` induction hypothesis — so its clause set is established by
  assume-guarantee induction, not asserted.

## What the measurement changed

The previous encoder classified a terminator by direction before `rd`, treated
every `jalr` as a return, and cut a back-edge by ending the path. Each of those
silently produced a verdict about something other than the residual's span:

* a backward `jal ra` is a CALL, not a loop back-edge — the two
  `jal ra, 0x80003164` inside the EX_BINARY arm made 38 spans reflect as one
  bogus `define-fun-rec`;
* `jalr x0, 0(rN)` for `rN ≠ ra` is a computed goto — the statement-arm spans
  ended seven instructions in, at `exec_stmt`'s dispatch header, and their
  "VALID" frame verdicts were verdicts about that stub;
* whatever followed a loop was dropped;
* `mkLine` falls back to `addi x0, x0, 0` on an unrecognised word, so an
  unmodelled instruction became a silent NOP.

The class map in `RESIDUAL-PLAN.md` was wrong in both directions and is now
measured rather than guessed: `hNeg`/`hNot` are loop-bearing, and
`hSExpr`/`hSRet`/`hSVarInit`/`hSRetNull`/`hSVarNull` are loop-free.

## The ground-truth cross-check

`machineSmt` is the same relation with nothing elided at all: the PC lives in
`rr[32]`, `mstep` is a balanced binary dispatch over every PC in the image, and
`mrun` is its closure. Over `[0x80000000, 0x80018be0)` that is **25336
instructions, 0 unmodelled, 0 summaries** — `Steps` with no control-flow
analysis anywhere. It is kept as the fidelity reference, not as the working
encoder: Z3 parses the 10 MB in a second but cannot take even ONE step through a
25000-arm dispatch, which is why the concrete-PC executor is the one that runs.

## Everything is in the bitvector theory

Registers and addresses are `(_ BitVec 64)` and memory is
`(Array (_ BitVec 64) (_ BitVec 8))`. Arithmetic WRAPS, as RV64 does. The earlier
`Int`-plus-`int2bv`/`bv2int` encoding was wrong twice over: it dropped 64-bit
wraparound, and it modelled `addiw`/`addw`/`subw` and the `*w` shifts as their
64-bit siblings. It was also the performance wall — `bv-bit2core` was 19350 on a
34 KB obligation, coupling the arithmetic solver to the bit-blaster.

Three further encoding choices were needed before Z3 would decide anything, each
found by measurement (see `RESIDUAL-PLAN.md` "Making it decidable"): explicit
patterns and a single address constant to break a matching loop the `qi.profile`
named; top-level `declare-const` + equational `assert` instead of `let`, so every
intermediate state is nameable and clauses ground-instantiate at the actual
application sites (QF_ABV, no quantifiers); and, for the frame / `StoreRepr` /
code-preservation family, dropping the array theory in favour of the emitted
STORE FOOTPRINT — "was this address written" is address arithmetic, and the
encoder already knows every store.

Files: `experiments/smt/ReflectSpan.lean`, `experiments/smt/ReflectResiduals.lean`,
`scripts/houdini_summary.py`.
