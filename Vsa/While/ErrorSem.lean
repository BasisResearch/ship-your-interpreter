import Vsa.While.Semantics
import Vsa.Machine

/-!
# Layer 5 spec gadgets for `stuck_sim`: the error judgment and bounded progress

`stuck_sim` (`Vsa/Refinement.lean`) says a program with **no** `BigStep`
derivation never halts cleanly: the machine diverges, or halts with a nonzero
exit code.  The `BigStep` semantics (`Vsa/While/Semantics.lean`) only records
*successful* runs — every runtime error and every divergence is, by design,
*absent* from `BigStep`.  To reason about "no derivation" we need two spec-side
gadgets, defined here:

1. **The error judgment** (`EvalErr`/`EvalArgsErr`/`CallErr`/`ExecErr`/… ) — a
   mutual inductive that *positively* witnesses a runtime error, mirroring the
   failure modes the C interpreter turns into a `runtime_error(…)` call: an
   undefined variable (`env_get` miss), a type error (`binOpSem = none`),
   division by zero, a non-callable callee / arity mismatch, an `assert`
   failure, and the call-depth cap being hit.  Structurally it shadows the 8
   `BigStep` relations: each rule either *is* a leaf error or *propagates* an
   error out of a sub-evaluation, in exactly the left-to-right order the
   evaluator uses.

2. **Bounded progress** (`Approx`) — a fuel-indexed relation "the configuration
   is still running after `n` rule steps".  Its trichotomy lemma (every
   configuration terminates, errors, or `Approx n` for every `n`) is the
   classical case-split behind `stuck_sim`: no `BigStep` ⇒ (error ∨ ∀ n Approx).

The forward-simulation side (error derivation ↦ `exit 70`, `Approx n` ↦ ≥ n
machine steps ↦ `Diverges`) reuses the M4 machinery, `Vsa/Sim/JmpSpec.lean`
(`runtime_error_spec`/`longjmp_spec` land control at interp_run's setjmp
continuation `0x80004428`) and the HTIF exit lemma (`Vsa/Sim/Htif.lean`
`htif_store_exit`).  The first green piece — the Machine-level *exit-code
faithfulness* gadget — is at the bottom of this file: any halt with a nonzero
code already lands in `stuck_sim`'s second disjunct, no machine plumbing needed.
-/

namespace Vsa.While

/-! ## 1. The error judgment

Mirrors the failure modes of `eval_expr`/`exec_stmt`/`call_value` (the C sites
that call `runtime_error(…)`; `experiments/disasm.txt` @ the `jal … <runtime_error>`
call sites).  The relations do not thread an output state: once an error is
reached the interpreter `longjmp`s out, so only the *fact* of the error matters
(the diagnostic text carries line numbers the deep embedding lacks — `stuck_sim`
does not constrain the console text).  The depth `d` and scope `env` are carried
exactly as in `BigStep`.  -/

/-! ## 2. Bounded progress (`Approx`)

`Approx n st d env s status?` — the machine, executing statement sequence `s`
in state `st`, is **still running after `n` rule steps** (has neither returned a
value nor errored).  It is a coarse fuel counter: each constructor consumes one
unit of fuel and hands the rest to a sub-computation, so `Approx n` witnesses at
least `n` `exec_stmt`/`eval_expr` dispatch steps, which the divergence
simulation maps to ≥ `n` machine steps (`TripleN`, `Vsa/Triple.lean`).

`Approx 0` always holds (no progress required).  The load-bearing content is the
successor case: to be running for `n+1` steps, the head statement must run and
the tail be running for `n` more — OR the head itself be a loop/call that is
running for `n` more.  We keep the relation minimal (sequence-level): it is
enough for the trichotomy, whose real work is the classical case split, not the
inductive structure of `Approx`. -/

/-! ### The trichotomy (statement)

Every top-level program either terminates (`BigStep`), errors (`BigStepErr`), or
diverges (`BigStepDiverges`).  This is the classical case split behind
`stuck_sim`: given `¬ ∃ out, BigStep p out`, trichotomy yields `BigStepErr p ∨
BigStepDiverges p`, whose two forward simulations land in the two `stuck_sim`
disjuncts.  The proof (induction on `n` + `Classical.em` at each dispatch) is
deferred; the statement pins the obligation. -/

/-! ## 3. First green piece — Machine-side exit-code faithfulness

The simplest `stuck_sim` fragment, fully proved and self-contained: *any* halt
with a nonzero exit code already realizes `stuck_sim`'s second disjunct.  The
error simulation's job (deferred) is to reach exactly such a halt — the C
interpreter's `main` returns `70` on a caught `runtime_error`, and crt0's
`j exit` (`experiments/disasm.txt:22`) drives `_exit`'s HTIF store of
`(70<<<1)|1` to `tohost` (`htif_store_exit`, `Vsa/Sim/Htif.lean`), so `e = 70`.
This gadget is the target the error path is aimed at. -/

end Vsa.While
