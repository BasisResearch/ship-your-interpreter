import Vsa.Triple
import Vsa.MemRepr
import Vsa.Sim.InterpEntry

/-!
# `argsLoopSpillPreserved` — the BMC campaign's one undischarged premise

The SMT campaign reports 68 of its footprint verdicts as
`VALID[modulo argsLoopBoundAcrossCall]` (`IV_PREMISE` in
`scripts/houdini_summary.py`, listed in `bmc/assumed-final.tsv`).  This file
states, over the machine relation the residuals themselves use, what that
premise actually needs.  It is a NAMED RESIDUAL in the sense of CLAUDE.md law 2
— a statement-only `def`, no proof term, nothing that could pass for one.

## What the campaign cannot discharge

`loop_0x800031dc` is the argument-marshalling loop of `eval_expr`'s `EX_CALL`
arm.  It writes argument slot `n` at `sp + 240 + 24n`, and the 1088-byte frame
needs `n < 35`.  The invariant that gives it is, over the machine's registers
(`a5 = x15` the count, `a6 = x16` the counter), and SIGNED because every
comparison the machine makes here is:

    0 ≤s a6  ∧  a6 <s a5  ∧  a5 ≤s 32

That bound is ESTABLISHED before the loop by the arm's own branch guards —
`blt a4,a5` at `0x800031c8` is the `MAX_ARGS` check that `c/src/interp.c:251`
performs (`if (argc > MAX_ARGS) runtime_error(...)`), `bge zero,a5` at
`0x800031d8` skips an empty loop, `bne a6,a5` at `0x80003250` closes it.  So
nothing here is an axiom about the program; the bound is a consequence of code
the machine runs.

What defeats the solver is TRANSPORT.  The loop body makes the recursive call
`jal ra, eval_expr` at `0x80003220`, and `a5`/`a6` are caller-saved, so the body
spills them and reloads them across it:

| | address | site |
|---|---|---|
| spill `a5` | `sp + 24` | `sd a5,24(sp)` at `0x800031fc` |
| spill `a6` | `sp + 16` | `sd a6,16(sp)` at `0x80003214` |
| reload `a6` | `sp + 16` | `ld a6,16(sp)` at `0x8000322c` |
| reload `a5` | `sp + 24` | `ld a5,24(sp)` at `0x80003230` |

Discharging the invariant at the loop's own recursive occurrence therefore needs
the bound carried through MEMORY across an uninterpreted callee summary.  Five
routes are measured dead in `experiments/observations.md`
(`smt-args-loop-IV-obstruction`): a havoc-cut abstraction over 19 candidate cut
points in both walk orders, a two-step lemma over 18 anchors, a reload-address
cap sweep, relevance-selected reload addresses, and a clause-bank formulation in
quantified and ground forms.  Two measured facts explain all five at once:

* **the guards cannot be weakened** — drop them and the invariant is REFUTED
  (`sat`) at 7 of the cut points, correctly, since the bound lives in them;
* **size is not the problem** — the sliced query is 484 lines and z3 still
  answers `unknown` at 150 s, identically on the later 93-summary encoder, so
  the obstruction is encoder-independent.

## Why this is the statement, and not the transport

An earlier attempt stated the premise as "given the bound, and given that the
run preserves the two slots, the reloaded values satisfy the bound".  That is a
TAUTOLOGY: the conclusion reduces to the hypothesis.  It assumed the hard part
and proved the part needing none.

The hard part is the preservation itself, and it is not derivable from the
clause bank.  `above_sp` — "a callee writes nothing at or above its entry `sp`,
outside the arena" — is FALSE of `eval_expr`, which writes its result into the
sret buffer the caller passed, an address at or above `sp`.  That is why
`above_sp` is dropped for the assumed summaries (`houdini_summary.py`) and why
no clause the campaign can mine supplies this.

What IS true is the restriction of that claim to these two addresses:
`eval_expr`'s own frame lies below the caller's `sp`, and the sret buffer it
writes is a different address from the caller's spill slots.  Stating and
proving the restriction is what the proof layer can do by induction over the
callee's run, and the solver cannot.
-/

namespace Vsa.Sim

open Vsa.Machine
open Vsa.Logic
open Vsa.MemRepr
open LeanRV64DExecutable
open Register

/-- The caller-frame slot holding the spilled argument count `a5`, relative to
the args loop's entry stack pointer. -/
def a5SpillSlot (sp : Nat) : Nat := sp + 24

/-- The caller-frame slot holding the spilled counter `a6`. -/
def a6SpillSlot (sp : Nat) : Nat := sp + 16

/-!
## Two retractions, and the shape that works

**First attempt, a TAUTOLOGY.**  It assumed the run preserves the two slots and
concluded the reloaded values satisfy the bound.  The conclusion reduces to the
hypothesis: it assumed the hard part.

**Second attempt, FALSE.**  It quantified over an arbitrary configuration
reachable from the call site.  The machine refutes that, because BOTH spills are
inside the loop body:

    0x800031fc  sd x15,24(x2)      spill a5
    0x80003214  sd x16,16(x2)      spill a6
    0x80003220  jal ra, eval_expr
    0x8000322c  ld x16,16(x2)      reload a6
    0x80003230  ld x15,24(x2)      reload a5
    0x80003250  bne x16,x15, 0x800031dc    BACK EDGE

A `c'` in the second iteration, past `0x80003214`, has a different byte at
`sp + 16`: `a6` was incremented.  (`a5`'s slot survives only because the count
is loop-invariant — a coincidence of this loop, not a property.)

**What both attempts got wrong** is the same thing: preservation has to be
bounded to ONE callee activation, and `Steps` — a reflexive-transitive closure —
cannot say "the matching return" on its own.

**The shape that works is already in the repo.**  `Vsa.Alloc.MallocContract.spec`
is a `Triple`, and `Triple P Q := ∀ c, P c → ∃ c', Steps c c' ∧ Q c'`.  The
existential names the return state of THIS call, so an activation is
characterised by its entry and exit rather than by reachability — exactly the
missing piece.  Its frame conjunct is the model to copy:

    ∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?

"untouched outside the private footprint and outside the stack strictly BELOW
the entry `sp`".  The callee's own frame lives below entry `sp` and may change;
everything at or above it is preserved.  The args loop's spill slots are at
`sp + 16` and `sp + 24`, above `eval_expr`'s entry `sp`, so they fall in the
preserved half — which is precisely why the restricted claim is true where the
unrestricted `above_sp` clause is false.  `above_sp` fails only on the sret
buffer the callee writes, and that is a different address from these two.
-/

/-- **THE RESIDUAL**, in the `MallocContract.spec` shape.

One activation of `eval_expr`, entered with return address `r` and stack pointer
`sp`, returns to `r` with `sp` restored and leaves the caller's two argument-loop
spill slots byte-for-byte unchanged.

The `Triple` is what bounds this to a SINGLE activation: its existential is the
return state of this call, so nothing here quantifies over reachability and the
second-iteration counterexample above cannot arise.

Only the two slots are claimed, not the whole region at or above `sp`.  That
restriction is the point: the unrestricted claim (`above_sp`) is FALSE of
`eval_expr`, which writes its result into the caller-passed sret buffer, and the
campaign correctly refutes it.  These two addresses are not that buffer.

Proving this discharges `argsLoopBoundAcrossCall` (`IV_PREMISE` in
`scripts/houdini_summary.py`) and promotes 68 campaign verdicts from
`VALID[modulo ...]` to unqualified.  STATEMENT ONLY — no proof term here. -/
def argsLoopSpillPreserved : Prop :=
  ∀ (sp r : BitVec 64) (m0 : Mem),
    Triple
      (fun c =>
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) ∧
        c.σ.regs.get? Register.x1 = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.mem = m0)
      (fun c =>
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ∀ k, k < 8 →
          c.σ.mem[a5SpillSlot sp.toNat + k]? = m0[a5SpillSlot sp.toNat + k]?
          ∧ c.σ.mem[a6SpillSlot sp.toNat + k]? = m0[a6SpillSlot sp.toNat + k]?)

end Vsa.Sim
