import Vsa.Machine

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
open LeanRV64DExecutable
open Register

/-- The caller-frame slot holding the spilled argument count `a5`, relative to
the args loop's entry stack pointer. -/
def a5SpillSlot (sp : Nat) : Nat := sp + 24

/-- The caller-frame slot holding the spilled counter `a6`. -/
def a6SpillSlot (sp : Nat) : Nat := sp + 16

/-- **THE RESIDUAL.**  Any machine run that starts where the args loop makes its
recursive call leaves the caller's two spill slots untouched.

`c` is the configuration at `0x80003220` with the loop's entry stack pointer in
`x2`; `c'` is any configuration the machine can reach from it.  The claim is
per-byte over the eight bytes of each slot, matching how the model reads them
(`readByte` is `getD 0`, so a byte-level equality is what a load consumes).

This is DELIBERATELY stated over an arbitrary reachable `c'` rather than over
`eval_expr`'s return specifically: the loop reloads after the call returns, and
any intermediate state reached during the call is also covered, which is what
makes the property an induction over the run rather than a fact about one exit.

Proving it discharges `argsLoopBoundAcrossCall` and promotes the campaign's 68
`VALID[modulo ...]` verdicts to unqualified.  NO PROOF IS PROVIDED HERE — this
is the statement, named so the gap is visible rather than implicit. -/
def argsLoopSpillPreserved : Prop :=
  ∀ (c c' : Config) (sp : Nat),
    c.σ.regs.get? Register.x2 = some (BitVec.ofNat 64 sp) →
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 0x80003220) →
    Steps c c' →
    ∀ k, k < 8 →
      (c'.σ.mem[a5SpillSlot sp + k]? = c.σ.mem[a5SpillSlot sp + k]?
       ∧ c'.σ.mem[a6SpillSlot sp + k]? = c.σ.mem[a6SpillSlot sp + k]?)

end Vsa.Sim
