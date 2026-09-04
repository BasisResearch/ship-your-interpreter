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

/-!
## RETRACTED: the obvious statement is FALSE, and here is the counterexample

`argsLoopSpillPreserved`, as first written here, quantified over an ARBITRARY
configuration `c'` reachable from the call site and claimed both slots are
preserved.  That is false, and the machine says so directly.  Disassembling the
loop body `0x800031dc .. 0x80003250`:

    0x800031fc  sd x15,24(x2)      spill a5
    0x80003214  sd x16,16(x2)      spill a6
    0x80003220  jal ra, eval_expr  the recursive call
    0x8000322c  ld x16,16(x2)      reload a6
    0x80003230  ld x15,24(x2)      reload a5
    0x80003250  bne x16,x15, 0x800031dc   BACK EDGE

**Both spills are inside the loop body.**  So a `c'` in the second iteration,
after `0x80003214` has run again, has a DIFFERENT byte at `sp + 16`: `a6` was
incremented.  Reachability from the call site therefore includes states where
the slot is legitimately rewritten, and the universally quantified claim is
refuted by the program's own control flow.

(The `a5` slot happens to survive, because the count is loop-invariant and the
re-spill writes the same value.  That is a coincidence of this loop, not a
property worth stating.)

## What the statement has to say instead, and why it is not written here

The preservation must be bounded to ONE callee activation — from the call at
`0x80003220` to its matching return at `0x80003224`, with no intervening pass
through the loop header.  Expressing "the matching return" is the whole
difficulty: `Steps` is a reflexive-transitive closure with no notion of the
first arrival, and `eval_expr` is recursive, so a later configuration with the
same PC and the same `sp` may belong to a different activation.

Getting that right means either a step-indexed formulation (`StepsN`, with the
callee's run bounded) or a callee-contract shape of the kind
`Vsa.Alloc.MallocContract` uses, where the run is characterised by its entry and
exit rather than by reachability.  Both are real design decisions about the
proof layer, and this file will not guess at one: two attempts have already been
retracted here, a tautology and then this falsity, both from reaching for
something shaped like the premise without checking it against the machine.

What this file now carries is what is CHECKED: the addresses, the guards that
establish the bound, the counterexample above, and the five measured-dead SMT
routes.  `IV_PREMISE` in `scripts/houdini_summary.py` remains the operative
record that 68 verdicts rest on the unproved premise.
-/

end Vsa.Sim
