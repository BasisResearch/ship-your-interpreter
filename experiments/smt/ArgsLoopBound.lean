/-
# `argsLoopBoundAcrossCall` — the one premise the BMC campaign cannot discharge

The campaign reports 68 of its footprint verdicts as `VALID[modulo
argsLoopBoundAcrossCall]`.  This file says, in Lean, what that premise IS, so it
can be proved rather than described.  It is STATEMENT ONLY: a `Prop`-valued
definition with no proof term anywhere, and nothing imported into `Vsa`.  Proving `argsLoopBoundAcrossCall` and
removing the entry from `IV_PREMISE` in `scripts/houdini_summary.py` promotes
those 68 verdicts to unqualified.

## What has to hold

`loop_0x800031dc` is the argument-marshalling loop of `eval_expr`'s `EX_CALL`
arm.  It writes slot `n` of the outgoing-argument array at `sp + 240 + 24n`, and
the 1088-byte frame needs `n < 35`.  The invariant that gives it, over the
machine's own registers (`a5 = x15`, the argument count; `a6 = x16`, the
counter), SIGNED because every comparison the machine makes here is signed:

    0 ≤s a6  ∧  a6 <s a5  ∧  a5 ≤s 32

`a5 ≤s 32` is `MAX_ARGS` (`c/src/interp.c:8`), checked at runtime by
`c/src/interp.c:251` — `if (argc > MAX_ARGS) runtime_error(...)` — which the
machine performs as `blt a4,a5` at `0x800031c8`.  `bge zero,a5` at `0x800031d8`
skips an empty loop and `bne a6,a5` at `0x80003250` closes it.

So the bound is ESTABLISHED, by the arm's own branch guards, before the loop.
Nothing here is an axiom about the program.

## Why the solver cannot carry it

The loop body contains the recursive `jal ra, eval_expr` at `0x80003220`.
`a5`/`a6` are caller-saved, so the body spills them (`sd a5,24(sp)` at
`0x800031fc`, `sd a6,16(sp)` at `0x80003214`) and reloads them after
(`ld a5,24(sp)` at `0x80003230`, `ld a6,16(sp)` at `0x8000322c`).  Discharging
the invariant at the loop's OWN recursive occurrence therefore needs the bound
transported through memory across an uninterpreted callee summary.

Five routes are measured dead in `experiments/observations.md`
(`smt-args-loop-IV-obstruction`): a havoc-cut abstraction over 19 candidates in
both walk orders, a two-step lemma over 18 anchors, a reload-address cap sweep,
relevance-selected reload addresses, and a clause-bank formulation in quantified
and ground forms.  Two measured facts explain all five:

* the guards that establish the bound CANNOT be weakened — drop them and the
  invariant is REFUTED (`sat`) at 7 of the cut points, correctly;
* size is not the problem — the sliced query is 484 lines and z3 still answers
  `unknown` at 150s, and re-testing on the later 93-summary encoder fails
  identically, so the obstruction is encoder-independent.

Induction over the loop is what the proof layer can do and the solver cannot.

## The statement — AND WHY IT IS NOT HERE

A first draft of this file stated the premise as: given the bound, given the
spills agreeing with the registers, and given that the intervening run preserves
those two slots, the reloaded values satisfy the bound.

**That is a tautology.**  With `memOut slot = memIn slot` and `memIn slot = a5`,
the conclusion reduces to the hypothesis.  It assumes exactly the hard part —
that the callee does not write the caller's spill slots — and then proves the
part that needs no proof.  Shipping it would have been the same vacuity this
campaign spent a night finding in its own queries, in a file whose purpose is to
record an obstruction honestly.

The load-bearing content is the PRESERVATION itself:

    every machine run of `eval_expr` from the state at `0x80003220`
    leaves memory at `sp + 24` and `sp + 16` unchanged,
    where `sp` is the args loop's entry stack pointer

and that cannot be stated abstractly without becoming an assumption again.  It
has to be said over `Vsa.Machine.Steps`, the relation the residuals themselves
are stated over, with `sp` tied to the loop's entry state — which means it
belongs in `Vsa/Sim/` beside the other named residuals (the `hInitSome_resid`
shape), not in a standalone file under `experiments/`.

So this file deliberately stops short of a definition.  What it carries is the
address arithmetic, the provenance, and the five measured-dead routes, so that
whoever writes the real statement does not re-derive them.  `IV_PREMISE` in
`scripts/houdini_summary.py` remains the operative record that 68 verdicts rest
on it.

## The addresses, which are the reusable part

* args loop entry `0x800031dc`, recursive call `jal ra, eval_expr` at
  `0x80003220`
* spills: `sd a5,24(sp)` at `0x800031fc`, `sd a6,16(sp)` at `0x80003214`
* reloads: `ld a6,16(sp)` at `0x8000322c`, `ld a5,24(sp)` at `0x80003230`
* the bound's guards: `blt a4,a5` at `0x800031c8` (MAX_ARGS), `bge zero,a5` at
  `0x800031d8` (empty loop), `bne a6,a5` at `0x80003250` (loop close)
-/

namespace Vsa.Smt.ArgsLoopBound

/-- The two caller-frame slots the args loop spills `a5`/`a6` into, relative to
the loop's entry `sp`.  `sd a5,24(sp)` at `0x800031fc`, `sd a6,16(sp)` at
`0x80003214`.  These are the addresses the preservation obligation is about. -/
def a5Slot (sp : Nat) : Nat := sp + 24
def a6Slot (sp : Nat) : Nat := sp + 16

/-- `0 <=s a6 < a5 <=s 32`, signed, over the two register values.  Signed
because every comparison the machine makes here is: an unsigned reading lets
`a5` be `0x8000..0`, which passes the signed check and blows the bound. -/
def Bound (a5 a6 : Int) : Prop := 0 ≤ a6 ∧ a6 < a5 ∧ a5 ≤ 32

end Vsa.Smt.ArgsLoopBound
