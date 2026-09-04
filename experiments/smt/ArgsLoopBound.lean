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

## The statement

`Vsa.Machine.Steps` is the machine step relation the residuals are stated over.
`argsLoopSpill`/`argsLoopReload` name the four slots above, relative to the
loop's entry `sp`.  The premise is a preservation property of ONE iteration:
enter the body with the bound and the spills agreeing with the registers, and
whatever the recursive call does, the reloads bring the bound back.

The obligation is deliberately stated over an ARBITRARY intervening run rather
than over `eval_expr` specifically: what it needs is that the callee does not
write the caller's two spill slots, which is `above_sp` restricted to those two
addresses, and `eval_expr`'s own frame lies below them.  That restriction is
true where the unrestricted `above_sp` is false (the sret buffer the callee
writes is a DIFFERENT address at or above `sp`), which is why the clause bank
cannot supply it and this premise must.
-/

namespace Vsa.Smt.ArgsLoopBound

/-- The two caller-frame slots the args loop spills `a5`/`a6` into, relative to
the loop's entry `sp`.  `sd a5,24(sp)` at `0x800031fc`, `sd a6,16(sp)` at
`0x80003214`. -/
def a5Slot (sp : Nat) : Nat := sp + 24
def a6Slot (sp : Nat) : Nat := sp + 16

/-- `0 ≤s a6 < a5 ≤s 32`, signed, over the two register values. -/
def Bound (a5 a6 : Int) : Prop := 0 ≤ a6 ∧ a6 < a5 ∧ a5 ≤ 32

/-- **THE PREMISE.**  If the bound holds on entry to one iteration of
`loop_0x800031dc`, and the two spill slots agree with the registers there, then
for any run that preserves memory at those two slots, the bound holds again at
the reload.

`preserves` is the only thing asked of the intervening call, and it is strictly
weaker than `above_sp`: it constrains two addresses, not every address at or
above `sp`.  That is what makes it TRUE of `eval_expr`, whose result write goes
to the caller-passed sret buffer — a different address in the same region, which
is exactly why the unrestricted clause is false and this one is not.

Proving this discharges `argsLoopBoundAcrossCall` and promotes 68 campaign
verdicts from `VALID[modulo ...]` to unqualified. -/
def argsLoopBoundAcrossCall : Prop :=
  ∀ (sp : Nat) (a5 a6 : Int) (memIn memOut : Nat → Int),
    Bound a5 a6 →
    memIn (a5Slot sp) = a5 →
    memIn (a6Slot sp) = a6 →
    -- the intervening run preserves the caller's two spill slots
    (memOut (a5Slot sp) = memIn (a5Slot sp)) →
    (memOut (a6Slot sp) = memIn (a6Slot sp)) →
    -- so the reloaded values still satisfy it, and the counter may advance once
    Bound (memOut (a5Slot sp)) (memOut (a6Slot sp))

end Vsa.Smt.ArgsLoopBound
