import Vsa.Triple

/-!
# `DeriveCallSeg` — the reusable `jal rd` call-splice combinator (Shape D, v2 layer)

This is the LAST v2 metaprogram piece from
`experiments/exponentiation-endgame-design.md` (Shape D — "call/marshal w/ callee
contract"): a machine call site is a `jal rd` splice `prefix ≫ callee ≫ suffix`,
composed with `Triple.seq`.  The closure crux
`Vsa/Sim/EvalCallClosure.lean` (`callClosureSim`) ALREADY does exactly this by
hand — its final line is literally

```
Triple.seq (Triple.seq (hEntry …) hBodyIH) (hRet …)   -- prefix ≫ body-IH ≫ return
```

— prefix seam ≫ body-IH (the named callee) ≫ return seam.  Every other call site
(native calls, `env_new`/`env_define`/`realloc` composition, the closure body-IH)
has the same three-seam shape.  This file extracts that pattern into a REUSABLE,
named combinator so any call site drops in: name the callee contract once, and the
two `Triple.seq`s are free.

Everything here is pure `Triple.seq`/`Triple.conseq` plumbing — NO reflection, NO
machine unfolding — so it is model-independent and lives over abstract
`Config → Prop` predicates.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

namespace Vsa.Sim

open Vsa.Machine (Config)
open Vsa.Logic (Triple)

/-! ## The core combinator

A call site splices three straight/contract segments at two seam predicates
`Mid1` (the callee-entry marshalling boundary) and `Mid2` (the callee-return
marshalling boundary):

* `pre    : Triple P    Mid1` — the caller-side prefix (arg marshalling, arity /
  depth guards, `jal rd` link, frame setup) up to the callee's entry;
* `callee : Triple Mid1 Mid2` — the NAMED callee contract (body IH / native
  contract / `env_new` etc.); nothing is proven here, it is threaded in;
* `suf    : Triple Mid2 Q` — the caller-side return marshalling (result copy,
  `--call_depth`, epilogue join) from the callee's exit to the call site's post.

The value is entirely in the packaging: one lemma name that documents the
call-splice idiom, so a caller writes `callSeg pre callee suf` instead of a bare
nested `Triple.seq (Triple.seq …) …` whose associativity/seam order must be
re-derived at each site. -/

/-- **The `jal rd` call-splice combinator.**  `prefix ≫ callee ≫ suffix`.
Given the caller prefix `Triple P Mid1`, the named callee contract
`Triple Mid1 Mid2`, and the caller return-suffix `Triple Mid2 Q`, produce the
whole call site `Triple P Q`.  This is exactly the composition line at the end of
`callClosureSim`, extracted so every call site reuses it. -/
theorem callSeg {P Mid1 Mid2 Q : Config → Prop}
    (pre : Triple P Mid1) (callee : Triple Mid1 Mid2) (suf : Triple Mid2 Q) :
    Triple P Q :=
  Triple.seq (Triple.seq pre callee) suf

/-! ## Seam-massaging variant

In practice the callee contract is stated over its OWN entry/exit predicates
(`C_in`/`C_out`) that are only propositionally equal to the prefix post / suffix
pre — e.g. the closure body IH is a `SegEntry → SegExit` at the closure's chosen
PCs, which the prefix lands at and the suffix consumes, but the marshalling
between them needs a `Triple.conseq`.  `callSegConseq` threads two entailments
(`hin : Mid1 ⊆ C_in`, `hout : C_out ⊆ Mid2`) so the caller can drop the callee
contract in at its native predicates without re-plumbing the seams. -/

/-- **Seam-adapted call-splice.**  Same `prefix ≫ callee ≫ suffix`, but the named
callee contract is stated over its own boundary predicates `C_in`/`C_out`; the
seam entailments `hin`/`hout` glue the prefix post `Mid1` into `C_in` and the
callee exit `C_out` into the suffix pre `Mid2`.  This is `callSeg` with a
`Triple.conseq` wrapped around the callee — the exact glue a real call site needs
when the callee contract's predicates are named independently. -/
theorem callSegConseq {P Mid1 Mid2 Q C_in C_out : Config → Prop}
    (pre : Triple P Mid1) (callee : Triple C_in C_out) (suf : Triple Mid2 Q)
    (hin : ∀ c, Mid1 c → C_in c) (hout : ∀ c, C_out c → Mid2 c) :
    Triple P Q :=
  callSeg pre (Triple.conseq callee hin hout) suf

/-! ## Demo (a): the abstract 3-seam splice mirroring `callClosureSim`

Over abstract `P/Mid1/Mid2/Q` predicates, `callSeg` reconstructs the exact shape
of `callClosureSim`'s final composition: prefix seam ≫ body-IH (callee) ≫ return
seam.  This is the combinator firing — the whole `Call.closure` crux composition
reduced to the reusable idiom. -/
theorem callSegDemo {P Mid1 Mid2 Q : Config → Prop}
    (hEntry : Triple P Mid1)      -- the ClosureEntrySpec prefix seam
    (hBodyIH : Triple Mid1 Mid2)  -- the recursive body IH (the callee contract)
    (hRet : Triple Mid2 Q) :      -- the ClosureRetSpec return seam
    Triple P Q :=
  callSeg hEntry hBodyIH hRet

#print axioms callSegDemo

/-! ## Demo (b): reproducing `callClosureSim`'s composition line

A faithful stand-in for `callClosureSim`: the three seams named exactly as there
(`ClosureEntrySpec`-post / body-IH / `ClosureRetSpec`), threaded through `callSeg`
to yield the `CallEntryP → CallExitP` call-site Triple.  Here `CallEntryP`,
`SegEntry`(body-loop head), `SegExit`(body-ret PC), `CallExitP` are abstract
`Config → Prop` placeholders standing for the concrete predicates in
`EvalCallClosure.lean`; the point is that the SAME `callSeg` call reproduces the
crux's composition without the hand-rolled nested `Triple.seq`. -/
theorem callClosureSimShape
    {CallEntryP SegEntryBody SegExitBody CallExitP : Config → Prop}
    (hEntry : Triple CallEntryP SegEntryBody)   -- prefix: dispatch → body-loop head
    (hBodyIH : Triple SegEntryBody SegExitBody) -- body-IH: the recursor's mExecSeq
    (hRet : Triple SegExitBody CallExitP) :     -- return: body-exit → epilogue join
    Triple CallEntryP CallExitP :=
  callSeg hEntry hBodyIH hRet

#print axioms callClosureSimShape

/-! ## Demo (c): the seam-massaging variant firing

The callee contract stated over independent boundaries `C_in`/`C_out`, glued into
the prefix/suffix seams by `callSegConseq`. -/
theorem callSegConseqDemo
    {P Mid1 Mid2 Q C_in C_out : Config → Prop}
    (pre : Triple P Mid1) (callee : Triple C_in C_out) (suf : Triple Mid2 Q)
    (hin : ∀ c, Mid1 c → C_in c) (hout : ∀ c, C_out c → Mid2 c) :
    Triple P Q :=
  callSegConseq pre callee suf hin hout

#print axioms callSegConseqDemo

end Vsa.Sim
