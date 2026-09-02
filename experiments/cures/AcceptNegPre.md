# Cure candidates — `CegisAcceptA.AcceptNegPre`

Source: `experiments/cegis/AcceptA_Neg.lean`  
Detected defects: headroom-no-entry → (i) entry-conditioning  
Entry hypothesis already present: False  
Template space: 1 candidate(s).  
Filter kills: syntactic 0, Z3-refute 0, semantic 0.  
Survivors: 1.

## Candidate 1 — (i) entry-conditioning

_insert leading `StackOK SL sp 3264` entry-ground hypothesis_  
Edit cost: +1 premise(s).

```lean
def AcceptNegPre …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64),
    StackOK SL sp 3264 →
    SL.lo + 3264 ≤ sp.toNat
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3: negation UNSAT (no countermodel in fragment)
- **semantic**: PASS — semantic rule: every demand address covered (or SMT territory)

Relights: B2/47i class — value-path sims relight verbatim; row dispatcher threads the entry hyp at each cell site (mechanical).

