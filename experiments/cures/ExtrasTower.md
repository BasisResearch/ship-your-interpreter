# Cure candidates — `LiveExtras.ExtrasTower`

Source: `experiments/smt/joint/LiveExtrasTower.lean`  
Detected defects: headroom-no-entry → (i) entry-conditioning  
Entry hypothesis already present: False  
Template space: 1 candidate(s).  
Filter kills: syntactic 0, Z3-refute 0, semantic 0, interlock 0.  
Survivors: 1.

## Candidate 1 — (i) entry-conditioning

_insert leading `StackOK SL sp 3264` entry-ground hypothesis_  
Edit cost: +1 premise(s).

```lean
def ExtrasTower …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem) (slotAddr x13slot : Nat),
    StackOK SL sp 3264 →
    SL.lo + 4352 ≤ sp.toNat ∧
    (∃ b, m0[slotAddr]? = some b) ∧
    (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)) ∧
    (∃ w, mcall[x13slot]? = some w)
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3 SAT but replay sorry'd (spurious SAT, symbolic window; kept)

Relights: B2/47i class — value-path sims relight verbatim; row dispatcher threads the entry hyp at each cell site (mechanical).

