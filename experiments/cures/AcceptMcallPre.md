# Cure candidates — `CegisAcceptC.AcceptMcallPre`

Source: `experiments/cegis/AcceptC_McallPair.lean`  
Detected defects: mcall-total-presence → (ii) quantifier repair, agree-off-window → (iii) guard repair  
Entry hypothesis already present: False  
Template space: 2 candidate(s).  
Filter kills: syntactic 0, Z3-refute 0, semantic 0, interlock 0.  
Survivors: 2.

## Candidate 1 — (iii) guard repair

_flip agree-OFF-[SL.lo,sp) to agree-ON-[SL.lo,SL.hi) (covering window)_  
Edit cost: 0 premise(s).

```lean
def AcceptMcallPre …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, (SL.lo ≤ a ∧ a < SL.hi) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, ∃ b, mcall[a]? = some b
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3 SAT but replay sorry'd (spurious SAT, symbolic window; kept)

Relights: EntryStackSurv/47e class — the store-survival + agree conduits widen to the full stack window; children absorbed.

## Candidate 2 — (ii) quantifier repair

_bound the ∀a presence demand to the dead-byte read footprint_  
Edit cost: 0 premise(s).

```lean
def AcceptMcallPre …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat,
        ((sp.toNat - 1120 ≤ a ∧ a < sp.toNat)) →
        ∃ b, mcall[a]? = some b
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3 SAT but replay sorry'd (spurious SAT, symbolic window; kept)

Relights: McallPop class — the 6 unary/logical Resid + NegResid/NotResid presence conjuncts; SubEvalReturn buffer-write supplies the footprint presence.

