# Cure candidates — `CegisAcceptB.AcceptMemExtPre`

Source: `experiments/cegis/AcceptB_MemExt.lean`  
Detected defects: memext-over-quant → (iv) conjunct deletion, memext-over-quant → (iii) guard repair  
Entry hypothesis already present: False  
Template space: 2 candidate(s).  
Filter kills: syntactic 0, Z3-refute 0, semantic 0, interlock 0.  
Survivors: 2.

## Candidate 1 — (iv) conjunct deletion

_DELETE the ∀m→MemExtends conjunct (block output `_hpresM` supplies it)_  
Edit cost: -1 premise(s).

```lean
def AcceptMemExtPre …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    True
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3 SAT modulo opaque symbol (not machine-checked; kept)
- **semantic**: PASS — semantic rule: every demand address covered (or SMT territory)

Relights: 48f class — `blockA_k`/`blockA_binaryArm` `_hpresM` output supplies it; zero downstream churn (consumers take the struct as a hypothesis).

## Candidate 2 — (iii) guard repair

_flip agree-OFF-[SL.lo,sp) to agree-ON-[SL.lo,SL.hi) (covering window)_  
Edit cost: 0 premise(s).

```lean
def AcceptMemExtPre …: Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    True ∧
    (∀ m : Mem,
      (∀ a : Nat, (SL.lo ≤ a ∧ a < SL.hi) → m[a]? = m0[a]?) →
      MemExtends m0 m)
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — Z3 SAT modulo opaque symbol (not machine-checked; kept)
- **semantic**: PASS — semantic rule: every demand address covered (or SMT territory)

Relights: EntryStackSurv/47e class — the store-survival + agree conduits widen to the full stack window; children absorbed.

