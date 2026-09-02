# Cure candidates — `CegisLive.BinIntLive`

Source: `experiments/cegis/LiveBinIntCell.lean`  
Detected defects: size-eq-unrelated → (i) entry-conditioning, extras-bundle-entry-pins → (i) entry-conditioning  
Entry hypothesis already present: False  
Template space: 1 candidate(s).  
Filter kills: syntactic 0, Z3-refute 0, semantic 0.  
Survivors: 1.

## Candidate 1 — (i) entry-conditioning

_insert leading `StackOK SL sp 3264` entry-ground hypothesis_  
Edit cost: +1 premise(s).

```lean
def BinIntCellResid_live …: Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat) (st st' st'' : While.St) (el er : Expr) (a b : Int) (sp r sret aExpr : BitVec 64) (m0 : Mem),
    StackOK SL sp 3264 →
    st'.store.frames.size = st''.store.frames.size ∧
    st'.store.closures.size = st''.store.closures.size ∧
    StoreBodiesBound st'.store perCallBudget ∧
    ∃ aLOp aROp Wl, BinArmExtras g N A SL BinOp.add el er sp r sret aExpr aLOp aROp m0 ∧
    ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64), (∀ (c' : Config), TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size st' st'' (Value.int a) (Value.int b) sp r sret v8 v9 v18 m0 c' → AddResid gpre N A SL sp r sret aExpr Wl c') ∧ g x8 = some v8 ∧ g x9 = some v9 ∧ g x18 = some v18 ∧ g x2 = some sp ∧ g x19 = some v19 ∧ ∀ (R : Register), AbiPreservedNoise R → (x8 == R) = false → (x9 == R) = false → (x18 == R) = false → (x2 == R) = false → gpre R = g R
```

Per-filter evidence:
- **syntactic**: PASS — elaborates
- **smt**: PASS — encoder gap (kept, defer to semantic filter)
- **semantic**: PASS — semantic rule: every demand address covered (or SMT territory)

Relights: B2/47i class — value-path sims relight verbatim; row dispatcher threads the entry hyp at each cell site (mechanical).

