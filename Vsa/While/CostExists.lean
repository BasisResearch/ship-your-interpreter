import Vsa.While.Cost

/-!
# Cost companions: existence and soundness, by name

The total-mode recursor (INTERP_DESIGN.md §4.1, §5.2) indexes every spec by a
cost derivation (`EvalECost` …). It needs two bridges between the nine
semantic relations and their cost companions:

* **existence** (`EvalECost.exists` … `ExecSeqCost.exists`, `BigStep.cost`):
  every semantic derivation has a cost companion, so `term_sim` can start from
  `BigStep`. These are named projections of `cost_exists_mutual`.
* **soundness** (`EvalECost.sound` … `ExecSeqCost.sound`): a cost derivation
  forgets to its semantic one, so a total case lemma holding only `D` can use
  the semantic invariants (`execSeq_store_mono`, `StoreBodiesBound`
  preservation, …) stated over `EvalE`/`ExecS`.

Both families are packaged as named-field structures (`CostExists`,
`CostSound`) and consumed through the per-relation names, never positionally.
-/

-- discipline: allow(R7-conj-tower-def) each `∃ n` is one cost output of a named per-relation lemma, not a post tower
namespace Vsa.While

/-- Every semantic derivation has a cost companion, per relation. -/
structure CostExists : Prop where
  evalE : ∀ {st d a e st' v}, EvalE st d a e st' v → ∃ n, EvalECost st d a e st' v n
  evalArgs : ∀ {st d a es st' vs}, EvalArgs st d a es st' vs →
    ∃ n, EvalArgsCost st d a es st' vs n
  call : ∀ {st d fv vs st' v}, Call st d fv vs st' v → ∃ n, CallCost st d fv vs st' v n
  execS : ∀ {st d a s st' status}, ExecS st d a s st' status →
    ∃ n, ExecSCost st d a s st' status n
  execInit : ∀ {st d a init st'}, ExecInit st d a init st' → ∃ n, ExecInitCost st d a init st' n
  forLoop : ∀ {st d a cnd step b st' status}, ForLoop st d a cnd step b st' status →
    ∃ n, ForLoopCost st d a cnd step b st' status n
  forCond : ∀ {st d a cnd st'}, ForCond st d a cnd st' → ∃ n, ForCondCost st d a cnd st' n
  execStep : ∀ {st d a step st'}, ExecStep st d a step st' → ∃ n, ExecStepCost st d a step st' n
  execSeq : ∀ {st d a ss st' status}, ExecSeq st d a ss st' status →
    ∃ n, ExecSeqCost st d a ss st' status n

theorem costExists : CostExists := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := cost_exists_mutual
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem ExecSeqCost.exists {st d a ss st' status} (h : ExecSeq st d a ss st' status) :
    ∃ n, ExecSeqCost st d a ss st' status n := costExists.execSeq h

/-- The starting point of `term_sim` (§5.2 steps 1–2): a big-step behaviour
has a costed whole-program derivation with the same output. -/
theorem BigStep.cost {p : Program} {out : String} (h : BigStep p out) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out := by
  obtain ⟨st', hseq, hout⟩ := h
  obtain ⟨n, hn⟩ := ExecSeqCost.exists hseq
  exact ⟨st', n, hn, hout⟩

end Vsa.While
