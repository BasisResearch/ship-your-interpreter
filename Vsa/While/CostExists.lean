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

theorem EvalECost.exists {st d a e st' v} (h : EvalE st d a e st' v) :
    ∃ n, EvalECost st d a e st' v n := costExists.evalE h
theorem EvalArgsCost.exists {st d a es st' vs} (h : EvalArgs st d a es st' vs) :
    ∃ n, EvalArgsCost st d a es st' vs n := costExists.evalArgs h
theorem CallCost.exists {st d fv vs st' v} (h : Call st d fv vs st' v) :
    ∃ n, CallCost st d fv vs st' v n := costExists.call h
theorem ExecSCost.exists {st d a s st' status} (h : ExecS st d a s st' status) :
    ∃ n, ExecSCost st d a s st' status n := costExists.execS h
theorem ExecInitCost.exists {st d a init st'} (h : ExecInit st d a init st') :
    ∃ n, ExecInitCost st d a init st' n := costExists.execInit h
theorem ForLoopCost.exists {st d a cnd step b st' status}
    (h : ForLoop st d a cnd step b st' status) :
    ∃ n, ForLoopCost st d a cnd step b st' status n := costExists.forLoop h
theorem ForCondCost.exists {st d a cnd st'} (h : ForCond st d a cnd st') :
    ∃ n, ForCondCost st d a cnd st' n := costExists.forCond h
theorem ExecStepCost.exists {st d a step st'} (h : ExecStep st d a step st') :
    ∃ n, ExecStepCost st d a step st' n := costExists.execStep h
theorem ExecSeqCost.exists {st d a ss st' status} (h : ExecSeq st d a ss st' status) :
    ∃ n, ExecSeqCost st d a ss st' status n := costExists.execSeq h

/-- The starting point of `term_sim` (§5.2 steps 1–2): a big-step behaviour
has a costed whole-program derivation with the same output. -/
theorem BigStep.cost {p : Program} {out : String} (h : BigStep p out) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out := by
  obtain ⟨st', hseq, hout⟩ := h
  obtain ⟨n, hn⟩ := ExecSeqCost.exists hseq
  exact ⟨st', n, hn, hout⟩

/-- Every cost derivation forgets to its semantic derivation, per relation. -/
structure CostSound : Prop where
  evalE : ∀ {st d a e st' v n}, EvalECost st d a e st' v n → EvalE st d a e st' v
  evalArgs : ∀ {st d a es st' vs n}, EvalArgsCost st d a es st' vs n → EvalArgs st d a es st' vs
  call : ∀ {st d fv vs st' v n}, CallCost st d fv vs st' v n → Call st d fv vs st' v
  execS : ∀ {st d a s st' status n}, ExecSCost st d a s st' status n → ExecS st d a s st' status
  execInit : ∀ {st d a init st' n}, ExecInitCost st d a init st' n → ExecInit st d a init st'
  forLoop : ∀ {st d a cnd step b st' status n}, ForLoopCost st d a cnd step b st' status n →
    ForLoop st d a cnd step b st' status
  forCond : ∀ {st d a cnd st' n}, ForCondCost st d a cnd st' n → ForCond st d a cnd st'
  execStep : ∀ {st d a step st' n}, ExecStepCost st d a step st' n → ExecStep st d a step st'
  execSeq : ∀ {st d a ss st' status n}, ExecSeqCost st d a ss st' status n →
    ExecSeq st d a ss st' status

/-- The cost companions' mutual recursor with the forgetful motives: each
cost constructor is closed by the semantic constructor of the same name, fed
the forgotten children. `constructor` takes the first constructor whose
conclusion unifies, so constructors sharing a conclusion with an earlier one
(`ifFalse` after `ifTrue`, …) are named explicitly in the fallback. -/
local macro "cost_sound_rec " r:ident h:ident : tactic => `(tactic| (
  refine $r
    (motive_1 := fun st d a e st' v _ _ => EvalE st d a e st' v)
    (motive_2 := fun st d a es st' vs _ _ => EvalArgs st d a es st' vs)
    (motive_3 := fun st d fv vs st' v _ _ => Call st d fv vs st' v)
    (motive_4 := fun st d a s st' status _ _ => ExecS st d a s st' status)
    (motive_5 := fun st d a init st' _ _ => ExecInit st d a init st')
    (motive_6 := fun st d a cnd step b st' status _ _ => ForLoop st d a cnd step b st' status)
    (motive_7 := fun st d a cnd st' _ _ => ForCond st d a cnd st')
    (motive_8 := fun st d a step st' _ _ => ExecStep st d a step st')
    (motive_9 := fun st d a ss st' status _ _ => ExecSeq st d a ss st' status)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $h
  all_goals intros
  all_goals first | (constructor <;> assumption) |
    (apply EvalE.orFalse <;> assumption) | (apply EvalE.andTrue <;> assumption) | (apply Call.closure <;> assumption) | (apply Call.print <;> assumption) | (apply Call.println <;> assumption) | (apply Call.assertOk <;> assumption) | (apply ExecS.ifFalse <;> assumption) | (apply ExecS.ifNone <;> assumption) | (apply ExecS.whileFalse <;> assumption) | (apply ExecS.whileBreak <;> assumption) | (apply ExecS.whileRet <;> assumption) | (apply ExecS.whileLoop <;> assumption) | (apply ForLoop.condFalse <;> assumption) | (apply ForLoop.bodyBreak <;> assumption) | (apply ForLoop.bodyRet <;> assumption) | (apply ForLoop.loop <;> assumption) | (apply ExecSeq.consNormal <;> assumption) | (apply ExecSeq.consAbrupt <;> assumption)))

theorem costSound : CostSound where
  evalE h := by cost_sound_rec EvalECost.rec h
  evalArgs h := by cost_sound_rec EvalArgsCost.rec h
  call h := by cost_sound_rec CallCost.rec h
  execS h := by cost_sound_rec ExecSCost.rec h
  execInit h := by cost_sound_rec ExecInitCost.rec h
  forLoop h := by cost_sound_rec ForLoopCost.rec h
  forCond h := by cost_sound_rec ForCondCost.rec h
  execStep h := by cost_sound_rec ExecStepCost.rec h
  execSeq h := by cost_sound_rec ExecSeqCost.rec h

theorem EvalECost.sound {st d a e st' v n} (h : EvalECost st d a e st' v n) :
    EvalE st d a e st' v := costSound.evalE h
theorem EvalArgsCost.sound {st d a es st' vs n} (h : EvalArgsCost st d a es st' vs n) :
    EvalArgs st d a es st' vs := costSound.evalArgs h
theorem CallCost.sound {st d fv vs st' v n} (h : CallCost st d fv vs st' v n) :
    Call st d fv vs st' v := costSound.call h
theorem ExecSCost.sound {st d a s st' status n} (h : ExecSCost st d a s st' status n) :
    ExecS st d a s st' status := costSound.execS h
theorem ExecInitCost.sound {st d a init st' n} (h : ExecInitCost st d a init st' n) :
    ExecInit st d a init st' := costSound.execInit h
theorem ForLoopCost.sound {st d a cnd step b st' status n}
    (h : ForLoopCost st d a cnd step b st' status n) :
    ForLoop st d a cnd step b st' status := costSound.forLoop h
theorem ForCondCost.sound {st d a cnd st' n} (h : ForCondCost st d a cnd st' n) :
    ForCond st d a cnd st' := costSound.forCond h
theorem ExecStepCost.sound {st d a step st' n} (h : ExecStepCost st d a step st' n) :
    ExecStep st d a step st' := costSound.execStep h
theorem ExecSeqCost.sound {st d a ss st' status n} (h : ExecSeqCost st d a ss st' status n) :
    ExecSeq st d a ss st' status := costSound.execSeq h

#print axioms costExists
#print axioms BigStep.cost
#print axioms costSound

end Vsa.While
