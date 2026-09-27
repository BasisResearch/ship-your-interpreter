import Vsa.While.Cost

namespace Vsa.While

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

theorem BigStep.cost {p : Program} {out : String} (h : BigStep p out) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out := by
  obtain ⟨st', hseq, hout⟩ := h
  obtain ⟨n, hn⟩ := ExecSeqCost.exists hseq
  exact ⟨st', n, hn, hout⟩

end Vsa.While
