import VsaIris.Vsa.Tools
import VsaIris.LocalRun

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config)
open Vsa.Sim

section SegRun

variable {live : Nat → Prop}

theorem segFrom_of_segW {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (MR : List (Nat × DFrac × BitVec 8))
    (W : List (Nat × BitVec 8)) (n : Nat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG L) bs) (hkeys : KeysOK (keysG L))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG L)
    (hcover : ∀ a, (∀ q ∈ W, q.1 ≠ a) → OutL (segOut bs L lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs L lds pc0) (segMW bs L lds W) →
      ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hMR : ∀ q ∈ MR, (q.1, q.2.2) ∈ text ∨ (S q.1 ∧ mv q.1 = q.2.2))
    (hW : ∀ q ∈ W, S q.1 ∧ mv q.1 = q.2)
    (hPC : VsaIris.PC ∈ rs) (hpc : rv VsaIris.PC = pc0)
    (hL : ∀ q ∈ L, q.1 ∈ rs ∧ q.2 = rv q.1)
    (hP : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init L lds) bs →
      (∀ q ∈ L, rv' q.1 = finReg bs L lds q.1) →
      (∀ k ∈ rs, k ≠ VsaIris.PC → (∀ q ∈ L, q.1 ≠ k) → rv' k = rv k) →
      (∀ q ∈ W, mv' q.1 = newByte bs L lds W q.1) →
      (∀ a, S a → (∀ q ∈ W, q.1 ≠ a) → mv' a = mv a) → P rv' mv') :
    SegFrom (vsaModel live) ro text rs S n rv mv P := by
  refine segFrom_of_runFact
    (seg_runFact live bs L lds pc0 MR W n hlen hwf hkeys hwr hcover hfacts)
    (fun p hp => nomatch hp) hMR ?_ ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl ⟨hPC, hpc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact Or.inl ⟨(hL q hq).1, (hL q hq).2.symm⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hW q hq
  · intro rv' mv' hnew hframe hmemNew hmem
    refine hP rv' mv' (hnew _ List.mem_cons_self) (fun q hq => hnew _ (.tail _
      (List.mem_map_of_mem (f := fun p : Nat × BitVec 64 => (p.1, p.2, finReg bs L lds p.1)) hq)))
      (fun k hk hkpc hkL => hframe k hk fun p hp => ?_)
      (fun q hq => hmemNew _ (List.mem_map_of_mem
        (f := fun p : Nat × BitVec 8 =>
          (p.1, p.2, ((writeLog (wbase W) (segOut bs L lds).log)[p.1]?).getD 0)) hq))
      (fun a ha hne => hmem a ha fun p hp => ?_)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact fun e => hkpc e.symm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hkL q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hne q hq

def leafL (regs : List Nat) (rv : Nat → BitVec 64) : GRegs := regs.map (fun k => (k, rv k))

theorem keysG_leafL : ∀ (regs : List Nat) (rv : Nat → BitVec 64), keysG (leafL regs rv) = regs
  | [], _ => rfl
  | k :: ks, rv => by
    show k :: keysG (leafL ks rv) = k :: ks
    rw [keysG_leafL ks rv]

theorem leafStep {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (regs : List Nat) (m : Nat)
    (bs : List BBlock) (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (MR : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hkeys : KeysOK regs) (hwf : ChainOK pc0 regs bs)
    (hwr : ∀ k ∈ wrChain bs, k ∈ regs)
    (hcover : ∀ a, (∀ q ∈ W, q.1 ≠ a) → OutL (segOut bs (leafL regs rv) lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs (leafL regs rv) lds pc0)
        (segMW bs (leafL regs rv) lds W) →
      ChainFacts c.σ.mem c.σ.mem (leafL regs rv) lds bs)
    (hMR : ∀ q ∈ MR, (q.1, q.2.2) ∈ text ∨ (S q.1 ∧ mv q.1 = q.2.2))
    (hW : ∀ q ∈ W, S q.1 ∧ mv q.1 = q.2)
    (hpc : rv VsaIris.PC = pc0)
    (hnext : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init (leafL regs rv) lds) bs →
      (∀ k ∈ regs, rv' k = finReg bs (leafL regs rv) lds k) →
      (∀ q ∈ W, mv' q.1 = newByte bs (leafL regs rv) lds W q.1) →
      (∀ a, S a → (∀ q ∈ W, q.1 ≠ a) → mv' a = mv a) →
      LocalRun (vsaModel live) ro text (VsaIris.PC :: regs) S Q m rv' mv') :
    LocalRun (vsaModel live) ro text (VsaIris.PC :: regs) S Q (m + 1) rv mv := by
  refine Or.inr ⟨n, segFrom_of_segW bs (leafL regs rv) lds pc0 MR W n hlen
    (by rw [keysG_leafL]; exact hwf) (by rw [keysG_leafL]; exact hkeys)
    (by rw [keysG_leafL]; exact hwr) hcover hfacts hMR hW List.mem_cons_self hpc
    (fun q hq => ?_) (fun rv' mv' h1 h2 h3 h4 h5 => hnext rv' mv' h1 (fun k hk => ?_) h4 h5)⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    exact ⟨.tail _ hk, rfl⟩
  · exact h2 (k, rv k) (List.mem_map_of_mem (f := fun k => (k, rv k)) hk)

def AluStep (live : Nat → Prop) (i : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (rd : Nat) (val : BitVec 64) : Prop :=
  ∀ c : Config, VsaOk live c → vsaReg c VsaIris.PC = BitVec.ofNat 64 i →
    (∀ q ∈ RR, vsaReg c q.1 = q.2.2) → (∀ q ∈ MR, (vsaModel live).mem c q.1 = q.2.2) →
    ∃ c' : Config, Vsa.Machine.Step c c' ∧ VsaOk live c' ∧
      vsaReg c' VsaIris.PC = BitVec.ofNat 64 (i + 4) ∧ vsaReg c' rd = val ∧
      (∀ k, k ≠ VsaIris.PC → k ≠ rd → vsaReg c' k = vsaReg c k) ∧
      (∀ a, (vsaModel live).mem c' a = (vsaModel live).mem c a) ∧
      (vsaModel live).out c' = (vsaModel live).out c

theorem runFact_of_aluStep {live : Nat → Prop} {i : Nat}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {rd : Nat} {old val : BitVec 64} (h : AluStep live i RR MR rd val) :
    RunFact (vsaModel live) 0 RR MR
      [(VsaIris.PC, BitVec.ofNat 64 i, BitVec.ofNat 64 (i + 4)), (rd, old, val)] [] := by
  intro c hok hfoot
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hpc : vsaReg c VsaIris.PC = BitVec.ofNat 64 i := hRW _ List.mem_cons_self
  obtain ⟨c', hstep, hok', hpc', hrd', hframe, hmem, hout⟩ := h c hok hpc hRR hMR
  refine ⟨c', ReachesN.succ (M := vsaModel live) (vsaStep_of_step hstep) (ReachesN.zero (M := vsaModel live) c'), hok', ⟨?_, ?_, ?_, ?_⟩,
    hout⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpc'
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hrd'
      · cases hq
  · intro k hk
    exact hframe k (fun e => hk _ List.mem_cons_self e.symm)
      (fun e => hk _ (.tail _ List.mem_cons_self) e.symm)
  · intro q hq; cases hq
  · intro a _; exact hmem a

theorem localRun_succ {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} :
    ∀ (n : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
      LocalRun (vsaModel live) ro text rs S Q n rv mv →
      LocalRun (vsaModel live) ro text rs S Q (n + 1) rv mv
  | 0, _, _, h => .inl h
  | n + 1, rv, mv, h => by
    rcases h with h | ⟨k, h⟩
    · exact .inl h
    · exact .inr ⟨k, h.mono fun rv' mv' hr => localRun_succ n rv' mv' hr⟩

theorem localRun_le {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {n n' : Nat} (hn : n ≤ n') {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LocalRun (vsaModel live) ro text rs S Q n rv mv) :
    LocalRun (vsaModel live) ro text rs S Q n' rv mv := by
  induction n' with
  | zero => rwa [Nat.le_zero.mp hn] at h
  | succ m ih =>
    rcases Nat.lt_or_ge m n with hm | hm
    · rwa [show m + 1 = n from by omega]
    · exact localRun_succ m rv mv (ih hm)

theorem readBytes_present {c : Config} (hok : VsaOk live c)
    (MR : List (Nat × DFrac × BitVec 8))
    (hmr : ∀ p ∈ MR, (vsaModel live).mem c p.1 = p.2.2)
    (hlive : ∀ p ∈ MR, live p.1) : ∀ p ∈ MR, c.σ.mem[p.1]? = some p.2.2 :=
  code_present hok MR hmr hlive

end SegRun

end VsaIris.Inst
