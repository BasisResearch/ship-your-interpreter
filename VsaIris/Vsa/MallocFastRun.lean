import VsaIris.Vsa.MallocFastSegs
import VsaIris.Vsa.RunBase
import VsaIris.Vsa.MallocFastHeap
import VsaIris.Vsa.Tools
import VsaIris.LocalRun
import VsaIris.Vsa.MallocFastJal

/-!
# Chaining the fast path into a local run

`seg_step` is the one step every piece of the fast path takes: a reflected
segment (`seg_runFact`) from the current owned values becomes one `LocalRun`
segment (`segFrom_of_runFact`). The continuation receives the successor's
registers and its byte image. The image is tracked as the total read of a
memory `Mt` that the segment's write log advances. The code is `pathText`,
read-only; loaded owned bytes (`LD`) and written owned bytes (`W`) are listed
explicitly. `jal_step` is the same for a `jal` site (`JalExec`).
-/

namespace VsaIris.MallocFast

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.Sim Vsa.MemRepr VsaIris.Inst
open Vsa.Machine (Config)

/-- The allocator code as read-only footprint bytes. -/
abbrev textMR : List (Nat × DFrac × BitVec 8) := pathText.map fun p => (p.1, DFrac.discard, p.2)

section Steps

variable {live : Nat → Prop} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem pathLoaded_of_foot {c : Config} (hok : VsaOk live c) (hlive : ∀ p ∈ pathText, live p.1)
    {LD : List (Nat × DFrac × BitVec 8)}
    (hmr : ∀ p ∈ textMR ++ LD, (vsaModel live).mem c p.1 = p.2.2) : PathLoaded c.σ.mem := by
  have h := code_present hok textMR (fun q hq => hmr q (List.mem_append_left _ hq))
    (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact hlive p hp)
  intro p hp
  exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)

/-- **One reflected segment of the allocator's run.** -/
theorem seg_step {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} {Mt : Mem}
    (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (LD : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 (keysG L) bs)
    (hkeys : KeysOK (keysG L)) (hwr : ∀ x ∈ wrChain bs, x ∈ keysG L)
    (hcover : ∀ a, (∀ p ∈ W, p.1 ≠ a) → OutL (segOut bs L lds).log a)
    (hlive : ∀ p ∈ pathText, live p.1)
    (hfacts : ∀ c : Config, VsaOk live c → PathLoaded c.σ.mem →
      (∀ p ∈ LD, (c.σ.mem[p.1]?).getD 0 = p.2.2) → ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hPC : VsaIris.PC ∈ rs) (hpc : rv VsaIris.PC = pc0)
    (hL : ∀ p ∈ L, (p.1 ∈ rs ∧ rv p.1 = p.2) ∨ ((p.1, p.2) ∈ roR ∧ finReg bs L lds p.1 = p.2))
    (hLD : ∀ p ∈ LD, S p.1 ∧ mv p.1 = p.2.2)
    (hW : ∀ p ∈ W, S p.1 ∧ mv p.1 = p.2)
    (himg : ∀ a, S a → mv a = imgM Mt a)
    (hnext : ∀ rv' mv', rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init L lds) bs →
      (∀ p ∈ L, rv' p.1 = finReg bs L lds p.1) →
      (∀ r ∈ rs, r ≠ VsaIris.PC → (∀ p ∈ L, p.1 ≠ r) → rv' r = rv r) →
      (∀ a, S a → mv' a = imgM (writeLog Mt (segOut bs L lds).log) a) →
      LocalRun (vsaModel live) roR pathText rs S Q n rv' mv') :
    LocalRun (vsaModel live) roR pathText rs S Q (n + 1) rv mv := by
  refine .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs L lds pc0 (textMR ++ LD) W k hlen hwf hkeys hwr hcover ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    exact hfacts c hok (pathLoaded_of_foot hok hlive hMR)
      (fun p hp => hMR p (List.mem_append_right _ hp))
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · exact .inr (hLD p hp)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl ⟨hPC, hpc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      rcases hL q hq with h | ⟨h1, h2⟩
      · exact .inl h
      · exact .inr ⟨h1, h2⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hW q hq
  · intro rv' mv' h1 h2 h3 h4
    refine hnext rv' mv' (h1 _ List.mem_cons_self)
      (fun p hp => h1 _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs L lds p.1)) hp)))
      (fun r hr hne hnL => h2 r hr fun p hp => ?_) (fun a ha => ?_)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact fun e => hne e.symm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hnL q hq
    · by_cases hw : ∃ p ∈ W, p.1 = a
      · obtain ⟨p, hp, rfl⟩ := hw
        have := h3 _ (List.mem_map_of_mem
          (f := fun p => (p.1, p.2, ((writeLog (wbase W) (segOut bs L lds).log)[p.1]?).getD 0)) hp)
        refine this.trans (writeLog_getD_congr _ _ _ _ ?_)
        obtain ⟨o', ho', hg⟩ := wbase_get hp
        rw [hg]
        have := hW _ ho'
        simp only at this
        rw [← this.2]
        exact himg _ this.1
      · have hout : ∀ p ∈ W, p.1 ≠ a := fun p hp e => hw ⟨p, hp, e⟩
        rw [h4 a ha fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact hout q hq]
        rw [himg a ha]
        unfold imgM
        rw [writeLog_out _ _ _ (hcover a hout)]

/-- **One `jal` of the allocator's run.** -/
theorem jal_step {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} {Mt : Mem}
    (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64)
    (hexec : JalExec (vsaModel live) i code tgt)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ pathText)
    (hPC : VsaIris.PC ∈ rs) (hra : VsaIris.ra ∈ rs) (hpc : rv VsaIris.PC = BitVec.ofNat 64 i)
    (himg : ∀ a, S a → mv a = imgM Mt a)
    (hnext : ∀ rv' mv', rv' VsaIris.PC = tgt → rv' VsaIris.ra = BitVec.ofNat 64 (i + 4) →
      (∀ r ∈ rs, r ≠ VsaIris.PC → r ≠ VsaIris.ra → rv' r = rv r) →
      (∀ a, S a → mv' a = imgM Mt a) →
      LocalRun (vsaModel live) roR pathText rs S Q n rv' mv') :
    LocalRun (vsaModel live) roR pathText rs S Q (n + 1) rv mv := by
  refine .inr ⟨0, segFrom_of_runFact (RR := []) (MW := [])
    (RW := [(VsaIris.PC, BitVec.ofNat 64 i, tgt), (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4))])
    (fun σ hok hf => by
      obtain ⟨σ', hs, hok', hloc⟩ := hexec (rv VsaIris.ra) σ hok hf
      exact ⟨σ', .succ hs (.zero _), hok', hloc⟩)
    (fun p hp => by cases hp) (fun p hp => .inl (hcode p hp)) ?_ (fun p hp => by cases hp) ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hpc⟩
    · exact .inl ⟨hra, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hnext rv' mv' (h1 _ List.mem_cons_self) (h1 (VsaIris.ra, rv VsaIris.ra, BitVec.ofNat 64 (i + 4)) (by simp))
      (fun r hr h1' h2' => h2 r hr fun p hp => ?_) (fun a ha => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun e => h1' e.symm
      · exact fun e => h2' e.symm
    · rw [h4 a ha (fun p hp => by cases hp), himg a ha]

end Steps

end VsaIris.MallocFast
