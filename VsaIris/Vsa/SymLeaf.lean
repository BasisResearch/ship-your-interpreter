import VsaIris.Vsa.SymRunO

/-!
# A leaf call inside a symbolic run (lane N1)

A callee that is a silent local run on a SMALLER footprint (fewer registers
`rs'`, fewer owned bytes `S'`, a sub-list `T` of the read-only bytes, no
read-only register) — `strlen` (`StrLeaf.strlenRunL`) — runs inside a
caller's `SWPO` run: `LocalRun.frame` widens it to the caller's footprint,
keeping every caller register outside `rs'` and every caller byte outside
`S'`, and `swpo_leaf` continues the caller from each state the callee ends
in. The continuation is an `LRO` (a least fixed point), so it needs no fuel
bound uniform in the callee's end state.
-/

namespace VsaIris

variable {M : MachineModel}

/-- The caller's registers outside `rs'` and bytes outside `S'` as at `rv0`/`mv0`. -/
def LeafFrame (rs rs' : List Nat) (S S' : Nat → Prop) (rv0 : Nat → BitVec 64) (mv0 : Nat → BitVec 8)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  (∀ x ∈ rs, x ∉ rs' → rv x = rv0 x) ∧ (∀ a, S a → ¬ S' a → mv a = mv0 a)

/-- **Framing a local run** into a larger footprint. -/
theorem LocalRun.frame {ro : List (Nat × BitVec 64)} {text T : List (Nat × BitVec 8)}
    {rs rs' : List Nat} {S S' : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hT : ∀ q ∈ T, q ∈ text) (hrs : ∀ r ∈ rs', r ∈ rs) (hS : ∀ a, S' a → S a)
    (rv0 : Nat → BitVec 64) (mv0 : Nat → BitVec 8) :
    ∀ n rv mv, LocalRun M [] T rs' S' Q n rv mv → LeafFrame rs rs' S S' rv0 mv0 rv mv →
      LocalRun M ro text rs S (fun rv mv => Q rv mv ∧ LeafFrame rs rs' S S' rv0 mv0 rv mv) n rv mv
  | 0, _, _, h, hf => ⟨h, hf⟩
  | n + 1, rv, mv, h, hf => by
    rcases h with h | ⟨k, hseg⟩
    · exact .inl ⟨h, hf⟩
    refine .inr ⟨k, fun σ hok hro hr hm => ?_⟩
    obtain ⟨σ', hreach, hok', hreg, hmem, hout, hP⟩ :=
      hseg σ hok ⟨fun p hp => (List.not_mem_nil hp).elim, fun p hp => hro.2 p (hT p hp)⟩
        (fun r hr' => hr r (hrs r hr')) (fun a ha => hm a (hS a ha))
    refine ⟨σ', hreach, hok', fun key hk => hreg key (fun h => hk (hrs key h)),
      fun a ha => hmem a (fun h => ha (hS a h)), hout, ?_⟩
    refine LocalRun.frame hT hrs hS rv0 mv0 n _ _ hP ⟨fun x hx hx' => ?_, fun a ha ha' => ?_⟩
    · rw [hreg x hx', hr x hx]; exact hf.1 x hx hx'
    · rw [hmem a ha', hm a ha]; exact hf.2 a ha ha'

end VsaIris

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

/-- **A leaf call inside a printing run.** From every state matching the
call's entry, the leaf's run on `[] / T / rs' / S'` ends in `Q1`; from each
such end state, with the caller's other registers and bytes as at the call,
the caller's run continues. -/
theorem swpo_leaf {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {T : List (Nat × BitVec 8)} {rs' : List Nat} {S' : Nat → Prop}
    {Q1 : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hT : ∀ q ∈ T, q ∈ text) (hrs : ∀ r ∈ rs', r ∈ rs) (hpc : VsaIris.PC ∈ rs')
    (hS : ∀ a, S' a → S a)
    (hleaf : ∃ n, ∀ rv mv, Matches rs' S' pc R Mt rv mv →
      LocalRun (vsaModel live) [] T rs' S' Q1 n rv mv)
    (hk : ∀ rv mv, Q1 rv mv → (∀ x ∈ rs, x ∉ rs' → rv x = R x) →
      (∀ a, S a → ¬ S' a → mv a = imgM Mt a) → LRO (vsaModel live) roR text rs S Q t rv mv) :
    SWPO live text rs S Q t pc R Mt := by
  obtain ⟨n, hn⟩ := hleaf
  refine ⟨0, fun rv mv hm => ?_⟩
  show LRO (vsaModel live) roR text rs S Q t rv mv
  have hl := hn rv mv ⟨hm.pc, fun r hr hr' => hm.regs r (hrs r hr) hr', fun a ha => hm.img a (hS a ha)⟩
  have hf := LocalRun.frame (ro := roR) (text := text) (rs := rs) (S := S) hT hrs hS rv mv n rv mv hl
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  refine lro_of_localRun n rv mv (LocalRun.mono (fun rv' mv' ⟨hq, hfr⟩ => ?_) n rv mv hf)
  refine hk rv' mv' hq (fun x hx hx' => ?_) (fun a ha ha' => ?_)
  · rw [hfr.1 x hx hx', hm.regs x hx (fun e => hx' (e ▸ hpc))]
  · rw [hfr.2 a ha ha', hm.img a ha]

end VsaIris.Sym
