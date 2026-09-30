import VsaIris.LocalRun
import VsaIris.MachWP

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

def SegFromO (M : MachineModel) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) (k : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8)
    (P : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : Prop :=
  ∀ σ, M.ok σ → ROHolds M σ ro text → (∀ r ∈ rs, M.reg σ r = rv r) →
    (∀ a, S a → M.mem σ a = mv a) →
    ∃ σ' o, ReachesN M (k + 1) σ σ' ∧ M.ok σ' ∧ (∀ key, key ∉ rs → M.reg σ' key = M.reg σ key) ∧
      (∀ a, ¬ S a → M.mem σ' a = M.mem σ a) ∧ M.out σ' = M.out σ ++ o ∧
      P o (M.reg σ') (M.mem σ')

theorem SegFromO.mono {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P P' : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h : SegFromO M ro text rs S k rv mv P) (hP : ∀ o rv' mv', P o rv' mv' → P' o rv' mv') :
    SegFromO M ro text rs S k rv mv P' := by
  intro σ hok hro hrs hS
  obtain ⟨σ', o, hre, hok', hregs, hmems, hout, hp⟩ := h σ hok hro hrs hS
  exact ⟨σ', o, hre, hok', hregs, hmems, hout, hP _ _ _ hp⟩

theorem SegFrom.toO {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h : SegFrom M ro text rs S k rv mv P) :
    SegFromO M ro text rs S k rv mv (fun o rv' mv' => o = "" ∧ P rv' mv') := by
  intro σ hok hro hrs hS
  obtain ⟨σ', hre, hok', hregs, hmems, hout, hp⟩ := h σ hok hro hrs hS
  exact ⟨σ', "", hre, hok', hregs, hmems, by rw [hout, String.append_empty], rfl, hp⟩

def LRO (M : MachineModel) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop)
    (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  ∀ X : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
    (∀ t rv mv, Q t rv mv → X t rv mv) →
    (∀ t rv mv k, SegFromO M ro text rs S k rv mv (fun o => X (t ++ o)) → X t rv mv) →
    X t rv mv

variable {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)} {rs : List Nat}
  {S : Nat → Prop} {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem LRO.done {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (h : Q t rv mv) :
    LRO M ro text rs S Q t rv mv := fun _ hd _ => hd _ _ _ h

theorem LRO.ind {X : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hd : ∀ t rv mv, Q t rv mv → X t rv mv)
    (hs : ∀ t rv mv k, SegFromO M ro text rs S k rv mv (fun o => X (t ++ o)) → X t rv mv)
    {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LRO M ro text rs S Q t rv mv) : X t rv mv := h X hd hs

theorem LRO.seg {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (k : Nat)
    (h : SegFromO M ro text rs S k rv mv (fun o => LRO M ro text rs S Q (t ++ o))) :
    LRO M ro text rs S Q t rv mv :=
  fun X hd hs => hs _ _ _ k (h.mono fun _ _ _ hr => hr X hd hs)

theorem lro_of_localRun {t : String} :
    ∀ n rv mv, LocalRun M ro text rs S (LRO M ro text rs S Q t) n rv mv →
      LRO M ro text rs S Q t rv mv
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    rcases h with h | ⟨k, h⟩
    · exact h
    · refine LRO.seg k ((SegFrom.toO h).mono fun o rv' mv' ⟨ho, hr⟩ => ?_)
      subst ho
      rw [String.append_empty]
      exact lro_of_localRun n rv' mv' hr

theorem SegFromO.lagFoot {rs l : List Nat} (hmem : ∀ a, a ∈ l ↔ S a) {K : Nat}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} {t : String}
    {P : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hseg : SegFromO M ro text rs S K rv mv P) :
    LagFoot (GF := GF) M iprop(runFoot ro text rs l rv mv ∗ consoleOwn t)
      (fun σf => iprop(runFoot ro text rs l (M.reg σf) (M.mem σf) ∗ consoleOwn (M.out σf)))
      (fun σ => (ROHolds M σ ro text ∧ (∀ r ∈ rs, M.reg σ r = rv r) ∧
        (∀ a ∈ l, M.mem σ a = mv a)) ∧ M.out σ = t)
      (fun σ σf => M.out σ = t ∧ ∃ o, M.out σf = M.out σ ++ o ∧ P o (M.reg σf) (M.mem σf) ∧
        (∀ key, key ∉ rs → M.reg σf key = M.reg σ key) ∧ (∀ a, ¬ S a → M.mem σf a = M.mem σ a))
      K where
  look mr mm mo := by
    unfold mauths
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf, Hs⟩
    ihave ⟨Hr, Hm, Hf, %h⟩ := runFoot_lookup (M := M) mr mm ro text rs l rv mv $$ [Hr Hm Hf]
    · iframe Hr Hm Hf
    unfold consoleOwn
    ihave %hs := ghost_map_lookup $$ Ho Hs
    iframe Hr Hm Ho Hf Hs
    ipureintro
    exact fun σ hr hm ho => ⟨h σ hr hm, ho t hs⟩
  run σ hok hp := by
    obtain ⟨⟨hro, hrs, hl⟩, ht⟩ := hp
    obtain ⟨σ', o, hre, hok', hregs, hmems, hout, hP⟩ :=
      hseg σ hok hro hrs (fun a ha => hl a ((hmem a).2 ha))
    exact ⟨σ', hre, hok', ht, o, hout, hP, hregs, hmems⟩
  commit mr mm mo σ σf hr hm ho hp := by
    obtain ⟨_, o, _, _, hregs, hmems⟩ := hp
    unfold mauths
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf, Hs⟩
    imod runFoot_update (M := M) mr mm ro text rs l S hmem rv mv hr hm hregs hmems $$ [Hr Hm Hf]
      with ⟨%mr', %mm', Hr, Hm, Hf, %⟨hr', hm'⟩⟩
    · iframe Hr Hm Hf
    unfold consoleOwn
    imod ghost_map_update (M.out σf) $$ Ho Hs with ⟨Ho, Hs⟩
    imodintro
    iexists mr', mm', _
    iframe Hr Hm Ho Hf Hs
    ipureintro
    refine ⟨hr', hm', fun v hv => ?_⟩
    rw [LawfulPartialMap.get?_insert_eq rfl] at hv
    cases hv
    rfl

abbrev runKontO (Wp : MachWP (GF := GF) M) (Φ : Nat × String → IProp GF) (rs : List Nat)
    (S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : IProp GF :=
  iprop(∀ t' rv' mv', ⌜Q t' rv' mv'⌝ -∗ sepL rs (fun r => r ↦ᵣ rv' r) -∗
    ownSet S (fun a => a ↦ₘ mv' a) -∗ consoleOwn t' -∗ Wp.W Φ)

theorem wp_lroW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF}
    {t : String} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LRO M ro text rs S Q t rv mv) :
    roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗
      consoleOwn t ∗ runKontO Wp Φ rs S Q ⊢ Wp.W Φ := by
  refine LRO.ind (X := fun t rv mv => roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗
      ownSet S (fun a => a ↦ₘ mv a) ∗ consoleOwn t ∗ runKontO Wp Φ rs S Q ⊢ Wp.W Φ)
    (fun t rv mv hq => ?_) (fun t rv mv K hseg => ?_) h
  · iintro ⟨_, Hrs, HS, Hc, Hk⟩
    iapply Hk $$ %t %rv %mv %hq Hrs HS Hc
  · unfold roOwn ownSet
    iintro ⟨⟨#Hro, #Htx⟩, Hrs, ⟨%l, %⟨hnd, hmem⟩, Hl⟩, Hc, Hk⟩
    iapply Wp.lagRun (hseg.lagFoot (t := t) hmem)
    unfold runFoot
    isplitl [Hrs Hl Hc]
    · iframe Hro Htx Hrs Hl Hc
    iintro %σ %σf %⟨ht, o, hout, hP, _, _⟩ ⟨⟨_, _, Hrs, Hl⟩, Hc⟩
    iapply Wp.lat_intro
    rw [hout, ht]
    have hP' := hP
    iapply hP'
    unfold roOwn ownSet
    iframe Hro Htx Hrs Hk Hc
    iexists l
    iframe Hl
    ipureintro; exact ⟨hnd, hmem⟩

theorem segFromO_of_runFactO {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {RW : List (Nat × BitVec 64 × BitVec 64)} {MW : List (Nat × BitVec 8 × BitVec 8)}
    {o : String} {P : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hrun : RunFactO M n RR MR RW MW (some o))
    (hRR : ∀ p ∈ RR, (p.1, p.2.2) ∈ ro ∨ (p.1 ∈ rs ∧ rv p.1 = p.2.2))
    (hMR : ∀ p ∈ MR, (p.1, p.2.2) ∈ text ∨ (S p.1 ∧ mv p.1 = p.2.2))
    (hRW : ∀ p ∈ RW, (p.1 ∈ rs ∧ rv p.1 = p.2.1) ∨ ((p.1, p.2.1) ∈ ro ∧ p.2.2 = p.2.1))
    (hMW : ∀ p ∈ MW, S p.1 ∧ mv p.1 = p.2.1)
    (hP : ∀ rv' mv', (∀ p ∈ RW, rv' p.1 = p.2.2) →
      (∀ r ∈ rs, (∀ p ∈ RW, p.1 ≠ r) → rv' r = rv r) →
      (∀ p ∈ MW, mv' p.1 = p.2.2) → (∀ a, S a → (∀ p ∈ MW, p.1 ≠ a) → mv' a = mv a) →
      P o rv' mv') :
    SegFromO M ro text rs S n rv mv P := by
  intro σ hok hro hrs hS
  have hfoot : FootHolds (M := M) σ RR MR RW MW := by
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rcases hRR p hp with h | ⟨h1, h2⟩
      · exact hro.1 _ h
      · rw [hrs _ h1, h2]
    · rcases hMR p hp with h | ⟨h1, h2⟩
      · exact hro.2 _ h
      · rw [hS _ h1, h2]
    · rcases hRW p hp with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [hrs _ h1, h2]
      · exact hro.1 _ h1
    · obtain ⟨h1, h2⟩ := hMW p hp; rw [hS _ h1, h2]
  obtain ⟨σ', hre, hok', hloc, hout⟩ := hrun σ hok hfoot
  refine ⟨σ', o, hre, hok', fun key hk => ?_,
    fun a ha => hloc.mem_frame a fun p hp h => ha (h ▸ (hMW p hp).1), hout, hP _ _ hloc.reg_new
    (fun r hr hne => (hloc.reg_frame r hne).trans (hrs r hr)) hloc.mem_new
    (fun a ha hne => (hloc.mem_frame a hne).trans (hS a ha))⟩
  by_cases hin : ∃ p ∈ RW, p.1 = key
  · obtain ⟨p, hp, rfl⟩ := hin
    rcases hRW p hp with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 hk
    · obtain ⟨_, _, hrw, _⟩ := hfoot
      rw [hloc.reg_new p hp, h2]; exact (hrw p hp).symm
  · exact hloc.reg_frame key fun p hp h => hin ⟨p, hp, h⟩

end

end VsaIris
