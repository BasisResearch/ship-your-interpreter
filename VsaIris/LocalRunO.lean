import VsaIris.LocalRun
import VsaIris.MachWP

/-!
# Printing local runs (lane N1)

`LocalRun` (LocalRun.lean) describes a silent run over an owned footprint. A
newlib stdout call prints: `_write`'s `tohost` store (`Inst.putc_runFact`)
sits inside a run of hundreds of silent instructions, inside loops. This
module extends the owned-footprint rule to runs that print:

* `SegFromO`: one segment from owned values, which may print a string `o`;
  its continuation receives `o`.
* `LRO … Q t rv mv`: the run from owned values `rv`/`mv` with the console at
  `t` reaches `Q t' rv' mv'`. It is the least predicate closed under "done"
  and "one segment, then the rest", encoded impredicatively, so a run's
  length needs no uniform fuel bound: the successor of a segment may run for
  a number of segments that depends on its state (a loop over a string's
  bytes).
* `wp_lroW`: owning the footprint and the console cell `t` proves the run,
  for either WP, by induction on `LRO`. Each segment is one `lagRun` whose
  footprint carries the console cell (as `RunFactO.lagFootPrint` does).
* `lro_of_localRun`: a silent `LocalRun` ending in `LRO` is an `LRO`, so every
  `SWP` step lemma (`SymRun.lean`, the generated step tables) drives a
  printing run between its printing steps.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- One segment of a printing run: from every well-formed state holding the
owned values, the machine runs exactly `k + 1` steps, changing only owned
cells, appending some string `o` to the output; `P o` holds of the
successor's values. -/
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

/-- A silent segment is a printing segment that prints `""`. -/
theorem SegFrom.toO {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h : SegFrom M ro text rs S k rv mv P) :
    SegFromO M ro text rs S k rv mv (fun o rv' mv' => o = "" ∧ P rv' mv') := by
  intro σ hok hro hrs hS
  obtain ⟨σ', hre, hok', hregs, hmems, hout, hp⟩ := h σ hok hro hrs hS
  exact ⟨σ', "", hre, hok', hregs, hmems, by rw [hout, String.append_empty], rfl, hp⟩

/-- **A printing run** from owned values `rv`/`mv` with the console at `t`:
the least predicate closed under `Q` (done) and one segment followed by a run
from the successor (`LRO.done`, `LRO.seg`, eliminated by `LRO.ind`). -/
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

/-- **Silent runs into printing runs.** A `LocalRun` whose end condition is
a printing run from the end values is a printing run. -/
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

theorem LRO.mono {Q' : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hQ : ∀ t rv mv, Q t rv mv → Q' t rv mv) {t : String} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (h : LRO M ro text rs S Q t rv mv) : LRO M ro text rs S Q' t rv mv :=
  LRO.ind (X := LRO M ro text rs S Q') (fun t' rv' mv' hq => LRO.done (hQ t' rv' mv' hq))
    (fun _ _ _ k hs => LRO.seg k hs) h

/-- **A printing segment is a lagged run** over the run footprint and the
console cell: the lookup reads the console from its authority (`ConAgree`),
and the commit moves the cell to the end state's output. -/
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

/-- The continuation of a printing run. -/
abbrev runKontO (Wp : MachWP (GF := GF) M) (Φ : Nat × String → IProp GF) (rs : List Nat)
    (S : Nat → Prop) (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : IProp GF :=
  iprop(∀ t' rv' mv', ⌜Q t' rv' mv'⌝ -∗ sepL rs (fun r => r ↦ᵣ rv' r) -∗
    ownSet S (fun a => a ↦ₘ mv' a) -∗ consoleOwn t' -∗ Wp.W Φ)

/-- **The printing owned-footprint run rule**, for either WP. Owning the
run's registers and bytes at their current values, the read-only cells and
the console cell at `t`, and handing the continuation the end values and the
console, proves the run. -/
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

/-- **A printing `RunFactO` is a printing segment**: the owned-footprint
reading of a run fact that appends `o` (`segFrom_of_runFact`'s printing
twin). -/
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
