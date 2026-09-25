import VsaIris.Vsa.SymRun
import VsaIris.Vsa.SymData
import VsaIris.Vsa.Console

/-!
# Local runs that may print (lane N3)

`LocalRun` (`VsaIris/LocalRun.lean`) is silent: every segment keeps the
output. newlib's write path ends in `_write`'s `tohost` store, which prints
one byte per loop iteration, so a run through it is not a `LocalRun`. This
file generalizes it:

* `SegFromO`/`LocalRunO`: a segment may extend the output by any string;
* `wp_localRunOW`: owning the run's cells and the console cell `s`, the
  continuation gets the console at `s ++ o` for some `o`, for either WP (the
  lag kernel at `SegFromO.lagFoot`, whose footprint carries the console cell);
* `SWPO`: the symbolic form (`SWP` over `LocalRunO`);
* `swpo_of_swp`: every silent `SWP` step lemma (the generated step tables)
  is a step of `SWPO`, by instantiating its end condition at the successor's
  `Matches` (`LocalRun.toO_bind`);
* `swpo_putc`: `_write`'s console store (`Inst.putcSite`) as one printing step.

The output is existential: the newlib holes print "some string".
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section RunO

variable {M : MachineModel}

/-- `SegFrom` whose output may grow: from every well-formed state holding the
owned values, `k + 1` steps to a well-formed state, confined to the owned
cells, extending the output. -/
def SegFromO (M : MachineModel) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) (k : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8)
    (P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) : Prop :=
  ∀ σ, M.ok σ → ROHolds M σ ro text → (∀ r ∈ rs, M.reg σ r = rv r) →
    (∀ a, S a → M.mem σ a = mv a) →
    ∃ σ', ReachesN M (k + 1) σ σ' ∧ M.ok σ' ∧ (∀ key, key ∉ rs → M.reg σ' key = M.reg σ key) ∧
      (∀ a, ¬ S a → M.mem σ' a = M.mem σ a) ∧ (∃ o, M.out σ' = M.out σ ++ o) ∧
      P (M.reg σ') (M.mem σ')

/-- `LocalRun` over `SegFromO`. -/
def LocalRunO (M : MachineModel) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Nat → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop
  | 0, rv, mv => Q rv mv
  | n + 1, rv, mv => Q rv mv ∨
      ∃ k, SegFromO M ro text rs S k rv mv (LocalRunO M ro text rs S Q n)

variable {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)} {rs : List Nat}
  {S : Nat → Prop}

theorem SegFrom.toO {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (h : SegFrom M ro text rs S k rv mv P) :
    SegFromO M ro text rs S k rv mv P := by
  intro σ hok hro hrs hS
  obtain ⟨σ', h1, h2, h3, h4, h5, h6⟩ := h σ hok hro hrs hS
  exact ⟨σ', h1, h2, h3, h4, ⟨"", by rw [h5, String.append_empty]⟩, h6⟩

theorem SegFromO.mono {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P P' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h : SegFromO M ro text rs S k rv mv P) (hP : ∀ rv' mv', P rv' mv' → P' rv' mv') :
    SegFromO M ro text rs S k rv mv P' := by
  intro σ hok hro hrs hS
  obtain ⟨σ', h1, h2, h3, h4, h5, h6⟩ := h σ hok hro hrs hS
  exact ⟨σ', h1, h2, h3, h4, h5, hP _ _ h6⟩

variable {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem LocalRunO.fuel_succ : ∀ {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8},
    LocalRunO M ro text rs S Q n rv mv → LocalRunO M ro text rs S Q (n + 1) rv mv
  | 0, _, _, h => .inl h
  | _ + 1, _, _, h => h.imp id fun ⟨k, hk⟩ => ⟨k, hk.mono fun _ _ h' => LocalRunO.fuel_succ h'⟩

theorem LocalRunO.fuel_mono {n n' : Nat} (hle : n ≤ n') {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} (h : LocalRunO M ro text rs S Q n rv mv) :
    LocalRunO M ro text rs S Q n' rv mv := by
  induction hle with
  | refl => exact h
  | step _ ih => exact LocalRunO.fuel_succ ih

theorem LocalRunO.mono {Q' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hQ : ∀ rv' mv', Q rv' mv' → Q' rv' mv') :
    ∀ n rv mv, LocalRunO M ro text rs S Q n rv mv → LocalRunO M ro text rs S Q' n rv mv
  | 0, _, _, h => hQ _ _ h
  | n + 1, _, _, h => by
    rcases h with h | ⟨k, h⟩
    · exact .inl (hQ _ _ h)
    · exact .inr ⟨k, h.mono fun rv' mv' hr => LocalRunO.mono hQ n rv' mv' hr⟩

/-- **A silent run, then a printing one.** A `LocalRun` to `Q`, followed from
every `Q` state by a `LocalRunO` of fuel `m`, is a `LocalRunO`. -/
theorem LocalRun.toO_bind {Q' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m : Nat}
    (hk : ∀ rv mv, Q rv mv → LocalRunO M ro text rs S Q' m rv mv) :
    ∀ n rv mv, LocalRun M ro text rs S Q n rv mv → LocalRunO M ro text rs S Q' (m + n) rv mv
  | 0, rv, mv, h => hk rv mv h
  | n + 1, rv, mv, h => by
    rcases h with h | ⟨k, h⟩
    · exact LocalRunO.fuel_mono (by omega) (hk rv mv h)
    · exact .inr ⟨k, h.toO.mono fun rv' mv' hr => LocalRun.toO_bind hk n rv' mv' hr⟩

/-- A `RunFactO` (silent or printing) whose footprint is owned is one
`SegFromO` segment (`segFrom_of_runFact`, with output). -/
theorem segFromO_of_runFactO {n : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {RW : List (Nat × BitVec 64 × BitVec 64)} {MW : List (Nat × BitVec 8 × BitVec 8)}
    {oo : Option String} {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hrun : RunFactO M n RR MR RW MW oo)
    (hRR : ∀ p ∈ RR, (p.1, p.2.2) ∈ ro ∨ (p.1 ∈ rs ∧ rv p.1 = p.2.2))
    (hMR : ∀ p ∈ MR, (p.1, p.2.2) ∈ text ∨ (S p.1 ∧ mv p.1 = p.2.2))
    (hRW : ∀ p ∈ RW, (p.1 ∈ rs ∧ rv p.1 = p.2.1) ∨ ((p.1, p.2.1) ∈ ro ∧ p.2.2 = p.2.1))
    (hMW : ∀ p ∈ MW, S p.1 ∧ mv p.1 = p.2.1)
    (hP : ∀ rv' mv', (∀ p ∈ RW, rv' p.1 = p.2.2) →
      (∀ r ∈ rs, (∀ p ∈ RW, p.1 ≠ r) → rv' r = rv r) →
      (∀ p ∈ MW, mv' p.1 = p.2.2) → (∀ a, S a → (∀ p ∈ MW, p.1 ≠ a) → mv' a = mv a) →
      P rv' mv') :
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
  have hout' : ∃ o, M.out σ' = M.out σ ++ o := by
    cases oo with
    | none => exact ⟨"", by rw [show M.out σ' = M.out σ from hout, String.append_empty]⟩
    | some o => exact ⟨o, hout⟩
  refine ⟨σ', hre, hok', fun key hk => ?_,
    fun a ha => hloc.mem_frame a fun p hp h => ha (h ▸ (hMW p hp).1), hout', hP _ _ hloc.reg_new
    (fun r hr hne => (hloc.reg_frame r hne).trans (hrs r hr)) hloc.mem_new
    (fun a ha hne => (hloc.mem_frame a hne).trans (hS a ha))⟩
  by_cases hin : ∃ p ∈ RW, p.1 = key
  · obtain ⟨p, hp, rfl⟩ := hin
    rcases hRW p hp with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 hk
    · obtain ⟨_, _, hrw, _⟩ := hfoot
      rw [hloc.reg_new p hp, h2]; exact (hrw p hp).symm
  · exact hloc.reg_frame key fun p hp h => hin ⟨p, hp, h⟩

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A `SegFromO` segment is a lagged run over `runFoot` and the console cell;
the commit sets the cell to the end state's output. -/
theorem SegFromO.lagFoot {l : List Nat} (hmem : ∀ a, a ∈ l ↔ S a) {K : Nat}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hseg : SegFromO M ro text rs S K rv mv P) (s : String) :
    LagFoot (GF := GF) M iprop(runFoot ro text rs l rv mv ∗ consoleOwn s)
      (fun σf => iprop(runFoot ro text rs l (M.reg σf) (M.mem σf) ∗ consoleOwn (M.out σf)))
      (fun σ => (ROHolds M σ ro text ∧ (∀ r ∈ rs, M.reg σ r = rv r) ∧
        (∀ a ∈ l, M.mem σ a = mv a)) ∧ M.out σ = s)
      (fun σ σf => (∀ key, key ∉ rs → M.reg σf key = M.reg σ key) ∧
        (∀ a, ¬ S a → M.mem σf a = M.mem σ a) ∧ (∃ o, M.out σf = s ++ o) ∧
        P (M.reg σf) (M.mem σf)) K where
  look mr mm mo := by
    unfold mauths
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf, Hs⟩
    ihave ⟨Hr, Hm, Hf, %h⟩ := runFoot_lookup (M := M) mr mm ro text rs l rv mv $$ [Hr Hm Hf]
    · iframe Hr Hm Hf
    unfold consoleOwn
    ihave %hs := ghost_map_lookup $$ Ho Hs
    iframe Hr Hm Ho Hf Hs
    ipureintro
    exact fun σ hr hm ho => ⟨h σ hr hm, ho s hs⟩
  run σ hok h := by
    obtain ⟨⟨hro, hrs, hl⟩, hout⟩ := h
    obtain ⟨σ', h1, h2, h3, h4, ⟨o, h5⟩, h6⟩ :=
      hseg σ hok hro hrs (fun a ha => hl a ((hmem a).2 ha))
    exact ⟨σ', h1, h2, h3, h4, ⟨o, by rw [h5, hout]⟩, h6⟩
  commit mr mm mo σ σf hr hm _ hp := by
    unfold mauths consoleOwn
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf, Hs⟩
    imod runFoot_update (M := M) mr mm ro text rs l S hmem rv mv hr hm hp.1 hp.2.1 $$ [Hr Hm Hf]
      with ⟨%mr', %mm', Hr, Hm, Hf, %⟨hr', hm'⟩⟩
    · iframe Hr Hm Hf
    imod ghost_map_update (M.out σf) $$ Ho Hs with ⟨Ho, Hs⟩
    imodintro
    iexists mr', mm', _
    iframe Hr Hm Ho Hf Hs
    ipureintro
    refine ⟨hr', hm', fun v hv => ?_⟩
    rw [LawfulPartialMap.get?_insert_eq rfl] at hv
    cases hv
    rfl

/-- The continuation of a printing local run: the final owned values and the
console extended by some string. -/
abbrev runKontOW (Wp : MachWP (GF := GF) M) (Φ : Nat × String → IProp GF) (rs : List Nat)
    (S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (s : String) : IProp GF :=
  iprop(∀ rv' mv' o, ⌜Q rv' mv'⌝ -∗ sepL rs (fun r => r ↦ᵣ rv' r) -∗
    ownSet S (fun a => a ↦ₘ mv' a) -∗ consoleOwn (s ++ o) -∗ Wp.W Φ)

/-- **Owned-footprint run rule, printing**, for either WP: `wp_localRunW`
with the console cell. The run is bounded by fuel, so no Löb is needed. -/
theorem wp_localRunOW (Wp : MachWP (GF := GF) M) {Φ : Nat × String → IProp GF} :
    ∀ n rv mv (s : String), LocalRunO M ro text rs S Q n rv mv →
      roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗
        consoleOwn s ∗ runKontOW Wp Φ rs S Q s
      ⊢ Wp.W Φ := by
  intro n
  induction n with
  | zero =>
    intro rv mv s hQ
    iintro ⟨_, Hrs, HS, Hc, Hk⟩
    iapply Hk $$ %rv %mv %"" %hQ Hrs HS
    rw [String.append_empty]
    iexact Hc
  | succ n ih =>
    intro rv mv s hrun
    rcases hrun with hQ | ⟨K, hseg⟩
    · iintro ⟨_, Hrs, HS, Hc, Hk⟩
      iapply Hk $$ %rv %mv %"" %hQ Hrs HS
      rw [String.append_empty]
      iexact Hc
    unfold roOwn ownSet
    iintro ⟨⟨#Hro, #Htx⟩, Hrs, ⟨%l, %⟨hnd, hmem⟩, Hl⟩, Hc, Hk⟩
    iapply Wp.lagRun (hseg.lagFoot (GF := GF) hmem s)
    unfold runFoot
    isplitl [Hrs Hl Hc]
    · iframe Hro Htx Hrs Hl Hc
    iintro %σ %σf %⟨_, _, ⟨o, ho⟩, hP⟩ ⟨⟨_, _, Hrs, Hl⟩, Hc⟩
    iapply Wp.lat_intro
    iapply ih _ _ _ hP
    unfold roOwn ownSet
    iframe Hro Htx Hrs Hc
    isplitl [Hl]
    · iexists l
      iframe Hl
      ipureintro; exact ⟨hnd, hmem⟩
    iintro %rv' %mv' %o' %hq Hrs HS Hc
    iapply Hk $$ %rv' %mv' %(o ++ o') %hq Hrs HS
    rw [ho, String.append_assoc]
    iexact Hc

end Wp

end RunO

end VsaIris

namespace VsaIris.Sym

open Iris Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

section SWPO

variable (live : Nat → Prop) (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
  (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)

/-- **The weakest precondition of a printing run at a symbolic state**:
`SWP` over `LocalRunO`. -/
def SWPO (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop :=
  ∃ n, ∀ rv mv, Matches rs S pc R Mt rv mv →
    LocalRunO (vsaModel live) roR text rs S Q n rv mv

variable {live text rs S Q}

theorem swpo_done {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches rs S pc R Mt rv mv → Q rv mv) : SWPO live text rs S Q pc R Mt :=
  ⟨0, h⟩

theorem swpo_congr {pc : BitVec 64} {R R' : Nat → BitVec 64} {Mt : Mem}
    (hR : ∀ r ∈ rs, r ≠ VsaIris.PC → R' r = R r) (h : SWPO live text rs S Q pc R' Mt) :
    SWPO live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv
    ⟨hm.pc, fun r hr hne => (hm.regs r hr hne).trans (hR r hr hne).symm, hm.img⟩⟩

theorem swpo_congr_mem {pc : BitVec 64} {R : Nat → BitVec 64} {Mt Mt' : Mem}
    (hM : ∀ a, S a → imgM Mt' a = imgM Mt a) (h : SWPO live text rs S Q pc R Mt') :
    SWPO live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv
    ⟨hm.pc, hm.regs, fun a ha => (hm.img a ha).trans (hM a ha).symm⟩⟩

theorem swpo_cases {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (P : Prop)
    (h1 : P → SWPO live text rs S Q pc R Mt) (h2 : ¬ P → SWPO live text rs S Q pc R Mt) :
    SWPO live text rs S Q pc R Mt := by
  by_cases h : P
  · exact h1 h
  · exact h2 h

/-- **Silent steps inside a printing run.** An `SWP` run whose end condition
is the successor symbolic state, followed by a printing run from it. Every
generated step lemma `st_<pc>`/`nt_<pc>` applies at `hk := swp_done fun _ _ h => h`. -/
theorem swpo_of_swp {pc pc' : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (h : SWP live text rs S (Matches rs S pc' R' Mt') pc R Mt)
    (hk : SWPO live text rs S Q pc' R' Mt') : SWPO live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := hk
  exact ⟨m + n, fun rv mv hmt => LocalRun.toO_bind hm n rv mv (hn rv mv hmt)⟩

/-- `swpo_of_swp` for a family of successors indexed by a word (a havoc
load): the fuel is uniform over the finitely many words (`fuel_unif`). -/
theorem swpo_of_swpV {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {pcf : BitVec 64 → BitVec 64} {Rf : BitVec 64 → Nat → BitVec 64} {Mtf : BitVec 64 → Mem}
    (h : SWP live text rs S (fun rv mv => ∃ v, Matches rs S (pcf v) (Rf v) (Mtf v) rv mv) pc R Mt)
    (hk : ∀ v, SWPO live text rs S Q (pcf v) (Rf v) (Mtf v)) : SWPO live text rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := fuel_unif (P := fun m v => ∀ rv mv, Matches rs S (pcf v) (Rf v) (Mtf v) rv mv →
      LocalRunO (vsaModel live) roR text rs S Q m rv mv)
    (fun _ _ _ hle h rv mv hmt => LocalRunO.fuel_mono hle (h rv mv hmt)) hk
  exact ⟨m + n, fun rv mv hmt =>
    LocalRun.toO_bind (fun rv' mv' ⟨v, hv⟩ => hm v rv' mv' hv) n rv mv (hn rv mv hmt)⟩

/-- **`_write`'s console store** (`0x8000005c: sd a5,-856(a6)`) prints the
byte whose putchar word is in `a5`. -/
theorem swpo_putc {R : Nat → BitVec 64} {Mt : Mem} (c : BitVec 8)
    (hcode : ∀ p ∈ codeFoot putcSite.pc putcSite.code, (p.1, p.2.2) ∈ text)
    (hlive : ∀ p ∈ codeFoot putcSite.pc putcSite.code, live p.1)
    (hPC : VsaIris.PC ∈ rs) (h16 : (16 : Nat) ∈ rs) (h15 : (15 : Nat) ∈ rs)
    (hb : R 16 = putcSite.base) (hw : R 15 = putcWord c)
    (hk : SWPO live text rs S Q 0x80000060#64 R Mt) :
    SWPO live text rs S Q 0x8000005c#64 R Mt := by
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFromO_of_runFactO
    (putc_runFact live putcSite putcSite_cert c (DFrac.own 1) (DFrac.own 1) hlive)
    ?_ (fun p hp => .inl (hcode p hp)) ?_ (fun p hp => by cases hp) ?_⟩⟩
  · intro p hp
    simp only [TohostSite.regsRead, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inr ⟨h16, (hm.regs 16 h16 (by decide)).trans hb⟩
    · exact .inr ⟨h15, (hm.regs 15 h15 (by decide)).trans hw⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact .inl ⟨hPC, hm.pc⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun e => hne e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end SWPO

end VsaIris.Sym
