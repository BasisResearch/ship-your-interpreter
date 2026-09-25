import VsaIris.Vsa.SymRunO
import VsaIris.Vsa.SymData

/-!
# Running a sub-run proved over another step table (lane N5)

Each generated step table (`interpText`, `stdioText`, …) states its lemmas
over `SWP` at its own read-only list. A routine proved over one table (E2's
`udiv_iw` over the interpreter's) is reusable inside a run over another when
the first list is contained in the second: a segment only reads its
read-only cells (`ROHolds`), so more cells never hurt (`SegFrom.text_mono`,
`LocalRun.text_mono`, `swp_text_mono`).

`swpo_bridge` is the composition: a continuation-form lemma over `T1`
(stated for every end condition `Q'`), instantiated at the printing run's
own end condition over `T2 ⊇ T1`, whose continuation is read back from the
`T2` run (`swpo_run`). The usual way to get `T1 ⊆ T2` is to put the other
table's code into the data view (`mem_dataOf`): code is read-only bytes of
the fixed image either way.
-/

namespace VsaIris

variable {M : MachineModel}

theorem SegFrom.text_mono {ro : List (Nat × BitVec 64)} {text text' : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (ht : ∀ p ∈ text, p ∈ text')
    (h : SegFrom M ro text rs S k rv mv P) : SegFrom M ro text' rs S k rv mv P :=
  fun σ hok hro hrs hS => h σ hok ⟨hro.1, fun p hp => hro.2 p (ht p hp)⟩ hrs hS

/-- **Local runs are monotone in their read-only cells.** -/
theorem LocalRun.text_mono {ro : List (Nat × BitVec 64)} {text text' : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (ht : ∀ p ∈ text, p ∈ text') :
    ∀ n rv mv, LocalRun M ro text rs S Q n rv mv → LocalRun M ro text' rs S Q n rv mv
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    rcases h with h | ⟨k, h⟩
    · exact .inl h
    · exact .inr ⟨k, (h.text_mono ht).mono fun rv' mv' hr => LocalRun.text_mono ht n rv' mv' hr⟩

end VsaIris

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

variable {live : Nat → Prop} {rs : List Nat} {S : Nat → Prop}

theorem swp_text_mono {T1 T2 : List (Nat × BitVec 8)}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (ht : ∀ p ∈ T1, p ∈ T2)
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} (h : SWP live T1 rs S Q pc R Mt) :
    SWP live T2 rs S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => LocalRun.text_mono ht n rv mv (hn rv mv hm)⟩

/-- **A sub-run over a smaller read-only list inside a printing run.** `run`
is a continuation-form lemma over `T1`, for every end condition; its exits
(`C`) continue as the printing run over `T2`. -/
theorem swpo_bridge {T1 T2 : List (Nat × BitVec 8)} (ht : ∀ p ∈ T1, p ∈ T2)
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {C : BitVec 64 → (Nat → BitVec 64) → Mem → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (run : ∀ Q' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      (∀ pc' R' Mt', C pc' R' Mt' → SWP live T1 rs S Q' pc' R' Mt') → SWP live T1 rs S Q' pc R Mt)
    (hk : ∀ pc' R' Mt', C pc' R' Mt' → SWPO live T2 rs S Q t pc' R' Mt') :
    SWPO live T2 rs S Q t pc R Mt :=
  swp_text_mono ht (run _ fun pc' R' Mt' hc => swp_done fun _ _ hm => swpo_run (hk pc' R' Mt' hc) hm)

/-- A table in the data view: its bytes are data bytes when the view's
addresses list them and its memory agrees. -/
theorem mem_dataOf {T : List (Nat × BitVec 8)} {Dt : Mem} {DA : List Nat}
    (hA : ∀ p ∈ T, p.1 ∈ DA) (hD : ∀ p ∈ T, imgM Dt p.1 = p.2) :
    ∀ p ∈ T, p ∈ dataOf Dt DA := by
  intro p hp
  have e : p = (p.1, imgM Dt p.1) := by rw [hD p hp]
  rw [e]
  exact List.mem_map_of_mem (f := fun a => (a, imgM Dt a)) (hA p hp)

end VsaIris.Sym
