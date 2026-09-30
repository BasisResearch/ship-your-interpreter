import VsaIris.Vsa.SymRunO
import VsaIris.Vsa.SymData

namespace VsaIris

variable {M : MachineModel}

theorem SegFrom.text_mono {ro : List (Nat × BitVec 64)} {text text' : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {k : Nat} {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (ht : ∀ p ∈ text, p ∈ text')
    (h : SegFrom M ro text rs S k rv mv P) : SegFrom M ro text' rs S k rv mv P :=
  fun σ hok hro hrs hS => h σ hok ⟨hro.1, fun p hp => hro.2 p (ht p hp)⟩ hrs hS

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

theorem swpo_bridge {T1 T2 : List (Nat × BitVec 8)} (ht : ∀ p ∈ T1, p ∈ T2)
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {C : BitVec 64 → (Nat → BitVec 64) → Mem → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (run : ∀ Q' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop,
      (∀ pc' R' Mt', C pc' R' Mt' → SWP live T1 rs S Q' pc' R' Mt') → SWP live T1 rs S Q' pc R Mt)
    (hk : ∀ pc' R' Mt', C pc' R' Mt' → SWPO live T2 rs S Q t pc' R' Mt') :
    SWPO live T2 rs S Q t pc R Mt :=
  swp_text_mono ht (run _ fun pc' R' Mt' hc => swp_done fun _ _ hm => swpo_run (hk pc' R' Mt' hc) hm)

end VsaIris.Sym
