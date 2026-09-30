import VsaIris.Vsa.MallocFastHeap

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.append_inv {m : Mem} {cs ds : List Chunk} :
    ∀ {p top : Nat}, ChunkWalk m p top (cs ++ ds) →
      ∃ mid, ChunkWalk m p mid cs ∧ ChunkWalk m mid top ds := by
  induction cs with
  | nil => intro p top h; exact ⟨p, .top, h⟩
  | cons c cs ih =>
    intro p top h
    cases h with
    | chunk hh hlow hmin hal hn rest =>
      obtain ⟨mid, h1, h2⟩ := ih rest
      exact ⟨mid, .chunk hh hlow hmin hal hn h1, h2⟩

end VsaIris.VsaHeap
