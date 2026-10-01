import VsaIris.Vsa.Malloc
import Vsa.Sim.ValueSpec
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.InterpSpillReads

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.extend {m m' : Mem} {p top top' : Nat}
    {cs ds : List Chunk} (h : ChunkWalk m p top cs)
    (hdr : ∀ c ∈ cs, read64 (m') (c.addr + 8) = read64 m (c.addr + 8))
    (htop : ∀ h1, read64 m (top + 8) = some h1 →
      ∃ h2, read64 (m') (top + 8) = some h2 ∧ prevInuse h2 = prevInuse h1)
    (hds : ChunkWalk (m') top top' ds) : ChunkWalk (m') p top' (cs ++ ds) := by
  induction h with
  | top => exact hds
  | @chunk p top hh h' cs hh0 hlow hmin hal hn rest ih =>
    have hp : read64 (m') (p + 8) = some hh := by
      rw [hdr _ List.mem_cons_self]; exact hh0
    have ih' := ih (fun c hc => hdr c (List.mem_cons_of_mem _ hc)) htop hds
    rcases rest.head_or_top with he | ⟨c, hc, hca⟩
    · obtain ⟨h2, hr2, hpi⟩ := htop h' (he ▸ hn)
      have w := ChunkWalk.chunk (m := m') hp hlow hmin hal (he ▸ hr2) ih'
      rw [hpi] at w
      exact w
    · have hn' : read64 (m') (p + chunkSize hh + 8) = some h' := by
        rw [← hca, hdr c (List.mem_cons_of_mem _ hc), hca]; exact hn
      exact ChunkWalk.chunk hp hlow hmin hal hn' ih'

end VsaIris.VsaHeap
