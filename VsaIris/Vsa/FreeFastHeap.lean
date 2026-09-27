import VsaIris.Vsa.MallocFastHeap

/-!
# Freeing into the top, at the level of the heap shape

`_free_r`'s path for the chunk just below the top, with its predecessor in use
and the merged top below the trim threshold, stores two words:

* the chunk's header, `(size + topsize) | PREV_INUSE`, making it the top;
* `av->top` (`topAddr`): the chunk's address.

`FastAt.merge` proves these stores take the fast heap with the block live to
the fast heap without it, with every credit kept.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

/-- Split a walk at a list boundary. -/
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
