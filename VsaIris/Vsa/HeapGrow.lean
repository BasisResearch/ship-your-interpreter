import VsaIris.Vsa.HeapSplit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

def GrowW (top : Nat) (a : Nat) : Prop :=
  (top + 8 ≤ a ∧ a < top + 16) ∨ (brkAddr ≤ a ∧ a < topPadAddr) ∨
    (mallinfoAddr ≤ a ∧ a < mallinfoAddr + 8) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (0x8001b538 ≤ a ∧ a < 0x8001b53c)

theorem PHeapAt.topResize {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {brk' : Nat} (htr : top + 16 ≤ brk') (hend : brk' ≤ heapEnd) (hpage : brk' % 4096 = 0)
    (hbrk : read64 m' brkAddr = some brk')
    (htop : read64 m' (top + 8) = some (brk' - top + 1))
    (hmi : (read64 m' mallinfoAddr).isSome) (hmax : (read64 m' maxSbrkedAddr).isSome)
    (hag : ∀ a, vsaFoot H a → ¬ GrowW top a → m'[a]? = m[a]?) :
    PHeapAt m' H top brk' chunks bins := by
  obtain ⟨B, _, hbbl⟩ := h
  have hH := B.heap
  have hlo := hH.walk.le
  have hcb := hH.walk.chunk_bounds
  have htle := hH.top_le
  have htop16 := hH.aligned.2
  unfold heapStart at hlo
  have hV : ∀ w, allocGlobal w → GrowW top w → volGlobal w := by
    intro w hg hu; unfold allocGlobal InRange at hg; unfold GrowW volGlobal at *; omega
  obtain ⟨gS, gP, gBb, -⟩ := hH.keep_stable hag hV
  obtain ⟨kBins, kFoot⟩ := B.keep_freeV hag hV fun c hc _ w hw => by
    have := hcb c hc; unfold GrowW brkAddr topPadAddr mallinfoAddr at hw; unfold heapStart at this; omega
  have Kc : ∀ c ∈ chunks, read64 m' (c.addr + 8) = read64 m (c.addr + 8) := fun c hc =>
    B.keep_hdr hag (.inr ⟨c, hc, rfl⟩) fun w hw => by
      have := hcb c hc; unfold GrowW brkAddr topPadAddr mallinfoAddr at hw; unfold heapStart at this; omega
  have hpi : ∀ h1, read64 m (top + 8) = some h1 →
      ∃ h2, read64 m' (top + 8) = some h2 ∧ prevInuse h2 = prevInuse h1 := by
    intro h1 hh1
    rw [hH.top_header] at hh1
    cases hh1
    refine ⟨_, htop, ?_⟩
    have := hH.top_size
    unfold prevInuse
    rw [show (brk' - top + 1) % 2 = 1 by omega, show (brkv - top + 1) % 2 = 1 by omega]
  have hwalk : ChunkWalk m' heapStart top chunks := by
    have w := hH.walk.extend (m' := m') Kc hpi (.top (p := top))
    rwa [List.append_nil] at w
  refine ⟨⟨{ sbrk_base := gS, brk := hbrk, brk_le := hend
             top_ptr := (win_read64 hag (fun k hk => .inl (by unfold allocGlobal InRange topAddr avAddr; omega))
               fun k hk hu => by unfold GrowW topAddr avAddr brkAddr topPadAddr mallinfoAddr at hu; omega).trans hH.top_ptr
             top_le := by omega, top_size := by omega, top_header := htop
             top_pad := gP, max_sbrked := hmax, mallinfo := hmi, first_prev := ?_
             walk := hwalk, coalesced := hH.coalesced, footer := kFoot
             bins_list := kBins, bins_nodup := hH.bins_nodup
             bin_free := hH.bin_free, free_binned := hH.free_binned, remainder := hH.remainder
             binblocks_present := gBb ▸ hH.binblocks_present
             binblocks := fun bb hbb => hH.binblocks bb (gBb ▸ hbb)
             live := hH.live, exact := hH.exact }, by have := B.top_room; omega⟩, hpage,
    fun bb hbb => hbbl bb (gBb ▸ hbb)⟩
  rcases hH.walk.head_or_top with he | ⟨c, hc, hca⟩
  · rw [show heapStart = top from he, htop]
    simp only [Option.any, beq_iff_eq]
    have := hH.top_size
    omega
  · rw [show heapStart = c.addr from hca.symm, Kc c hc, hca]
    exact hH.first_prev

theorem PHeapAt.topGrow {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    {brk' : Nat} (hle : brkv ≤ brk') (hend : brk' ≤ heapEnd) (hpage : brk' % 4096 = 0)
    (hbrk : read64 m' brkAddr = some brk')
    (htop : read64 m' (top + 8) = some (brk' - top + 1))
    (hmi : (read64 m' mallinfoAddr).isSome) (hmax : (read64 m' maxSbrkedAddr).isSome)
    (hag : ∀ a, vsaFoot H a → ¬ GrowW top a → m'[a]? = m[a]?) :
    PHeapAt m' H top brk' chunks bins :=
  h.topResize (by have := h.heap.top_room; omega) hend hpage hbrk htop hmi hmax hag

end VsaIris.VsaHeap
