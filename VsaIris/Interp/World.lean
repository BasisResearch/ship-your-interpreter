import VsaIris.Interp.Boundary
import VsaIris.Interp.Need
import VsaIris.Vsa.CostRoom
import VsaIris.Vsa.Instance
import Vsa.Sim.LayoutInstance

/-!
# The boundary world (package A0, INTERP_DESIGN.md §5.1)

From `Loaded interpRunLayout p c` (`InterpRunReadyFacts`, including S1's
`stack_admissible`) and the program's `ProgramRepr`, this file carves the
initial ownership the assembly (A) starts from, in both regimes.

## 1. The heap image at a filled memory

The boundary does not assert that every arena byte is present in the sparse
machine memory, but `isHeap`'s image must satisfy `imgShape`, which reads the
image at SOME memory holding it on the whole allocator footprint. `fillMem`
is that memory: the machine memory with every absent byte below a bound set to
the total read (`memImg`). `HeapAt` reads only present words, so it survives
the extension (`HeapAt.extend`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris VsaIris.VsaHeap
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim Vsa.Sim.DlHeap

/-! ## 1. Filling a memory -/

/-- The memory `m` with every byte below `B` set to its total read. -/
def fillMem (m : Mem) (B : Nat) : Mem :=
  (List.range B).foldl (fun acc a => acc.insert a (memImg m a)) m

theorem foldl_insert_get? (f : Nat → BitVec 8) :
    ∀ (l : List Nat) (acc : Mem) (a : Nat),
      (l.foldl (fun acc a => acc.insert a (f a)) acc)[a]? =
        if a ∈ l then some (f a) else acc[a]?
  | [], acc, a => by simp
  | x :: xs, acc, a => by
    rw [List.foldl_cons, foldl_insert_get? f xs]
    by_cases hx : a ∈ xs
    · simp [hx]
    · by_cases hax : a = x
      · subst hax; simp [hx]
      · simp [hx, hax, Std.ExtHashMap.getElem?_insert, Ne.symm hax]

theorem fillMem_get? (m : Mem) (B a : Nat) :
    (fillMem m B)[a]? = if a < B then some (memImg m a) else m[a]? := by
  unfold fillMem
  rw [foldl_insert_get?]
  simp

/-- The fill only adds bytes. -/
theorem fillMem_extends {m : Mem} {B a : Nat} {b : BitVec 8} (h : m[a]? = some b) :
    (fillMem m B)[a]? = some b := by
  rw [fillMem_get?]
  split
  · rw [memImg_eq h]
  · exact h

/-- Below the bound, the fill holds the total read. -/
theorem fillMem_imgOn {m : Mem} {B : Nat} {S : Nat → Prop} (hS : ∀ a, S a → a < B) :
    ImgOn S (memImg m) (fillMem m B) := by
  intro a ha
  simp [fillMem_get?, hS a ha]

/-! ## 2. Heap shape under memory extension -/

/-- `m'` holds every byte `m` holds. -/
def MemGrows (m m' : Mem) : Prop := ∀ (a : Nat) (b : BitVec 8), m[a]? = some b → m'[a]? = some b

theorem readLE_grow {m m' : Mem} (h : MemGrows m m') :
    ∀ {a n v : Nat}, readLE m a n = some v → readLE m' a n = some v
  | _, 0, _, hv => hv
  | a, n + 1, v, hv => by
    simp only [readLE] at hv ⊢
    cases hb : m[a]? with
    | none => rw [hb] at hv; cases hv
    | some b =>
      rw [hb] at hv
      cases hr : readLE m (a + 1) n with
      | none => rw [hr] at hv; cases hv
      | some r =>
        rw [hr] at hv
        rw [h a b hb, readLE_grow h hr]
        exact hv

theorem read64_grow {m m' : Mem} (h : MemGrows m m') {a v : Nat}
    (hv : read64 m a = some v) : read64 m' a = some v := readLE_grow h hv

theorem read64_isSome_grow {m m' : Mem} (h : MemGrows m m') {a : Nat}
    (hv : (read64 m a).isSome) : (read64 m' a).isSome := by
  cases hr : read64 m a with
  | none => rw [hr] at hv; cases hv
  | some v => rw [read64_grow h hr]; rfl

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.grow {m m' : Mem} (h : MemGrows m m') {p top : Nat} {cs : List Chunk}
    (hw : ChunkWalk m p top cs) : ChunkWalk m' p top cs := by
  induction hw with
  | top => exact .top
  | chunk hh hlow hmin hal hn _ ih =>
    exact .chunk (read64_grow h hh) hlow hmin hal (read64_grow h hn) ih

theorem _root_.Vsa.Sim.DlHeap.BinChain.grow {m m' : Mem} (h : MemGrows m m') {b q prev : Nat} {qs : List Nat}
    (hc : BinChain m b q prev qs) : BinChain m' b q prev qs := by
  induction hc with
  | close hb => exact .close (read64_grow h hb)
  | link hne hp hn _ ih => exact .link hne (read64_grow h hp) (read64_grow h hn) ih

/-- **`HeapAt` survives memory growth**: it reads only present words. -/
theorem _root_.Vsa.Sim.DlHeap.HeapAt.grow {m m' : Mem} (h : MemGrows m m') {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (hH : HeapAt m exts reallocs top brkv chunks bins) :
    HeapAt m' exts reallocs top brkv chunks bins where
  sbrk_base := read64_grow h hH.sbrk_base
  brk := read64_grow h hH.brk
  brk_le := hH.brk_le
  top_ptr := read64_grow h hH.top_ptr
  top_le := hH.top_le
  top_size := hH.top_size
  top_header := read64_grow h hH.top_header
  top_pad := read64_grow h hH.top_pad
  max_sbrked := read64_isSome_grow h hH.max_sbrked
  mallinfo := read64_isSome_grow h hH.mallinfo
  first_prev := by
    have hp := hH.first_prev
    cases hr : read64 m (heapStart + 8) with
    | none => rw [hr] at hp; cases hp
    | some v => rw [hr] at hp; rw [read64_grow h hr]; exact hp
  walk := hH.walk.grow h
  coalesced := hH.coalesced
  footer := fun c hc hf => read64_grow h (hH.footer c hc hf)
  bins_list := by
    intro i h0 h1
    obtain ⟨first, hfirst, hchain⟩ := hH.bins_list i h0 h1
    exact ⟨first, read64_grow h hfirst, hchain.grow h⟩
  bins_nodup := hH.bins_nodup
  bin_free := hH.bin_free
  free_binned := hH.free_binned
  remainder := hH.remainder
  binblocks_present := read64_isSome_grow h hH.binblocks_present
  binblocks := by
    intro bb hbb
    cases hr : read64 m binblocksAddr with
    | none => have := hH.binblocks_present; rw [hr] at this; cases this
    | some bb0 =>
      have h2 := read64_grow h hr
      rw [hbb] at h2
      obtain rfl := Option.some.inj h2.symm
      exact hH.binblocks _ hr
  live := hH.live
  exact := hH.exact

/-- Every allocator-footprint byte is below the stack top. -/
theorem vsaFoot_lt {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) : a < 0x88000000 := by
  rcases h with hg | ⟨_, h2, _⟩
  · unfold allocGlobal InRange at hg; omega
  · unfold heapEnd at h2; omega

/-- **The Iris heap shape of the boundary memory's image**, read at the
filled memory. -/
theorem imgShape_of_blockHeapAt {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins) :
    vsaLayout.Shape (memImg m) H :=
  ⟨fillMem m 0x88000000, fillMem_imgOn (fun _ ha => vsaFoot_lt ha),
    ⟨top, brkv, chunks, bins, ⟨h.heap.grow (fun _ _ hb => fillMem_extends hb), h.top_room⟩⟩⟩

/-- **The counted regime's capacity of the boundary image**, from a reserve
at the machine memory. -/
theorem costRoom_of_reserve {m : Mem} {H : List (Nat × Nat)} {k : Nat} (h : CostReserve m k) :
    costRoom (memImg m) H k := by
  obtain ⟨top, t⟩ := h
  exact ⟨fillMem m 0x88000000, fillMem_imgOn (fun _ ha => vsaFoot_lt ha), top,
    read64_grow (fun _ _ hb => fillMem_extends hb) t.top_pointer, t.fits⟩

/-! ## 3. The boundary data

`Loaded interpRunLayout p c` is a chain of existentials (`InterpRunReady`,
`InitialOwned`'s `InitialOwnershipData`, `InitialAllocator`'s heap walk).
`Boot c p` names every witness once (CLAUDE.md law 6); `boot_of_loaded`
extracts it. -/

open Vsa.Sim.LayoutInstance Vsa.Sim.RuntimeOwnership in
/-- **The boundary, with every witness named.** -/
structure Boot (c : Vsa.Machine.Config) (p : Program) where
  stmts : Nat
  count : Nat
  inp : BitVec 64
  N : NativeAddrs
  A : Arena
  φf : Addr → Nat
  φc : Addr → Nat
  aLeft : Nat
  D : InitialOwnershipData
  top : Nat
  brkv : Nat
  chunks : List Chunk
  bins : Nat → List Nat
  repr : ProgramRepr c.σ.mem stmts count p
  ready : Vsa.Sim.LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft
  owned : InitialOwned c.σ.mem A stackSL φf φc stmts count D
  alloc : InitialAllocatorAt c.σ.mem D.exts (ReallocExtent D.allocations) stmts count
    top brkv chunks bins

open Vsa.Sim.LayoutInstance in
theorem boot_of_loaded {p : Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) : Nonempty (Boot c p) := by
  obtain ⟨a, n, hp, inp, N, A, φf, φc, aLeft, F⟩ := h
  obtain ⟨D, hD⟩ := F.ownership
  obtain ⟨top, brkv, chunks, bins, hA⟩ := hD.allocator
  exact ⟨⟨a, n, inp, N, A, φf, φc, aLeft, D, top, brkv, chunks, bins, hp, F, hD, hA⟩⟩

theorem initSt_frame0 : 0 < initSt.store.frames.size := by decide

/-- The global frame of `initSt`: `print`, `println`, `assert`. -/
abbrev frame0 : Frame := initSt.store.frames[0]'initSt_frame0

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)

/-- The program fits the stack (S1's `stack_admissible`). -/
theorem fits (b : Boot c p) : Vsa.Sim.LayoutInstance.ProgramStackFits p :=
  b.ready.stack_admissible p b.repr

/-- The global frame's `Env*`. -/
abbrev env : Nat := b.φf 0

theorem frameRepr : FrameRepr c.σ.mem b.N b.φf b.φc b.env frame0 :=
  b.ready.store.frames 0 initSt_frame0

theorem frameOwned :
    Vsa.Sim.RuntimeOwnership.FrameOwned c.σ.mem b.φf b.D.allocations b.D.shared 0 frame0 :=
  b.owned.heap.store.frames 0 initSt_frame0

theorem env_ne : b.φf 0 ≠ 0 := by
  have h := (b.ready.store.frames_arena 0 initSt_frame0).1.1
  have hlo := b.owned.heapLower
  omega

/-- The boundary heap in block form: every in-use chunk payload is live. -/
abbrev H : List (Nat × Nat) := inuseBlocks b.chunks

end Boot

/-! ## 4. The one fact the boundary does not state

`InitialOwned` places every live extent inside SOME in-use chunk
(`HeapAt.live`), but not alone in it: the `Env` struct of the global frame
may, as far as the boundary says, share a chunk with a binding name, and the
two arrays may share their chunk's tail with other extents. §3's `world`
needs the store's blocks to be members of the heap's live-block list (whole
chunk payloads, the user's ruling), exclusively owned, so the three chunks must
be distinct and hold no shared byte. `interp_init` allocates each by its own
`malloc` and nothing else into them, so the fact is true of every real
boundary, and it is checked at the control program
(`VsaIris/Interp/WorldVacuity.lean`). It is also where `BlockHeapAt`'s
`top_room` (dlmalloc keeps the top chunk at least `MINSIZE`) enters: the
boundary's `HeapAt` does not state it.

Supplier: an `InterpRunReadyFacts` field (a statement change like S1's
`stack_admissible`, the user's decision), recorded in
`experiments/smt/PROOF_CLOSURE_PLAN.md`. -/

/-- The global frame's geometry against the boundary heap walk. -/
structure FrameChunks (m : Mem) (chunks : List Chunk) (shared : Nat → Prop) (e : Nat)
    (G : FrameGeom) : Prop where
  env : G.e = e
  cap : read32 m (e + 4) = some G.cap
  names : read64 m (e + 8) = some G.pn
  vals : read64 m (e + 16) = some G.pv
  par : G.par = 0
  sblk : G.sblk.1 ≤ e ∧ e + 32 ≤ G.sblk.1 + G.sblk.2
  arrays : 0 < G.cap → G.nblk.1 = G.pn ∧ 8 * G.cap ≤ G.nblk.2 ∧
    G.vblk.1 = G.pv ∧ 24 * G.cap ≤ G.vblk.2
  /-- Each block is a whole in-use chunk payload. -/
  live : ∀ b ∈ G.blocks, b ∈ inuseBlocks chunks
  /-- Three different chunks. -/
  nodup : G.blocks.Nodup
  /-- No immutable byte lives in them. -/
  unshared : ∀ k, BlocksCover G.blocks k → ¬ shared k

/-- **The boundary gap** (named premise; see §4 above). -/
structure BootGap {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) : Prop where
  top_room : b.top + 16 ≤ b.brkv
  frame : ∃ G, FrameChunks c.σ.mem b.chunks b.D.shared b.env G

/-! ## 5. The global frame's boundary data -/

/-- Two different in-use payloads of one walk share no byte. -/
theorem inuseBlocks_disj {m : Mem} {p top : Nat} {chunks : List Chunk}
    (hw : ChunkWalk m p top chunks) {b b' : Nat × Nat} (hb : b ∈ inuseBlocks chunks)
    (hb' : b' ∈ inuseBlocks chunks) (hne : b ≠ b') : ExtDisj b b' := by
  obtain ⟨c, hc, _, rfl⟩ := mem_inuseBlocks.1 hb
  obtain ⟨c', hc', _, rfl⟩ := mem_inuseBlocks.1 hb'
  have h1 := hw.chunk_bounds c hc
  have h2 := hw.chunk_bounds c' hc'
  intro a ha ha'
  unfold InExt at ha ha'
  simp only at ha ha'
  rcases hw.chunk_sep c hc c' hc' with rfl | hs | hs
  · exact hne rfl
  · omega
  · omega

/-- Distinct live payloads are pairwise disjoint. -/
theorem FrameChunks.disjoint {m m' : Mem} {chunks : List Chunk} {shared : Nat → Prop} {e : Nat}
    {G : FrameGeom} {p top : Nat} (h : FrameChunks m chunks shared e G)
    (hw : ChunkWalk m' p top chunks) : G.blocks.Pairwise ExtDisj :=
  h.nodup.imp_of_mem fun ha hb hne => inuseBlocks_disj hw (h.live _ ha) (h.live _ hb) hne

/-- An owned value's payload string is shared. -/
theorem payloadShared_of_valueOwned {m : Mem} {shared : Nat → Prop} {a : Nat} {v : Value}
    (h : Vsa.Sim.RuntimeOwnership.ValueOwned m shared a v) : PayloadShared shared m a v := by
  intro s hs q hq i hi
  cases v with
  | str t =>
    obtain ⟨p, hp, hsh⟩ := h
    simp only [payloadStr, Option.some.injEq] at hs
    subst hs
    obtain rfl : p = q := Option.some.inj (hp.symm.trans hq)
    exact hsh.bytes i hi
  | native f =>
    obtain ⟨p, hp, hsh⟩ := h
    simp only [payloadStr, Option.some.injEq] at hs
    subst hs
    obtain rfl : p = q := Option.some.inj (hp.symm.trans hq)
    exact hsh.bytes i hi
  | _ => simp [payloadStr] at hs

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program}

theorem frameReads (b : Boot c p) : FrameReads c.σ.mem b.N b.φf b.φc (b.φf 0) frame0 :=
  FrameReads.of_frameRepr b.frameRepr

/-- **The global frame's `FrameBridge`**, from the boundary and the chunk
premise, at the memory's own image. -/
theorem frameBridge (b : Boot c p) {G : FrameGeom}
    (h : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) :
    FrameBridge b.D.shared c.σ.mem b.N b.φc G frame0 (memImg c.σ.mem) := by
  have hr := b.frameReads
  have ho := b.frameOwned
  obtain ⟨st, hst⟩ := ho.arrays
  have hpn : st.names = G.pn := Option.some.inj (hst.namesRead.symm.trans (h.env ▸ h.names))
  have hcap : G.cap = st.cap := by
    have := hst.capRead
    rw [← h.env] at this
    exact Option.some.inj ((h.env ▸ h.cap).symm.trans this)
  refine
    { e_ne := h.env ▸ b.env_ne
      sblk := h.env ▸ h.sblk
      cap := h.env ▸ h.cap
      names := h.env ▸ h.names
      vals := h.env ▸ h.vals
      parent := by rw [h.par, h.env]; exact hr.parentNone rfl
      count_le := hcap ▸ hst.bound
      empty := by
        intro h0
        have := hst.bound
        rw [← hcap, h0] at this
        exact absurd this (by decide)
      arrays := h.arrays
      disjoint := h.disjoint b.alloc.heap.walk
      agree := fun _ _ => rfl
      nameShared := ?_
      payloadShared := ?_ }
  · intro i hi q hq j hj
    obtain ⟨q', hq', hcs⟩ := hst.keys i hi
    rw [hpn] at hq'
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact hcs.immutable.bytes j hj
  · intro i hi
    exact payloadShared_of_valueOwned (ho.values G.pv (h.env ▸ h.vals) i hi)

end Boot

#print axioms Boot.frameBridge
#print axioms Vsa.Sim.DlHeap.HeapAt.grow
#print axioms imgShape_of_blockHeapAt
#print axioms costRoom_of_reserve

end VsaIris.Interp
