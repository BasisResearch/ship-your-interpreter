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
open Vsa.Sim.LayoutInstance (stackSL spEntry interpObject interpRunFrame)
open Vsa.Sim.RuntimeOwnership (InitialWriteByte)

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

/-! ## 6. The boundary's bytes, partitioned

Everything the initial world owns, as disjoint sets of addresses. All lie
below `2^32` (`BootByte_lt`), so one finite list enumerates them. -/

/-- The fixed binary's text and read-only data (below the writable sections). -/
def CodeByte (k : Nat) : Prop := 0x80000000 ≤ k ∧ k < 0x8001ad00

/-- Writable ELF data outside the allocator's globals (newlib's `FILE`
state, `_impure_ptr`, the interpreter's statics). -/
def StaticByte (k : Nat) : Prop := (0x8001ad00 ≤ k ∧ k < 0x8001c168) ∧ ¬ allocGlobal k

/-- The whole C stack. -/
def StackByte (k : Nat) : Prop := stackSL.lo ≤ k ∧ k < stackSL.hi

/-- `struct Interp` (384 bytes, `interp.h`), inside `main`'s frame. -/
def InterpByte (inp k : Nat) : Prop := InExt (inp, 384) k

/-- The owned stack below `interp_run`'s entry `sp`. -/
def FreeStackByte (k : Nat) : Prop := InExt (stackSL.lo, spEntry - stackSL.lo) k

/-- The stack above `interp_run`'s entry `sp` outside `struct Interp`:
`main`'s saved registers and locals, owned at their values. -/
def CallerByte (inp k : Nat) : Prop := (spEntry ≤ k ∧ k < stackSL.hi) ∧ ¬ InterpByte inp k

/-- Read-only bytes: the code and the boundary's immutable (shared) set. -/
def RoByte (shared : Nat → Prop) (k : Nat) : Prop := shared k ∨ CodeByte k

/-- Every byte the boundary world owns. -/
def BootByte (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) (k : Nat) : Prop :=
  RoByte shared k ∨ BlocksCover G.blocks k ∨ heapFoot vsaLayout H k ∨ StackByte k ∨ StaticByte k

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program}

theorem inp_toNat (b : Boot c p) : b.inp.toNat = interpObject := by
  rw [b.ready.interp_local]; decide

theorem blockHeapAt (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) :
    BlockHeapAt c.σ.mem b.H b.top b.brkv b.chunks b.bins :=
  (blockHeapAt_of_heapAt b.alloc.heap hroom).1

/-- Shared bytes are outside every writable byte of the boundary. -/
theorem shared_not_write (b : Boot c p) {k : Nat} (hk : b.D.shared k) :
    ¬ InitialWriteByte stackSL k :=
  b.owned.heap.immutable.outsideWrites k hk

theorem shared_lt (b : Boot c p) {k : Nat} (hk : b.D.shared k) : k < 2 ^ 32 := by
  have := (b.owned.heap.immutable.readable k hk).2
  exact this

/-- Shared arena bytes lie in a live block, so the allocator does not own them. -/
theorem shared_not_heapFoot (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {k : Nat}
    (hk : b.D.shared k) :
    ¬ heapFoot vsaLayout b.H k := by
  rintro (hg | ⟨hlo, hhi, hout⟩)
  · apply b.shared_not_write hk
    left
    change allocGlobal k at hg
    unfold allocGlobal InRange at hg
    omega
  · have harena := b.owned.arenaHeap
    obtain ⟨e, he, hek⟩ := b.owned.heap.reserved.live k hk
      (by rw [harena.1]; exact hlo) (by rw [harena.2]; exact hhi)
    obtain ⟨blk, hblk, hcov⟩ := (blockHeapAt_of_heapAt b.alloc.heap hroom).2 e he
    exact hout blk hblk (hcov k hek)

end Boot

theorem stackSL_lo : stackSL.lo = 0x87800000 := rfl
theorem stackSL_hi : stackSL.hi = 0x88000000 := rfl
theorem spEntry_eq : spEntry = 0x87fffd00 := rfl
theorem interpObject_eq : interpObject = 0x87fffe10 := rfl

theorem heapFoot_cases {H : List (Nat × Nat)} {k : Nat} (h : heapFoot vsaLayout H k) :
    (0x8001ad10 ≤ k ∧ k < 0x8001ba68 ∧ allocGlobal k) ∨
      (heapStart ≤ k ∧ k < heapEnd ∧ ∀ e ∈ H, ¬ InExt e k) := by
  rcases h with hg | h
  · left
    change allocGlobal k at hg
    refine ⟨?_, ?_, hg⟩ <;> (unfold allocGlobal InRange at hg; omega)
  · exact .inr h

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program}

/-- The store's blocks are arena bytes. -/
theorem store_arena (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) {k : Nat}
    (hk : BlocksCover G.blocks k) : heapStart ≤ k ∧ k < heapEnd := by
  obtain ⟨blk, hblk, hin⟩ := hk
  exact (b.blockHeapAt hroom).block_arena (hG.live blk hblk) hin

theorem store_not_heapFoot (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) {k : Nat}
    (hk : BlocksCover G.blocks k) : ¬ heapFoot vsaLayout b.H k := by
  have ha := b.store_arena hroom hG hk
  intro hf
  rcases heapFoot_cases hf with ⟨_, h2, _⟩ | ⟨_, _, hout⟩
  · unfold heapStart at ha; omega
  · obtain ⟨blk, hblk, hin⟩ := hk
    exact hout blk (hG.live blk hblk) hin

/-- Every boot byte is a 32-bit address. -/
theorem bootByte_lt (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) {k : Nat}
    (hk : BootByte b.D.shared G b.H k) : k < 2 ^ 32 := by
  rcases hk with (hs | hc) | hst | hh | hstk | hsta
  · exact b.shared_lt hs
  · unfold CodeByte at hc; omega
  · have := b.store_arena hroom hG hst; unfold heapEnd at this; omega
  · rcases heapFoot_cases hh with h | h
    · omega
    · unfold heapEnd at h; omega
  · unfold StackByte at hstk; rw [stackSL_hi] at hstk; omega
  · unfold StaticByte at hsta; omega

/-- The five parts of `BootByte` are pairwise disjoint (in the order the
carving peels them). -/
theorem ro_disj (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) (k : Nat)
    (hk : RoByte b.D.shared k) :
    ¬ (BlocksCover G.blocks k ∨ heapFoot vsaLayout b.H k ∨ StackByte k ∨ StaticByte k) := by
  rcases hk with hs | hc
  · have hw := b.shared_not_write hs
    unfold InitialWriteByte at hw
    rintro (hst | hh | hstk | hsta)
    · exact hG.unshared k hst hs
    · exact b.shared_not_heapFoot hroom hs hh
    · exact hw (.inr hstk)
    · exact hw (.inl hsta.1)
  · unfold CodeByte at hc
    rintro (hst | hh | hstk | hsta)
    · have := b.store_arena hroom hG hst; unfold heapStart at this; omega
    · rcases heapFoot_cases hh with h | h
      · omega
      · unfold heapStart at h; omega
    · unfold StackByte at hstk; rw [stackSL_lo] at hstk; omega
    · unfold StaticByte at hsta; omega

theorem store_disj (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.chunks b.D.shared (b.φf 0) G) (k : Nat)
    (hk : BlocksCover G.blocks k) :
    ¬ (heapFoot vsaLayout b.H k ∨ StackByte k ∨ StaticByte k) := by
  have ha := b.store_arena hroom hG hk
  unfold heapStart heapEnd at ha
  rintro (hh | hstk | hsta)
  · exact b.store_not_heapFoot hroom hG hk hh
  · unfold StackByte at hstk; rw [stackSL_lo] at hstk; omega
  · unfold StaticByte at hsta; omega

end Boot

theorem heap_disj {H : List (Nat × Nat)} (k : Nat) (hk : heapFoot vsaLayout H k) :
    ¬ (StackByte k ∨ StaticByte k) := by
  rintro (hstk | hsta)
  · unfold StackByte at hstk; rw [stackSL_lo] at hstk
    rcases heapFoot_cases hk with h | h
    · omega
    · unfold heapEnd at h; omega
  · unfold StaticByte at hsta
    rcases heapFoot_cases hk with h | h
    · exact hsta.2 h.2.2
    · unfold heapStart at h; omega

theorem stack_disj (k : Nat) (hk : StackByte k) : ¬ StaticByte k := by
  unfold StackByte at hk; rw [stackSL_lo] at hk
  unfold StaticByte; omega

/-- The stack below `interp_run`'s entry, `struct Interp`, and the rest of
`main`'s frame. -/
theorem stack_parts (inp k : Nat) (hinp : inp = interpObject) :
    StackByte k ↔ FreeStackByte k ∨ InterpByte inp k ∨ CallerByte inp k := by
  subst hinp
  unfold StackByte FreeStackByte InterpByte CallerByte InExt
  rw [stackSL_lo, stackSL_hi, spEntry_eq, interpObject_eq]
  dsimp only
  constructor
  · intro h
    by_cases h1 : k < 0x87fffd00
    · exact .inl ⟨by omega, by omega⟩
    · by_cases h2 : 0x87fffe10 ≤ k ∧ k < 0x87fffe10 + 384
      · exact .inr (.inl h2)
      · exact .inr (.inr ⟨⟨by omega, by omega⟩, h2⟩)
  · rintro (h | h | h) <;> omega

/-! ## 7. The finite byte map adequacy hands over -/

/-- Every boot byte, enumerated. -/
noncomputable def bootAddrs (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) :
    List Nat :=
  (List.range (2 ^ 32)).filter fun k => @decide (BootByte shared G H k) (Classical.propDecidable _)

theorem bootAddrs_nodup (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) :
    (bootAddrs shared G H).Nodup :=
  List.nodup_range.filter _

theorem mem_bootAddrs {shared : Nat → Prop} {G : FrameGeom} {H : List (Nat × Nat)}
    (hlt : ∀ k, BootByte shared G H k → k < 2 ^ 32) (k : Nat) :
    k ∈ bootAddrs shared G H ↔ BootByte shared G H k := by
  unfold bootAddrs
  rw [List.mem_filter, List.mem_range, @decide_eq_true_iff _ (Classical.propDecidable _)]
  exact ⟨fun h => h.2, fun h => ⟨hlt k h, h⟩⟩

/-- **The boundary's byte map**: the memory's own total read on every boot
byte. `A` passes it to adequacy as `mm`. -/
noncomputable def Boot.bytes {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    (G : FrameGeom) : NatMap (BitVec 8) :=
  imgMap (memImg c.σ.mem) (bootAddrs b.D.shared G b.H)

/-- It agrees with the configuration (the model's memory IS the total read). -/
theorem Boot.bytes_agree {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    (G : FrameGeom) (live : Nat → Prop) :
    MemAgree (VsaIris.Inst.vsaModel live) (b.bytes G) c :=
  memAgree_imgMap (fun _ _ => rfl)

/-! ## 8. Regimes

Total mode starts `isHeapRoom` at the cost of the program's derivation
(S1's `costRoom_of_bigStep`); partial mode starts `isHeap`. -/

/-- The pure side condition a regime needs at the boundary memory. -/
def RegimeOK (m : Mem) : Regime → Prop
  | .counted k => CostReserve m k
  | .uncounted => True

/-- **The counted regime's start**: a big-step behaviour has a costed
derivation whose cost the boundary heap covers. -/
theorem Boot.regime_of_bigStep {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {out : String} (hb : BigStep p out) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out ∧
      RegimeOK c.σ.mem (.counted n) := by
  obtain ⟨st', n, hn, hout⟩ := BigStep.cost hb
  exact ⟨st', n, hn, hout, b.top, costReserve_of_initial b.alloc b.repr hn⟩

theorem regimeOK_uncounted (m : Mem) : RegimeOK m .uncounted := trivial

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Cut an owned extent at `k`. -/
theorem ownImg_ext_split (a n k q r : Nat) (img : Nat → BitVec 8) (hk : k ≤ n)
    (hq : q = a + k) (hr : r = n - k) :
    ownImg (GF := GF) (InExt (a, n)) img ⊢
      ownImg (InExt (a, k)) img ∗ ownImg (InExt (q, r)) img := by
  subst hq hr
  iintro H
  ihave ⟨H1, H2⟩ := ownSet_split (InExt (a, n)) (InExt (a, k)) _ $$ H
  isplitl [H1]
  · iapply ownSet_iff _ _ $$ H1
    intro x; unfold InExt; dsimp only; omega
  · iapply ownSet_iff _ _ $$ H2
    intro x; unfold InExt; dsimp only; omega

/-- **The allocator in either regime**, from its footprint's bytes at the
boundary image. -/
theorem heapRes_of_bytes {m : Mem} {H : List (Nat × Nat)} {ρ : Regime}
    (hshape : vsaLayout.Shape (memImg m) H) (hρ : RegimeOK m ρ) :
    ownImg (GF := GF) (heapFoot vsaLayout H) (memImg m) ⊢ heapRes vsaLayout costRoom ρ H := by
  cases ρ with
  | counted k =>
    unfold heapRes isHeapRoom
    iintro Hb
    iexists memImg m
    iframe Hb
    ipureintro
    exact ⟨hshape, costRoom_of_reserve hρ⟩
  | uncounted =>
    unfold heapRes isHeap
    iintro Hb
    iexists memImg m
    iframe Hb
    ipureintro
    exact hshape

/-- The boundary stack below `interp_run`'s entry, cut where `interp_run`
spills its 176-byte frame; the rest is what `stackScratch_boundary` carves
the first `exec_stmt` call's budget from. -/
theorem freeStack_carve :
    blockOwn (GF := GF) stackSL.lo (spEntry - stackSL.lo) ⊢
      blockOwn stackSL.lo (spEntry - interpRunFrame - stackSL.lo) ∗
        blockOwn (spEntry - interpRunFrame) interpRunFrame :=
  blockOwn_split _ _ _ _ _ (by decide) (by decide) (by decide)

section Ghost

variable [I : InterpGS GF]

/-- **`struct Interp` at `interp_run`'s entry** from its 384 bytes. -/
theorem interpCtxPre_of_bytes {inp g : Nat} {img : Nat → BitVec 8}
    (hg : imgLE img inp 8 = g) (hd : imgLE img (inp + interpDepthOff) 4 = 0) :
    ownImg (GF := GF) (InExt (inp, 384)) img ∗ frameAt 0 g ⊢ |==> interpCtxPre inp 0 := by
  iintro ⟨H, #Hf⟩
  ihave ⟨Hg, H⟩ := ownImg_ext_split inp 384 8 (inp + interpDepthOff) 376 img
    (by decide) rfl rfl $$ H
  ihave ⟨Hd, H⟩ := ownImg_ext_split (inp + interpDepthOff) 376 4 (inp + interpDepthOff + 4) 372
    img (by decide) rfl rfl $$ H
  ihave ⟨Hp, H⟩ := ownImg_ext_split (inp + interpDepthOff + 4) 372 4 (inp + interpJmpOff) 368
    img (by decide) (by unfold interpDepthOff interpJmpOff; omega) rfl $$ H
  ihave ⟨Hj, He⟩ := ownImg_ext_split (inp + interpJmpOff) 368 interpJmpLen
    (inp + interpErrOff) interpErrLen img (by decide)
    (by unfold interpJmpOff interpJmpLen interpErrOff; omega) rfl $$ H
  imod wordRO_of_ownImg hg $$ Hg with Hg
  imodintro
  unfold interpCtxPre interpCore
  isplitl [Hg Hd Hp He]
  · iexists g
    iframe Hg Hf
    isplitl [Hd]
    · iapply wordAt_of_ownImg hd $$ Hd
    isplitl [Hp]
    · iapply blockOwn_of_ownImg _ _ _ $$ Hp
    · iapply blockOwn_of_ownImg _ _ _ $$ He
  · iapply blockOwn_of_ownImg _ _ _ $$ Hj

/-- The global frame binds only natives, so it needs no closure fragment. -/
theorem closSupply_frame0 (φc : Addr → Nat) :
    ⊢ closSupplyL (GF := GF) φc (frame0.vars.map Prod.snd) := by
  unfold closSupplyL
  imodintro
  iintro %v %hv
  iapply closSupply_of_ne ?_
  simp [frame0, initSt] at hv
  rcases hv with rfl | rfl | rfl <;> (intro ca h; exact absurd h (by simp))

end Ghost

end Iris

#print axioms Boot.frameBridge
#print axioms Vsa.Sim.DlHeap.HeapAt.grow
#print axioms imgShape_of_blockHeapAt
#print axioms costRoom_of_reserve

end VsaIris.Interp
