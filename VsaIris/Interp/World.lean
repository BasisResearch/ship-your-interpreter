import VsaIris.Interp.Boundary
import VsaIris.Interp.Need
import VsaIris.Vsa.HeapRoom
import Vsa.While.CostExists
import VsaIris.Vsa.Instance
import Vsa.Sim.LayoutInstance
import VsaIris.Vsa.Newlib
import VsaIris.Interp.WorldStdio
import VsaIris.Vsa.HeapAlg

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

set_option autoImplicit false

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

/-- **The page-aligned heap at the filled memory.** `HeapAt` reads only
present words; the `binblocks` word is one of them (`binblocks_present`), so
the filled memory reads the same word. -/
theorem pHeapAt_fill {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    (hpage : brkv % 4096 = 0) (hbb : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32) :
    PHeapAt (fillMem m 0x88000000) H top brkv chunks bins where
  heap := ⟨h.heap.grow (fun _ _ hb => fillMem_extends hb), h.top_room⟩
  brk_page := hpage
  bb_lt := by
    intro bb hr
    cases h0 : read64 m binblocksAddr with
    | none => have := h.heap.binblocks_present; rw [h0] at this; cases this
    | some bb0 =>
      have h2 := read64_grow (m' := fillMem m 0x88000000) (fun _ _ hb => fillMem_extends hb) h0
      rw [hr] at h2
      obtain rfl := Option.some.inj h2
      exact hbb _ h0

/-- **The page-aligned Iris heap shape of the boundary memory's image**
(`vsaLayoutP`, the layout of `IrisHoles.alloc`), read at the filled memory. -/
theorem pShape_of_blockHeapAt {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    (hpage : brkv % 4096 = 0) (hbb : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32)
    (hst : Starts H) :
    vsaLayoutP.Shape (memImg m) H :=
  ⟨hst, fillMem m 0x88000000, top, brkv, chunks, bins, fillMem_imgOn (fun _ ha => vsaFoot_lt ha),
    pHeapAt_fill h hpage hbb⟩

/-- **The counted regime's capacity of the boundary image** (`vsaRoomB`). -/
theorem roomB_of_blockHeapAt {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    (hpage : brkv % 4096 = 0) (hbb : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32)
    (hst : Starts H) {k : Nat} (hk : 2 * k + extendSlack ≤ heapEnd - top) :
    vsaRoomB (memImg m) H k :=
  ⟨hst, fillMem m 0x88000000, top, brkv, chunks, bins, fillMem_imgOn (fun _ ha => vsaFoot_lt ha),
    pHeapAt_fill h hpage hbb, hk⟩

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

/-- Shrinking live blocks in place (same start, no longer) keeps the block
heap: `HeapAt.live`/`.exact` bound a block by its chunk's payload only. -/
theorem _root_.VsaIris.VsaHeap.BlockHeapAt.shrink {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    (f : Nat × Nat → Nat × Nat) (hf : ∀ e ∈ H, (f e).1 = e.1 ∧ (f e).2 ≤ e.2) :
    BlockHeapAt m (H.map f) top brkv chunks bins where
  heap := { h.heap with
    live := fun e' he' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      obtain ⟨c, hc, hu, h1, h2⟩ := h.heap.live e he
      have := hf e he
      exact ⟨c, hc, hu, by omega, by omega⟩
    exact := fun e' he' _ => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      obtain ⟨c, hc, hu, h1, h2⟩ := h.heap.exact e he he
      have := hf e he
      exact ⟨c, hc, hu, by omega, by omega⟩ }
  top_room := h.top_room

/-- Shrinking in place keeps the starts. -/
theorem Starts.map {H : List (Nat × Nat)} (f : Nat × Nat → Nat × Nat)
    (hf : ∀ e ∈ H, (f e).1 = e.1) (h : Starts H) : Starts (H.map f) := by
  show ((H.map f).map Prod.fst).Nodup
  rw [List.map_map, List.map_congr_left (g := Prod.fst) fun e he => by
    simp only [Function.comp_apply]; exact hf e he]
  exact h

/-- **The boundary frame's arrays at their exact extents** (H1's
`FrameLayout.arrays`): the names and values chunks' payloads cut to `8 cap`
and `24 cap` bytes; every other block is unchanged. -/
def trimArrays (F : Vsa.Sim.LayoutInstance.BootFrame) (e : Nat × Nat) : Nat × Nat :=
  if 0 < F.cap ∧ e = F.nblk then (F.pn, 8 * F.cap)
  else if 0 < F.cap ∧ e = F.vblk then (F.pv, 24 * F.cap) else e

theorem trimArrays_sub {F : Vsa.Sim.LayoutInstance.BootFrame}
    (hA : 0 < F.cap → F.nblk.1 = F.pn ∧ 8 * F.cap ≤ F.nblk.2 ∧
      F.vblk.1 = F.pv ∧ 24 * F.cap ≤ F.vblk.2) (e : Nat × Nat) :
    (trimArrays F e).1 = e.1 ∧ (trimArrays F e).2 ≤ e.2 := by
  unfold trimArrays
  by_cases h1 : 0 < F.cap ∧ e = F.nblk
  · rw [if_pos h1]
    obtain ⟨hc, rfl⟩ := h1
    obtain ⟨ha, hb, -, -⟩ := hA hc
    exact ⟨ha.symm, hb⟩
  · rw [if_neg h1]
    by_cases h2 : 0 < F.cap ∧ e = F.vblk
    · rw [if_pos h2]
      obtain ⟨hc, rfl⟩ := h2
      obtain ⟨-, -, ha, hb⟩ := hA hc
      exact ⟨ha.symm, hb⟩
    · rw [if_neg h2]
      exact ⟨rfl, Nat.le_refl _⟩

theorem inExt_of_sub {e e' : Nat × Nat} (h : e'.1 = e.1 ∧ e'.2 ≤ e.2) {a : Nat}
    (ha : InExt e' a) : InExt e a := by
  unfold InExt at ha ⊢; omega

/-- The shared bytes' geometry gives every shared byte a string read window. -/
theorem sharedWin_of_geom {P : Nat → Prop} (h : Vsa.Sim.SharedGeom P stackSL) : SharedWin P := by
  intro k hk
  have h1 := h.ram k hk
  have h2 := h.htif k hk
  rw [Vsa.Sim.tohostAddr_val] at h2
  unfold htifLo
  omega

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
  /-- The global frame's heap geometry. -/
  frame : BootFrame
  /-- The boundary heap facts `InitialAllocatorAt` does not state
  (`InterpRunReadyFacts.boot`). -/
  heapFacts : BootHeapFacts c.σ.mem D.shared (φf 0) top brkv chunks frame

open Vsa.Sim.LayoutInstance in
theorem boot_of_loaded {p : Program} {c : Vsa.Machine.Config}
    (h : Vsa.Refine.Loaded interpRunLayout p c) : Nonempty (Boot c p) := by
  obtain ⟨a, n, hp, inp, N, A, φf, φc, aLeft, F⟩ := h
  obtain ⟨D, top, brkv, chunks, bins, G, hB⟩ := F.boot
  exact ⟨⟨a, n, inp, N, A, φf, φc, aLeft, D, top, brkv, chunks, bins, hp, F, hB.owned, hB.alloc,
    G, hB.facts⟩⟩

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

/-- The boundary heap in block form: every in-use chunk payload is live,
the global frame's arrays at their exact extents (`trimArrays`). -/
abbrev H : List (Nat × Nat) := (inuseBlocks b.chunks).map (trimArrays b.frame)

theorem H_sub : ∀ e ∈ inuseBlocks b.chunks,
    (trimArrays b.frame e).1 = e.1 ∧ (trimArrays b.frame e).2 ≤ e.2 :=
  fun e _ => trimArrays_sub b.heapFacts.frame.arrays e

theorem starts : Starts b.H :=
  Starts.map _ (fun e he => (b.H_sub e he).1) (starts_inuseBlocks b.alloc.heap.walk)

/-- A live payload holding a shared byte is not one of the frame's arrays. -/
theorem trim_of_shared {blk : Nat × Nat} {k : Nat} (hk : b.D.shared k) (hin : InExt blk k) :
    trimArrays b.frame blk = blk := by
  have hne : ∀ x ∈ b.frame.blocks, blk ≠ x := fun x hx heq => by
    subst heq; exact b.heapFacts.frame.unshared blk hx k hin.1 hin.2 hk
  have hmem : ∀ hc : 0 < b.frame.cap,
      b.frame.nblk ∈ b.frame.blocks ∧ b.frame.vblk ∈ b.frame.blocks := fun hc => by
    simp [Vsa.Sim.LayoutInstance.BootFrame.blocks, Nat.pos_iff_ne_zero.1 hc]
  unfold trimArrays
  rw [if_neg (fun ⟨hc, he⟩ => hne _ (hmem hc).1 he),
    if_neg (fun ⟨hc, he⟩ => hne _ (hmem hc).2 he)]

/-- The shared bytes' string read windows (`InterpRunReadyFacts.boot`). -/
theorem sharedWin : SharedWin b.D.shared := sharedWin_of_geom b.heapFacts.shared_geom

end Boot

/-! ## 4. The boundary heap facts (`BootGap`)

`InitialOwned` places every live extent inside SOME in-use chunk
(`HeapAt.live`), but not alone in it. §3's `world` needs the store's blocks to
be members of the heap's live-block list (whole chunk payloads, the user's
ruling), exclusively owned, so the global frame's three chunks must be
distinct and hold no shared byte (`FrameChunks`). The other fields:
`BlockHeapAt.top_room`, H4's page-aligned break and 32-bit `binblocks` word
(`PHeapAt`, INTERP_DESIGN.md Q5/Q5b), and `_impure_data._stderr`
(`Stdio.StdioOK`, Q6).

`Loaded` states them (`InterpRunReadyFacts.boot`, `LayoutInstance.BootHeap`);
`Boot.gap` projects them at the frame geometry `Boot.G`. -/

/-- The global frame's geometry against the boundary heap's live blocks `H`. -/
structure FrameChunks (m : Mem) (H : List (Nat × Nat)) (shared : Nat → Prop) (e : Nat)
    (G : FrameGeom) : Prop where
  env : G.e = e
  cap : read32 m (e + 4) = some G.cap
  names : read64 m (e + 8) = some G.pn
  vals : read64 m (e + 16) = some G.pv
  par : G.par = 0
  sblk : G.sblk.1 ≤ e ∧ e + 32 ≤ G.sblk.1 + G.sblk.2
  /-- The arrays at their exact extents (H1's `FrameLayout.arrays`). -/
  arrays : 0 < G.cap → G.nblk = (G.pn, 8 * G.cap) ∧ G.vblk = (G.pv, 24 * G.cap)
  /-- Each block is a live block of the heap. -/
  live : ∀ b ∈ G.blocks, b ∈ H
  /-- In three different chunks. -/
  disjoint : G.blocks.Pairwise ExtDisj
  /-- No immutable byte lives in them. -/
  unshared : ∀ k, BlocksCover G.blocks k → ¬ shared k
  /-- The capacity of `interp_init`'s three natives (`capFor 3`). -/
  cap_canon : G.cap = 8

/-- **The boundary gap** (named premise; see §4 above). -/
structure BootGap {c : Vsa.Machine.Config} {p : Program} (b : Boot c p) (G : FrameGeom) :
    Prop where
  /-- dlmalloc keeps the top chunk at least `MINSIZE`. -/
  top_room : b.top + 16 ≤ b.brkv
  /-- The break is page-aligned (INTERP_DESIGN.md Q5, `PHeapAt.brk_page`). -/
  brk_page : b.brkv % 4096 = 0
  /-- `binblocks` fits in 32 bits (INTERP_DESIGN.md Q5b, `PHeapAt.bb_lt`). -/
  binblocks : ∀ bb, read64 c.σ.mem binblocksAddr = some bb → bb < 2 ^ 32
  /-- The global frame's three blocks are whole, distinct, unshared chunk payloads. -/
  frame : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G
  /-- `_impure_data._stderr` points at `__sf[2]` (INTERP_DESIGN.md Q6):
  `Stdio.StdioOK` needs it and `ExitRuntimeData` does not state it. -/
  stderr : read64 c.σ.mem Stdio.stderrPtrAddr = some exitStderr
  /-- The shared bytes' string read windows (H1's `SharedWin`). -/
  sharedWin : SharedWin b.D.shared

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program}

/-- The global frame's geometry, from the boundary's `BootFrame`. -/
def G (b : Boot c p) : FrameGeom where
  e := b.φf 0
  cap := b.frame.cap
  pn := b.frame.pn
  pv := b.frame.pv
  par := 0
  sblk := b.frame.sblk
  nblk := (b.frame.pn, 8 * b.frame.cap)
  vblk := (b.frame.pv, 24 * b.frame.cap)

/-- The global frame's blocks are the boundary frame's payloads, trimmed. -/
theorem G_blocks (b : Boot c p) : b.G.blocks = b.frame.blocks.map (trimArrays b.frame) := by
  have hnd := b.heapFacts.frame.nodup
  by_cases hc : b.frame.cap = 0
  · simp [G, FrameGeom.blocks, Vsa.Sim.LayoutInstance.BootFrame.blocks, hc, trimArrays]
  · have hc' : 0 < b.frame.cap := Nat.pos_of_ne_zero hc
    simp only [Vsa.Sim.LayoutInstance.BootFrame.blocks, if_neg hc, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := hnd
    simp [G, FrameGeom.blocks, Vsa.Sim.LayoutInstance.BootFrame.blocks, hc, trimArrays, h1, h2,
      h3, Ne.symm h3]

theorem frameChunks (b : Boot c p) :
    FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) b.G := by
  have h := b.heapFacts.frame
  have hwhole : ∀ e ∈ b.frame.blocks, e ∈ inuseBlocks b.chunks :=
    fun e he => mem_inuseBlocks.2 (h.live e he)
  have hsub : ∀ e ∈ b.frame.blocks,
      (trimArrays b.frame e).1 = e.1 ∧ (trimArrays b.frame e).2 ≤ e.2 :=
    fun e he => b.H_sub e (hwhole e he)
  exact
    { env := rfl
      cap := h.cap
      names := h.names
      vals := h.vals
      par := rfl
      sblk := h.sblk
      arrays := fun _ => ⟨rfl, rfl⟩
      live := fun e he => by
        rw [b.G_blocks] at he
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        exact List.mem_map_of_mem (hwhole e0 he0)
      disjoint := by
        rw [b.G_blocks, List.pairwise_map]
        refine (h.nodup.imp_of_mem fun ha hb hne =>
          inuseBlocks_disj b.alloc.heap.walk (hwhole _ ha) (hwhole _ hb) hne).imp_of_mem ?_
        intro x y hx hy hd a hxa hya
        exact hd a (inExt_of_sub (hsub x hx) hxa) (inExt_of_sub (hsub y hy) hya)
      unshared := fun k ⟨e, he, hk⟩ => by
        rw [b.G_blocks] at he
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        have := inExt_of_sub (hsub e0 he0) hk
        exact h.unshared e0 he0 k this.1 this.2
      cap_canon := h.cap_canon }

/-- **The boundary gap, derived from `Loaded`** (`InterpRunReadyFacts.boot`). -/
theorem gap (b : Boot c p) : BootGap b b.G where
  top_room := b.heapFacts.top_room
  brk_page := b.heapFacts.brk_page
  binblocks := b.heapFacts.binblocks
  frame := b.frameChunks
  stderr := b.heapFacts.stderr
  sharedWin := b.sharedWin

end Boot

/-! ## 5. The global frame's boundary data -/

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

/-- Every live block of the boundary heap sits in the arena, 16-aligned: an
in-use chunk payload of the walk from `heapStart`, possibly trimmed. -/
theorem win_of_mem (b : Boot c p) {blk : Nat × Nat} (h : blk ∈ b.H) : BlockWin blk := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
  have hs := b.H_sub w hw
  obtain ⟨ch, hc, _, rfl⟩ := mem_inuseBlocks.1 hw
  have hb := b.alloc.heap.walk.chunk_bounds ch hc
  have hal := (walk_aligned b.alloc.heap.walk (by unfold heapStart; decide)).1 ch hc
  have := b.alloc.heap.top_le
  have := b.alloc.heap.brk_le
  simp only at hs
  unfold heapStart at hb
  unfold heapEnd at this
  exact ⟨by omega, by omega, by unfold htifLo; omega, by omega⟩

/-- **The global frame's `FrameBridge`**, from the boundary and the chunk
premise, at the memory's own image. -/
theorem frameBridge (b : Boot c p) {G : FrameGeom}
    (h : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) :
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
      disjoint := h.disjoint
      win := fun blk hblk => b.win_of_mem (h.live blk hblk)
      e_align := h.env ▸ (b.ready.store.frames_arena 0 initSt_frame0).2
      cap_canon := by rw [h.cap_canon]; rfl
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

/-- Writable ELF data owned by neither the allocator nor newlib's runtime
data (`Stdio.stdioFoot`): the interpreter's statics and padding. -/
def OtherStaticByte (k : Nat) : Prop := StaticByte k ∧ ¬ Stdio.stdioFoot k

theorem static_parts (k : Nat) :
    StaticByte k ↔ Stdio.stdioFoot k ∨ OtherStaticByte k := by
  unfold OtherStaticByte
  constructor
  · intro h; by_cases hs : Stdio.stdioFoot k
    · exact .inl hs
    · exact .inr ⟨h, hs⟩
  · rintro (h | h)
    · refine ⟨?_, Newlib.stdioFoot_off_alloc k h⟩
      unfold Stdio.stdioFoot Stdio.InRange at h; omega
    · exact h.1

theorem stdio_disj (k : Nat) (h : Stdio.stdioFoot k) : ¬ OtherStaticByte k :=
  fun h' => h'.2 h

/-- The whole C stack. -/
def StackByte (k : Nat) : Prop := stackSL.lo ≤ k ∧ k < stackSL.hi

/-- `struct Interp` (480 bytes, `interp.h`: `err_msg[256]` at 224), inside
`main`'s frame. -/
def InterpByte (inp k : Nat) : Prop := InExt (inp, 480) k

/-- The owned stack below `interp_run`'s entry `sp`. -/
def FreeStackByte (k : Nat) : Prop := InExt (stackSL.lo, spEntry - stackSL.lo) k

/-- The stack above `interp_run`'s entry `sp` outside `struct Interp`:
`main`'s saved registers and locals, owned at their values. -/
def CallerByte (inp k : Nat) : Prop := (spEntry ≤ k ∧ k < stackSL.hi) ∧ ¬ InterpByte inp k

/-- Read-only bytes: the code and the boundary's immutable (shared) set. -/
def RoByte (shared : Nat → Prop) (k : Nat) : Prop := shared k ∨ CodeByte k

/-- Every byte the boundary world owns. -/
def BootByte (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) (k : Nat) : Prop :=
  RoByte shared k ∨ BlocksCover G.blocks k ∨ heapFoot vsaLayoutP H k ∨ StackByte k ∨ StaticByte k

namespace Boot

variable {c : Vsa.Machine.Config} {p : Program}

theorem inp_toNat (b : Boot c p) : b.inp.toNat = interpObject := by
  rw [b.ready.interp_local]; decide

theorem blockHeapAt (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) :
    BlockHeapAt c.σ.mem b.H b.top b.brkv b.chunks b.bins :=
  (blockHeapAt_of_heapAt b.alloc.heap hroom).1.shrink _ b.H_sub

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
    ¬ heapFoot vsaLayoutP b.H k := by
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
    have hin := hcov k hek
    refine hout _ (List.mem_map_of_mem hblk) ?_
    rw [b.trim_of_shared hk hin]
    exact hin

end Boot

theorem stackSL_lo : stackSL.lo = 0x87800000 := rfl
theorem stackSL_hi : stackSL.hi = 0x88000000 := rfl
theorem spEntry_eq : spEntry = 0x87fffd00 := rfl
theorem interpObject_eq : interpObject = 0x87fffe10 := rfl

theorem heapFoot_cases {H : List (Nat × Nat)} {k : Nat} (h : heapFoot vsaLayoutP H k) :
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
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) {k : Nat}
    (hk : BlocksCover G.blocks k) : heapStart ≤ k ∧ k < heapEnd := by
  obtain ⟨blk, hblk, hin⟩ := hk
  exact (b.blockHeapAt hroom).block_arena (hG.live blk hblk) hin

theorem store_not_heapFoot (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) {k : Nat}
    (hk : BlocksCover G.blocks k) : ¬ heapFoot vsaLayoutP b.H k := by
  have ha := b.store_arena hroom hG hk
  intro hf
  rcases heapFoot_cases hf with ⟨_, h2, _⟩ | ⟨_, _, hout⟩
  · unfold heapStart at ha; omega
  · obtain ⟨blk, hblk, hin⟩ := hk
    exact hout blk (hG.live blk hblk) hin

/-- Every boot byte is a 32-bit address. -/
theorem bootByte_lt (b : Boot c p) (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) {k : Nat}
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
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) (k : Nat)
    (hk : RoByte b.D.shared k) :
    ¬ (BlocksCover G.blocks k ∨ heapFoot vsaLayoutP b.H k ∨ StackByte k ∨ StaticByte k) := by
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
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) (k : Nat)
    (hk : BlocksCover G.blocks k) :
    ¬ (heapFoot vsaLayoutP b.H k ∨ StackByte k ∨ StaticByte k) := by
  have ha := b.store_arena hroom hG hk
  unfold heapStart heapEnd at ha
  rintro (hh | hstk | hsta)
  · exact b.store_not_heapFoot hroom hG hk hh
  · unfold StackByte at hstk; rw [stackSL_lo] at hstk; omega
  · unfold StaticByte at hsta; omega

end Boot

theorem heap_disj {H : List (Nat × Nat)} (k : Nat) (hk : heapFoot vsaLayoutP H k) :
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
    · by_cases h2 : 0x87fffe10 ≤ k ∧ k < 0x87fffe10 + 480
      · exact .inr (.inl h2)
      · exact .inr (.inr ⟨⟨by omega, by omega⟩, h2⟩)
  · rintro (h | h | h) <;> omega

/-! ## 7. The finite byte map adequacy hands over -/

theorem bootAddrs_exists (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) :
    ∃ l : List Nat, l.Nodup ∧ ∀ k, k ∈ l ↔ k < 2 ^ 32 ∧ BootByte shared G H k := by
  refine ⟨(List.range (2 ^ 32)).filter
    fun k => @decide (BootByte shared G H k) (Classical.propDecidable _),
    List.nodup_range.filter _, fun k => ?_⟩
  rw [List.mem_filter, List.mem_range, @decide_eq_true_iff _ (Classical.propDecidable _)]

/-- Every boot byte, enumerated. Sealed behind `Classical.choose`: the kernel
must never see the `2 ^ 32`-element range it is cut from. -/
noncomputable def bootAddrs (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) :
    List Nat :=
  Classical.choose (bootAddrs_exists shared G H)

theorem bootAddrs_nodup (shared : Nat → Prop) (G : FrameGeom) (H : List (Nat × Nat)) :
    (bootAddrs shared G H).Nodup :=
  (Classical.choose_spec (bootAddrs_exists shared G H)).1

theorem mem_bootAddrs {shared : Nat → Prop} {G : FrameGeom} {H : List (Nat × Nat)}
    (hlt : ∀ k, BootByte shared G H k → k < 2 ^ 32) (k : Nat) :
    k ∈ bootAddrs shared G H ↔ BootByte shared G H k := by
  unfold bootAddrs
  rw [(Classical.choose_spec (bootAddrs_exists shared G H)).2 k]
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

Total mode starts `isHeapRoom vsaLayoutP vsaRoomB` at the cost of the
program's derivation (`InitialAllocatorAt.capacity`, as H4's
`roomB_of_initial`); partial mode starts `isHeap vsaLayoutP`. -/

/-- The pure side condition a regime needs at the boundary top chunk. -/
def RegimeOK (top : Nat) : Regime → Prop
  | .counted k => 2 * k + extendSlack ≤ heapEnd - top
  | .uncounted => True

/-- **The counted regime's start**: a big-step behaviour has a costed
derivation whose cost the boundary heap covers. -/
theorem Boot.regime_of_bigStep {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    {out : String} (hb : BigStep p out) :
    ∃ st' n, ExecSeqCost initSt 0 0 p st' .normal n ∧ st'.out = out ∧
      RegimeOK b.top (.counted n) := by
  obtain ⟨st', n, hn, hout⟩ := BigStep.cost hb
  exact ⟨st', n, hn, hout, b.alloc.capacity p b.repr st' n hn⟩

theorem regimeOK_uncounted (top : Nat) : RegimeOK top .uncounted := trivial

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The byte map as exclusive ownership of every boot byte. -/
theorem Boot.bytes_own {c : Vsa.Machine.Config} {p : Program} (b : Boot c p)
    (hroom : b.top + 16 ≤ b.brkv) {G : FrameGeom}
    (hG : FrameChunks c.σ.mem b.H b.D.shared (b.φf 0) G) :
    ([∗map] k ↦ v ∈ b.bytes G, iprop(k ↦ₘ v)) ⊢
      ownImg (GF := GF) (fun k => RoByte b.D.shared k ∨ BlocksCover G.blocks k ∨
        heapFoot vsaLayoutP b.H k ∨ StackByte k ∨ StaticByte k) (memImg c.σ.mem) :=
  ownImg_of_memMap (bootAddrs_nodup _ _ _) (mem_bootAddrs fun _ hk => b.bootByte_lt hroom hG hk)

/-- **Text out of a read-only view**: every `textOwn` a block lemma needs is
a projection of `roOn CodeByte m` (the fixed binary is in the memory). -/
theorem textOwn_of_roOn {P : Nat → Prop} {m : Mem} :
    ∀ {text : List (Nat × BitVec 8)}, (∀ q ∈ text, P q.1 ∧ m[q.1]? = some q.2) →
      roOn (GF := GF) P m ⊢ textOwn text
  | [], _ => by
    unfold textOwn
    iintro _
    simp only [sepL_nil]
    iempintro
  | q :: text, h => by
    unfold textOwn
    iintro #H
    simp only [sepL_cons]
    isplitl []
    · iapply roOn_byte (h q (.head _)).1 (h q (.head _)).2 $$ H
    · have ht := textOwn_of_roOn (P := P) (m := m) (text := text)
        (fun q' hq' => h q' (.tail _ hq'))
      unfold textOwn at ht
      iapply ht $$ H

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
theorem heapRes_of_bytes {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : BlockHeapAt m H top brkv chunks bins)
    (hpage : brkv % 4096 = 0) (hbb : ∀ bb, read64 m binblocksAddr = some bb → bb < 2 ^ 32)
    (hst : Starts H) {ρ : Regime} (hρ : RegimeOK top ρ) :
    ownImg (GF := GF) (heapFoot vsaLayoutP H) (memImg m) ⊢ heapRes vsaLayoutP vsaRoomB ρ H := by
  cases ρ with
  | counted k =>
    unfold heapRes isHeapRoom
    iintro Hb
    iexists memImg m
    iframe Hb
    ipureintro
    exact ⟨pShape_of_blockHeapAt h hpage hbb hst, roomB_of_blockHeapAt h hpage hbb hst hρ⟩
  | uncounted =>
    unfold heapRes isHeap
    iintro Hb
    iexists memImg m
    iframe Hb
    ipureintro
    exact pShape_of_blockHeapAt h hpage hbb hst

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

/-- **`struct Interp` at `interp_run`'s entry** from its 480 bytes. -/
theorem interpCtxPre_of_bytes {inp g : Nat} {img : Nat → BitVec 8}
    (hg : imgLE img inp 8 = g) (hd : imgLE img (inp + interpDepthOff) 4 = 0) :
    ownImg (GF := GF) (InExt (inp, 480)) img ∗ frameAt 0 g ⊢ |==> interpCtxPre inp 0 := by
  iintro ⟨H, #Hf⟩
  ihave ⟨Hg, H⟩ := ownImg_ext_split inp 480 8 (inp + interpDepthOff) 472 img
    (by decide) rfl rfl $$ H
  ihave ⟨Hd, H⟩ := ownImg_ext_split (inp + interpDepthOff) 472 4 (inp + interpDepthOff + 4) 468
    img (by decide) rfl rfl $$ H
  ihave ⟨Hp, H⟩ := ownImg_ext_split (inp + interpDepthOff + 4) 468 4 (inp + interpJmpOff) 464
    img (by decide) (by unfold interpDepthOff interpJmpOff; omega) rfl $$ H
  ihave ⟨Hj, He⟩ := ownImg_ext_split (inp + interpJmpOff) 464 interpJmpLen
    (inp + interpErrOff) interpErrLen img (by decide)
    (by unfold interpJmpOff interpJmpLen interpErrOff; omega) rfl $$ H
  imod wordRO_of_ownImg hg $$ Hg with Hg
  imodintro
  unfold interpCtxPre interpCore interpCoreE errAny
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

/-! ## 9. The boundary world -/

section Assembly

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] {c : Vsa.Machine.Config}
  {p : Program}

/-- §3's `world` at `interp_run`'s ENTRY: identical except that the
`jmp_buf` is still exclusive (`interpCtxPre`); `setjmp` (H5) turns it into
`world`'s read-only one. -/
def worldPre [InterpGS GF] (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  iprop(∃ H B, heapRes L Room ρ H ∗ storeRepr N st.store B ∗ consoleOwn st.out ∗
    Stdio.stdioOwn ∗ interpCtxPre inp d ∗ ⌜∀ b ∈ B, b ∈ H⌝)

/-- **The boundary world**: what `interp_run`'s entry owns, in regime `ρ`.

* `worldPre … ρ initSt 0`: the allocator (`isHeapRoom` at the derivation's
  cost, or `isHeap`), the store (one frame, three natives), the console at
  the initial output, and `struct Interp`;
* `frameAt 0 (φf 0)`: the global frame's address, forever;
* `astSs stmts count p`: the program, persistent;
* `roOn CodeByte m`: the fixed binary's text and read-only data, persistent
  (every `textOwn` a block lemma needs is a projection, `textOwn_of_roOn`);
* `roOn shared m`: the boundary's immutable heap bytes;
* the stack below `interp_run`'s entry `sp` (`freeStack_carve`, then F3's
  `stackScratch_boundary` with `Boot.fits`);
* `main`'s frame above `sp` (outside `struct Interp`) and the writable ELF
  statics outside the allocator's globals, both at their boundary values. -/
def bootRes [InterpGS GF] (b : Boot c p) (ρ : Regime) : IProp GF :=
  iprop(worldPre b.N vsaLayoutP vsaRoomB b.inp.toNat ρ initSt 0 ∗
    frameAt 0 (b.φf 0) ∗ astSs b.stmts b.count p ∗ roOn CodeByte c.σ.mem ∗
    roOn b.D.shared c.σ.mem ∗ blockOwn stackSL.lo (spEntry - stackSL.lo) ∗
    ownImg (CallerByte b.inp.toNat) (memImg c.σ.mem) ∗ ownImg OtherStaticByte (memImg c.σ.mem))

theorem freeStack_disj (inp : Nat) (hinp : inp = interpObject) (k : Nat)
    (hk : FreeStackByte k) : ¬ (InterpByte inp k ∨ CallerByte inp k) := by
  subst hinp
  unfold FreeStackByte InterpByte CallerByte InExt at *
  rw [stackSL_lo, spEntry_eq, interpObject_eq] at *
  dsimp only at *
  omega

theorem interp_disj (inp k : Nat) (hk : InterpByte inp k) : ¬ CallerByte inp k :=
  fun h => h.2 hk

/-- **The carving, at fixed ghost names.** -/
theorem boot_of_bytes [I : InterpGS GF] (b : Boot c p)
    (ρ : Regime) (hρ : RegimeOK b.top ρ) :
    ghost_map_auth (GF := GF) I.frameName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ghost_map_auth I.closName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ([∗map] k ↦ v ∈ b.bytes b.G, iprop(k ↦ₘ v)) ∗ consoleOwn (Vsa.Machine.output c.σ) ⊢
      |==> bootRes b ρ := by
  have gap := b.gap
  generalize b.G = G at gap ⊢
  have hroom := gap.top_room
  have hH : Starts b.H := b.starts
  have hG := gap.frame
  have hout : Vsa.Machine.output c.σ = initSt.out := b.ready.out
  have hg : imgLE (memImg c.σ.mem) b.inp.toNat 8 = G.e := by
    rw [hG.env]; exact readLE_memImg b.ready.globals
  have hd : imgLE (memImg c.σ.mem) (b.inp.toNat + interpDepthOff) 4 = 0 :=
    readLE_memImg b.ready.call_depth
  have hrd : FrameReads c.σ.mem b.N b.φf b.φc G.e frame0 := hG.env ▸ b.frameReads
  unfold bootRes worldPre
  rw [← hG.env, ← hout]
  iintro ⟨Hf, Hc, Hm, Hcon⟩
  ihave Hall := b.bytes_own hroom hG $$ Hm
  ihave ⟨Hro, Hall⟩ := ownSet_unglue _ _ _ (b.ro_disj hroom hG) $$ Hall
  ihave ⟨Hst, Hall⟩ := ownSet_unglue _ _ _ (b.store_disj hroom hG) $$ Hall
  ihave ⟨Hh, Hall⟩ := ownSet_unglue _ _ _ (fun k hk => heap_disj k hk) $$ Hall
  ihave ⟨Hstk, Hsta⟩ := ownSet_unglue _ _ _ stack_disj $$ Hall
  ihave Hsta := ownSet_iff _ static_parts $$ Hsta
  ihave ⟨Hstd, Hsta⟩ := ownSet_unglue _ _ _ stdio_disj $$ Hsta
  ihave Hstk := ownSet_iff _ (fun k => stack_parts b.inp.toNat k b.inp_toNat) $$ Hstk
  ihave ⟨Hfree, Hstk⟩ := ownSet_unglue _ _ _ (freeStack_disj _ b.inp_toNat) $$ Hstk
  ihave ⟨Hint, Hcal⟩ := ownSet_unglue _ _ _ (interp_disj _) $$ Hstk
  ihave Hint := ownSet_iff (S := InterpByte b.inp.toNat) (T := InExt (b.inp.toNat, 480)) _ (fun _ => Iff.rfl) $$ Hint
  ihave Hfree := ownSet_iff (S := FreeStackByte) (T := InExt (stackSL.lo, spEntry - stackSL.lo)) _
    (fun _ => Iff.rfl) $$ Hfree
  imod roOn_of_ownImg (m := c.σ.mem) (fun k v _ hv => memImg_eq hv) $$ Hro with #Hro
  ihave #Hsh := roOn_mono (Q := RoByte b.D.shared) (P := b.D.shared) (m := c.σ.mem)
    (fun k h => Or.inl h) $$ Hro
  ihave Hempty := storeRepr_empty (N := b.N) $$ [Hf Hc]
  · iframe Hf Hc
  ihave Hbody := frameBody_of_frameRepr hrd (b.frameBridge hG) gap.sharedWin $$ [Hst]
  · iframe Hsh Hst
    isplitl []
    · iapply closSupply_frame0
    · rw [show frame0.parent = none from rfl, hG.par]
      iapply parentSupply_none
  imod storeRepr_allocFrame (N := b.N) (s := ⟨#[], #[]⟩) (B := []) (s' := initSt.store)
    (f := frame0) (Gm := G) (by rfl) (by rfl) Vsa.Sim.storeInvariant_initSt $$ [Hempty Hbody] with ⟨Hs, #He⟩
  · iframe Hempty Hbody
  imod interpCtxPre_of_bytes hg hd $$ [Hint He] with Hi
  · iframe Hint He
  imodintro
  iframe He Hsta Hcal
  isplitl [Hh Hs Hcon Hstd Hi]
  · iexists b.H, ([] ++ G.blocks)
    iframe Hs Hcon Hi
    isplitl [Hh]
    · iapply heapRes_of_bytes (b.blockHeapAt hroom) gap.brk_page gap.binblocks hH hρ $$ Hh
    isplitl [Hstd]
    · unfold Stdio.stdioOwn Stdio.stdioAt
      iexists memImg c.σ.mem
      iframe Hstd
      ipureintro
      exact stdioOK_of_mem b.ready.console b.ready.exit_runtime gap.stderr
    · ipureintro
      intro blk hblk
      exact hG.live blk (by simpa using hblk)
  isplitl []
  · iapply astSs_of_programRepr (b.owned.program p b.repr) $$ Hsh
  isplitl []
  · iapply roOn_mono (Q := RoByte b.D.shared) (P := CodeByte) (m := c.σ.mem)
      (fun k h => Or.inr h) $$ Hro
  iframe Hsh
  iapply blockOwn_of_ownImg _ _ _ $$ Hfree

/-- **`world_of_boundary`** (INTERP_DESIGN.md §5.1): from the bytes adequacy
hands the client (`Boot.bytes`, which agrees with the configuration:
`Boot.bytes_agree`) and the console cell at the initial output, allocate the
two `InterpGS` ghost maps and carve the boundary world in regime `ρ`. The
boundary heap facts come from `Loaded` (`Boot.gap`). -/
theorem world_of_boundary (b : Boot c p) (ρ : Regime) (hρ : RegimeOK b.top ρ) :
    ([∗map] k ↦ v ∈ b.bytes b.G, iprop(k ↦ₘ v)) ∗ consoleOwn (GF := GF) (Vsa.Machine.output c.σ) ⊢
      |==> ∃ γf γc : GName, (letI : InterpGS GF := ⟨γf, γc⟩; bootRes b ρ) := by
  iintro ⟨Hm, Hcon⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) (H := NatMap) with ⟨%γf, Hf⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) (H := NatMap) with ⟨%γc, Hc⟩
  iexists γf, γc
  iapply (boot_of_bytes (I := ⟨γf, γc⟩) b ρ hρ) $$ [Hf Hc Hm Hcon]
  iframe Hf Hc Hm Hcon

end Assembly

#print axioms boot_of_bytes
#print axioms world_of_boundary

#print axioms Boot.frameBridge
#print axioms Vsa.Sim.DlHeap.HeapAt.grow
#print axioms pShape_of_blockHeapAt
#print axioms roomB_of_blockHeapAt

end VsaIris.Interp
