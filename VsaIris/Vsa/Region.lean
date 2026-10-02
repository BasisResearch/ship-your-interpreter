import VsaIris.Vsa.MallocCtx
import VsaIris.Vsa.RegionCore
import VsaIris.Vsa.KeyNF
import VsaIris.Vsa.Dbm

/-!
# Region-keyed memory for allocator path proofs (candidate KT)

Every address an allocator path touches is `region ⊕ offset`. A region is a
base and an extent whose bytes all satisfy an ownership predicate; regions are
minted once:

* a heap chunk from the chunk walk of `PHeapAt` (`BlockHeapAt.chunkK`,
  `.freeSpan`, `.next`, `.nodeK`),
* the program-lifetime static table (`globRgn`, `binRgn`),
* the stack frame (`MWin`'s stack half, `win_stack`).

The laws are proved once over regions:

* in-window / off-mailbox (L3): `Rgn.ldOK`, `Rgn.stOK`, `WOK.rgn`;
* off-stack (L3): `Rgn.offStack`;
* frame (L5): a store log is summarised by its key list; `LogIn` says every
  key lies in a region, and `frame_log` carries the frame post through the
  whole log at once;
* read-over-write (L2) stays `read64_hit_eq`/`read64_miss` keyed by the log.

The tactics (`rgn_side`, `rgn_run`, `rgn_win`, `log_in`, `rgn_arith`, `open_fields`) are in
`RegionTac.lean`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

namespace Rgn

variable {P P' : Nat → Prop} {b e : Nat}

theorem lower {H : List (Nat × Nat)} {x : Nat × Nat} (r : Rgn (vsaFoot (x :: H)) b e) :
    Rgn (vsaFoot H) b e :=
  r.mono fun _ => vsaFoot_of_cons'
where
  vsaFoot_of_cons' {a : Nat} : vsaFoot (x :: H) a → vsaFoot H a
    | .inl h => .inl h
    | .inr ⟨h1, h2, h3⟩ => .inr ⟨h1, h2, fun e' he' => h3 e' (List.mem_cons_of_mem _ he')⟩

end Rgn

theorem vsaFoot_range {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) :
    0x8001ad10 ≤ a ∧ a < 0x87800000 := by
  rcases h with h | ⟨h1, h2, _⟩
  · unfold allocGlobal InRange at h; omega
  · unfold heapStart at h1; unfold heapEnd at h2; omega

section Laws

variable {H : List (Nat × Nat)} {b e a w : Nat}

/-! Each law takes the key-in-region check as ONE conjunction, so a candidate
region costs one arithmetic query. -/

theorem Rgn.ldOK (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e ∧ 0 < w) : LdOK a w := by
  have l := vsaFoot_range (r.mem h.1 (by omega))
  have u := vsaFoot_range (r.mem (a := a + w - 1) (by omega) (by omega))
  unfold LdOK Vsa.Sim.tohostAddr; omega

theorem Rgn.stOK (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e ∧ 0 < w ∧ a % w = 0) :
    StOK a w := by
  have l := vsaFoot_range (r.mem h.1 (by omega))
  have u := vsaFoot_range (r.mem (a := a + w - 1) (by omega) (by omega))
  unfold StOK Vsa.Sim.tohostAddr; omega

theorem WOK.rgn {C : MCtx} (O : WOK C) (r : Rgn (vsaFoot C.H) b e) (h : b ≤ a ∧ a + w ≤ b + e) :
    ∀ x ∈ accAddrs a w, C.S x :=
  O.foot (r.word h.1 h.2)

theorem Rgn.win {s : BitVec 64} (r : Rgn (vsaFoot H) b e) (h : b ≤ a ∧ a + w ≤ b + e) :
    ∀ x, a ≤ x → x < a + w → MWin H s x :=
  fun _ hx1 hx2 => .inl (r.mem (by omega) (by omega))

theorem win_stack' {s : BitVec 64} (h : s.toNat - 256 ≤ a ∧ a + w ≤ s.toNat) :
    ∀ x, a ≤ x → x < a + w → MWin H s x :=
  win_stack (by unfold mHead; exact h.1) h.2

/-- A heap region never meets the stack window. -/
theorem Rgn.offStack {s : BitVec 64} (r : Rgn (vsaFoot H) b e)
    (hd : ∀ a, s.toNat - mHead ≤ a → a < s.toNat → ¬ vsaFoot H a) (he : 0 < e) :
    b + e ≤ s.toNat - mHead ∨ s.toNat ≤ b := by
  refine Classical.byContradiction fun hc => ?_
  by_cases h : s.toNat - mHead ≤ b
  · exact hd b h (by omega) (r.mem (by omega) (by omega))
  · exact hd _ (Nat.le_refl _) (by unfold mHead at *; omega) (r.mem (by omega) (by omega))

/-- A single owned byte is off the stack window. -/
theorem offStack_pt {s : BitVec 64} (hd : ∀ a, s.toNat - mHead ≤ a → a < s.toNat → ¬ vsaFoot H a)
    (ha : vsaFoot H a) : a < s.toNat - 256 ∨ s.toNat ≤ a := by
  have := (⟨fun k hk => by rwa [show k = 0 by omega]⟩ : Rgn (vsaFoot H) a 1).offStack hd (by decide)
  unfold mHead at this; omega

/-- The allocator's stack window, as an access region. -/
theorem WOK.stackRgn {C : MCtx} (O : WOK C) : ARgn C.S (C.s.toNat - 256) 256 := by
  have := O.sp.lo; have := O.sp.hi; unfold mHead Vsa.Sim.tohostAddr at *
  exact ⟨⟨fun k hk => O.own _ (.inr ⟨by unfold mHead; omega, by omega⟩)⟩, by omega, by omega⟩

end Laws

/-! Key laws (see `RegionCore`): the region is picked by atom match and the membership
check is a closed boolean on literal offsets. -/

section KeyLaws

variable {H : List (Nat × Nat)} {b e t c0 c L A m : Nat}

theorem Rgn.lt_k (r : Rgn (vsaFoot H) b e) (hb : b = t + c0) (he : L ≤ e) (c w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    t + c < 18446744073709551616 := by
  have h := key_chk h; subst hb
  have := vsaFoot_range (r.mem (a := t + c) (by omega) (by omega)); omega

theorem Rgn.ldOK_k (r : Rgn (vsaFoot H) b e) (hb : b = t + c0) (he : L ≤ e) (hA : t + c = A)
    (w : Nat) (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    LdOK A w := by
  have h := key_chk h; subst hb hA; exact r.ldOK (by omega)

theorem Rgn.stOK_k (r : Rgn (vsaFoot H) b e) (hb : b = t + c0) (he : L ≤ e) (hA : t + c = A)
    (w : Nat) (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true)
    (hal : t % m = 0) (ha : (m % w == 0 && c % w == 0) = true) : StOK A w := by
  have h2 := key_al hal ha
  have h := key_chk h; subst hb hA; exact r.stOK ⟨by omega, by omega, by omega, h2⟩

theorem WOK.rgn_k {C : MCtx} (O : WOK C) (r : Rgn (vsaFoot C.H) b e) (hb : b = t + c0)
    (he : L ≤ e) (hA : t + c = A) (w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    ∀ x ∈ accAddrs A w, C.S x := by
  have h := key_chk h; subst hb hA; exact O.rgn r ⟨by omega, by omega⟩

theorem Rgn.win_k {s : BitVec 64} (r : Rgn (vsaFoot H) b e) (hb : b = t + c0) (he : L ≤ e)
    (hA : t + c = A) (w : Nat)
    (h : (Nat.ble c0 c && Nat.ble (c + w) (c0 + L) && Nat.blt 0 w) = true) :
    ∀ x, A ≤ x → x < A + w → MWin H s x := by
  have h := key_chk h; subst hb hA; exact r.win ⟨by omega, by omega⟩

end KeyLaws

/-! ## The static table (V1): minted once against the fixed layout. -/

theorem globRgn (H : List (Nat × Nat)) : Rgn (vsaFoot H) 0x8001ad10 0x810 :=
  ⟨fun k hk => .inl (.inl ⟨by omega, by omega⟩)⟩

/-- The `errno` word of the reentrancy structure. -/
theorem errnoRgn (H : List (Nat × Nat)) : Rgn (vsaFoot H) 0x8001b538 4 :=
  ⟨fun k hk => .inl (.inr (.inl ⟨by omega, by omega⟩))⟩

/-- The `fd`/`bk` link words of bin `j`'s header. -/
theorem binRgn (H : List (Nat × Nat)) {j : Nat} (hj : j < numBins) :
    Rgn (vsaFoot H) (binAt j + 16) 16 := by
  have := binAt_geo j hj
  exact (globRgn H).sub (by omega) (by omega)

/-! ## Chunk regions, minted from the chunk walk. -/

/-- The local section of one chunk of the walk: bounds, alignment, its two header
regions (own header, next boundary header), the two header reads and its walk
successor. -/
structure ChunkK (m : Mem) (H : List (Nat × Nat)) (top brkv : Nat) (chunks : List Chunk)
    (c : Chunk) : Prop where
  lo : 0x8001c170 ≤ c.addr
  hi : c.addr + c.size ≤ top
  room : top + 16 ≤ brkv
  brk : brkv ≤ 0x87800000
  al : c.addr % 16 = 0
  topal : top % 16 = 0
  sz16 : c.size % 16 = 0
  sz32 : 32 ≤ c.size
  hdr : Rgn (vsaFoot H) (c.addr + 8) 8
  nhdr : Rgn (vsaFoot H) (c.addr + c.size + 8) 8
  hdrv : ∃ h, read64 m (c.addr + 8) = some h ∧ chunkSize h = c.size ∧ h % 4 < 2
  nhdrv : ∃ hn, read64 m (c.addr + c.size + 8) = some hn ∧ prevInuse hn = c.inuse
  next : c.addr + c.size = top ∨ ∃ d ∈ chunks, d.addr = c.addr + c.size

variable {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat}

theorem BlockHeapAt.chunkK (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) : ChunkK m H top brkv chunks c := by
  have HH := B.heap
  have hb := HH.walk.chunk_bounds c hc
  have hs := walk_sizes HH.walk c hc
  have hbrk := HH.brk_le
  unfold heapStart heapEnd at *
  exact ⟨hb.1, hb.2.1, B.top_room, hbrk, HH.aligned.1 c hc, HH.aligned.2, hs.1, hs.2,
    ⟨foot_header B (.inr ⟨c, hc, rfl⟩)⟩, ⟨foot_header B (HH.end_bnd hc)⟩, (HH.headers hc).1,
    (HH.headers hc).2, HH.end_bnd hc⟩

theorem ChunkK.lower {x : Nat × Nat} {c : Chunk} (K : ChunkK m (x :: H) top brkv chunks c) :
    ChunkK m H top brkv chunks c :=
  { K with hdr := K.hdr.lower, nhdr := K.nhdr.lower }

/-- A free chunk owns its whole span, header to next header. -/
theorem BlockHeapAt.freeSpan (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) : Rgn (vsaFoot H) (c.addr + 8) (c.size + 8) := by
  have hb := B.heap.walk.chunk_bounds
  have hs := B.heap.walk.chunk_sep
  have hroom := B.top_room
  have hbrk := B.heap.brk_le
  have hle := B.heap.walk.le
  have hbc := hb c hc
  refine ⟨fun k hk => ?_⟩
  by_cases hh : k < 8
  · exact (⟨foot_header B (.inr ⟨c, hc, rfl⟩)⟩ : Rgn _ _ 8).byte k hh
  by_cases ht : c.size ≤ k
  · have := foot_header B (B.heap.end_bnd hc) (k - c.size) (by omega)
    rwa [show c.addr + c.size + 8 + (k - c.size) = c.addr + 8 + k by omega] at this
  refine foot_of_arena B.heap (by unfold heapStart at *; omega) (by omega) ?_
  intro c' hc' hu hin
  have := hb c' hc'
  rcases hs c' hc' c hc with rfl | h3 | h3
  · rw [hu] at hf; cases hf
  · omega
  · omega

theorem foot_free_span (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) :
    ∀ a, c.addr + 8 ≤ a → a < c.addr + c.size + 16 → vsaFoot H a :=
  fun _ h1 h2 => (B.freeSpan hc hf).mem h1 (by omega)

/-- The neighbour region: a chunk that does not end at `top` is followed by a
chunk starting at its end. -/
theorem BlockHeapAt.next (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk} (hc : c ∈ chunks)
    (hne : c.addr + c.size ≠ top) :
    ∃ cs₁ d cs₃, chunks = cs₁ ++ c :: d :: cs₃ ∧ d.addr = c.addr + c.size := by
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
  have hw := B.heap.walk
  rw [hsplit] at hw
  rcases (walk_next_of hw).2 with ⟨he, _⟩ | ⟨d, cs₃, rfl, hd⟩
  · exact absurd he hne
  · exact ⟨cs₁, d, cs₃, hsplit, hd⟩

/-- The walk successor of `c` is the given chunk `d` at `c`'s end. -/
theorem BlockHeapAt.next_eq (B : BlockHeapAt m H top brkv chunks bins) {c d : Chunk}
    (hc : c ∈ chunks) (hd : d ∈ chunks) (hda : d.addr = c.addr + c.size) :
    ∃ cs₁ cs₃, chunks = cs₁ ++ c :: d :: cs₃ := by
  have hb := B.heap.walk.chunk_bounds d hd
  obtain ⟨cs₁, d', cs₃, hsplit, hd'⟩ := B.next hc (by omega)
  have hdm : d' ∈ chunks := by rw [hsplit]; simp
  obtain rfl := B.heap.chunk_eq hdm hd (by omega)
  exact ⟨cs₁, cs₃, hsplit⟩

/-- A bin-ring node (a bin header or a binned free chunk): alignment, bounds, its
`fd`/`bk` link region, and separation of its link words from chunk boundaries. -/
structure NodeK (H : List (Nat × Nat)) (top : Nat) (chunks : List Chunk) (x : Nat) : Prop where
  al : x % 16 = 0
  lo : 0x8001ad20 ≤ x
  hi : x + 32 ≤ top
  links : Rgn (vsaFoot H) (x + 16) 16
  bnd : ∀ b, (b = top ∨ ∃ c ∈ chunks, c.addr = b) → ∀ k, 0 < k → k < 32 → b ≠ x + k

theorem BlockHeapAt.nodeK (B : BlockHeapAt m H top brkv chunks bins) {j x : Nat} (hj0 : 0 < j)
    (hj : j < numBins) (hx : x = binAt j ∨ x ∈ bins j) : NodeK H top chunks x := by
  have HH := B.heap
  obtain ⟨hx16, hnode⟩ := HH.node hj0 hj hx
  have hloc : 0x8001ad20 ≤ x ∧ x + 32 ≤ top := by
    rcases hnode with rfl | ⟨cx, hcx, rfl, _, _⟩
    · have := binAt_geo j hj; have := HH.walk.le
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  exact ⟨hx16, hloc.1, hloc.2, ⟨fun k hk => by
    have := B.node_foot hj0 hj hx (16 + k) (by omega) (by omega)
    rwa [← Nat.add_assoc] at this⟩, fun b hb k hk0 hk => HH.bnd_ne_node hj hnode hb k hk0 hk⟩

/-- The ring neighbours of a position in bin `j`'s list are ring nodes of bin `j`. -/
theorem ring_nbr_mem {bins : Nat → List Nat} {j pred succ : Nat} {pre post : List Nat}
    (hpos : bins j = pre ++ post) (hpred : (binAt j :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt j]).head? = some succ) :
    (pred = binAt j ∨ pred ∈ bins j) ∧ (succ = binAt j ∨ succ ∈ bins j) := by
  rw [hpos]
  refine ⟨?_, ?_⟩
  · rcases List.mem_cons.mp (List.mem_of_getLast? hpred) with h1 | h1
    · exact .inl h1
    · exact .inr (List.mem_append_left _ h1)
  · rcases List.mem_append.mp (List.mem_of_head? hsucc) with h1 | h1
    · exact .inr (List.mem_append_right _ h1)
    · exact .inl (List.mem_singleton.mp h1)

/-- The ring neighbours of a binned chunk `x`, as node regions. -/
theorem BlockHeapAt.nbrK (B : BlockHeapAt m H top brkv chunks bins) {j x pred succ : Nat}
    {pre post : List Nat} (hj0 : 0 < j) (hj : j < numBins) (hmem : bins j = pre ++ x :: post)
    (hpred : (binAt j :: pre).getLast? = some pred) (hsucc : (post ++ [binAt j]).head? = some succ) :
    NodeK H top chunks pred ∧ NodeK H top chunks succ := by
  refine ⟨B.nodeK hj0 hj ?_, B.nodeK hj0 hj ?_⟩
  · rcases List.mem_cons.mp (List.mem_of_getLast? hpred) with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hmem]; exact List.mem_append_left _ h1)
  · rcases List.mem_append.mp (List.mem_of_head? hsucc) with h1 | h1
    · exact .inr (by rw [hmem]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)

theorem NodeK.lower {x : Nat × Nat} {z : Nat} (K : NodeK (x :: H) top chunks z) :
    NodeK H top chunks z :=
  { K with links := K.links.lower }

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap in
theorem NodeK.end_sep {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {x : Nat} (N : NodeK H top chunks x)
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {a s : Nat} {u : Bool}
    (hc : (⟨a, s, u⟩ : Chunk) ∈ chunks) : a + s ≤ x ∨ x + 32 ≤ a + s := by
  have hb := N.bnd _ (h.end_bnd hc) (a + s - x)
  simp only at hb
  omega


/-- An 8-byte heap word is off the allocator's stack frame. -/
theorem off_stack_of {C : MCtx} {a : Nat}
    (hd : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) : a + 8 ≤ C.s.toNat - 256 ∨ C.s.toNat ≤ a :=
  (⟨hf⟩ : Rgn (vsaFoot C.H) a 8).offStack hd (by decide)

/-! ## Store logs as key lists (T). -/

theorem writeLog_nest (m : Mem) (l1 l2 : List WEntry) :
    writeLog (writeLog m l1) l2 = writeLog m (l1 ++ l2) :=
  (writeLog_append m l1 l2).symm

/-- Every key written by the log lies in `P`. -/
def LogIn (P : Nat → Prop) : List WEntry → Prop
  | [] => True
  | e :: L => (∀ b, e.1 ≤ b → b < e.1 + e.2.1 → P b) ∧ LogIn P L

theorem outL_of_logIn {P : Nat → Prop} : ∀ {L : List WEntry}, LogIn P L → ∀ b, ¬ P b → OutL L b
  | [], _, _, _ => trivial
  | _ :: _, ⟨h1, h2⟩, b, hb => ⟨Classical.byContradiction fun hc => hb (h1 b (by omega) (by omega)),
      outL_of_logIn h2 b hb⟩

/-- Frame (L5) through a whole log whose keys lie in the window. -/
theorem frame_log {C : MCtx} {Mt : Mem} {L : List WEntry} (hL : LogIn (MWin C.H C.s) L)
    (hf : ∀ b, ¬ MWin C.H C.s b → Mt[b]? = C.Mt0[b]?) :
    ∀ b, ¬ MWin C.H C.s b → (writeLog Mt L)[b]? = C.Mt0[b]? :=
  fun b hb => by rw [writeLog_out _ _ _ (outL_of_logIn hL b hb), hf b hb]

theorem pres_log {C : MCtx} {Mt : Mem} (L : List WEntry)
    (hp : ∀ b, vsaFoot C.H b → (Mt[b]?).isSome) :
    ∀ b, vsaFoot C.H b → ((writeLog Mt L)[b]?).isSome :=
  fun b hb => writeLog_present _ _ _ (hp b hb)

/-! ## Tactics -/

/-- A negative literal offset: adding `c` modulo `2^64` subtracts `2^64 - c`. -/
theorem key_sub (a c : Nat) (h : 18446744073709551616 - c ≤ a ∧ a < 18446744073709551616 ∧
    c < 18446744073709551616) :
    (a + c) % 18446744073709551616 = a - (18446744073709551616 - c) := by omega

/-- Keying an access: the goal about the address `a` follows from the same goal
about any `A` equal to it. The key `A` stays a bound variable of the argument, so
the kernel never unfolds the address term while checking the arithmetic. -/
theorem key_gen (a : Nat) (G : Nat → Prop) (h : ∀ A, a = A → G A) : G a := h a rfl

end VsaIris.VsaHeap
