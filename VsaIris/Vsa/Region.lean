import VsaIris.Vsa.MallocCtx
import VsaIris.Vsa.RegionCore
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

`rgn_side` extends `sx_side`, so the `sx_run` driver discharges ownership and
access-range obligations from any region in the local context: the access is
keyed once (`rgnKey`: a bound key `A` with the address equation normalised to Nat arithmetic), regions are ranked
by the atoms they share with the key, and each candidate is one linear check.
`rgn_win` closes one `LogIn` key the same way; `log_in` closes a whole key list.
`open_fields` exposes a minted structure's geometry to the arithmetic deciders.
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

/-- `BitVec.toNat_add` as a propositional rewrite. The core lemma is an `rfl` lemma,
so `simp` would leave the kernel a definitional check that unfolds `Nat.mod` on
the offset literal (2^64 steps for a negative offset); through this lemma the
kernel only infers a type. -/
theorem key_toNat_add (x y : BitVec 64) :
    (x + y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := (BitVec.toNat_add x y).trans rfl

theorem key_toNat_ofNat (x : Nat) : (BitVec.ofNat 64 x).toNat = x % 18446744073709551616 :=
  (BitVec.toNat_ofNat x 64).trans rfl

/-- A negative literal offset: adding `c` modulo `2^64` subtracts `2^64 - c`. -/
theorem key_sub (a c : Nat) (h : 18446744073709551616 - c ≤ a ∧ a < 18446744073709551616 ∧
    c < 18446744073709551616) :
    (a + c) % 18446744073709551616 = a - (18446744073709551616 - c) := by omega

/-- Address arithmetic on the goal only: normalise register updates and `BitVec`
additions, then `omega` over the facts in context (no hypothesis rewriting). -/
macro "rgn_arith" : tactic =>
  `(tactic| first
    | omega_dc
    | (simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceAppend,
        BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
        VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod]
       repeat (first
         | (rw [Nat.mod_eq_of_lt]; rotate_left; omega_dc)
         | (rw [VsaIris.VsaHeap.key_sub]; rotate_left; omega_dc)
         | fail "no wrap-around to remove")
       first | done | omega_dc)
    | fail "rgn_arith: address arithmetic failed")

/-- Keying an access: the goal about the address `a` follows from the same goal
about any `A` equal to it. The key `A` stays a bound variable of the argument, so
the kernel never unfolds the address term while checking the arithmetic. -/
theorem key_gen (a : Nat) (G : Nat → Prop) (h : ∀ A, a = A → G A) : G a := h a rfl

/-- Normalise a freshly introduced key equation `hA : a = A` to Nat arithmetic
(register updates, register additions, literal offsets of either sign,
wrap-around removed when the bound is in context). -/
macro "rgn_key_norm" : tactic =>
  `(tactic| (intro A hA
             (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
               LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
               BitVec.reduceAppend, BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
        VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat,
               Nat.reducePow, Nat.reduceMod] at hA)
             (repeat (first
               | (rw [Nat.mod_eq_of_lt] at hA; rotate_left; omega_dc)
               | (rw [VsaIris.VsaHeap.key_sub] at hA; rotate_left; omega_dc)
               | fail "no wrap-around to remove"))))

/-- Normalise the goal only (register updates, immediates, loads through stores). -/
macro "rgn_norm" : tactic =>
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, reduceIte, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.reduceSignExtend, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat,
      VsaIris.Sym.ldv_store_hit, VsaIris.Sym.ldv_ld_hit_eq, VsaIris.Sym.ldv_ld_miss])

/-- Replace loads whose value the context knows (`read64 M a' = some x`) in the goal. -/
macro "rgn_ld " "[" hs:term,* "]" : tactic => do
  let ls ← hs.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| VsaIris.Sym.ldv_at $h)
  `(tactic| simp (disch := rgn_arith) only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true,
      ite_false, VsaIris.Sym.ldv_ld_miss, $ls,*])

open Lean Elab Tactic Meta

/-- A region hypothesis: its name, base and extent. -/
structure RgnHyp where
  name : Name
  base : Expr
  ext : Expr
  acc : Bool := false

/-- The regions and ownership contexts in the local context. -/
def rgnScan (g : MVarId) : TacticM (Array Syntax.Term × Array RgnHyp) :=
  g.withContext do
    let mut oks : Array Syntax.Term := #[]
    let mut rgns : Array RgnHyp := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      let fn := ty.getAppFn
      if fn.isConstOf ``Rgn then rgns := rgns.push ⟨d.userName, ty.appFn!.appArg!, ty.appArg!, false⟩
      else if fn.isConstOf ``ARgn then
        rgns := rgns.push ⟨d.userName, ty.appFn!.appArg!, ty.appArg!, true⟩
      else if let .const n _ := fn then
        if n == ``WOK then oks := oks.push (mkIdent d.userName)
        else if (← getEnv).contains (n ++ `toWOK) then
          oks := oks.push (← `(($(mkIdent d.userName)).toWOK))
    return (oks, rgns)

/-- The first-order atoms (local constants other than register files) of `e`,
after replacing each `x.toNat` by the right side of a context equation
`x.toNat = rhs`. -/
def rgnAtoms (g : MVarId) (e : Expr) : MetaM (Array FVarId) := g.withContext do
  let mut eqs : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      if l.isAppOfArity ``BitVec.toNat 2 then eqs := eqs.push (l, r)
  let e' := e.replace fun t => eqs.findSome? fun (l, r) => if l == t then some r else none
  let mut out : Array FVarId := #[]
  for f in (collectFVars {} e').fvarIds do
    let fty ← whnfR (← f.getType)
    unless fty.isForall do out := out.push f
  return out

/-- Key an access (V5): replace the address term `a` in the goal of `g` by a bound
key `A` with `a = A`, through `key_gen`. -/
def rgnKey (g : MVarId) (a : Expr) : MetaM MVarId := g.withContext do
  let nat := mkConst ``Nat
  let abst ← kabstract (← instantiateMVars (← g.getType)) a
  let ty := mkForall `A .default nat
    (mkForall `hA .default (mkApp3 (mkConst ``Eq [levelOne]) nat a (mkBVar 0))
      (abst.liftLooseBVars 0 1))
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  g.assign (mkApp3 (mkConst ``key_gen) a (mkLambda `A .default nat abst) m)
  return m.mvarId!

/-- Normalise a freshly introduced key equation `hA : a = A` (register updates, register
additions, literal offsets) without removing wrap-around: the key route removes it from the
bound the chosen region gives. -/
macro "rgn_key_simp" : tactic =>
  `(tactic| (intro A hA
             (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false,
               LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
               BitVec.reduceAppend, BitVec.reduceSignExtend, VsaIris.VsaHeap.key_toNat_add,
               VsaIris.VsaHeap.key_toNat_ofNat, BitVec.reduceToNat,
               Nat.reducePow, Nat.reduceMod] at hA)))

def natRefl (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit n)
def trueRefl : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
def isZeroLit (e : Expr) : Bool := e.nat? == some 0

/-- The context facts the key route reads syntactically: atom rewrites `x.toNat = r`,
literal floors `L ≤ s` and alignments `t % m = 0`. -/
structure KeyFacts where
  eqs : Array (Expr × Expr × Expr) := #[]
  floors : Array (Expr × Nat × Expr) := #[]
  aligns : Array (Expr × Nat × Expr) := #[]

def keyFacts : MetaM KeyFacts := do
  let mut kf : KeyFacts := {}
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (α, l, r) := ty.eq? then
      if l.isAppOfArity ``BitVec.toNat 2 ||
          (α.isConstOf ``Nat && l.isApp && l.nat?.isNone && r.isAppOfArity ``HAdd.hAdd 6 &&
            r.appArg!.nat?.isSome) then
        kf := { kf with eqs := kf.eqs.push (l, r, d.toExpr) }
      else if l.isAppOfArity ``HMod.hMod 6 && isZeroLit r then
        if let some m := l.appArg!.nat? then
          kf := { kf with aligns := kf.aligns.push (l.appFn!.appArg!, m, d.toExpr) }
    else if ty.isAppOfArity ``LE.le 4 then
      if let some n := ty.appFn!.appArg!.nat? then
        kf := { kf with floors := kf.floors.push (ty.appArg!, n, d.toExpr) }
  return kf

/-- `e = t + c` with `t` an atom (or the literal `0`) and `c` a literal, atoms rewritten by
the context's `x.toNat = r` facts. A wrap-around `y % 2^64` (when `mods`) is transparent; with
`bnd = some (t, c, hlt)` its removal is proved from `hlt : t + c < 2^64` (pass 2), without it the
proof is a placeholder (pass 1, which only computes the form). -/
partial def linNF (kf : KeyFacts) (fuel : Nat) (bnd : Option (Expr × Nat × Expr)) (mods : Bool)
    (e : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  if let some n := e.nat? then return some (mkNatLit 0, n, mkApp (mkConst ``lin_lit) e)
  if e.isAppOfArity ``HAdd.hAdd 6 && (e.getArg! 0).isConstOf ``Nat then
    let x := e.getArg! 4; let y := e.getArg! 5
    let some (tx, cx, px) ← linNF kf fuel bnd mods x | return none
    let some (ty, cy, py) ← linNF kf fuel bnd mods y | return none
    let args (t : Expr) (p q : Expr) :=
      #[x, y, t, mkNatLit cx, mkNatLit cy, mkNatLit (cx + cy), p, q, natRefl (cx + cy)]
    if isZeroLit ty then return some (tx, cx + cy, mkAppN (mkConst ``lin_addL) (args tx px py))
    if isZeroLit tx then return some (ty, cx + cy, mkAppN (mkConst ``lin_addR) (args ty px py))
    return some (e, 0, mkApp (mkConst ``lin_atom) e)
  if mods && e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat &&
      e.appArg!.nat? == some 18446744073709551616 then
    let y := e.appFn!.appArg!
    let some (ty, cy, py) ← linNF kf fuel bnd mods y | return none
    match bnd with
    | none => return some (ty, cy, mkConst ``True)
    | some (t, c, hlt) =>
      if isZeroLit ty then
        unless cy < 18446744073709551616 do return none
        return some (ty, cy, mkAppN (mkConst ``lin_mod0) #[y, mkNatLit cy, e.appArg!, py, trueRefl])
      unless ty == t && cy ≤ c do return none
      return some (ty, cy,
        mkAppN (mkConst ``lin_mod) #[y, t, mkNatLit cy, mkNatLit c, e.appArg!, py, hlt, trueRefl])
  if fuel > 0 then
    if let some (_, r, h) := kf.eqs.find? (·.1 == e) then
      let some (t, c, p) ← linNF kf (fuel - 1) bnd mods r | return none
      return some (t, c, mkAppN (mkConst ``lin_trans) #[e, r, t, mkNatLit c, h, p])
  return some (e, 0, mkApp (mkConst ``lin_atom) e)

inductive KeyKind | ld | st | acc (oks : Array Syntax.Term) | win (s : Expr)

/-- The key route (no candidate trying): key the access, normalise the key to `t + c`, pick a
region whose base normalises to `t + c0` and whose literal check holds, and close the goal
by that region's key law (a closed boolean check on literals). `none` (state restored) when
no key form applies. -/
def rgnKeyed (g : MVarId) (a : Expr) (rgns : Array RgnHyp) (kind : KeyKind) :
    TacticM (Option Name) := do
  let s0 ← saveState
  let [g'] ← evalTacticAt (← `(tactic| rgn_key_simp)) (← rgnKey g a) | s0.restore; return none
  let r? ← tryCatchRuntimeEx (g'.withContext do
    let some hAd := (← getLCtx).lastDecl | return none
    let some (_, lhs, Ae) := (← instantiateMVars hAd.type).eq? | return none
    let kf ← keyFacts
    let some (t, c, _) ← linNF kf 3 none true lhs | return none
    let tgt ← instantiateMVars (← g'.getType)
    let wE? : Option Expr := match kind with
      | .win _ => match tgt with
        | .forallE _ _ (.forallE _ _ (.forallE _ lt _ _) _) _ => some lt.appArg!.appArg!
        | _ => none
      | _ => (tgt.find? fun e => e.isAppOfArity ``accAddrs 2 || e.isAppOfArity ``LdOK 2 ||
          e.isAppOfArity ``StOK 2).map (·.appArg!)
    let some w := wE?.bind (·.nat?) | return none
    for r in rgns do
      if (kind matches .win _) && r.acc then continue
      let some (tb, c0, hb) ← linNF kf 3 none false r.base | continue
      unless tb == t do continue
      let some (L, he) ← (do
          if let some L := r.ext.nat? then return some (L, mkApp (mkConst ``ext_lit) r.ext)
          let some (s, k, pe) ← linNF kf 3 none false r.ext | return none
          let some (_, L0, hs) := kf.floors.find? (·.1 == s) | return none
          return some (L0 + k, mkAppN (mkConst ``ext_le)
            #[r.ext, s, mkNatLit k, mkNatLit L0, mkNatLit (L0 + k), pe, hs, natRefl (L0 + k)]) :
          MetaM (Option (Nat × Expr)))
        | continue
      unless c0 ≤ c && c + w ≤ c0 + L && 0 < w do continue
      let rv := mkFVar (← getLocalDeclFromUserName r.name).fvarId
      let pre := if r.acc then ``ARgn else ``Rgn
      let hlt ← mkAppM (pre ++ `lt_k) #[rv, hb, he, mkNatLit c, mkNatLit w, trueRefl]
      let some (_, _, px) ← linNF kf 3 (some (t, c, hlt)) true lhs | continue
      let hA := mkAppN (mkConst ``lin_key) #[lhs, t, mkNatLit c, Ae, px, hAd.toExpr]
      let pf? : Option Expr ← match kind with
        | .ld => some <$> mkAppM (pre ++ `ldOK_k) #[rv, hb, he, hA, mkNatLit w, trueRefl]
        | .st => do
          let al? : Option (Nat × Expr) :=
            if w == 1 then some (1, mkApp (mkConst ``Nat.mod_one) t)
            else if isZeroLit t then some (w, mkApp (mkConst ``Nat.zero_mod) (mkNatLit w))
            else (kf.aligns.find? fun (x, m, _) => x == t && m % w == 0).map fun (_, m, h) => (m, h)
          let some (m, hal) := al? | pure none
          if m % w != 0 || c % w != 0 then pure none else
          some <$> mkAppM (pre ++ `stOK_k) #[rv, hb, he, hA, mkNatLit w, trueRefl, hal, trueRefl]
        | .acc oks =>
          if r.acc then some <$> mkAppM ``ARgn.acc_k #[rv, hb, he, hA, mkNatLit w, trueRefl] else do
            let mut res := none
            for o in oks do
              let some oe ← (try some <$> Term.withoutErrToSorry (Tactic.elabTerm o none)
                catch _ => pure none) | continue
              if let some p ← (try some <$> mkAppM ``WOK.rgn_k #[oe, rv, hb, he, hA, mkNatLit w,
                  trueRefl] catch _ => pure none) then
                res := some p; break
            pure res
        | .win s => some <$> mkAppOptM ``Rgn.win_k #[none, none, none, none, none, none, none, none, s,
            rv, hb, he, hA, mkNatLit w, trueRefl]
      let some pf := pf? | continue
      if ← isDefEq (← inferType pf) tgt then
        g'.assign pf
        return some r.name
    return none) (fun _ => pure none)
  if r?.isNone then s0.restore
  return r?

/-- Key the access `a` of goal `g`, rank the regions (the hinted one first, then
by atoms shared with the key, symbolic extents before literal ones), and try each
region's candidate tactics. Returns the region that closed the goal. -/
def rgnTry (g : MVarId) (a : Expr) (rgns : Array RgnHyp) (hint : Option Name)
    (mk : RgnHyp → TacticM (Array (TSyntax `tactic))) (extra : Array (TSyntax `tactic)) :
    TacticM (Option Name) := do
  let ka ← rgnAtoms g a
  let mut scored : Array (Int × RgnHyp) := #[]
  for r in rgns do
    let kb ← rgnAtoms g r.base
    let shared := (kb.filter ka.contains).size
    let sc : Int := (4 * shared : Int) - (2 * (kb.size - shared) : Nat) +
      (if r.ext.nat?.isNone then 1 else 0) + (if hint == some r.name then 1000 else 0)
    scored := scored.push (sc, r)
  let ranked := scored.qsort (fun x y => x.1 > y.1)
  let mut cands : Array (Name × TSyntax `tactic) := extra.map (Name.anonymous, ·)
  for (_, r) in ranked do
    for t in ← mk r do cands := cands.push (r.name, t)
  let s0 ← saveState
  let [g'] ← evalTacticAt (← `(tactic| rgn_key_norm)) (← rgnKey g a) | s0.restore; return none
  for (r, t) in cands do
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do pure (← evalTacticAt t g').isEmpty) (fun _ => pure false)
    if ok then return some r
    s.restore
  s0.restore
  return none

/-- Close an access goal of `g` (`∀ x ∈ accAddrs a w, C.S x`, `LdOK` or `StOK`) from
a region in context. -/
def rgnSide (g : MVarId) (hint : Option Name) : TacticM (Option Name) := do
  let (oks, rgns) ← rgnScan g
  if rgns.isEmpty then return none
  let tgt ← instantiateMVars (← g.getType)
  let some app := tgt.find? fun e =>
      e.isAppOfArity ``accAddrs 2 || e.isAppOfArity ``LdOK 2 || e.isAppOfArity ``StOK 2
    | return none
  let mk : RgnHyp → TacticM (Array (TSyntax `tactic)) := fun h => do
    let r := mkIdent h.name
    if app.isAppOf ``LdOK then
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.ldOK $r ?_; omega_dc))]
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.ldOK $r ?_; omega_dc))]
    else if app.isAppOf ``StOK then
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.stOK $r ?_; omega_dc))]
      return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.stOK $r ?_; omega_dc))]
    else
      if h.acc then return #[← `(tactic| (refine VsaIris.VsaHeap.ARgn.acc $r ?_; omega_dc))]
      oks.mapM fun o => `(tactic| (refine VsaIris.VsaHeap.WOK.rgn $o $r ?_; omega_dc))
  let kind : KeyKind :=
    if app.isAppOf ``LdOK then .ld else if app.isAppOf ``StOK then .st else .acc oks
  if let some r ← rgnKeyed g app.appFn!.appArg! rgns kind then return some r
  rgnTry g app.appFn!.appArg! rgns hint mk #[]

/-- Close an ownership (`∀ x ∈ accAddrs a w, C.S x`), `LdOK` or `StOK` goal
from any region in context. -/
elab "rgn_side" : tactic => do
  let g ← getMainGoal
  match ← rgnSide g none with
  | some _ => setGoals []
  | none => throwError "rgn_side: no region closes the goal"

macro_rules | `(tactic| sx_side) => `(tactic| rgn_side)

/-- Step the `st` family from `cur`, closing each access obligation with
`rgnSide` and leaving the context untouched; after each step the register reads in
the goal are resolved, so values stay terms over the entry registers. Stops at a listed pc, at a branch,
or when no step lemma applies; obligations no region closes are returned as
pending goals. -/
def rgnStep (h : Syntax) (stopPCs : List Nat) : TacticM (List MVarId × List MVarId) := do
  let mut cur ← getMainGoal
  let mut pending : List MVarId := []
  repeat
    let some pc ← cur.withContext (do VsaIris.Sym.swpPC? (← cur.getType)) | break
    if stopPCs.contains pc then break
    let some gs ← VsaIris.Sym.sxStep h cur | break
    let mut conts : List MVarId := []
    let mut hint : Option Name := none
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => VsaIris.Sym.isSWP b) then
        conts := conts ++ [g]
      else
        match ← rgnSide g hint with
        | some r => hint := some r
        | none =>
          -- a control-transfer side condition (link-register alignment): literal arithmetic
          let s ← saveState
          try
            let gs' ← evalTacticAt (← `(tactic| (simp only [VsaIris.Sym.upd_apply, VsaIris.ra,
              Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd, BitVec.reduceOfNat,
              BitVec.reduceToNat, Nat.reduceMod])) ) g
            unless gs'.isEmpty do s.restore; pending := pending ++ [g]
          catch _ => s.restore; pending := pending ++ [g]
    match conts with
    | [c] =>
      -- keep the register file normal: every value is a term over the entry registers, and
      -- the pc after a call or return is a literal
      match ← evalTacticAt (← `(tactic| try simp only [VsaIris.Sym.upd_apply, VsaIris.ra,
          Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd, BitVec.reduceOfNat])) c with
      | [c'] => cur := c'
      | cs => return (pending, cs)
    | cs => return (pending, cs)
  return (pending, [cur])

/-- `rgn_run h at pc…`: step to a listed pc, then normalise the final goal with
`rgn_norm`. -/
elab "rgn_run " h:term " at " stops:num+ : tactic => do
  let rest := (← getGoals).tail
  let (pending, conts) ← rgnStep h (stops.toList.map (·.getNat))
  match conts with
  | [c] => setGoals (pending ++ (← evalTacticAt (← `(tactic| try rgn_norm)) c) ++ rest)
  | cs => setGoals (pending ++ cs ++ rest)

/-- `rgn_step h at pc…`: as `rgn_run`, leaving the final goal as the step lemmas
produce it (for paths with their own memory normal form). -/
elab "rgn_step " h:term " at " stops:num+ : tactic => do
  let rest := (← getGoals).tail
  let (pending, conts) ← rgnStep h (stops.toList.map (·.getNat))
  setGoals (pending ++ conts ++ rest)

/-- Close one `LogIn (MWin H s)` key `∀ b, a ≤ b → b < a + w → MWin H s b`: from a
region in context, or the stack window. -/
elab "rgn_win" : tactic => do
  let g ← getMainGoal
  let (_, rgns) ← rgnScan g
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ _ body _ := tgt | throwError "rgn_win: not a key goal"
  let .forallE _ le _ _ := body | throwError "rgn_win: not a key goal"
  let a := le.appFn!.appArg!
  if a.hasLooseBVars then throwError "rgn_win: not a key goal"
  let stack ← `(tactic| (refine VsaIris.VsaHeap.win_stack' ?_; omega_dc))
  let mk : RgnHyp → TacticM (Array (TSyntax `tactic)) := fun h => do
    if h.acc then return #[]
    return #[← `(tactic| (refine VsaIris.VsaHeap.Rgn.win $(mkIdent h.name) ?_; omega_dc))]
  -- a key over the context's stack pointer is tried against the stack window first; any
  -- other key against the regions first (a failing stack check is a wasted `omega`)
  let onStack := (a.find? (·.isConstOf ``MCtx.s)).isSome
  let rest := (← getGoals).tail
  let r ← if onStack then rgnTry g a rgns none mk #[stack] else do
    let k ← match (tgt.find? (·.isAppOfArity ``MWin 3)).map (·.getArg! 1) with
      | some s => rgnKeyed g a rgns (.win s)
      | none => pure none
    if k.isSome then pure k else
    match ← rgnTry g a rgns none mk #[] with
    | some r => pure (some r)
    | none => rgnTry g a #[] none mk #[stack]
  match r with
  | some _ => setGoals rest
  | none => throwError "rgn_win: no region contains the key"

syntax openFieldsSel := " [" ident,* "]"

/-- `open_fields h [f₁, …]` adds only the listed fields (a short proof should not pay for
unused geometry in every arithmetic query). `open_fields h` adds every field of the named-field structure `h` as a
hypothesis `h_<field>` (projections of constructor terms reduced), so the
arithmetic deciders see a minted region's geometry. -/
elab "open_fields " h:ident sel:(openFieldsSel)? : tactic => do
  let only : Option (Array Name) := sel.map fun s =>
    match s with
    | `(openFieldsSel| [$ids,*]) => ids.getElems.map (·.getId)
    | _ => #[]
  let g ← getMainGoal
  let n ← g.withContext do
    let d ← getLocalDeclFromUserName h.getId
    let ty ← whnfR (← instantiateMVars d.type)
    let .const n _ := ty.getAppFn | throwError "open_fields: not a structure"
    pure n
  let some info := getStructureInfo? (← getEnv) n | throwError "open_fields: not a structure"
  for f in info.fieldNames do
    if let some fs := only then unless fs.contains f do continue
    let nm := mkIdent (Name.mkSimple s!"{h.getId}_{f}")
    let pj := mkIdent (h.getId ++ f)
    evalTactic (← `(tactic| have $nm := $pj:ident))
    evalTactic (← `(tactic| try simp only at $nm:ident))

/-- Discharge `LogIn (MWin H s) L` for an explicit key list. -/
macro "log_in" : tactic =>
  `(tactic| (simp only [VsaIris.VsaHeap.LogIn, and_true]; repeat' apply And.intro) <;> rgn_win)

end VsaIris.VsaHeap
