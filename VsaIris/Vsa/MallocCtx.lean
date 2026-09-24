import VsaIris.Vsa.MallocGen

/-!
# The context of a `_malloc_r` run

Every join lemma of `_malloc_r` (`MallocPaths.lean`) is stated over one call
context `MCtx` and its obligations `MOK`:

* the owned bytes `S` contain the run's write window `MWin` (the allocator's
  footprint and `mHead` bytes of stack below the caller's `sp`);
* `ok` continues from a return with a fresh block (`MRet`), `null` from a
  NULL return (`MNull`), which records why the heap could not serve the
  request (`starved`).

The same lemmas serve the top-level runs in both regimes (the counted one
refutes `null` from its credits) and `_realloc_r`'s nested call, whose owned
bytes and continuation differ. `MFrame` and `MHeap` are the run's invariant
between joins: the saved registers in the frame, the heap in shape, and the
memory outside the write window at its entry value.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Stack bytes below the caller's `sp` that a `_malloc_r` run uses: its
96-byte frame and those of its callees (`_sbrk_r`, `_sbrk`, and `_free_r`
from `malloc_extend_top`). -/
def mHead : Nat := 256

/-- The caller's `sp` for a `_malloc_r` call. -/
structure MSp (s : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + mHead ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

theorem MSp.of_spOKA {s : BitVec 64} (h : SpOKA s) : MSp s where
  lo := by
    have := h.lo
    simp only [allocHeadroom, mHead, Vsa.Sim.tohostAddr] at *
    omega
  hi := h.hi
  align := h.align

/-- The bytes a `_malloc_r` run may write. -/
def MWin (H : List (Nat × Nat)) (s : BitVec 64) (a : Nat) : Prop :=
  vsaFoot H a ∨ (s.toNat - mHead ≤ a ∧ a < s.toNat)

/-- The context of a `_malloc_r` call: the code, the owned bytes and the
final postcondition of the enclosing run, the request, the caller's return
address and `sp`, the entry registers and tracking memory, and the entry top. -/
structure MCtx where
  live : Nat → Prop
  S : Nat → Prop
  Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop
  H : List (Nat × Nat)
  n : BitVec 64
  r : BitVec 64
  s : BitVec 64
  rv0 : Nat → BitVec 64
  Mt0 : Mem
  top0 : Nat

/-- The caller's registers at the return. -/
structure MRegs (C : MCtx) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = C.r
  sp : R 2 = C.s
  s0 : R 8 = C.rv0 8
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

/-- A return with a fresh block: the heap extended by it, the top grown by at
most the block's chunk, the footprint present, and every byte outside the
write window at its entry value. -/
structure MRet (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  regs : MRegs C R
  fresh : FreshAt C.H (R 10).toNat C.n.toNat
  align : (R 10).toNat % 16 = 0
  heap : ∃ top brkv chunks bins,
    PHeapAt Mt (((R 10).toNat, C.n.toNat) :: C.H) top brkv chunks bins ∧
      top ≤ C.top0 + physSize C.n.toNat
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- **Starvation**: the arena above the entry top cannot hold twice the
request's chunk with a page to spare. `malloc_extend_top` asks `sbrk` for the
chunk plus `MINSIZE`, rounded up to a page, on top of a top chunk that may
already hold up to the chunk plus `MINSIZE`, so a failed `sbrk` bounds the
arena by this much. The counted regime's credits refute it (`mOK_chg`). -/
def Starved (top0 n : Nat) : Prop := heapEnd + 4096 < top0 + 2 * physSize n + extendSlack

/-- A request whose chunk alone overruns the arena starves. -/
theorem Starved.of_lt {top0 n : Nat} (h : heapEnd < top0 + physSize n) : Starved top0 n :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right h 4096) (by
    generalize physSize n = P
    unfold extendSlack; omega)

/-- A NULL return: the heap in shape at the same live blocks, and the reason,
the arena cannot hold the request (`Starved`). -/
structure MNull (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  regs : MRegs C R
  a0 : R 10 = 0
  heap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?
  starved : Starved C.top0 C.n.toNat

/-- The obligations every allocator call context shares: the code is live,
the caller's `sp` has room, the write window is owned, and the return
address is word-aligned. -/
structure WOK (C : MCtx) : Prop where
  live : AllocLive C.live
  sp : MSp C.s
  own : ∀ a, MWin C.H C.s a → C.S a
  ral : C.r.toNat % 4 = 0

/-- The obligations of a `_malloc_r` call context. -/
structure MOK (C : MCtx) : Prop extends WOK C where
  ok : ∀ R Mt, MRet C R Mt → AW C.live C.S C.Q C.r R Mt
  null : ∀ R Mt, MNull C R Mt → AW C.live C.S C.Q C.r R Mt

/-- The run's stack frame between joins: `sp` 96 bytes below the caller's,
`s0` and `ra` in their slots, `s1-s3` untouched. -/
structure MFrame (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  sp : R 2 = C.s + 18446744073709551520#64
  s0 : read64 Mt (C.s.toNat - 96 + 80) = some (C.rv0 8).toNat
  ra : read64 Mt (C.s.toNat - 96 + 88) = some C.r.toNat
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

/-- The heap between joins, at the entry top: in shape on the tracking
memory, its footprint present, off the stack, and every byte outside the
write window at its entry value. -/
structure MHeap (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mt C.H C.top0 brkv chunks bins
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-! ## Ownership -/

/-- Stack bytes of the window are owned. -/
theorem WOK.stack {C : MCtx} (O : WOK C) {a w : Nat} (h1 : C.s.toNat - mHead ≤ a)
    (h2 : a + w ≤ C.s.toNat) : ∀ b ∈ accAddrs a w, C.S b := by
  intro b hb
  have := of_mem_accAddrs hb
  exact O.own b (.inr ⟨by omega, by omega⟩)

/-- Footprint bytes are owned. -/
theorem WOK.foot {C : MCtx} (O : WOK C) {a w : Nat} (h : ∀ k, k < w → vsaFoot C.H (a + k)) :
    ∀ b ∈ accAddrs a w, C.S b := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact O.own _ (.inl (h j (List.mem_range.mp hj)))

/-- An owned footprint doubleword at an address equal to `a'`. -/
theorem WOK.foot_at {C : MCtx} (O : WOK C) {a' : Nat} (h : ∀ k, k < 8 → vsaFoot C.H (a' + k)) :
    ∀ a, a = a' → ∀ b ∈ accAddrs a 8, C.S b := by
  intro a he; subst he; exact O.foot h

/-- An allocator-global doubleword is owned. -/
theorem WOK.glob {C : MCtx} (O : WOK C) {a : Nat} (h1 : 0x8001ad10 ≤ a) (h2 : a + 8 ≤ 0x8001b520) :
    ∀ b ∈ accAddrs a 8, C.S b :=
  O.foot fun k hk => .inl (.inl ⟨by omega, by omega⟩)

/-- The bin headers' link words are owned. -/
theorem WOK.bin_link {C : MCtx} (O : WOK C) {j a : Nat} (hj : j < numBins)
    (ha : a = binAt j + 16 ∨ a = binAt j + 24) : ∀ b ∈ accAddrs a 8, C.S b := by
  have := binAt_geo j hj
  rcases ha with rfl | rfl <;> exact O.glob (by omega) (by omega)

theorem MOK.stack {C : MCtx} (O : MOK C) {a w : Nat} (h1 : C.s.toNat - mHead ≤ a)
    (h2 : a + w ≤ C.s.toNat) : ∀ b ∈ accAddrs a w, C.S b := O.toWOK.stack h1 h2

theorem MOK.foot {C : MCtx} (O : MOK C) {a w : Nat} (h : ∀ k, k < w → vsaFoot C.H (a + k)) :
    ∀ b ∈ accAddrs a w, C.S b := O.toWOK.foot h

/-- Frame bytes are owned: the `sx_side` rule for stack accesses. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.MOK.stack ‹VsaIris.VsaHeap.MOK _› ?_ ?_ <;> ((try unfold VsaIris.VsaHeap.mHead) ; sx_addr)))

/-- Allocator globals are owned: the `sx_side` rule for accesses at a literal
global address. -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.MOK.foot ‹VsaIris.VsaHeap.MOK _› (fun k hk => Or.inl ?_); unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange; omega))

/-! ## Stack arithmetic -/

theorem MSp.sp96 {s : BitVec 64} (h : MSp s) (d : Nat) (hd : d ≤ 96) :
    (s + 18446744073709551520#64 + BitVec.ofNat 64 d).toNat = s.toNat - 96 + d := by
  have := h.lo; have := h.hi
  unfold mHead Vsa.Sim.tohostAddr at *
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- A footprint doubleword lies wholly below or above the stack window. -/
theorem MHeap.off_stack {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : MHeap C Mt brkv chunks bins) {a : Nat}
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) :
    a + 8 ≤ C.s.toNat - mHead ∨ C.s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hk : (if a ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - a) < 8 := by
    split <;> omega
  exact Hp.disj _ (by split <;> omega) (by unfold mHead at *; split <;> omega) (hf _ hk)

/-- The stack window misses the `_errno` word and the run of allocator
globals from `__malloc_sbrk_base` to `__malloc_current_mallinfo`: every gap
between them is narrower than the window. -/
theorem MHeap.glob_off {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : MHeap C Mt brkv chunks bins) :
    (C.s.toNat ≤ 0x8001b538 ∨ 0x8001b53c + mHead ≤ C.s.toNat) ∧
      (C.s.toNat ≤ 0x8001b960 ∨ 0x8001ba68 + mHead ≤ C.s.toNat) := by
  have g : ∀ a, allocGlobal a → ¬ (C.s.toNat - mHead ≤ a ∧ a < C.s.toNat) :=
    fun a ha hw => Hp.disj a hw.1 hw.2 (.inl ha)
  have h1 := g 0x8001b538 (by unfold allocGlobal InRange; omega)
  have h2 := g 0x8001b53b (by unfold allocGlobal InRange; omega)
  have h3 := g 0x8001b960 (by unfold allocGlobal InRange; omega)
  have h4 := g 0x8001b990 (by unfold allocGlobal InRange; omega)
  have h5 := g 0x8001ba08 (by unfold allocGlobal InRange; omega)
  have h6 := g 0x8001ba18 (by unfold allocGlobal InRange; omega)
  have h7 := g 0x8001ba67 (by unfold allocGlobal InRange; omega)
  unfold mHead at *
  omega

/-- A footprint range of positive width lies wholly below or above the stack window. -/
theorem MHeap.off_stack_w {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : MHeap C Mt brkv chunks bins) {a w : Nat} (hw : 0 < w)
    (hf : ∀ k, k < w → vsaFoot C.H (a + k)) :
    a + w ≤ C.s.toNat - mHead ∨ C.s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hm : 0 < mHead := by unfold mHead; omega
  by_cases h : C.s.toNat - mHead ≤ a
  · have := hf 0 hw
    rw [Nat.add_zero] at this
    exact Hp.disj a h (by omega) this
  · have := hf (C.s.toNat - mHead - a) (by omega)
    rw [show a + (C.s.toNat - mHead - a) = C.s.toNat - mHead by omega] at this
    exact Hp.disj _ (Nat.le_refl _) (by omega) this

/-! ## The write window through stores -/

/-- A store inside the write window keeps the memory outside it. -/
theorem frame_store {C : MCtx} {Mt : Mem} {a w : Nat} {v : BitVec 64}
    (hw : ∀ b, a ≤ b → b < a + w → MWin C.H C.s b)
    (hf : ∀ b, ¬ MWin C.H C.s b → Mt[b]? = C.Mt0[b]?) :
    ∀ b, ¬ MWin C.H C.s b → (writeLog Mt [(a, w, v)])[b]? = C.Mt0[b]? := by
  intro b hb
  have ho : OutL [(a, w, v)] b := ⟨Classical.byContradiction fun hc => hb (hw b (by simp only at hc; omega)
    (by simp only at hc; omega)), trivial⟩
  rw [writeLog_out _ _ _ ho, hf b hb]

/-- A footprint doubleword is in the write window. -/
theorem win_foot {H : List (Nat × Nat)} {s : BitVec 64} {a : Nat}
    (hf : ∀ k, k < 8 → vsaFoot H (a + k)) : ∀ b, a ≤ b → b < a + 8 → MWin H s b := by
  intro b h1 h2
  have := hf (b - a) (by omega)
  rw [show a + (b - a) = b by omega] at this
  exact .inl this

/-- Stack bytes of the window are in the write window. -/
theorem win_stack {H : List (Nat × Nat)} {s : BitVec 64} {a w : Nat} (h1 : s.toNat - mHead ≤ a)
    (h2 : a + w ≤ s.toNat) : ∀ b, a ≤ b → b < a + w → MWin H s b :=
  fun _ hb1 hb2 => .inr ⟨by omega, by omega⟩

/-- A store keeps the footprint present. -/
theorem pres_store {C : MCtx} {Mt : Mem} {a w : Nat} {v : BitVec 64}
    (hp : ∀ b, vsaFoot C.H b → (Mt[b]?).isSome) :
    ∀ b, vsaFoot C.H b → ((writeLog Mt [(a, w, v)])[b]?).isSome :=
  fun b hb => writeLog_present _ _ _ (hp b hb)

/-- `PHeapAt` through memories that agree on the bytes it reads. -/
theorem PHeapAt.transport_read {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins)
    (hag : AgreeP (vsaRead H) m m') : PHeapAt m' H top brkv chunks bins :=
  ⟨h.heap.transport_read hag, h.brk_page, fun bb hbb => h.bb_lt bb (by
    rw [read64_agreeP hag fun k hk => ?_]; exact hbb
    refine ⟨.inl (.inl ⟨?_, ?_⟩), ?_, ?_⟩ <;> simp only [InRange, binblocksAddr, avAddr] <;> omega)⟩

/-- The heap invariant through a store to the run's stack. -/
theorem MHeap.store_stack {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : MHeap C Mt brkv chunks bins) {a w : Nat} {v : BitVec 64}
    (h1 : C.s.toNat - mHead ≤ a) (h2 : a + w ≤ C.s.toNat) :
    MHeap C (writeLog Mt [(a, w, v)]) brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have hd := Hp.disj x
    have ho : OutL [(a, w, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd (by omega) (by omega) hx.1, trivial⟩
    rw [writeLog_out _ _ _ ho]
  pres := pres_store Hp.pres
  disj := Hp.disj
  frame := frame_store (win_stack h1 h2) Hp.frame

/-- The heap invariant through a store to `_errno`, which `HeapAt` never reads. -/
theorem MHeap.store_errno {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : MHeap C Mt brkv chunks bins) {v : BitVec 64} :
    MHeap C (writeLog Mt [(0x8001b538, 4, v)]) brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have ho : OutL [(0x8001b538, 4, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hx.2.1 ⟨by omega, by omega⟩, trivial⟩
    rw [writeLog_out _ _ _ ho]
  pres := pres_store Hp.pres
  disj := Hp.disj
  frame := frame_store (fun b h1 h2 => .inl (.inl (.inr (.inl ⟨h1, h2⟩)))) Hp.frame

/-- The frame through a register write other than `sp` and `s1-s3`. -/
theorem MFrame.upd {C : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (F : MFrame C R Mt) {k : Nat}
    {v : BitVec 64} (hk : k ≠ 2 ∧ k ≠ 9 ∧ k ≠ 18 ∧ k ≠ 19) : MFrame C (VsaIris.Sym.upd R k v) Mt where
  sp := by rw [upd_other _ _ (Ne.symm hk.1)]; exact F.sp
  s0 := F.s0
  ra := F.ra
  s1 := by rw [upd_other _ _ (Ne.symm hk.2.1)]; exact F.s1
  s2 := by rw [upd_other _ _ (Ne.symm hk.2.2.1)]; exact F.s2
  s3 := by rw [upd_other _ _ (Ne.symm hk.2.2.2)]; exact F.s3

/-- The frame depends only on `sp` and `s1`-`s3`: a register file that agrees
with `R` on them has the same frame. -/
theorem MFrame.of_regs {C : MCtx} {R R' : Nat → BitVec 64} {Mt : Mem} (F : MFrame C R Mt)
    (h2 : R' 2 = R 2) (h9 : R' 9 = R 9) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) :
    MFrame C R' Mt :=
  ⟨h2.trans F.sp, F.s0, F.ra, h9.trans F.s1, h18.trans F.s2, h19.trans F.s3⟩

/-- The frame through a store that misses the saved `s0` and `ra`. -/
theorem MFrame.store {C : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (F : MFrame C R Mt)
    {a w : Nat} {v : BitVec 64} (h : a + w ≤ C.s.toNat - 96 + 80 ∨ C.s.toNat - 96 + 96 ≤ a) :
    MFrame C R (writeLog Mt [(a, w, v)]) where
  sp := F.sp
  s0 := by rw [read64_store_miss _ _ (by omega)]; exact F.s0
  ra := by rw [read64_store_miss _ _ (by omega)]; exact F.ra
  s1 := F.s1
  s2 := F.s2
  s3 := F.s3

/-! ## The epilogue -/

/-- **The epilogue** `ld ra,88(sp); ld s0,80(sp); addi sp,sp,96; ret` at any
of its copies (the four step lemmas as arguments): the caller's registers
restored, every other register kept. -/
theorem epi_core {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {pc1 pc2 pc3 pc4 : BitVec 64}
    (st1 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x058#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc2
        (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x058#12)).toNat)) Mt →
      AW C.live C.S C.Q pc1 R Mt)
    (st2 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x050#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc3
        (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x050#12)).toNat)) Mt →
      AW C.live C.S C.Q pc2 R Mt)
    (st3 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      AW C.live C.S C.Q pc4
        (upd R 2 ((R 2) + sign_extend (m := 64) (0x060#12))) Mt →
      AW C.live C.S C.Q pc3 R Mt)
    (st4 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, (R 1).toNat % 4 = 0 →
      AW C.live C.S C.Q (R 1) R Mt →
      AW C.live C.S C.Q pc4 R Mt)
    (F : MFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q pc1 R Mt := by
  have hsp := O.sp
  have hlo := hsp.lo; have hhi := hsp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  refine st1 (by rw [hs2]; sx_addr) (O.stack (by rw [hs2]; unfold mHead; sx_addr)
    (by rw [hs2]; sx_addr)) ?_
  refine st2 (by rw [upd_other _ _ (by decide), hs2]; sx_addr)
    (O.stack (by rw [upd_other _ _ (by decide), hs2]; unfold mHead; sx_addr)
      (by rw [upd_other _ _ (by decide), hs2]; sx_addr)) ?_
  refine st3 ?_
  have hr : ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat = C.r :=
    ldv_ld (by rw [show (R 2 + sign_extend (m := 64) (0x058#12)).toNat = C.s.toNat - 96 + 88 by
      rw [hs2]; sx_addr]; exact F.ra)
  have hs0 : ldv .ld Mt ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
      sign_extend (m := 64) (0x050#12)).toNat = C.rv0 8 :=
    ldv_ld (by rw [upd_other _ _ (by decide), show (R 2 + sign_extend (m := 64) (0x050#12)).toNat =
      C.s.toNat - 96 + 80 by rw [hs2]; sx_addr]; exact F.s0)
  refine st4 (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hr]; exact O.ral) ?_
  have hpc : (upd (upd (upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 8
      (ldv .ld Mt ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
        sign_extend (m := 64) (0x050#12)).toNat)) 2
      ((upd (upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 8
        (ldv .ld Mt ((upd R 1 (ldv .ld Mt (R 2 + sign_extend (m := 64) (0x058#12)).toNat)) 2 +
          sign_extend (m := 64) (0x050#12)).toNat)) 2 + sign_extend (m := 64) (0x060#12))) 1 = C.r := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
  rw [hpc]
  have hs96 : R 2 + sign_extend (m := 64) (0x060#12) = C.s := by
    apply BitVec.eq_of_toNat_eq; rw [hs2]; sx_addr
  refine hfin _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (fun x h1 h2 h8 => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hr
  · exact hs96
  · exact hs0
  · exact F.s1
  · exact F.s2
  · exact F.s3
  · simp only [h1, h2, h8, ite_false]

/-- The epilogue's end with a fresh block in `a0`. -/
theorem MOK.fin_ok {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    (hfresh : FreshAt C.H (R 10).toNat C.n.toNat) (hal : (R 10).toNat % 16 = 0)
    (hheap : ∃ top brkv chunks bins,
      PHeapAt Mt (((R 10).toNat, C.n.toNat) :: C.H) top brkv chunks bins ∧
        top ≤ C.top0 + physSize C.n.toNat)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?) :
    ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt := by
  intro R' hR hk
  have h10 : R' 10 = R 10 := hk 10 (by decide) (by decide) (by decide)
  exact O.ok R' Mt ⟨hR, h10 ▸ hfresh, h10 ▸ hal, h10 ▸ hheap, hpres, hframe⟩

/-- The epilogue's end with NULL in `a0`. -/
theorem MOK.fin_null {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    (h0 : R 10 = 0) (hheap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?)
    (hst : Starved C.top0 C.n.toNat) :
    ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt := by
  intro R' hR hk
  have h10 : R' 10 = R 10 := hk 10 (by decide) (by decide) (by decide)
  exact O.null R' Mt ⟨hR, h10.trans h0, hheap, hpres, hframe, hst⟩

/-- **What a take owes its caller**: the block `v + 16` is fresh and aligned,
the heap holds it with the top grown by at most the request's chunk, the
footprint is present, and every byte outside the write window is at its entry
value. Every path that hands out a block — a small-bin take, the exact-fit
last remainder, the top split, a large-bin take — produces exactly this. -/
structure TakeRet (C : MCtx) (Mt : Mem) (v : Nat) : Prop where
  fresh : FreshAt C.H (v + 16) C.n.toNat
  align : (v + 16) % 16 = 0
  heap : ∃ top brkv chunks bins,
    PHeapAt Mt ((v + 16, C.n.toNat) :: C.H) top brkv chunks bins ∧
      top ≤ C.top0 + physSize C.n.toNat
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- **The epilogue's end with a freshly taken block.** `MOK.fin_ok` at the
pointer every take's `addi a0,a5,16` leaves in `a0`. -/
theorem MOK.fin_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {v : Nat}
    (h10 : (R 10).toNat = v + 16) (T : TakeRet C Mt v) :
    ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt := by
  refine O.fin_ok ?_ ?_ ?_ T.pres T.frame <;> rw [h10]
  · exact T.fresh
  · exact T.align
  · exact T.heap

/-- The epilogue at `0x80004830`. -/
theorem epi_80004830 {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} (F : MFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x80004830#64 R Mt :=
  epi_core O (st_80004830 O.live) (st_80004834 O.live) (st_80004838 O.live) (st_8000483c O.live)
    F hfin

/-- The epilogue at `0x8000484c`. -/
theorem epi_8000484c {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} (F : MFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 8 → R' x = R x) →
      AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x8000484c#64 R Mt :=
  epi_core O (st_8000484c O.live) (st_80004850 O.live) (st_80004854 O.live) (st_80004858 O.live)
    F hfin

/-! ## The counted top-level context -/

/-- The context of a counted `malloc` run at the binary: the owned bytes and
postcondition of `MallocChgRun`. -/
def mChgCtx (live : Nat → Prop) (H : List (Nat × Nat)) (n r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (k : Nat) (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) :
    MCtx :=
  ⟨live, mS H s, mQ H n r s saved k, H, n, r, s, rv0, Mt0, top0⟩

/-- The counted context owns the write window. -/
theorem mChg_own {H : List (Nat × Nat)} {s : BitVec 64} (hsp : SpOKA s) (a : Nat)
    (ha : MWin H s a) : mS H s a := by
  rcases ha with hf | ⟨h1, h2⟩
  · exact .inr hf
  · have hl := hsp.lo
    unfold mHead at h1
    unfold allocHeadroom Vsa.Sim.tohostAddr at hl
    -- `omega` hits its recursion limit on `s - 256 ≤ a → s - 512 ≤ a` (a gap of 256 or more
    -- between the subtracted constants), so the bounds go by monotonicity
    have hs : 512 ≤ s.toNat := by omega
    refine .inl ⟨?_, ?_⟩ <;> simp only [allocHeadroom]
    · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : 256 ≤ 512) _) h1
    · rw [Nat.sub_add_cancel hs]; exact h2

/-- The callee-saved registers the caller passed are back at a return. -/
theorem saved_of_regs {C : MCtx} {R : Nat → BitVec 64} {saved : List (Nat × BitVec 64)}
    {r n s : BitVec 64} (hsv : saved.map Prod.fst = vsaSaved)
    (hE : EntryRegs C.rv0 mallocEntryBV r n s saved) (h : MRegs C R) :
    ∀ p ∈ saved, R p.1 = p.2 := by
  intro p hp
  have hk : p.1 ∈ vsaSaved := by rw [← hsv]; exact List.mem_map_of_mem hp
  have hv := hE.saved p hp
  unfold vsaSaved at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h' | h' | h' | h' <;> rw [h'] at hv ⊢ <;> rw [← hv]
  · exact h.s0
  · exact h.s1
  · exact h.s2
  · exact h.s3

/-- **The counted context's obligations.** A return's top grows by at most
the request's chunk, which the credits cover; NULL is refuted by them. -/
theorem mOK_chg {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {k c : Nat} {rv0 : Nat → BitVec 64} {Mt0 : Mem} {top0 : Nat}
    (hlive : AllocLive live) (hsv : saved.map Prod.fst = vsaSaved) (hchg : vsaChg n.toNat c)
    (hsp : SpOKA s) (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved)
    (hst : Starts H) (hcap : 2 * (k + c) + extendSlack ≤ heapEnd - top0) :
    MOK (mChgCtx live H n r s saved k rv0 Mt0 top0) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := mChg_own hsp
  ral := hral
  ok := by
    intro R Mt h
    have hP := physSize_le_chg hchg
    obtain ⟨top, brkv, chunks, bins, hheap, htop⟩ := h.heap
    exact malloc_exit (brkv := brkv) (chunks := chunks) (bins := bins) hsv h.regs.ra h.regs.sp
      (saved_of_regs hsv hE h.regs) h.fresh hst h.align hheap (by simp only [mChgCtx] at htop; omega)
      h.pres
  null := by
    intro R Mt h
    have hP := physSize_le_chg16 hchg
    have := h.starved
    simp only [mChgCtx] at this
    unfold Starved extendSlack at *
    omega

/-! ## The uncounted top-level context -/

/-- The context of an uncounted `malloc` run at the binary: the owned bytes
and postcondition of `MallocLocalRun`. -/
def mLocCtx (live : Nat → Prop) (H : List (Nat × Nat)) (n r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv0 : Nat → BitVec 64) (Mt0 : Mem) (top0 : Nat) : MCtx :=
  ⟨live, mS H s, MallocEnd vsaLayoutP H n r s saved, H, n, r, s, rv0, Mt0, top0⟩

/-- **The uncounted context's obligations.** A return hands out the block; a
NULL return keeps the heap. -/
theorem mOK_loc {live : Nat → Prop} {H : List (Nat × Nat)} {n r s : BitVec 64}
    {saved : List (Nat × BitVec 64)} {rv0 : Nat → BitVec 64} {Mt0 : Mem} {top0 : Nat}
    (hlive : AllocLive live) (hsv : saved.map Prod.fst = vsaSaved) (hsp : SpOKA s)
    (hral : r.toNat % 4 = 0) (hE : EntryRegs rv0 mallocEntryBV r n s saved) (hst : Starts H) :
    MOK (mLocCtx live H n r s saved rv0 Mt0 top0) where
  live := hlive
  sp := MSp.of_spOKA hsp
  own := mChg_own hsp
  ral := hral
  ok := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap, _⟩ := h.heap
    refine malloc_ret (F := vsaFoot (((R 10).toNat, n.toNat) :: H)) hsv h.regs.ra h.regs.sp
      (saved_of_regs hsv hE h.regs) (fun a ha => .inr (vsaFoot_cons_sub a ha)) (fun a ha => h.pres a (vsaFoot_cons_sub a ha))
      fun rv mv hfr ha0 him => ⟨hfr, .inr ⟨?_, ?_, ?_⟩⟩ <;> rw [ha0]
    · exact h.fresh.block
    · exact h.align
    · exact ⟨hst.cons h.fresh.start, Mt, top, brkv, chunks, bins, him, hheap⟩
  null := by
    intro R Mt h
    obtain ⟨top, brkv, chunks, bins, hheap⟩ := h.heap
    exact malloc_ret hsv h.regs.ra h.regs.sp (saved_of_regs hsv hE h.regs) (fun a ha => .inr ha)
      h.pres fun rv mv hfr ha0 him =>
        ⟨hfr, .inl ⟨ha0.trans h.a0, ⟨hst, Mt, top, brkv, chunks, bins, him, hheap⟩⟩⟩

end VsaIris.VsaHeap
