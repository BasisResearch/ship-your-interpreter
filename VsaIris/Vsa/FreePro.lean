import VsaIris.Vsa.FreeCtx

/-!
# `_free_r`'s prologue
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The heap before `_free_r` writes it: in shape with the block `(q, n)`
live, the footprint of the heap without it present and off the stack, and
every byte outside the write window at its entry value. -/
structure FHeap (C : MCtx) (Mt : Mem) (q n brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mt ((q, n) :: C.H) C.top0 brkv chunks bins
  starts : Starts ((q, n) :: C.H)
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

/-- The heap invariant through a store to the run's stack. -/
theorem FHeap.store_stack {C : MCtx} {Mt : Mem} {q n brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : FHeap C Mt q n brkv chunks bins) {a w : Nat} {v : BitVec 64}
    (h1 : C.s.toNat - mHead ≤ a) (h2 : a + w ≤ C.s.toNat) :
    FHeap C (writeLog Mt [(a, w, v)]) q n brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have hd := Hp.disj x
    have ho : OutL [(a, w, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd (by omega) (by omega) (vsaFoot_of_cons hx.1), trivial⟩
    rw [writeLog_out _ _ _ ho]
  starts := Hp.starts
  pres := pres_store Hp.pres
  disj := Hp.disj
  frame := frame_store (win_stack h1 h2) Hp.frame

/-- The chunk `_free_r` releases, as its prologue decodes it: the in-use
chunk `x` below the block, its header `hdr0` and size `sz`, and the header
`nh` after it. -/
structure FChunk (Mt : Mem) (q : Nat) (chunks : List Chunk) (x sz hdr0 nh : Nat) : Prop where
  mem : (⟨x, sz, true⟩ : Chunk) ∈ chunks
  addr : x + 16 = q
  hdr : read64 Mt (x + 8) = some hdr0
  hsz : chunkSize hdr0 = sz
  hlow : hdr0 % 4 < 2
  next : read64 Mt (x + sz + 8) = some nh

/-- The state at `_free_r`'s first branch (`0x80007398`): the frame, the heap
unwritten, the decoded chunk, and its registers (`av` in `a7`, the top in
`a6`, the chunk in `a4`, its size in `a5`, the next chunk in `a2`, its header
in `a0` and `PREV_INUSE` in `t1`, the next size in `a3`). -/
structure FDec (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) (q n brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (x sz hdr0 nh : Nat) : Prop where
  frame : FFrame C R Mt
  heap : FHeap C Mt q n brkv chunks bins
  chunk : FChunk Mt q chunks x sz hdr0 nh
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a6 : (R 16).toNat = C.top0
  a4 : (R 14).toNat = x
  a5 : (R 15).toNat = sz
  a2 : (R 12).toNat = x + sz
  a0 : (R 10).toNat = hdr0
  t1 : (R 6).toNat = hdr0 % 2
  a3 : (R 13).toNat = chunkSize nh

/-- **`_free_r`'s prologue** (`0x80007350`): a non-NULL block, the frame, the
lock, and the decoding of the chunk below the block. -/
theorem free_pro {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (E : FEntry C q R) (Hp : FHeap C C.Mt0 q n brkv chunks bins)
    (hk : ∀ R' Mt x sz hdr0 nh, FDec C R' Mt q n brkv chunks bins x sz hdr0 nh →
      AW C.live C.S C.Q 0x80007398#64 R' Mt) :
    AW C.live C.S C.Q 0x80007350#64 R C.Mt0 := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := E.sp
  have hs2n : (R 2).toNat = C.s.toNat := by rw [hs2]
  have HH := Hp.heap.heap.heap
  obtain ⟨c, hc, hcu, hca, hcn⟩ := HH.exact (q, n) List.mem_cons_self List.mem_cons_self
  have hcb := HH.walk.chunk_bounds c hc
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hcb; unfold heapEnd at hbrk
  simp only at hca hcn
  have hq := E.a1
  refine st_80007350 O.live (fun h => absurd (congrArg BitVec.toNat h) (by rw [hq]; simp; omega))
    (fun _ => ?_)
  sx_run [40] O.live at 0x8000736c
  rw [show (R 2 + 18446744073709551584#64 + 16#64).toNat = C.s.toNat - 32 + 16 by sx_addr,
    show (R 2 + 18446744073709551584#64 + 8#64).toNat = C.s.toNat - 32 + 8 by sx_addr,
    show (R 2 + 18446744073709551584#64 + 24#64).toNat = C.s.toNat - 32 + 24 by sx_addr]
  have Hp1 := ((Hp.store_stack (a := C.s.toNat - 32 + 16) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 32 + 8) (w := 8) (v := R 11) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 32 + 24) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog C.Mt0 [(C.s.toNat - 32 + 16, 8, R 8)])
    [(C.s.toNat - 32 + 8, 8, R 11)]) [(C.s.toNat - 32 + 24, 8, R 1)] = Mt1 at Hp1 ⊢
  have hA1 : read64 Mt1 (C.s.toNat - 32 + 8) = some (R 11).toNat := by
    rw [← hM1, read64_store_miss _ _ (by omega), read64_store_hit]
  have HH1 := Hp1.heap.heap.heap
  obtain ⟨hdr0, hdr0r, hdr0s, hdr0l⟩ := walk_header HH1.walk c hc
  obtain ⟨nh, nhr, nhp⟩ := (HH1.headers hc).2
  have htp := HH1.top_ptr
  sx_run [3] O.live at 0x80007370
  rw [show (R 2 + 18446744073709551584#64 + 8#64).toNat = C.s.toNat - 32 + 8 by sx_addr,
    ldv_at hA1 _ rfl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  sx_run [3] O.live at 0x8000737c
  rw [ldv_at htp 2147593504 (by unfold topAddr avAddr; rfl)]
  have hE8 : (R 11 + 18446744073709551608#64).toNat = c.addr + 8 := by
    rw [BitVec.toNat_add, hq]; simp; omega
  have hxf := fun k hk => vsaFoot_of_cons (foot_header Hp1.heap.heap (.inr ⟨c, hc, rfl⟩) k hk)
  refine st_8000737c O.live ?_ ?_ ?_
  · sx_norm; rw [hE8]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hE8]; exact O.foot hxf
  sx_norm
  rw [hE8, ldv_at hdr0r _ rfl]
  sx_run [3] O.live at 0x8000738c
  have hx : (R 11 + 18446744073709551600#64).toNat = c.addr := by
    rw [BitVec.toNat_add, hq]; simp; omega
  have hsz : (BitVec.ofNat 64 hdr0 &&& 18446744073709551614#64).toNat = c.size := by
    rw [toNat_and_m2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r)]
    unfold chunkSize at hdr0s; omega
  have hnx : (R 11 + 18446744073709551600#64 + (BitVec.ofNat 64 hdr0 &&& 18446744073709551614#64)).toNat
      = c.addr + c.size := by
    rw [BitVec.toNat_add, hx, hsz]; omega
  have hnf := fun k hk => vsaFoot_of_cons (foot_header Hp1.heap.heap (HH1.end_bnd hc) k hk)
  refine st_8000738c O.live ?_ ?_ ?_
  · sx_norm; rw [BitVec.toNat_add, hnx]; unfold LdOK Vsa.Sim.tohostAddr; simp; omega
  · sx_norm; rw [BitVec.toNat_add, hnx]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega)]; exact O.foot hnf
  sx_norm
  rw [BitVec.toNat_add, hnx]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega), ldv_at nhr _ rfl]
  refine st_80007390 O.live ?_
  refine st_80007394 O.live ?_
  have hS0 : read64 Mt1 (C.s.toNat - 32 + 16) = some (C.rv0 8).toNat := by
    rw [← hM1, read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_hit, E.s0]
  have hRA : read64 Mt1 (C.s.toNat - 32 + 24) = some C.r.toNat := by
    rw [← hM1, read64_store_hit, E.ra]
  obtain ⟨cx, csz, cu⟩ := c
  simp only at hcu hca hcn hcb hdr0r hdr0s hdr0l nhr hx hsz hnx hxf hnf
  subst hcu
  have h9 := E.s1; have h18 := E.s2; have h19 := E.s3; have h10 := E.a0
  refine hk _ Mt1 cx csz hdr0 nh ⟨⟨?_, hS0, hRA, ?_, ?_, ?_⟩, Hp1, ⟨hc, hca, hdr0r, hdr0s, hdr0l, nhr⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hs2]
  · exact h9
  · exact h18
  · exact h19
  · exact h10
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact hx
  · exact hsz
  · exact hnx
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r)]
  · simp only [sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r),
      show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · simp only [sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend]
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ nhr)]; rfl

end VsaIris.VsaHeap

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **`_free_r`'s epilogue** (`0x80007434`): restore `s0` and `ra`, pop the
frame, release the lock and return, owing `FRet`. -/
theorem free_epi {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} (F : FFrame C R Mt)
    (hheap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins ∧ top ≤ C.top0)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?) :
    AW C.live C.S C.Q 0x80007434#64 R Mt := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  have hs2n : (R 2).toNat = C.s.toNat - 32 := by
    rw [hs2, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hl16 : ldv .ld Mt (R 2 + 16#64).toNat = BitVec.ofNat 64 (C.rv0 8).toNat :=
    ldv_at F.s0 _ (by rw [BitVec.toNat_add, hs2n]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  have hl24 : ldv .ld Mt (R 2 + 24#64).toNat = BitVec.ofNat 64 C.r.toNat :=
    ldv_at F.ra _ (by rw [BitVec.toNat_add, hs2n]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hl16 hl24
  sx_run [20] O.live at 0x80007440
  rw [hl16, hl24]
  sx_run [20] O.live
  · sx_norm; exact O.ral
  have h9 := F.s1; have h18 := F.s2; have h19 := F.s3
  refine O.ok _ Mt ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hheap, hpres, hframe⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hs2]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · exact h9
  · exact h18
  · exact h19

end VsaIris.VsaHeap
