import VsaIris.Vsa.FreeLarge

/-!
# `_free_r`'s paths below the top

A chunk whose successor is not the top: the successor's header loses
`PREV_INUSE` (`0x8000739c`), and the header after it says whether the
successor is free (`FNt`). The chunk then coalesces with a free predecessor,
a free successor, both or neither, and goes to a bin — or, when a neighbour
is the last remainder, stays in or takes over bin 1.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state at `0x800073ac`: the chunk `x` (size `sz`, header `hdr0`) with
the chunk `d` after it, whose header now reads its size alone (`Mt1`), and
the header `hnn` after `d` giving `d`'s flag; the heap without the block at
the memory before that store (`Mt`). -/
structure FNt (C : MCtx) (R : Nat → BitVec 64) (Mt Mt1 : Mem) (brkv : Nat) (cs₁ cs₃ : List Chunk)
    (d : Chunk) (bins : Nat → List Nat) (x sz hdr0 hnn : Nat) (w : BitVec 64) : Prop where
  frame : FFrame C R Mt1
  mem : Mt1 = writeLog Mt [(x + sz + 8, 8, w)]
  wv : w.toNat = d.size
  heap : PHeapAt Mt C.H C.top0 brkv (cs₁ ++ ⟨x, sz, true⟩ :: d :: cs₃) bins
  hno : ∀ e ∈ C.H, e.1 ≠ x + 16
  starts : Starts C.H
  daddr : d.addr = x + sz
  hdr : read64 Mt (x + 8) = some hdr0
  hsz : chunkSize hdr0 = sz
  hlow : hdr0 % 4 < 2
  nnr : read64 Mt (x + sz + d.size + 8) = some hnn
  nnf : prevInuse hnn = d.inuse
  pres : ∀ a, vsaFoot C.H a → (Mt1[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt1[a]? = C.Mt0[a]?
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a1 : (R 11).toNat = x + 16
  a2 : (R 12).toNat = x + sz
  a3 : (R 13).toNat = d.size
  a4 : (R 14).toNat = x
  a5 : (R 15).toNat = sz
  a0 : (R 10).toNat = hdr0
  t1 : (R 6).toNat = hdr0 % 2
  a6 : (R 16).toNat = hnn % 2

/-- **Below the top** (`0x8000739c`): clear the successor's `PREV_INUSE` and
read the header after it. -/
theorem free_nt {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {x sz hdr0 nh : Nat}
    (D : FDec C R Mt q n brkv chunks bins x sz hdr0 nh) (hnt : x + sz ≠ C.top0)
    (hk : ∀ R' Mt1 cs₁ cs₃ d hnn w, FNt C R' Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w →
      AW C.live C.S C.Q 0x800073ac#64 R' Mt1) :
    AW C.live C.S C.Q 0x8000739c#64 R Mt := by
  have Hp := D.heap
  have HH := Hp.heap.heap.heap
  have K := D.chunk
  obtain ⟨hal, htop16⟩ := HH.aligned
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem K.mem
  have hw := HH.walk
  rw [hsplit] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  obtain ⟨d, cs₃, rfl, hda⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = x + sz := by
    rcases hnext with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
    · exact absurd he hnt
    · exact ⟨d, cs₃, h1, h2⟩
  have hdm : d ∈ chunks := by rw [hsplit]; simp
  obtain ⟨hdh, hdhr, hdhs, _⟩ := walk_header HH.walk d hdm
  rw [hda, K.next] at hdhr
  obtain rfl : nh = hdh := Option.some.inj hdhr
  obtain ⟨hnn, hnnr, hnnf⟩ := (HH.headers hdm).2
  rw [hda] at hnnr
  have hdb := HH.walk.chunk_bounds d hdm
  have hXb := HH.walk.chunk_bounds _ K.mem
  have hbrk := HH.brk_le; have htle := HH.top_le
  simp only at hXb
  unfold heapStart heapEnd at *
  have hx16 := hal _ K.mem
  have hd16 := hal d hdm
  simp only at hx16
  rw [hda] at hd16 hdb
  have hsz16 := (walk_sizes HH.walk _ K.mem).1
  have hdsz16 := (walk_sizes HH.walk d hdm).1
  simp only at hsz16
  have ha2 := D.a2; have ha3 := D.a3
  have hnf := fun k hk => vsaFoot_of_cons (foot_header Hp.heap.heap (HH.end_bnd K.mem) k hk)
  simp only at hnf
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hEn : (R 12 + sign_extend (m := 64) (0x008#12)).toNat = x + sz + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha2]; simp; omega
  refine st_8000739c O.live ?_ ?_ ?_
  · rw [hEn]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hEn]; exact O.foot hnf
  rw [hEn]
  refine st_800073a0 O.live ?_
  have hEnn : (R 12 + R 13 + sign_extend (m := 64) (0x008#12)).toNat = x + sz + d.size + 8 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha3, hdhs]; simp; omega
  have hnnF := fun k hk => vsaFoot_of_cons (foot_header Hp.heap.heap (HH.end_bnd hdm) k hk)
  rw [hda] at hnnF
  have hnnr' : read64 (writeLog Mt [(x + sz + 8, 8, R 13)]) (x + sz + d.size + 8) = some hnn := by
    rw [read64_store_miss _ _ (by omega)]; exact hnnr
  refine st_800073a4 O.live ?_ ?_ ?_
  · simp only [upd_apply, ite_true]; rw [hEnn]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · simp only [upd_apply, ite_true]; rw [hEnn]; exact O.foot hnnF
  simp only [upd_apply, ite_true]
  rw [hEnn, ldv_at hnnr' _ rfl]
  refine st_800073a8 O.live ?_
  have hnnlt := Vsa.Sim.read64_lt _ _ _ hnnr
  have hoN : x + sz + 8 + 8 ≤ C.s.toNat - mHead ∨ C.s.toNat ≤ x + sz + 8 := by
    refine Classical.byContradiction fun hc => ?_
    have hk : (if x + sz + 8 ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - (x + sz + 8)) < 8 := by
      split <;> omega
    exact Hp.disj _ (by split <;> omega) (by unfold mHead at *; split <;> omega) (hnf _ hk)
  unfold mHead at hoN
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have Hd := Hp.heap.drop
  rw [hsplit] at Hd
  refine hk _ _ cs₁ cs₃ d hnn (R 13) ⟨(D.frame.store (by omega)).of_regs ?_ ?_ ?_ ?_, rfl,
    by rw [ha3]; exact hdhs, Hd, fun e he heq => hst.1 (List.mem_map.2 ⟨e, he, by rw [heq, K.addr]⟩),
    hst.2, hda, K.hdr, K.hsz, K.hlow, hnnr, hnnf, fun a ha => writeLog_present _ _ _ (Hp.pres a ha),
    Hp.disj, frame_store (win_foot hnf) Hp.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact D.s0
  · exact D.a7
  · rw [D.a1, ← K.addr]
  · exact ha2
  · rw [ha3, hdhs]
  · exact D.a4
  · exact D.a5
  · exact D.a0
  · exact D.t1
  · sx_norm
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnnlt,
      show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

end VsaIris.VsaHeap
