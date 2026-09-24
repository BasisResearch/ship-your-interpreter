import VsaIris.Vsa.ReallocTail

/-!
# `_realloc_r`'s dispatch

At `0x800052e0` the old chunk `X` below the block is decoded. A chunk
already at least the request's `nb` goes straight to the tail; otherwise the
state `RD` is handed to the growth paths at `0x800052f0`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state at `0x800052f0`: the frame, the heap, the old chunk `X` of size
`S < nb` (header `hdr0`) holding the old block, and its registers. -/
structure RD (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt : Mem) (brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) (X S hdr0 nb : Nat) : Prop where
  frame : RFrame C R Mt
  heap : RHeap C B Mt brkv chunks bins
  nbok : NbOK C.n nb
  nb31 : nb < 2 ^ 31
  mem : (⟨X, S, true⟩ : Chunk) ∈ chunks
  addr : X + 16 = B.p
  hdr : read64 Mt (X + 8) = some hdr0
  hsz : chunkSize hdr0 = S
  hlow : hdr0 % 4 < 2
  lt : S < nb
  s0 : (R 8).toNat = X + 16
  s1 : R 9 = reentV
  a1 : R 11 = C.n
  a2 : (R 12).toNat = X
  a4 : (R 14).toNat = S
  a5 : (R 15).toNat = nb

/-- **The dispatch** (`0x800052e0`): decode `X`; a chunk of at least `nb`
bytes is the tail's (`realloc_tail`), any other the growth paths'. -/
theorem realloc_dec {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {nb brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mt) (Hp : RHeap C B Mt brkv chunks bins) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (h8 : (R 8).toNat = B.p) (h9 : R 9 = reentV) (h11 : R 11 = C.n) (h15 : (R 15).toNat = nb)
    (hk : ∀ R' X S hdr0, RD C B R' Mt brkv chunks bins X S hdr0 nb → (R' 13).toNat = hdr0 →
      AW C.live C.S C.Q 0x800052f0#64 R' Mt) :
    AW C.live C.S C.Q 0x800052e0#64 R Mt := by
  have HH := Hp.heap.heap.heap
  obtain ⟨c, hc, hu, hca, hcn⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
  simp only at hca hcn
  obtain ⟨X, S, ci⟩ := c
  simp only at hu hca hcn
  subst hu
  have hXb := HH.walk.chunk_bounds _ hc
  have hx16 := HH.aligned.1 _ hc
  have hS16 := (walk_sizes HH.walk _ hc).1
  simp only at hXb hx16 hS16
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapStart heapEnd at *
  obtain ⟨hdr0, hdr, hsz, hlow⟩ := walk_header HH.walk _ hc
  simp only at hdr hsz
  have hdrlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hhf : ∀ k, k < 8 → vsaFoot C.H (X + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header Hp.heap.heap (.inr ⟨_, hc, rfl⟩) k hk)
  have hE8 : (R 8 + sign_extend (m := 64) (0xff8#12)).toNat = X + 8 := by
    sx_norm; rw [BitVec.toNat_add, h8, ← hca]; simp; omega
  refine st_800052e0 O.live (by rw [hE8]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [hE8]; exact O.foot hhf) ?_
  rw [hE8, ldv_at hdr _ rfl]
  refine st_800052e4 O.live ?_
  refine st_800052e8 O.live ?_
  have hX : (R 8 + sign_extend (m := 64) (0xff0#12)).toNat = X := by
    sx_norm; rw [BitVec.toNat_add, h8, ← hca]; simp; omega
  have hSv : (BitVec.ofNat 64 hdr0 &&& sign_extend (m := 64) (0xffc#12)).toNat = S := by
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdrlt, ← hsz]; rfl
  have hnbP := hnb.eq
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [hnbP]; unfold physSize; omega
  have h14 : (BitVec.ofNat 64 hdr0 &&& sign_extend (m := 64) (0xffc#12)).toInt = (S : Int) :=
    toInt_small hSv (by omega)
  have h15' : (R 15).toInt = (nb : Int) := toInt_small h15 (by omega)
  refine st_800052ec O.live (fun hcmp => ?_) (fun hcmp => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h14, h15', Int.ofNat_le] at hcmp
  · -- the chunk already holds the request
    obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem hc
    have Hr := Hp.heap.reblock hc rfl hca (n' := C.n.toNat) (show C.n.toNat + 8 ≤ S by omega)
    rw [hsplit, ← hca] at Hr
    have hw := HH.walk
    rw [hsplit] at hw
    obtain ⟨⟨hn, hnr, hnp⟩, _⟩ := walk_next_of hw
    simp only at hnr hnp
    have hodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
    have hhdr : hdr0 = S + hdr0 % 2 := by unfold chunkSize at hsz; omega
    have hp := Hp.grow
    refine realloc_tail O (V := Mt) (X := X) (S := S) (nb := nb) (cs₁ := cs₁) (cs₂ := cs₂)
      ⟨F.of_regs ?_ ?_ ?_, Hr, by rw [hca]; exact Hp.starts, by omega, hnb, hcmp, ⟨hdr0, hdr, by rw [← hhdr]; exact hdr⟩,
      ⟨hn, hnr, by rw [show hn / 2 * 2 + 1 = hn by omega]; exact hnr⟩, fun _ _ _ _ => rfl,
      Hp.pres, Hp.disj, Hp.disjD, by rw [hca]; exact Hp.data, by omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [h8, hca]
    · exact h9
    · exact hX
    · exact hSv
    · exact h15
  · -- the chunk must grow
    refine hk _ X S hdr0 ⟨F.of_regs ?_ ?_ ?_, Hp, hnb, hnb31, hc, hca, hdr, hsz, hlow, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [h8, hca]
    · exact h9
    · exact h11
    · exact hX
    · exact hSv
    · exact h15
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdrlt]

end VsaIris.VsaHeap
