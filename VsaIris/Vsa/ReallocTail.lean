import VsaIris.Vsa.ReallocCall

/-!
# `_realloc_r`'s tail

Every in-place path joins at `0x80005414` with the chunk `X` (at least the
request's chunk `nb`) holding the result `X + 16`: `RT` is that state over a
virtual heap `V` in which `X` is already in use with its final size and the
header after it marks it in use; the machine memory still has the old words
there. With a remainder of at least `MINSIZE` the chunk is cut
(`PHeapAt.cut`) and the remainder released by a nested `_free_r`
(`rcall_free`); then `rtail_fin` unlocks and returns `X + 16`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **The return with the block in `s0`** (`0x80005440`): unlock, `a3 := s0`,
the epilogue, and the fresh-block continuation. -/
theorem rtail_fin {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {p top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mt) (hs0 : (R 8).toNat = p) (hp16 : p % 16 = 0)
    (hheap : PHeapAt Mt ((p, C.n.toNat) :: C.H) top brkv chunks bins)
    (hst : Starts ((p, C.n.toNat) :: C.H)) (htop : top ≤ C.top0 + physSize C.n.toNat)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hdata : ∀ k, k < B.nOld → Mt[p + k]? = some (B.old (B.p + k))) :
    AW C.live C.S C.Q 0x80005440#64 R Mt := by
  sx_run [12] O.live at 0x80005448
  refine st_80005448 O.live ?_
  refine repi O (F.of_regs ?_ ?_ ?_) fun R' hR h10 => O.ok R' Mt ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hp : (R' 10).toNat = p := by
    rw [h10]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; sx_norm; exact hs0
  refine ⟨hR, ?_, ?_, ⟨top, brkv, chunks, bins, ?_, htop⟩, hpres, ?_⟩ <;> rw [hp]
  · exact hheap.fresh_of_block hst
  · exact hp16
  · exact hheap
  · exact hdata

/-- `n ||| 1` sets the low bit. -/
theorem nat_or1 (n : Nat) : n ||| 1 = n / 2 * 2 + 1 := by
  have h1 : (n ||| 1) / 2 = n / 2 := by
    have := Nat.or_div_two_pow (a := n) (b := 1) (n := 1); simpa using this
  have h2 : (n ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
  have := Nat.div_add_mod (n ||| 1) 2
  omega

theorem or1_toNat' (x : BitVec 64) : (x ||| 1#64).toNat = x.toNat / 2 * 2 + 1 := by
  rw [BitVec.toNat_or, show (1#64 : BitVec 64).toNat = 1 from rfl, nat_or1]

theorem and1_toNat (x : BitVec 64) : (x &&& 1#64).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- An even word with a low bit or-ed in. -/
theorem or_bit_toNat {x y : BitVec 64} (hx : x.toNat % 2 = 0) (hy : y.toNat < 2) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h | h
  · have : y = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; simp
  · have : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this
    rw [or1_toNat', h]; omega

/-- The state at `_realloc_r`'s tail (`0x80005414`): the chunk `X` of size
`S ≥ nb` holding the new block `X + 16` in the virtual heap `V`, whose header
`V` already records as `S` with the machine's `PREV_INUSE`, and whose
successor's header `V` already marks in use; the machine memory agrees with
`V` elsewhere on the footprint, and holds the old contents at `X + 16`. -/
structure RT (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt V : Mem) (X S nb top brkv : Nat)
    (cs₁ cs₂ : List Chunk) (bins : Nat → List Nat) : Prop where
  frame : RFrame C R Mt
  heap : PHeapAt V ((X + 16, C.n.toNat) :: C.H) top brkv (cs₁ ++ ⟨X, S, true⟩ :: cs₂) bins
  starts : Starts ((X + 16, C.n.toNat) :: C.H)
  top_le : top ≤ C.top0 + physSize C.n.toNat
  nbok : NbOK C.n nb
  nbS : nb ≤ S
  hdr : ∃ hM, read64 Mt (X + 8) = some hM ∧ read64 V (X + 8) = some (S + hM % 2)
  nxt : ∃ hn, read64 Mt (X + S + 8) = some hn ∧ read64 V (X + S + 8) = some (hn / 2 * 2 + 1)
  agree : ∀ w, vsaFoot ((X + 16, C.n.toNat) :: C.H) w → ¬ (X + 8 ≤ w ∧ w < X + 16) →
    ¬ (X + S + 8 ≤ w ∧ w < X + S + 16) → Mt[w]? = V[w]?
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  data : ∀ k, k < B.nOld → Mt[X + 16 + k]? = some (B.old (B.p + k))
  old_le : B.nOld ≤ C.n.toNat
  s0 : (R 8).toNat = X + 16
  s1 : R 9 = reentV
  a2 : (R 12).toNat = X
  a4 : (R 14).toNat = S
  a5 : (R 15).toNat = nb

/-- **`_realloc_r`'s tail** (`0x80005414`): record the chunk's size (cut off
a remainder of at least `MINSIZE` and release it), mark it in use in the
next header, unlock, and return `X + 16`. -/
theorem realloc_tail {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt V : Mem}
    {X S nb top brkv : Nat} {cs₁ cs₂ : List Chunk} {bins : Nat → List Nat}
    (T : RT C B R Mt V X S nb top brkv cs₁ cs₂ bins) :
    AW C.live C.S C.Q 0x80005414#64 R Mt := by
  have HB := T.heap.heap
  have HH := HB.heap
  have hXm : (⟨X, S, true⟩ : Chunk) ∈ cs₁ ++ ⟨X, S, true⟩ :: cs₂ := by simp
  have hXb := HH.walk.chunk_bounds _ hXm
  have hx16 := HH.aligned.1 _ hXm
  have hS16 := (walk_sizes HH.walk _ hXm).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := T.heap.heap.top_room
  simp only at hXb hx16 hS16
  unfold heapStart heapEnd at *
  have hnb := T.nbok.eq
  have hnbS := T.nbS
  have hnP : C.n.toNat + 8 ≤ nb ∧ 32 ≤ nb ∧ nb % 16 = 0 := by rw [hnb]; unfold physSize; omega
  obtain ⟨hM, hMr, hVr⟩ := T.hdr
  obtain ⟨hn, hnr, hVn⟩ := T.nxt
  have hhf : ∀ k, k < 8 → vsaFoot C.H (X + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header HB (.inr ⟨_, hXm, rfl⟩) k hk)
  have hnf : ∀ k, k < 8 → vsaFoot C.H (X + S + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header HB (HH.end_bnd hXm) k hk)
  have hoX := off_stack_of T.disj hhf
  have hoN := off_stack_of T.disj hnf
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hMlt := Vsa.Sim.read64_lt _ _ _ hMr
  have hnlt := Vsa.Sim.read64_lt _ _ _ hnr
  have ha2 := T.a2; have ha4 := T.a4; have ha5 := T.a5
  have hE8 : (R 12 + sign_extend (m := 64) (0x008#12)).toNat = X + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha2]; simp; omega
  refine st_80005414 O.live (by rw [hE8]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [hE8]; exact O.foot hhf) ?_
  rw [hE8, ldv_at hMr _ rfl]
  refine st_80005418 O.live ?_
  refine st_8000541c O.live ?_
  refine st_80005420 O.live ?_
  refine st_80005424 O.live ?_
  have hrem : (R 14 - R 15).toNat = S - nb := by rw [BitVec.toNat_sub, ha4, ha5]; omega
  have hb : (BitVec.ofNat 64 hM &&& 1#64).toNat = hM % 2 := by
    rw [and1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hMlt]
  have hEn : (R 12 + R 14 + sign_extend (m := 64) (0x008#12)).toNat = X + S + 8 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha4]; simp; omega
  refine st_80005428 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hrem] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x01f#12) : BitVec 64).toNat = 31 from rfl] at hc
  · -- a remainder: cut it off and free it
    have hE8' : (R 12 + 8#64).toNat = X + 8 := by rw [BitVec.toNat_add, ha2]; simp; omega
    have hEn' : (R 12 + R 14 + 8#64).toNat = X + S + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha4]; simp; omega
    have hEr' : (R 12 + R 15 + 8#64).toNat = X + nb + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha5]; simp; omega
    have hEq : (R 12 + R 15 + 16#64).toNat = X + nb + 16 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha5]; simp; omega
    have hv1 : (R 15 ||| BitVec.ofNat 64 hM &&& 1#64).toNat = nb + hM % 2 := by
      rw [or_bit_toNat (by rw [ha5]; omega) (by rw [hb]; omega), ha5, hb]
    have hvr : (R 14 - R 15 ||| 1#64).toNat = S - nb + 1 := by
      rw [or1_toNat', hrem]; omega
    have hrf : ∀ k, k < 8 → vsaFoot C.H (X + nb + 8 + k) := fun k hk => .inr ⟨by
      show heapStart ≤ _; unfold heapStart; omega, by show _ < heapEnd; unfold heapEnd; omega,
      fun e he hin => by
        obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact e (List.mem_cons_of_mem _ he)
          (List.mem_cons_of_mem _ he)
        have := HH.walk.chunk_bounds c0 hc0
        unfold InExt at hin
        rcases HH.walk.chunk_sep c0 hc0 _ hXm with rfl | h3 | h3
        · have hst := T.starts
          unfold Starts at hst
          rw [List.map_cons, List.nodup_cons] at hst
          exact hst.1 (List.mem_map.2 ⟨e, he, by simp only at hc0a ⊢; omega⟩)
        · simp only at h3; omega
        · simp only at h3; omega⟩
    have hoR := off_stack_of T.disj hrf
    sx_norm
    refine st_80005488 O.live ?_
    refine st_8000548c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
    · rw [hE8']; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [hE8']; exact O.foot hhf
    rw [hE8']
    refine st_80005490 O.live ?_
    refine st_80005494 O.live ?_
    refine st_80005498 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
    · rw [hEr']; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [hEr']; exact O.foot hrf
    rw [hEr']
    have hnr2 : read64 (writeLog (writeLog Mt [(X + 8, 8, R 15 ||| BitVec.ofNat 64 hM &&& 1#64)])
        [(X + nb + 8, 8, R 14 - R 15 ||| 1#64)]) (X + S + 8) = some hn := by
      rw [rd_miss (by omega), rd_miss (by omega)]; exact hnr
    refine st_8000549c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
    · rw [hEn']; unfold LdOK Vsa.Sim.tohostAddr; omega
    · rw [hEn']; exact O.foot hnf
    rw [hEn', ldv_at hnr2 _ rfl]
    refine st_800054a0 O.live ?_
    refine st_800054a4 O.live ?_
    refine st_800054a8 O.live ?_
    refine st_800054ac O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
    · rw [hEn']; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [hEn']; exact O.foot hnf
    rw [hEn']
    refine st_800054b0 O.live ?_
    simp only [VsaIris.ra]
    have hv2 : (BitVec.ofNat 64 hn ||| 1#64).toNat = hn / 2 * 2 + 1 := by
      rw [or1_toNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt]
    generalize hM3 : writeLog (writeLog (writeLog Mt [(X + 8, 8, R 15 ||| BitVec.ofNat 64 hM &&& 1#64)])
      [(X + nb + 8, 8, R 14 - R 15 ||| 1#64)]) [(X + S + 8, 8, BitVec.ofNat 64 hn ||| 1#64)] = M3
    have hout : ∀ a, ¬ (X + 8 ≤ a ∧ a < X + 16) → ¬ (X + nb + 8 ≤ a ∧ a < X + nb + 16) →
        ¬ (X + S + 8 ≤ a ∧ a < X + S + 16) → M3[a]? = Mt[a]? := by
      intro a h1 h2 h3
      rw [← hM3, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
    -- the cut heap
    have hSd : S = nb + (S - nb) := by omega
    have HV := T.heap
    rw [hSd] at HV
    have hst := T.starts
    have HC := HV.cut (m' := M3) (h' := nb + hM % 2) (hy := S - nb + 1) (by omega) (by omega) (by omega)
      (fun e he heq => by
        rcases List.mem_cons.mp he with rfl | he
        · simp only; omega
        · unfold Starts at hst; rw [List.map_cons, List.nodup_cons] at hst
          exact absurd (List.mem_map.2 ⟨e, he, heq⟩) hst.1)
      (by rw [← hM3, rd_miss (by omega), rd_miss (by omega), read64_store_hit, hv1])
      (by unfold chunkSize; omega) (by omega)
      (fun h0 hr => by
        rw [hVr] at hr; cases hr; unfold prevInuse; congr 1; omega)
      (by rw [← hM3, rd_miss (by omega), read64_store_hit, hvr])
      (by unfold chunkSize; omega) (by omega) (by unfold prevInuse; simp; omega)
      (fun w hw h1 h2 => by
        refine agree_of_words (P := fun a => vsaFoot ((X + 16, C.n.toNat) :: C.H) a ∧
            ¬ (X + 8 ≤ a ∧ a < X + 16) ∧ ¬ (X + nb + 8 ≤ a ∧ a < X + nb + 16)) [X + S + 8]
          (fun w' hw' => ?_) (fun a ha hw' => ?_) w ⟨hw, h1, h2⟩
        · simp only [List.mem_singleton] at hw'; subst hw'
          exact ⟨hn / 2 * 2 + 1, by rw [← hM3, read64_store_hit, hv2], hVn⟩
        · simp only [List.mem_singleton, forall_eq] at hw'
          obtain ⟨ha1, ha2', ha3⟩ := ha
          rw [hout a ha2' ha3 (by omega)]
          exact T.agree a ha1 ha2' (by omega))
    -- the remainder's zero-length block starts where no live block does
    have hst' : Starts ((X + nb + 16, 0) :: (X + 16, C.n.toNat) :: C.H) := by
      refine hst.cons fun e he heq => ?_
      rcases List.mem_cons.mp he with rfl | he
      · simp only at heq; omega
      · obtain ⟨c0, hc0, _, hc0a, _⟩ := HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
        have := HH.walk.chunk_bounds c0 hc0
        rcases HH.walk.chunk_sep c0 hc0 _ hXm with rfl | h3 | h3
        · simp only at hc0a; omega
        · simp only at h3; omega
        · simp only at h3; omega
    have hpres3 : ∀ a, vsaFoot C.H a → (M3[a]?).isSome := fun a ha => by
      rw [← hM3]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _ (T.pres a ha)))
    have F3 : RFrame C R M3 := by
      rw [← hM3]
      exact ((T.frame.store (a := X + 8) (w := 8) (by omega)).store (a := X + nb + 8) (w := 8)
        (by omega)).store (a := X + S + 8) (w := 8) (by omega)
    have hsp := T.frame.sp
    refine rcall_free O (link := 0x800054b4#64) (by decide) (fun a ha => vsaFoot_cons_sub a ha) ?_ ?_ ?_ ?_
      HC hst' (fun a ha => hpres3 a (vsaFoot_cons_sub a ha)) T.disjD
      (fun R' Mt' h1 h2 h8 h9 h18 h19 hheap hpres hframe => ?_) <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hsp
    · exact T.s1
    · exact hEq
    -- back from `_free_r`: unlock and return `X + 16`
    obtain ⟨top', brkv', chunks', bins', H', htop'⟩ := hheap
    have hs64 := sp64_toNat O.spA
    have hlo' := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo'
    -- bytes off the callee's window keep their values
    have hkeep : ∀ a, (C.s.toNat - 64 ≤ a ∧ a < C.s.toNat) ∨ (¬ vsaFoot ((X + 16, C.n.toNat) :: C.H) a ∧
        vsaFoot C.H a) → Mt'[a]? = M3[a]? := by
      intro a ha
      refine hframe a fun hw => ?_
      rcases hw with hf | ⟨h1, h2⟩
      · rcases ha with ⟨h1, h2⟩ | ⟨hn', _⟩
        · exact T.disj a (by unfold mHead; omega) h2 (vsaFoot_cons_sub a hf)
        · exact hn' hf
      · rw [hs64] at h1 h2
        rcases ha with ⟨h3, _⟩ | ⟨_, hf⟩
        · omega
        · exact T.disjD a (win64_le h1) (by omega) hf
    have hslot : ∀ a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat → read64 Mt' a = read64 M3 a :=
      fun a h1 h2 => read64_keep fun k hk => hkeep _ (.inl ⟨by omega, by omega⟩)
    have hblk : ∀ k, k < C.n.toNat → ¬ vsaFoot ((X + 16, C.n.toNat) :: C.H) (X + 16 + k) ∧
        vsaFoot C.H (X + 16 + k) := fun k hk =>
      ⟨fun hf => by
        rcases hf with hg | ⟨_, _, h3⟩
        · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
        · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩,
       T.heap.block_foot T.starts k hk⟩
    have htl := T.top_le
    refine st_800054b4 O.live (rtail_fin O ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ (by omega) H'
      T.starts (by omega) (fun a ha => ?_) (fun k hk => ?_))
    · rw [h2]; exact hsp
    · rw [hslot _ (by omega) (by omega)]; exact F3.s0
    · rw [hslot _ (by omega) (by omega)]; exact F3.s1
    · rw [hslot _ (by omega) (by omega)]; exact F3.ra
    · rw [h18]; exact F3.s2
    · rw [h19]; exact F3.s3
    · rw [h8]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact T.s0
    · by_cases hf : vsaFoot ((X + 16, C.n.toNat) :: C.H) a
      · exact hpres a hf
      · rw [hkeep a (.inr ⟨hf, ha⟩)]; exact hpres3 a ha
    · have hk' : k < C.n.toNat := Nat.lt_of_lt_of_le hk T.old_le
      rw [hkeep _ (.inr (hblk k hk')), hout _ (by omega) (by omega) (by omega)]
      exact T.data k hk
  -- no remainder: `X` keeps its size
  have hE8' : (R 12 + 8#64).toNat = X + 8 := by rw [BitVec.toNat_add, ha2]; simp; omega
  have hEn' : (R 12 + R 14 + 8#64).toNat = X + S + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha4]; simp; omega
  have hv1 : (R 14 ||| BitVec.ofNat 64 hM &&& 1#64).toNat = S + hM % 2 := by
    rw [or_bit_toNat (by rw [ha4]; omega) (by rw [hb]; omega), ha4, hb]
  sx_norm
  refine st_8000542c O.live ?_
  refine st_80005430 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
  · rw [hE8']; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hE8']; exact O.foot hhf
  rw [hE8']
  have hnr1 : read64 (writeLog Mt [(X + 8, 8, R 14 ||| BitVec.ofNat 64 hM &&& 1#64)]) (X + S + 8) =
      some hn := by rw [rd_miss (by omega)]; exact hnr
  refine st_80005434 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
  · rw [hEn']; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEn']; exact O.foot hnf
  rw [hEn', ldv_at hnr1 _ rfl]
  refine st_80005438 O.live ?_
  refine st_8000543c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> (try sx_norm)
  · rw [hEn']; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hEn']; exact O.foot hnf
  rw [hEn']
  have hv2 : (BitVec.ofNat 64 hn ||| 1#64).toNat = hn / 2 * 2 + 1 := by
    rw [or1_toNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt]
  generalize hM2 : writeLog (writeLog Mt [(X + 8, 8, R 14 ||| BitVec.ofNat 64 hM &&& 1#64)])
    [(X + S + 8, 8, BitVec.ofNat 64 hn ||| 1#64)] = M2
  have hout : ∀ a, ¬ (X + 8 ≤ a ∧ a < X + 16) → ¬ (X + S + 8 ≤ a ∧ a < X + S + 16) → M2[a]? = Mt[a]? := by
    intro a h1 h2
    rw [← hM2, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have hag : ∀ a, vsaFoot ((X + 16, C.n.toNat) :: C.H) a → M2[a]? = V[a]? :=
    agree_of_words [X + 8, X + S + 8] (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨S + hM % 2, by rw [← hM2, rd_miss (by omega), read64_store_hit, hv1], hVr⟩
      · exact ⟨hn / 2 * 2 + 1, by rw [← hM2, read64_store_hit, hv2], hVn⟩)
      (fun a ha hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
        rw [hout a (by omega) (by omega)]
        exact T.agree a ha (by omega) (by omega))
  have H2 : PHeapAt M2 ((X + 16, C.n.toNat) :: C.H) top brkv (cs₁ ++ ⟨X, S, true⟩ :: cs₂) bins :=
    T.heap.transport_read fun a ha => (hag a ha.1).symm
  have F2 : RFrame C R M2 := by
    rw [← hM2]
    exact (T.frame.store (a := X + 8) (w := 8) (by omega)).store (a := X + S + 8) (w := 8) (by omega)
  refine rtail_fin O (F2.of_regs ?_ ?_ ?_) ?_ (by omega) H2 T.starts T.top_le (fun a ha => ?_)
    (fun k hk => ?_) <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact T.s0
  · rw [← hM2]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (T.pres a ha))
  · rw [hout _ (by omega) (by have := T.old_le; omega)]; exact T.data k hk

end VsaIris.VsaHeap
