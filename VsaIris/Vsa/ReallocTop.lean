import VsaIris.Vsa.ReallocNext

/-!
# `_realloc_r` into the top

A chunk just below the top that, with the top, holds the request and
`MINSIZE` more grows into the top in place (`0x80005740`,
`PHeapAt.growTop`): the top moves up past the request's chunk, and the
block is returned unmoved.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **Grow into the top** (`0x80005740`): `X` ends at the top and `S` plus the
top's size is at least `nb + 32`. -/
theorem realloc_topgrow {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (hXt : X + S = C.top0)
    (hroom : nb + 32 ≤ S + (brkv - C.top0)) (h16 : (R 16).toNat = S + (brkv - C.top0)) :
    AW C.live C.S C.Q 0x80005740#64 R Mt := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hXb := HH.walk.chunk_bounds _ hXm
  have hx16 := HH.aligned.1 _ hXm; have hS16 := (walk_sizes HH.walk _ hXm).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  simp only at hXb hx16 hS16
  unfold heapStart at hXb; unfold heapEnd at hbrk
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 := by rw [D.nbok.eq]; unfold physSize; omega
  have hbt : C.top0 + (brkv - C.top0) = brkv := by omega
  generalize hts' : brkv - C.top0 = ts at h16 hroom hbt hts
  subst hbt
  have hlt := D.lt
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  -- `X` is the last chunk
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  have hc2 : cs₂ = [] := by
    rcases hnext with ⟨_, h⟩ | ⟨d, cs₃, h1, h2⟩
    · exact h
    · exfalso
      have hdm : d ∈ chunks := by rw [hsp, h1]; simp
      have := HH.walk.chunk_bounds d hdm
      simp only at h2; omega
  subst hc2
  -- the top chunk's bytes are footprint
  have htf : ∀ a, C.top0 + 8 ≤ a → a < (C.top0 + ts) → vsaFoot C.H a := fun a h1 h2 => by
    refine .inr ⟨by show heapStart ≤ a; unfold heapStart; omega, by show a < heapEnd; unfold heapEnd; omega,
      fun e he hin => ?_⟩
    obtain ⟨c, hc, _, h3, h4⟩ := HH.live e (List.mem_cons_of_mem _ he)
    have := HH.walk.chunk_bounds c hc
    unfold InExt at hin
    omega
  have hXr := D.hdr; have hXs := D.hsz; have hXl := D.hlow
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  have ha2 := D.a2; have ha5 := D.a5; have hs0 := D.s0
  have hT : (R 12 + R 15).toNat = X + nb := by rw [BitVec.toNat_add, ha2, ha5]; omega
  have hsz' : (R 16 - R 15).toNat = S + ((C.top0 + ts) - C.top0) - nb := by rw [BitVec.toNat_sub, h16, ha5]; omega
  have hgT : ∀ k, k < 8 → vsaFoot C.H (0x8001ad20 + k) := fun k hk => .inl (by unfold allocGlobal InRange; omega)
  have hfN : ∀ k, k < 8 → vsaFoot C.H (X + nb + 8 + k) := fun k hk => htf _ (by omega) (by omega)
  have hfX : ∀ k, k < 8 → vsaFoot C.H (X + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header HB (.inr ⟨_, hXm, rfl⟩) k hk)
  have oT := off_stack_of Hp.disj hgT
  have oN := off_stack_of Hp.disj hfN
  have oX := off_stack_of Hp.disj hfX
  refine st_80005740 O.live ?_
  refine st_80005744 O.live ?_
  refine st_80005748 O.live ?_
  have eT : ((0x80005748#64) + (sign_extend (m := 64) ((0x00015#20) +++ (0x000#12))) +
      sign_extend (m := 64) (0x5d8#12)).toNat = 0x8001ad20 := by decide
  refine st_8000574c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eT]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eT]; exact O.foot hgT) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eT]
  refine st_80005750 O.live ?_
  have eN : (R 12 + R 15 + sign_extend (m := 64) (0x008#12)).toNat = X + nb + 8 := by
    rw [BitVec.toNat_add, hT]; simp; omega
  have sN : StOK (X + nb + 8) 8 := by
    have h1 : (X + nb + 8) % 8 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_add
      (Nat.dvd_trans (by decide : 8 ∣ 16) (Nat.dvd_of_mod_eq_zero hx16))
      (Nat.dvd_trans (by decide : 8 ∣ 16) (Nat.dvd_of_mod_eq_zero hnbv.2))) (Nat.dvd_refl 8))
    unfold StOK Vsa.Sim.tohostAddr
    exact ⟨by omega, by omega, by omega, h1⟩
  refine st_80005754 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]; exact sN)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]; exact O.foot hfN) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eN]
  have eX : (R 8 + sign_extend (m := 64) (0xff8#12)).toNat = X + 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub hs0 8 (by omega) (by omega)]; omega
  have hXr2 : read64 (writeLog (writeLog Mt [(0x8001ad20, 8, R 12 + R 15)])
      [(X + nb + 8, 8, R 16 - R 15 ||| sign_extend (m := 64) (0x001#12))]) (X + 8) = some hdr0 := by
    rw [rd_miss (by omega), rd_miss (by omega)]; exact hXr
  refine st_80005758 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eX]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eX]; exact O.foot hfX) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eX, ldv_at hXr2 _ rfl]
  refine st_8000575c O.live ?_
  refine st_80005760 O.live ?_
  refine st_80005764 O.live ?_
  refine st_80005768 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eX]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eX]; exact O.foot hfX) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eX]
  -- the grown heap
  have hv1 : (R 16 - R 15 ||| sign_extend (m := 64) (0x001#12)).toNat = S + ts - nb + 1 := by
    rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl, or1_toNat', hsz']; omega
  have hv2 : (BitVec.ofNat 64 hdr0 &&& sign_extend (m := 64) (0x001#12) ||| R 15).toNat = nb + hdr0 % 2 := by
    rw [BitVec.toNat_or, show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl, and1_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hXlt, ha5]
    have hb : hdr0 % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · rw [show hdr0 % 2 = 0 by omega, Nat.zero_or]; omega
    · rw [h, Nat.or_comm, nat_or1]; omega
  generalize hM3 : writeLog (writeLog (writeLog Mt [(2147593504, 8, R 12 + R 15)])
    [(X + nb + 8, 8, R 16 - R 15 ||| sign_extend (m := 64) (0x001#12))])
    [(X + 8, 8, BitVec.ofNat 64 hdr0 &&& sign_extend (m := 64) (0x001#12) ||| R 15)] = M3
  have hM3o : ∀ a, ¬ (0x8001ad20 ≤ a ∧ a < 0x8001ad28) → ¬ (X + nb + 8 ≤ a ∧ a < X + nb + 16) →
      ¬ (X + 8 ≤ a ∧ a < X + 16) → M3[a]? = Mt[a]? := fun a h1 h2 h3 => by
    rw [← hM3, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have H0 := Hp.heap
  rw [hsp] at H0
  have HG := H0.growTop (m' := M3) (d := nb - S) (by omega) (by omega) (h' := nb + hdr0 % 2)
    (by rw [← hM3, read64_store_hit, hv2]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by rw [hXr] at hr; cases hr; unfold prevInuse; rw [show (nb + hdr0 % 2) % 2 = hdr0 % 2 by omega])
    (by
      rw [← hM3]; unfold topAddr avAddr
      rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, hT]
      exact congrArg some (by omega))
    (by
      rw [← hM3, rd_miss (by omega), show X + S + (nb - S) + 8 = X + nb + 8 by omega, read64_store_hit, hv1]
      exact congrArg some (by omega))
    (fun w hw h1 h2 h3 => by
      unfold topAddr avAddr at h2
      exact hM3o w (by omega) (by omega) (by omega))
  rw [show X + S + (nb - S) = X + nb by omega, show S + (nb - S) = nb by omega] at HG
  have Hr := HG.reblock (c := ⟨X, nb, true⟩) (by simp) rfl D.addr (n' := C.n.toNat) (by simp only; omega)
  rw [← D.addr] at Hr
  have hst : Starts ((X + 16, C.n.toNat) :: C.H) := by rw [D.addr]; exact Hp.starts
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; have := D.addr; omega)
    subst this; simpa using hc0n
  have F3 : RFrame C R M3 := by
    rw [← hM3]
    exact ((D.frame.store (a := 0x8001ad20) (w := 8) (by omega)).store (a := X + nb + 8) (w := 8)
      (by omega)).store (a := X + 8) (w := 8) (by omega)
  sx_run [12] O.live at 0x80005770
  refine st_80005770 O.live ?_
  refine st_80005774 O.live ?_
  refine repi O (F3.of_regs ?_ ?_ ?_) fun R' hR h10 => O.ok R' M3 ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hp : (R' 10).toNat = X + 16 := by
    rw [h10]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      addr_add hs0 0 (by omega)]
  refine ⟨hR, ?_, ?_, ⟨X + nb, C.top0 + ts, cs₁ ++ [⟨X, nb, true⟩], bins, ?_, ?_⟩, fun a ha => ?_,
    fun k hk => ?_⟩ <;> try rw [hp]
  · exact Hr.fresh_of_block hst
  · omega
  · exact Hr
  · rw [D.nbok.eq] at hnbv ⊢; omega
  · rw [← hM3]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha)))
  · rw [hM3o _ (by omega) (by have := D.addr; have := Hp.grow; omega) (by omega),
      show X + 16 + k = B.p + k by rw [D.addr]]
    exact Hp.data k hk

end VsaIris.VsaHeap
