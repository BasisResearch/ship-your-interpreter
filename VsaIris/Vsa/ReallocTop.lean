import VsaIris.Vsa.ReallocNext

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem realloc_topgrow {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (hXt : X + S = C.top0)
    (hroom : nb + 32 ≤ S + (brkv - C.top0)) (h16 : (R 16).toNat = S + (brkv - C.top0)) :
    AW C.live C.S C.Q 0x80005740#64 R Mt := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hts := HH.top_size
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 := by rw [D.nbok.eq]; unfold physSize; omega
  have hbt : C.top0 + (brkv - C.top0) = brkv := by have := HH.top_le; omega
  generalize hts' : brkv - C.top0 = ts at h16 hroom hbt hts
  subst hbt; clear hts'
  have Xk := (HB.chunkK hXm).lower; have G := globRgn C.H
  open_fields Xk; clear Xk_hdrv Xk_nhdrv Xk_next Xk_topal
  have hlt := D.lt
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  have hnext := (walk_next_of hw).2
  have hc2 : cs₂ = [] := by
    rcases hnext with ⟨_, h⟩ | ⟨d, cs₃, h1, h2⟩
    · exact h
    · exfalso
      have hdm : d ∈ chunks := by rw [hsp, h1]; simp
      have := HH.walk.chunk_bounds d hdm
      simp only at h2; omega
  subst hc2; clear hnext hw
  have Tk : Rgn (vsaFoot C.H) (X + nb + 8) 8 := ⟨fun k hk => .inr ⟨by
    show heapStart ≤ _; unfold heapStart; omega, by show _ < heapEnd; unfold heapEnd; omega, fun e he hin => by
      obtain ⟨c, hc, _, h3, h4⟩ := HH.live e (List.mem_cons_of_mem _ he)
      have := HH.walk.chunk_bounds c hc
      unfold InExt at hin
      omega⟩⟩
  have hXr := D.hdr
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  have ha2 := D.a2; have ha5 := D.a5; have hs0 := D.s0
  rgn_run O.live at 0x8000574c
  rw [show (2147505992#64 + BitVec.signExtend 64 (21#20 +++ 0#12) : BitVec 64) = 0x8001a748#64 by decide]
  rgn_run O.live at 0x8000575c
  rgn_ld [hXr]
  rgn_run O.live at 0x8000544c
  rw [show (2147593504#64).toNat = 2147593504 from rfl,
    show (R 12 + R 15 + 8#64).toNat = X + nb + 8 by rgn_arith,
    show (R 8 + 18446744073709551608#64).toNat = X + 8 by rgn_arith]
  have hT : (R 12 + R 15).toNat = X + nb := by rgn_arith
  have hXs := D.hsz; have hXl := D.hlow
  have hv1 : (R 16 - R 15 ||| 1#64).toNat = S + ts - nb + 1 := by
    rw [or1_toNat', BitVec.toNat_sub, h16, ha5]; omega
  have hv2 : (BitVec.ofNat 64 hdr0 &&& 1#64 ||| R 15).toNat = nb + hdr0 % 2 := by
    rw [BitVec.toNat_or, and1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hXlt, ha5]
    have hb : hdr0 % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · rw [show hdr0 % 2 = 0 by omega, Nat.zero_or]; omega
    · rw [h, Nat.or_comm, nat_or1]; omega
  generalize hM3 : writeLog (writeLog (writeLog Mt [(2147593504, 8, R 12 + R 15)])
    [(X + nb + 8, 8, R 16 - R 15 ||| 1#64)]) [(X + 8, 8, BitVec.ofNat 64 hdr0 &&& 1#64 ||| R 15)] = M3
  have hM3o : ∀ a, ¬ (0x8001ad20 ≤ a ∧ a < 0x8001ad28) → ¬ (X + nb + 8 ≤ a ∧ a < X + nb + 16) →
      ¬ (X + 8 ≤ a ∧ a < X + 16) → M3[a]? = Mt[a]? := fun a h1 h2 h3 => by
    rw [← hM3, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have H0 := Hp.heap
  rw [hsp] at H0
  have HG := H0.growTop (m' := M3) (d := nb - S) (by omega) (by omega) (h' := nb + hdr0 % 2)
    (by rw [← hM3]; rd_log [hv2]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by rw [hXr] at hr; cases hr; unfold prevInuse; rw [show (nb + hdr0 % 2) % 2 = hdr0 % 2 by omega])
    (by rw [← hM3]; unfold topAddr avAddr; rd_log [hT]; exact congrArg some (by omega))
    (by rw [← hM3, show X + S + (nb - S) + 8 = X + nb + 8 by omega]; rd_log [hv1]
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
  have oT := G.offStack Hp.disj (by omega); have oN := Tk.offStack Hp.disj (by omega)
  have oX := Xk_hdr.offStack Hp.disj (by omega); unfold mHead at oT oN oX
  have F3 : RFrame C R M3 := by
    rw [← hM3]
    exact ((D.frame.store (a := 0x8001ad20) (w := 8) (by omega)).store (a := X + nb + 8) (w := 8)
      (by omega)).store (a := X + 8) (w := 8) (by omega)
  refine repi O (F3.of_regs ?_ ?_ ?_) fun R' hR h10 => O.ok R' M3 ?_ <;> try carry_close
  have hp : (R' 10).toNat = X + 16 := by rw [h10]; carry_close [hs0]
  refine ⟨hR, ?_, ?_, ⟨X + nb, C.top0 + ts, cs₁ ++ [⟨X, nb, true⟩], bins, ?_, ?_⟩, fun a ha => ?_,
    fun k hk => ?_⟩ <;> try rw [hp]
  · exact Hr.fresh_of_block hst
  · omega
  · exact Hr
  · rw [D.nbok.eq] at hnbv ⊢; omega
  · rw [← hM3]; exact pres_log _ (pres_log _ (pres_log _ Hp.pres)) a ha
  · rw [hM3o _ (by omega) (by have := D.addr; have := Hp.grow; omega) (by omega),
      show X + 16 + k = B.p + k by rw [D.addr]]
    exact Hp.data k hk

end VsaIris.VsaHeap
