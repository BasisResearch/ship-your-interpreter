import VsaIris.Vsa.ReallocPrevT

/-!
# `_realloc_r`'s growth dispatch

A chunk too small for the request (`RD`, `0x800052f0`) is dispatched on its
neighbours: the top after it (`realloc_topgrow`, or with a free predecessor
`realloc_pvT`), a free successor (`realloc_next`, or with a free predecessor
`realloc_pvXN`), a free predecessor alone (`realloc_pvX`), and otherwise a
fresh block (`realloc_mal`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `RD` through register writes that keep its registers. -/
theorem RD.of_regs {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {R' : Nat → BitVec 64}
    (h2 : R' 2 = R 2) (h8 : R' 8 = R 8) (h9 : R' 9 = R 9) (h11 : R' 11 = R 11)
    (h12 : R' 12 = R 12) (h14 : R' 14 = R 14) (h15 : R' 15 = R 15) (h18 : R' 18 = R 18)
    (h19 : R' 19 = R 19) : RD C B R' Mt brkv chunks bins X S hdr0 nb where
  frame := D.frame.of_regs h2 h18 h19
  heap := D.heap
  nbok := D.nbok
  nb31 := D.nb31
  mem := D.mem
  addr := D.addr
  hdr := D.hdr
  hsz := D.hsz
  hlow := D.hlow
  lt := D.lt
  s0 := by rw [h8]; exact D.s0
  s1 := by rw [h9]; exact D.s1
  a1 := by rw [h11]; exact D.a1
  a2 := by rw [h12]; exact D.a2
  a4 := by rw [h14]; exact D.a4
  a5 := by rw [h15]; exact D.a5

/-- `RD` through register writes, the kept registers read off `upd`. -/
macro "rd_regs " D:term : tactic => `(tactic| (refine RD.of_regs $D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))

/-- **The predecessor alone** (`0x80005348`): `S + ps` holds the request →
`realloc_pvX`, else a fresh block. -/
theorem grow_pvX {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (h6 : (R 6).toNat = P) (h17 : (R 17).toNat = ps) :
    AW C.live C.S C.Q 0x80005348#64 R Mt := by
  have HH := D.heap.heap.heap.heap
  have hXb := HH.walk.chunk_bounds _ D.mem
  have hps := PV.pend
  have hPb := HH.walk.chunk_bounds ⟨P, ps, false⟩ (by rw [hsp]; simp)
  have hbrk := HH.brk_le; have htle := HH.top_le
  simp only at hXb hPb
  unfold heapStart heapEnd at *
  have hnb31 := D.nb31
  have hS : (R 14 + R 17).toNat = ps + S := by rw [BitVec.toNat_add, D.a4, h17]; omega
  refine st_80005348 O.live (st_8000534c O.live (fun hc => ?_) (fun _ => ?_)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
  · rw [toInt_small D.a5 (by omega), toInt_small hS (by omega), Int.ofNat_le] at hc
    exact realloc_pvX O (by rd_regs D) hsp PV hc h6 (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hS)
  · exact realloc_mal O (by rd_regs D)

/-- **The free predecessor** of `X` when its header lacks `PREV_INUSE`: its
bin place (`FPv`) and its header, whose size bits are `ps`. -/
theorem grow_prev {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ rest : List Chunk}
    (hsp : chunks = cs₁ ++ ⟨X, S, true⟩ :: rest) (hpf : hdr0 % 2 = 0) :
    ∃ cs₀ P ps i pre post predP succP hh, cs₁ = cs₀ ++ [⟨P, ps, false⟩] ∧
      FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP ∧
      read64 Mt (P + 8) = some hh ∧ hh / 4 * 4 = ps := by
  have H0 := D.heap.heap
  rw [hsp] at H0
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, PV⟩ := pv_of_heap (C := C') H0 D.hdr hpf
  have hs := PV.split
  subst hs
  obtain ⟨hh, hhr, hhs, hhl⟩ := walk_header H0.heap.heap.walk ⟨P, ps, false⟩ (by simp)
  simp only at hhr hhs
  refine ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, ?_⟩
  unfold chunkSize at hhs; omega

/-- **Loading the predecessor** (`ld t1,-16(s0)`, `sub t1,a2,t1`,
`ld a7,8(t1)`, `andi a7,a7,-4`, at each of the dispatch's three sites):
`t1 := P`, `a7 := ps`, the other registers kept. -/
theorem prev_load {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP hh : Nat}
    (hsp : ∃ rest, chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hhr : read64 Mt (P + 8) = some hh) (hhs : hh / 4 * 4 = ps)
    {pc1 pc2 pc3 pc4 pc5 : BitVec 64}
    (st1 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, LdOK ((R 8) + sign_extend (m := 64) (0xff0#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) (0xff0#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc2 (upd R 6 (ldv .ld Mt ((R 8) + sign_extend (m := 64) (0xff0#12)).toNat)) Mt →
      AW C.live C.S C.Q pc1 R Mt)
    (st2 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, AW C.live C.S C.Q pc3 (upd R 6 ((R 12) - (R 6))) Mt →
      AW C.live C.S C.Q pc2 R Mt)
    (st3 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, LdOK ((R 6) + sign_extend (m := 64) (0x008#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 6) + sign_extend (m := 64) (0x008#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc4 (upd R 17 (ldv .ld Mt ((R 6) + sign_extend (m := 64) (0x008#12)).toNat)) Mt →
      AW C.live C.S C.Q pc3 R Mt)
    (st4 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      AW C.live C.S C.Q pc5 (upd R 17 ((R 17) &&& sign_extend (m := 64) (0xffc#12))) Mt →
      AW C.live C.S C.Q pc4 R Mt)
    (hk : ∀ R', (∀ k, k ≠ 6 → k ≠ 17 → R' k = R k) → (R' 6).toNat = P → (R' 17).toNat = ps →
      AW C.live C.S C.Q pc5 R' Mt) :
    AW C.live C.S C.Q pc1 R Mt := by
  obtain ⟨rest, hsp⟩ := hsp
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  rw [hsp] at HB HH
  have hPm : (⟨P, ps, false⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest := by simp
  have hPb := HH.walk.chunk_bounds _ hPm
  have hp16 := HH.aligned.1 _ hPm
  have hps := (walk_sizes HH.walk _ hPm).1
  have hbrk := HH.brk_le; have htle := HH.top_le
  simp only at hPb hp16 hps
  unfold heapStart heapEnd at *
  have hpend := PV.pend
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hfX : ∀ k, k < 8 → vsaFoot C.H (X + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := (foot_free HB hPm rfl).2 k hk; simp only at this; rwa [hpend] at this)
  have hfP : ∀ k, k < 8 → vsaFoot C.H (P + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header HB (.inr ⟨_, hPm, rfl⟩) k hk)
  have hXv := D.s0
  have e1 : (R 8 + sign_extend (m := 64) (0xff0#12)).toNat = X := by
    sx_norm; rw [BitVec.toNat_add, hXv]; simp; omega
  have hfl := Vsa.Sim.read64_lt _ _ _ PV.foot
  have hhl := Vsa.Sim.read64_lt _ _ _ hhr
  refine st1 (by rw [e1]; unfold LdOK Vsa.Sim.tohostAddr; omega) (by rw [e1]; exact O.foot hfX) ?_
  rw [e1, ldv_at PV.foot _ rfl]
  refine st2 ?_
  have e2 : (R 12 - BitVec.ofNat 64 ps + sign_extend (m := 64) (0x008#12)).toNat = P + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, D.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfl]
    simp; omega
  refine st3 (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e2]
                 unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e2]; exact O.foot hfP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [e2, ldv_at hhr _ rfl]
  refine st4 (hk _ (fun k h6 h17 => ?_) ?_ ?_)
  · simp only [upd_apply, h6, h17, if_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.toNat_sub, D.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfl]; omega
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhl, hhs]

end VsaIris.VsaHeap
