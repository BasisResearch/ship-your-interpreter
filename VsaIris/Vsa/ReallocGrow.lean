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

/-- `PREV_INUSE` clear in `hdr0` once `andi a3,a3,1` read zero. -/
theorem prev_bit {x : BitVec 64} {h : Nat} (hx : x.toNat = h)
    (hc : ¬ (x &&& sign_extend (m := 64) (0x001#12) ≠ 0#64)) : h % 2 = 0 := by
  have := congrArg BitVec.toNat (Classical.not_not.mp hc)
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl, and1_toNat, hx] at this
  exact this

/-- **The successor in use** (`0x80005464`): with the predecessor free,
`grow_pvX`; else a fresh block. -/
theorem grow_used {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ rest : List Chunk}
    (hsp : chunks = cs₁ ++ ⟨X, S, true⟩ :: rest) (h13 : (R 13).toNat = hdr0) :
    AW C.live C.S C.Q 0x80005464#64 R Mt := by
  refine st_80005464 O.live (st_80005468 O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ := grow_prev D hsp (prev_bit h13 hc)
  refine prev_load O (by rd_regs D) ⟨rest, hsp⟩ PV hhr hhs (st_8000546c O.live) (st_80005470 O.live)
    (st_80005474 O.live) (st_80005478 O.live) fun R' hK h6 h17 => st_8000547c O.live ?_
  have D' : RD C B R' Mt brkv chunks bins X S hdr0 nb := by
    refine RD.of_regs D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hK _ (by decide) (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  exact grow_pvX O D' hsp PV h6 h17

/-- **The top after the old chunk** (`0x800054dc`): grow into the top
(`realloc_topgrow`), or with a free predecessor take it and the top
(`realloc_pvT`) or it alone (`grow_pvX`); else a fresh block. -/
theorem grow_top {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ : List Chunk}
    (hsp : chunks = cs₁ ++ [⟨X, S, true⟩]) (hXt : X + S = C.top0)
    (h13 : (R 13).toNat = hdr0) (h10 : (R 10).toNat = brkv - C.top0 + 1) :
    AW C.live C.S C.Q 0x800054dc#64 R Mt := by
  have HB := D.heap.heap.heap
  have HH := HB.heap
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  have ht16 := HH.aligned.2; have hbp := D.heap.heap.brk_page
  unfold heapEnd at hbrk
  have hXb := HH.walk.chunk_bounds _ D.mem
  simp only at hXb
  have hnb31 := D.nb31
  have hlt := D.lt
  obtain ⟨ts, rfl⟩ : ∃ ts, brkv = C.top0 + ts := ⟨brkv - C.top0, by omega⟩
  rw [Nat.add_sub_cancel_left] at h10
  have e0 : (R 10 &&& sign_extend (m := 64) (0xffc#12)).toNat = ts := by
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, h10]; omega
  have e16 : ((R 10 &&& sign_extend (m := 64) (0xffc#12)) + R 14).toNat = ts + S := by
    rw [BitVec.toNat_add, e0, D.a4]; omega
  have e28 : (R 15 + sign_extend (m := 64) (0x020#12)).toNat = nb + 32 := by
    rw [BitVec.toNat_add, D.a5]; simp; omega
  refine st_800054dc O.live (st_800054e0 O.live (st_800054e4 O.live (st_800054e8 O.live
    (fun hc => ?_) (fun hc => ?_)))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc <;>
    rw [toInt_small e28 (by omega), toInt_small e16 (by omega)] at hc
  · -- into the top
    refine realloc_topgrow O (by rd_regs D) hXt (by omega) ?_
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e16]; omega
  refine st_800054ec O.live (st_800054f0 O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc' => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc'
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ :=
    grow_prev D (rest := []) hsp (prev_bit h13 hc')
  have hPb := HH.walk.chunk_bounds ⟨P, ps, false⟩ (by rw [hsp]; simp)
  simp only at hPb
  have hpend := PV.pend
  refine prev_load O (by rd_regs D) ⟨[], hsp⟩ PV hhr hhs (st_800054f4 O.live) (st_800054f8 O.live)
    (st_800054fc O.live) (st_80005500 O.live) fun R' hK h6 h17 => ?_
  have k10 := hK 10 (by decide) (by decide); have k14 := hK 14 (by decide) (by decide)
  have k28 := hK 28 (by decide) (by decide)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at k10 k14 k28
  have e10 : (R' 10 + R' 17).toNat = ts + ps := by rw [BitVec.toNat_add, k10, e0, h17]; omega
  have e16' : (R' 10 + R' 17 + R' 14).toNat = ts + ps + S := by rw [BitVec.toNat_add, e10, k14, D.a4]; omega
  have e28' : (R' 28).toNat = nb + 32 := by rw [k28, e28]
  refine st_80005504 O.live (st_80005508 O.live (st_8000550c O.live (fun hc'' => ?_) (fun hc'' => ?_))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc'' <;>
    rw [toInt_small e28' (by omega), toInt_small e16' (by omega)] at hc''
  all_goals
    have D' : RD C B (upd (upd R' 10 (R' 10 + R' 17)) 16 (R' 10 + R' 17 + R' 14)) Mt (C.top0 + ts)
        chunks bins X S hdr0 nb := by
      refine RD.of_regs D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false] <;>
        (rw [hK _ (by decide) (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  · exact grow_pvX O D' (rest := []) hsp PV (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h6)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)
  · refine realloc_pvT O D' hsp PV hXt (by omega) ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h6
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e16']; omega

/-- **A free successor** (`0x80005318`, `a0` its header): absorb it
(`realloc_next`), or with a free predecessor take both (`realloc_pvXN`) or the
predecessor alone (`grow_pvX`); else a fresh block. -/
theorem grow_free {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns hn : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ cs₃ : List Chunk}
    (hsp : chunks = cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    (h13 : (R 13).toNat = hdr0) (h10 : (R 10).toNat = hn) (hns : hn / 4 * 4 = ns)
    (h16 : (R 16).toNat = X + S) :
    AW C.live C.S C.Q 0x80005318#64 R Mt := by
  have HB := D.heap.heap.heap
  have HH := HB.heap
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapEnd at hbrk
  have hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
  have hNb := HH.walk.chunk_bounds _ hN
  simp only at hNb
  have hnb31 := D.nb31
  have e0 : (R 10 &&& sign_extend (m := 64) (0xffc#12)).toNat = ns := by
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, h10, hns]
  have e17 : (R 14 + (R 10 &&& sign_extend (m := 64) (0xffc#12))).toNat = S + ns := by
    rw [BitVec.toNat_add, e0, D.a4]; omega
  refine st_80005318 O.live (st_8000531c O.live (st_80005320 O.live (fun hc => ?_) (fun hc => ?_))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc <;>
    rw [toInt_small D.a5 (by omega), toInt_small e17 (by omega), Int.ofNat_le] at hc
  · -- the successor holds the rest
    refine realloc_next O (by rd_regs D) hN hc ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h16
    · exact e17
  refine st_80005324 O.live (st_80005328 O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc' => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc'
  have hpf := prev_bit h13 hc'
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ := grow_prev D hsp hpf
  have hPb := HH.walk.chunk_bounds ⟨P, ps, false⟩ (by rw [hsp]; simp)
  simp only at hPb
  have hpend := PV.pend
  refine prev_load O (by rd_regs D) ⟨_, hsp⟩ PV hhr hhs (st_8000532c O.live) (st_80005330 O.live)
    (st_80005334 O.live) (st_80005338 O.live) fun R' hK h6 h17 => ?_
  have k10 := hK 10 (by decide) (by decide); have k14 := hK 14 (by decide) (by decide)
  have k16 := hK 16 (by decide) (by decide); have k15 := hK 15 (by decide) (by decide)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at k10 k14 k16 k15
  have e10 : (R' 10 + R' 17).toNat = ns + ps := by rw [BitVec.toNat_add, k10, e0, h17]; omega
  have e13 : (R' 10 + R' 17 + R' 14).toNat = ps + (S + ns) := by
    rw [BitVec.toNat_add, e10, k14, D.a4]; omega
  have e15 : (R' 15).toNat = nb := by rw [k15, D.a5]
  refine st_8000533c O.live (st_80005340 O.live (st_80005344 O.live (fun hc'' => ?_) (fun hc'' => ?_))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc'' <;>
    rw [toInt_small e15 (by omega), toInt_small e13 (by omega), Int.ofNat_le] at hc''
  all_goals
    have D' : RD C B (upd (upd R' 10 (R' 10 + R' 17)) 13 (R' 10 + R' 17 + R' 14)) Mt brkv
        chunks bins X S hdr0 nb := by
      refine RD.of_regs D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false] <;>
        (rw [hK _ (by decide) (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  · -- both neighbours
    obtain ⟨iN, preN, postN, pred, succ, FB⟩ := free_bin_at D.heap.heap hN rfl
    refine realloc_pvXN O D' hsp hpf FB hc'' ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h6
    · exact e13
    · rw [k16, h16]
  · exact grow_pvX O D' hsp PV (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h6)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)

/-- **The growth dispatch** (`0x800052f0`): read the top pointer and the
header after `X`; the top (`grow_top`), an in-use successor (`grow_used`) or a
free one (`grow_free`). -/
theorem realloc_grow {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (h13 : (R 13).toNat = hdr0) :
    AW C.live C.S C.Q 0x800052f0#64 R Mt := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hXb := HH.walk.chunk_bounds _ hXm
  have hx16 := HH.aligned.1 _ hXm; have hS16 := (walk_sizes HH.walk _ hXm).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  simp only at hXb hx16 hS16
  unfold heapStart heapEnd at *
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  obtain ⟨⟨hn, hnr, _⟩, hnext⟩ := walk_next_of hw
  simp only at hnr hnext
  have hnl := Vsa.Sim.read64_lt _ _ _ hnr
  -- the top pointer
  have hgT : ∀ k, k < 8 → vsaFoot C.H (0x8001ad20 + k) := fun k hk => .inl (by unfold allocGlobal InRange; omega)
  have eT : ((0x800052f0#64) + (sign_extend (m := 64) ((0x00016#20) +++ (0x000#12))) +
      sign_extend (m := 64) (0xa30#12)).toNat = 0x8001ad20 := by decide
  have htp : read64 Mt 0x8001ad20 = some C.top0 := HH.top_ptr
  refine st_800052f0 O.live ?_
  refine st_800052f4 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; rw [eT]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; rw [eT]; exact O.foot hgT) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true]
  rw [eT, ldv_at htp _ rfl]
  refine st_800052f8 O.live ?_
  -- the header after `X`
  have hbE : X + S = C.top0 ∨ ∃ c ∈ chunks, c.addr = X + S := by
    rcases hnext with ⟨h1, _⟩ | ⟨d, cs₃, h1, h2⟩
    · exact .inl h1
    · exact .inr ⟨d, by rw [hsp, h1]; simp, h2⟩
  have hfE : ∀ k, k < 8 → vsaFoot C.H (X + S + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (foot_header HB hbE k hk)
  have e16 : (R 12 + R 14).toNat = X + S := by rw [BitVec.toNat_add, D.a2, D.a4]; omega
  have eE : (R 12 + R 14 + sign_extend (m := 64) (0x008#12)).toNat = X + S + 8 := by
    rw [BitVec.toNat_add, e16]; simp; omega
  refine st_800052fc O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eE]
        unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eE]; exact O.foot hfE) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eE, ldv_at hnr _ rfl]
  have hv10 : (BitVec.ofNat 64 hn).toNat = hn := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnl]
  have htl : C.top0 < 2 ^ 64 := by omega
  refine st_80005300 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- the top
    have hXt : X + S = C.top0 := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl, e16] at this; omega
    rcases hnext with ⟨_, rfl⟩ | ⟨d, cs₃, rfl, h2⟩
    · have hth := HH.top_header
      rw [← hXt, hnr] at hth
      cases hth
      refine grow_top O (by rd_regs D) hsp hXt ?_ ?_ <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact h13
      · rw [hv10, hXt]
    · exfalso
      have := HH.walk.chunk_bounds d (by rw [hsp]; simp)
      omega
  · -- a chunk after `X`
    rcases hnext with ⟨h1, _⟩ | ⟨d, cs₃, rfl, h2⟩
    · exact absurd (by rw [← h1]; exact BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), e16])) hc
    obtain ⟨dA, ns, b⟩ := d
    simp only at h2
    subst h2
    have hdm : (⟨X + S, ns, b⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
    obtain ⟨hd, hdr', hds, hdl⟩ := walk_header HH.walk _ hdm
    simp only at hdr' hds
    rw [hnr] at hdr'
    cases hdr'
    have hdb := HH.walk.chunk_bounds _ hdm
    simp only at hdb
    have hw2 := HH.walk
    rw [hsp] at hw2
    obtain ⟨⟨hnn, hnnr, hnnp⟩, hnext2⟩ :=
      walk_next_of (cs₁ := cs₁ ++ [⟨X, S, true⟩]) (by simpa using hw2)
    simp only at hnnr hnnp hnext2
    have hbN : X + S + ns = C.top0 ∨ ∃ c ∈ chunks, c.addr = X + S + ns := by
      rcases hnext2 with ⟨h1, _⟩ | ⟨d, cs₄, h1, h3⟩
      · exact .inl h1
      · exact .inr ⟨d, by rw [hsp, h1]; simp, h3⟩
    have hfN : ∀ k, k < 8 → vsaFoot C.H (X + S + ns + 8 + k) := fun k hk =>
      vsaFoot_cons_sub _ (foot_header HB hbN k hk)
    have e17 : (R 12 + R 14 + (BitVec.ofNat 64 hn &&& sign_extend (m := 64) (0xffe#12))).toNat =
        X + S + ns := by
      rw [BitVec.toNat_add, e16, and_m2_toNat, hv10]; unfold chunkSize at hds; omega
    have eN : (R 12 + R 14 + (BitVec.ofNat 64 hn &&& sign_extend (m := 64) (0xffe#12)) +
        sign_extend (m := 64) (0x008#12)).toNat = X + S + ns + 8 := by
      rw [BitVec.toNat_add, e17]; simp; omega
    have hnnl := Vsa.Sim.read64_lt _ _ _ hnnr
    refine st_80005304 O.live (st_80005308 O.live ?_)
    refine st_8000530c O.live
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]
          unfold LdOK Vsa.Sim.tohostAddr; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]; exact O.foot hfN) ?_
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [eN, ldv_at hnnr _ rfl]
    refine st_80005310 O.live (st_80005314 O.live (fun hu => ?_) (fun hu => ?_)) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hu
    · exact grow_used O (by rd_regs D) (rest := ⟨X + S, ns, b⟩ :: cs₃) (by rw [hsp]; try simp)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h13)
    · have hb : b = false := by
        have := prev_bit (x := BitVec.ofNat 64 hnn) (h := hnn)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnnl]) hu
        unfold prevInuse at hnnp; rw [← hnnp]; simp [this]
      subst hb
      refine grow_free O (by rd_regs D) (cs₁ := cs₁) (cs₃ := cs₃) (by rw [hsp]; try simp) ?_ ?_ hds ?_ <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact h13
      · exact hv10
      · exact e16

end VsaIris.VsaHeap
