import VsaIris.Vsa.ReallocPrevT
import VsaIris.Vsa.Carry

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

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

macro "rd_regs " D:term : tactic => `(tactic| (refine RD.of_regs $D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))

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
  refine (step% st 0x80005348) O.live ((step% st 0x8000534c) O.live (fun hc => ?_) (fun _ => ?_)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
  · rw [toInt_small D.a5 (by omega), toInt_small hS (by omega), Int.ofNat_le] at hc
    exact realloc_pvX O (by rd_regs D) hsp PV hc h6 (by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hS)
  · exact realloc_mal O (by rd_regs D)

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
  have HB := D.heap.heap.heap
  rw [hsp] at HB
  have hPm : (⟨P, ps, false⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest := by simp
  have K := HB.chunkK hPm
  have K_hi := K.hi; have K_lo := K.lo; have K_sz := K.sz32; have K_room := K.room; have K_brk := K.brk
  simp only at K_hi K_lo K_sz
  have rP := (HB.freeSpan hPm rfl).lower; simp only at rP
  have hpend := PV.pend; have h8 := D.s0; have h12 := D.a2
  have hfl := Vsa.Sim.read64_lt _ _ _ PV.foot
  have e6 : (R 12 - BitVec.ofNat 64 ps).toNat = P := by
    rw [BitVec.toNat_sub, D.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfl]; omega
  refine st1 (by rgn_side) (by rgn_side) ?_
  rgn_ld [PV.foot]
  refine st2 (st3 (by rgn_side) (by rgn_side) ?_)
  rgn_ld [hhr]
  refine st4 (hk _ (fun k h6 h17 => ?_) ?_ ?_)
  · simp only [upd_apply, h6, h17, if_false]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact e6
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hhr), hhs]

theorem prev_bit {x : BitVec 64} {h : Nat} (hx : x.toNat = h)
    (hc : ¬ (x &&& sign_extend (m := 64) (0x001#12) ≠ 0#64)) : h % 2 = 0 := by
  have := congrArg BitVec.toNat (Classical.not_not.mp hc)
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from rfl, and1_toNat, hx] at this
  exact this

theorem grow_used {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ rest : List Chunk}
    (hsp : chunks = cs₁ ++ ⟨X, S, true⟩ :: rest) (h13 : (R 13).toNat = hdr0) :
    AW C.live C.S C.Q 0x80005464#64 R Mt := by
  refine (step% st 0x80005464) O.live ((step% st 0x80005468) O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ := grow_prev D hsp (prev_bit h13 hc)
  refine prev_load O (by rd_regs D) ⟨rest, hsp⟩ PV hhr hhs ((step% st 0x8000546c) O.live) ((step% st 0x80005470) O.live)
    ((step% st 0x80005474) O.live) ((step% st 0x80005478) O.live) fun R' hK h6 h17 => (step% st 0x8000547c) O.live ?_
  have D' : RD C B R' Mt brkv chunks bins X S hdr0 nb := by
    refine RD.of_regs D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hK _ (by decide) (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  exact grow_pvX O D' hsp PV h6 h17

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
  refine (step% st 0x800054dc) O.live ((step% st 0x800054e0) O.live ((step% st 0x800054e4) O.live ((step% st 0x800054e8) O.live
    (fun hc => ?_) (fun hc => ?_)))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc <;>
    rw [toInt_small e28 (by omega), toInt_small e16 (by omega)] at hc
  ·
    refine realloc_topgrow O (by rd_regs D) hXt (by omega) ?_
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e16]; omega
  refine (step% st 0x800054ec) O.live ((step% st 0x800054f0) O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc' => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc'
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ :=
    grow_prev D (rest := []) hsp (prev_bit h13 hc')
  have hPb := HH.walk.chunk_bounds ⟨P, ps, false⟩ (by rw [hsp]; simp)
  simp only at hPb
  have hpend := PV.pend
  refine prev_load O (by rd_regs D) ⟨[], hsp⟩ PV hhr hhs ((step% st 0x800054f4) O.live) ((step% st 0x800054f8) O.live)
    ((step% st 0x800054fc) O.live) ((step% st 0x80005500) O.live) fun R' hK h6 h17 => ?_
  have k10 := hK 10 (by decide) (by decide); have k14 := hK 14 (by decide) (by decide)
  have k28 := hK 28 (by decide) (by decide)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at k10 k14 k28
  have e10 : (R' 10 + R' 17).toNat = ts + ps := by rw [BitVec.toNat_add, k10, e0, h17]; omega
  have e16' : (R' 10 + R' 17 + R' 14).toNat = ts + ps + S := by rw [BitVec.toNat_add, e10, k14, D.a4]; omega
  have e28' : (R' 28).toNat = nb + 32 := by rw [k28, e28]
  refine (step% st 0x80005504) O.live ((step% st 0x80005508) O.live ((step% st 0x8000550c) O.live (fun hc'' => ?_) (fun hc'' => ?_))) <;>
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
  refine (step% st 0x80005318) O.live ((step% st 0x8000531c) O.live ((step% st 0x80005320) O.live (fun hc => ?_) (fun hc => ?_))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc <;>
    rw [toInt_small D.a5 (by omega), toInt_small e17 (by omega), Int.ofNat_le] at hc
  ·
    refine realloc_next O (by rd_regs D) hN hc ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h16
    · exact e17
  refine (step% st 0x80005324) O.live ((step% st 0x80005328) O.live (fun _ => realloc_mal O (by rd_regs D)) (fun hc' => ?_))
  simp only [upd_apply, Nat.reduceEqDiff, ite_true] at hc'
  have hpf := prev_bit h13 hc'
  obtain ⟨cs₀, P, ps, i, pre, post, predP, succP, hh, rfl, PV, hhr, hhs⟩ := grow_prev D hsp hpf
  have hPb := HH.walk.chunk_bounds ⟨P, ps, false⟩ (by rw [hsp]; simp)
  simp only at hPb
  have hpend := PV.pend
  refine prev_load O (by rd_regs D) ⟨_, hsp⟩ PV hhr hhs ((step% st 0x8000532c) O.live) ((step% st 0x80005330) O.live)
    ((step% st 0x80005334) O.live) ((step% st 0x80005338) O.live) fun R' hK h6 h17 => ?_
  have k10 := hK 10 (by decide) (by decide); have k14 := hK 14 (by decide) (by decide)
  have k16 := hK 16 (by decide) (by decide); have k15 := hK 15 (by decide) (by decide)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at k10 k14 k16 k15
  have e10 : (R' 10 + R' 17).toNat = ns + ps := by rw [BitVec.toNat_add, k10, e0, h17]; omega
  have e13 : (R' 10 + R' 17 + R' 14).toNat = ps + (S + ns) := by
    rw [BitVec.toNat_add, e10, k14, D.a4]; omega
  have e15 : (R' 15).toNat = nb := by rw [k15, D.a5]
  refine (step% st 0x8000533c) O.live ((step% st 0x80005340) O.live ((step% st 0x80005344) O.live (fun hc'' => ?_) (fun hc'' => ?_))) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc'' <;>
    rw [toInt_small e15 (by omega), toInt_small e13 (by omega), Int.ofNat_le] at hc''
  all_goals
    have D' : RD C B (upd (upd R' 10 (R' 10 + R' 17)) 13 (R' 10 + R' 17 + R' 14)) Mt brkv
        chunks bins X S hdr0 nb := by
      refine RD.of_regs D ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false] <;>
        (rw [hK _ (by decide) (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  ·
    obtain ⟨iN, preN, postN, pred, succ, FB⟩ := free_bin_at D.heap.heap hN rfl
    refine realloc_pvXN O D' hsp hpf FB hc'' ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h6
    · exact e13
    · rw [k16, h16]
  · exact grow_pvX O D' hsp PV (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h6)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)

theorem realloc_grow {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (h13 : (R 13).toNat = hdr0) :
    AW C.live C.S C.Q 0x800052f0#64 R Mt := by
  have HB := D.heap.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have K := (HB.chunkK hXm).lower
  have K_hi := K.hi; have K_room := K.room; have K_brk := K.brk; have K_lo := K.lo; have K_nhdr := K.nhdr
  simp only at K_hi K_lo K_nhdr
  have rG := globRgn C.H
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  obtain ⟨⟨hn, hnr, _⟩, hnext⟩ := walk_next_of hw
  simp only at hnr hnext
  have hnl := Vsa.Sim.read64_lt _ _ _ hnr
  have htp : read64 Mt 0x8001ad20 = some C.top0 := HH.top_ptr
  have h12 := D.a2; have h14 := D.a4
  rgn_step O.live at 0x800052f4
  simp only [BitVec.reduceAppend, sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend, BitVec.reduceAdd]
  rgn_step O.live at 0x80005300
  rgn_ld [htp, hnr]
  have e16 : (R 12 + R 14).toNat = X + S := by rgn_arith
  have hv10 : (BitVec.ofNat 64 hn).toNat = hn := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnl]
  refine (step% st 0x80005300) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · have hXt : X + S = C.top0 := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), e16] at this; omega
    rcases hnext with ⟨_, rfl⟩ | ⟨d, cs₃, rfl, h2⟩
    · have hth := HH.top_header
      rw [← hXt, hnr] at hth
      cases hth
      refine grow_top O (by rd_regs D) hsp hXt ?_ ?_ <;> carry_close [h13, hv10, hXt]
    · exfalso
      have := HH.walk.chunk_bounds d (by rw [hsp]; simp)
      omega
  · rcases hnext with ⟨h1, _⟩ | ⟨d, cs₃, rfl, h2⟩
    · exact absurd (by rw [← h1]; exact BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), e16])) hc
    obtain ⟨dA, ns, b⟩ := d
    simp only at h2
    subst h2
    have hdm : (⟨X + S, ns, b⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
    have Kd := (HB.chunkK hdm).lower
    have Kd_hi := Kd.hi; have Kd_nhdr := Kd.nhdr; simp only at Kd_hi Kd_nhdr
    obtain ⟨hd, hdr', hds, hdl⟩ := Kd.hdrv
    simp only at hdr' hds
    rw [hnr] at hdr'
    cases hdr'
    obtain ⟨hnn, hnnr, hnnp⟩ := Kd.nhdrv
    simp only at hnnr hnnp
    have eA : (BitVec.ofNat 64 hn &&& 18446744073709551614#64).toNat = ns := by
      unfold chunkSize at hds; exact (and_m2_toNat _).trans (by rw [hv10]; omega)
    rgn_step O.live at 0x80005314
    rgn_ld [hnnr]
    refine (step% st 0x80005314) O.live (fun hu => ?_) (fun hu => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hu
    · exact grow_used O (by rd_regs D) (rest := ⟨X + S, ns, b⟩ :: cs₃) (by rw [hsp]; try simp)
        (by carry_close [h13])
    · have hb : b = false := by
        have := prev_bit (x := BitVec.ofNat 64 hnn) (h := hnn)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hnnr)]) hu
        unfold prevInuse at hnnp; rw [← hnnp]; simp [this]
      subst hb
      refine grow_free O (by rd_regs D) (cs₁ := cs₁) (cs₃ := cs₃) (by rw [hsp]; try simp) ?_ ?_ hds ?_ <;>
        carry_close [h13, hv10, e16]

end VsaIris.VsaHeap
