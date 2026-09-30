import VsaIris.Vsa.FreeTrim

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure FTop (C : MCtx) (R : Nat → BitVec 64) (Mt V : Mem) (brkv : Nat) (cs : List Chunk)
    (bins : Nat → List Nat) (p sz : Nat) : Prop where
  frame : FFrame C R Mt
  heap : PHeapAt V C.H C.top0 brkv (cs ++ [⟨p, sz, true⟩]) bins
  hno : ∀ e ∈ C.H, e.1 ≠ p + 16
  prev : ∀ h0, read64 V (p + 8) = some h0 → h0 % 2 = 1
  agree : ∀ w, vsaFoot C.H w → ¬ (p + 8 ≤ w ∧ w < p + 16) → Mt[w]? = V[w]?
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = p
  a3 : (R 13).toNat = brkv - p

theorem top_tail {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt V : Mem} {brkv : Nat}
    {cs : List Chunk} {bins : Nat → List Nat} {p sz : Nat} (T : FTop C R Mt V brkv cs bins p sz) :
    AW C.live C.S C.Q 0x80007558#64 R Mt := by
  have HH := T.heap.heap.heap
  have hpm : (⟨p, sz, true⟩ : Chunk) ∈ cs ++ [⟨p, sz, true⟩] := by simp
  have K := T.heap.heap.chunkK hpm
  open_fields K
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  unfold heapEnd at hbrk
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have rG := globRgn C.H
  have rTh : Rgn (vsaFoot C.H) 0x8001b968 8 := ⟨fun k hk => .inl (by unfold allocGlobal InRange; omega)⟩
  have rPd : Rgn (vsaFoot C.H) 0x8001b9a8 8 := ⟨fun k hk => .inl (by unfold allocGlobal InRange; omega)⟩
  have oH := K_hdr.offStack T.disj (by decide); have oG := rG.offStack T.disj (by decide)
  unfold mHead at oH oG
  have ha4 := T.a4; have ha3 := T.a3
  have h17 : (R 17).toNat = 2147593488 := by rw [T.a7]; rfl
  have hv : (R 13 ||| 1#64).toNat = brkv - p + 1 := or1_toNat ha3 (by omega)
  rgn_run O.live at 0x80007568
  rw [show (R 14 + 8#64).toNat = p + 8 by rgn_arith, show (R 17 + 16#64).toNat = 2147593504 by rgn_arith]
  generalize hM2 : writeLog (writeLog Mt [(p + 8, 8, R 13 ||| 1#64)])
    [(2147593504, 8, R 14)] = M2
  have hM2o : ∀ a, ¬ (p + 8 ≤ a ∧ a < p + 16) → ¬ (0x8001ad20 ≤ a ∧ a < 0x8001ad28) → M2[a]? = Mt[a]? := by
    intro a h1 h2
    rw [← hM2, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have H' : PHeapAt M2 C.H p brkv cs bins := by
    refine T.heap.toTop T.hno T.prev ?_ ?_ fun w hw h1 h2 => ?_
    · rw [← hM2]; unfold topAddr avAddr; rw [read64_store_hit, ha4]
    · rw [← hM2, read64_store_miss _ _ (by omega), read64_store_hit, hv]
    · unfold topAddr avAddr at h2
      rw [hM2o w h1 (by omega)]; exact T.agree w hw h1
  have F' : FFrame C R M2 := by rw [← hM2]; exact (T.frame.store (by omega)).store (by omega)
  have hpres : ∀ a, vsaFoot C.H a → (M2[a]?).isSome := by rw [← hM2]; exact pres_log _ (pres_log _ T.pres)
  have hframe : ∀ a, ¬ MWin C.H C.s a → M2[a]? = C.Mt0[a]? := by
    rw [← hM2, writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) T.frameM
  have hle : p ≤ C.top0 := by omega
  refine (step% st 0x80007568) O.live
    (fun _ => free_epi O (F'.of_regs rfl rfl rfl rfl) ⟨_, _, _, _, H', hle⟩ hpres hframe) (fun _ => ?_)
  have hpad := H'.heap.heap.top_pad
  unfold topPadAddr at hpad
  rgn_run O.live at 0x8000722c
  rgn_ld [hpad]
  refine trim_run O ⟨F'.of_regs ?_ ?_ ?_ ?_, H', hle, hpres, T.disj, hframe, ?_, ?_, ?_, ?_⟩
    (fun R' M' F h8 D => (step% st 0x80007578) O.live (free_epi O F D.heap D.pres D.frame)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact T.s0
  · rfl
  · exact T.s0

structure PvGeo (C : MCtx) (p psz sz predP succP : Nat) : Prop where
  p16 : p % 16 = 0
  plo : 0x8001c170 ≤ p
  psz16 : psz % 16 = 0
  psz32 : 32 ≤ psz
  sz16 : sz % 16 = 0
  sz32 : 32 ≤ sz
  xend : p + psz + sz ≤ C.top0
  top : C.top0 + 16 ≤ 0x87800000
  pp16 : predP % 16 = 0
  sp16 : succP % 16 = 0
  pplo : 0x8001ad20 ≤ predP
  splo : 0x8001ad20 ≤ succP
  pphi : predP + 32 ≤ C.top0
  sphi : succP + 32 ≤ C.top0
  sP : p ≠ succP + 16
  sX : p + psz ≠ succP + 16
  pP : p ≠ predP + 8
  pX : p + psz ≠ predP + 8
  ppfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (predP + k)
  spfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (succP + k)

theorem PvGeo.of_heap {C : MCtx} {Mt : Mem} {brkv : Nat} {cs₀ rest : List Chunk}
    {bins : Nat → List Nat} {x sz p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (h : PHeapAt Mt C.H C.top0 brkv ((cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest) bins)
    (P : FPv Mt (cs₀ ++ [⟨p, psz, false⟩]) bins x cs₀ p psz i pre post predP succP) :
    PvGeo C p psz sz predP succP := by
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest := by simp
  have hxm : (⟨x, sz, true⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest := by simp
  have Kp := h.heap.chunkK hpm; have Kx := h.heap.chunkK hxm
  have hpend := P.pend
  have hpredm : predP = binAt i ∨ predP ∈ bins i := by
    have := List.mem_of_getLast? P.hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [P.bin]; exact List.mem_append_left _ h1)
  have hsuccm : succP = binAt i ∨ succP ∈ bins i := by
    have := List.mem_of_head? P.hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [P.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  have Np := h.heap.nodeK P.i0 P.i1 hpredm; have Ns := h.heap.nodeK P.i0 P.i1 hsuccm
  open_fields Kp; open_fields Kx
  exact ⟨Kp.al, Kp.lo, Kp.sz16, Kp.sz32, Kx.sz16, Kx.sz32, by omega, by omega, Np.al, Ns.al, Np.lo, Ns.lo,
    Np.hi, Ns.hi, Ns.bnd _ (.inr ⟨_, hpm, rfl⟩) 16 (by omega) (by omega),
    hpend ▸ Ns.bnd _ (.inr ⟨_, hxm, rfl⟩) 16 (by omega) (by omega),
    Np.bnd _ (.inr ⟨_, hpm, rfl⟩) 8 (by omega) (by omega),
    hpend ▸ Np.bnd _ (.inr ⟨_, hxm, rfl⟩) 8 (by omega) (by omega),
    h.heap.node_foot P.i0 P.i1 hpredm, h.heap.node_foot P.i0 P.i1 hsuccm⟩

theorem pv_agree {C : MCtx} {Mt : Mem} {p psz sz hdr0 predP succP : Nat}
    (G : PvGeo C p psz sz predP succP) (hdr : read64 Mt (p + psz + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, vsaFoot C.H w0 → ¬ (p + 8 ≤ w0 ∧ w0 < p + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (b2Mem Mt p psz sz hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  intro w0 hw0 h1'
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (p + 8 ≤ x ∧ x < p + 16))
    [succP + 24, predP + 16, p + psz + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, h1'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · refine ⟨predP, ?_, ?_⟩
      · rw [rd_miss (by omega), read64_store_hit, h1]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨succP, ?_, ?_⟩
      · rw [read64_store_hit, h2]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
          read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨hdr0, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega)]; exact hdr
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out] <;> simp only [OutL, and_true] <;> omega

theorem free_top {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {x sz hdr0 nh : Nat}
    (D : FDec C R Mt q n brkv chunks bins x sz hdr0 nh) (hT : x + sz = C.top0) :
    AW C.live C.S C.Q 0x80007534#64 R Mt := by
  have Hp := D.heap
  have HH := Hp.heap.heap.heap
  have K := D.chunk
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem K.mem
  have hw := HH.walk
  rw [hsplit] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  have hc2 : cs₂ = [] := by
    rcases hnext with ⟨_, h⟩ | ⟨d, cs₃, h1, h2⟩
    · exact h
    · exfalso
      have hdm : d ∈ chunks := by rw [hsplit, h1]; simp
      have := HH.walk.chunk_bounds d hdm
      simp only at h2; omega
  subst hc2
  have hXb := HH.walk.chunk_bounds _ K.mem
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  have hx16 := HH.aligned.1 _ K.mem
  have hsz16 := (walk_sizes HH.walk _ K.mem).1
  simp only at hXb hx16 hsz16
  unfold heapStart heapEnd at *
  have hth := HH.top_header
  rw [← hT, K.next] at hth
  obtain rfl := Option.some.inj hth
  have ha3 := D.a3; have ha5 := D.a5; have ha4 := D.a4; have ht1 := D.t1
  unfold chunkSize at ha3
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hno : ∀ e ∈ C.H, e.1 ≠ x + 16 := fun e he heq => hst.1 (List.mem_map.2 ⟨e, he, by rw [heq, K.addr]⟩)
  have Hd := Hp.heap.drop
  rw [hsplit] at Hd
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  refine (step% st 0x80007534) O.live ?_
  have hsum : (R 15 + R 13).toNat = brkv - x := by rw [BitVec.toNat_add, ha5, ha3]; omega
  refine (step% st 0x80007538) O.live (fun h1 => ?_) (fun h0 => ?_)
  ·
    have hodd : hdr0 % 2 = 1 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false] at h1
      have : (R 6).toNat ≠ 0 := fun h => h1 (BitVec.eq_of_toNat_eq h)
      omega
    refine top_tail O (V := Mt) (cs := cs₁) (sz := sz) ⟨D.frame.of_regs ?_ ?_ ?_ ?_, Hd, hno,
      fun h0 hr => by rw [K.hdr] at hr; cases hr; exact hodd, fun _ _ _ => rfl, Hp.pres, Hp.disj,
      Hp.frame, ?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact D.s0
    · exact D.a7
    · exact ha4
    · exact hsum

  have hpf : hdr0 % 2 = 0 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false, ne_eq, Decidable.not_not] at h0
    rw [h0] at ht1; simp at ht1; omega
  obtain ⟨cs₀, p, psz, i, pre, post, predP, succP, P⟩ := pv_of_heap Hd K.hdr hpf
  have hsp := P.split
  subst hsp
  have G := PvGeo.of_heap Hd P
  have hpend := P.pend
  subst hpend
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ [⟨p + psz, sz, true⟩] := by simp
  have rF := Hd.heap.freeSpan hpm rfl
  have rPP : Rgn (vsaFoot C.H) (predP + 16) 16 :=
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.ppfoot _ (by omega) (by omega)⟩
  have rSP : Rgn (vsaFoot C.H) (succP + 16) 16 :=
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.spfoot _ (by omega) (by omega)⟩
  simp only at rF
  have hpsl := Vsa.Sim.read64_lt _ _ _ P.foot
  have hsl := Vsa.Sim.read64_lt _ _ _ P.fd
  have hpl := Vsa.Sim.read64_lt _ _ _ P.bk
  have ha1 : (R 11).toNat = p + psz + 16 := K.addr ▸ D.a1
  have hps32 := G.psz32; have hpp16 := G.pp16; have hsp16 := G.sp16
  have hpphi := G.pphi; have hsphi := G.sphi
  have hEp : (R 14 - BitVec.ofNat 64 psz).toNat = p := by
    rw [BitVec.toNat_sub, ha4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpsl]; omega
  rgn_run O.live at 0x80007540
  rgn_ld [P.foot]
  rgn_run O.live at 0x80007548
  rgn_ld [P.fd]
  rgn_run O.live at 0x80007550
  rgn_ld [P.bk]
  rgn_run O.live at 0x80007558
  rw [show (BitVec.ofNat 64 succP + 24#64).toNat = succP + 24 by rgn_arith,
    show (BitVec.ofNat 64 predP + 16#64).toNat = predP + 16 by rgn_arith]
  have o1 := rSP.offStack Hp.disj (by decide); have o2 := rPP.offStack Hp.disj (by decide)
  unfold mHead at o1 o2; open_fields G
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  have Hd' := Hd
  simp only [List.append_assoc, List.singleton_append] at Hd'
  have HP := Hd'.coalPrev (cs₂ := []) (b := sz) hno P.i0 P.i1 P.bin P.hpred P.hsucc K.hdr (h' := psz + sz + 1)
    (by have := G.sz16; unfold chunkSize; omega) (by omega)
    (fun h0 hr => by have := P.prev h0 hr; unfold prevInuse; rw [show (psz + sz + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hnoP : ∀ e ∈ C.H, e.1 ≠ p + 16 := by
    intro e he heq
    obtain ⟨c, hc, hu, h1, _⟩ := Hd.heap.heap.exact e he he
    have := Hd.heap.heap.chunk_eq hc hpm (by simp only; omega)
    rw [this] at hu; cases hu
  refine top_tail O (V := b2Mem Mt p psz sz hdr0 predP succP) (cs := cs₀) (sz := psz + sz)
    ⟨(D.frame.store (by omega)).store (by omega) |>.of_regs ?_ ?_ ?_ ?_, HP, hnoP, fun h0 hr => ?_,
    pv_agree G K.hdr hv1 hv2, pres_log _ (pres_log _ Hp.pres), Hp.disj,
    by rw [writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) Hp.frame, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · exact D.s0
  · exact D.a7
  · exact hEp
  · clear o1 o2 G_sP G_sX G_pP G_pX
    rw [BitVec.toNat_add, hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpsl]; omega

theorem free_body {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (E : FEntry C q R) (Hp : FHeap C C.Mt0 q n brkv chunks bins) :
    AW C.live C.S C.Q 0x80007350#64 R C.Mt0 :=
  free_pro O E Hp fun _ _ _ _ _ _ D => (step% st 0x80007398) O.live
    (fun h => free_top O D (by
      have := congrArg BitVec.toNat h; rw [D.a6, D.a2] at this; omega))
    (fun h => free_nt O D (fun he => h (BitVec.eq_of_toNat_eq (by rw [D.a6, D.a2]; omega)))
      fun _ _ _ _ _ _ _ N => free_split O N)

end VsaIris.VsaHeap
