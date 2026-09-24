import VsaIris.Vsa.FreeTrim

/-!
# `_free_r`'s top merge

A chunk whose successor is the top joins it (`0x80007534`), after absorbing a
free predecessor: the merged chunk becomes the top (`PHeapAt.toTop`, over the
virtual heap of `PHeapAt.coalPrev`). A top at the trim threshold goes to
`_malloc_trim_r` (`trim_run`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state at `0x80007558`: the chunk `p` of size `sz` ending at the top,
in use in the virtual heap `V`, with no live block at `p + 16` and its header
carrying `PREV_INUSE`; the machine memory `Mt` agrees with `V` on the
footprint but on `p`'s header. `p` is in `a4`, the merged size in `a3`. -/
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

/-- **The merged top** (`0x80007558`): `p` becomes the top; below the trim
threshold `_free_r` returns, otherwise it calls `_malloc_trim_r` first. -/
theorem top_tail {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt V : Mem} {brkv : Nat}
    {cs : List Chunk} {bins : Nat → List Nat} {p sz : Nat} (T : FTop C R Mt V brkv cs bins p sz) :
    AW C.live C.S C.Q 0x80007558#64 R Mt := by
  have HH := T.heap.heap.heap
  have hpm : (⟨p, sz, true⟩ : Chunk) ∈ cs ++ [⟨p, sz, true⟩] := by simp
  have hpb := HH.walk.chunk_bounds _ hpm
  have hp16 := HH.aligned.1 _ hpm
  have htop16 := HH.aligned.2
  simp only at hpb hp16
  have hbrk := HH.brk_le; have htle := HH.top_le; have hts := HH.top_size
  unfold heapStart heapEnd at *
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hhd := foot_header T.heap.heap (.inr ⟨_, hpm, rfl⟩)
  simp only at hhd
  have hoffH := off_stack_of T.disj hhd
  have hgT : ∀ k, k < 8 → vsaFoot C.H (0x8001ad20 + k) := fun k hk => .inl (by unfold allocGlobal InRange; omega)
  have hoffT := off_stack_of T.disj hgT
  have ha4 := T.a4; have ha3 := T.a3
  have hE8 : (R 14 + sign_extend (m := 64) (0x008#12)).toNat = p + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
  have hv : (R 13 ||| 1#64).toNat = brkv - p + 1 := or1_toNat ha3 (by omega)
  refine st_80007558 O.live ?_
  have hthr := O.foot (a := 0x8001b968) (w := 8) (fun k hk => .inl (by unfold allocGlobal InRange; omega))
  refine st_8000755c O.live (by sx_norm; exact hthr) ?_
  refine st_80007560 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hE8]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hE8]; exact O.foot hhd
  rw [hE8]
  have h17 := T.a7
  rw [← upd_self_eq h17]
  refine st_80007564 O.live (by sx_norm; decide) (by sx_norm; exact O.foot hgT) ?_
  sx_norm
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
  have F' : FFrame C (upd (upd (upd R 17 0x8001ad10#64) 12 (R 13 ||| 1#64)) 15
      (ldv .ld Mt 2147596648)) M2 := by
    rw [← hM2]
    refine ((T.frame.store (by omega)).store (by omega)).of_regs
      ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have hpres : ∀ a, vsaFoot C.H a → (M2[a]?).isSome := fun a ha => by
    rw [← hM2]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (T.pres a ha))
  have hframe : ∀ a, ¬ MWin C.H C.s a → M2[a]? = C.Mt0[a]? := by
    rw [← hM2]; exact frame_store (win_foot hgT) (frame_store (win_foot hhd) T.frameM)
  have hle : p ≤ C.top0 := by omega
  refine st_80007568 O.live (fun _ => free_epi O F' ⟨_, _, _, _, H', hle⟩ hpres hframe) (fun _ => ?_)
  have hpadS := O.foot (a := 0x8001b9a8) (w := 8) (fun k hk => .inl (by unfold allocGlobal InRange; omega))
  refine st_8000756c O.live (by sx_norm; exact hpadS) ?_
  have hpad := H'.heap.heap.top_pad
  unfold topPadAddr at hpad
  sx_norm
  simp (disch := decide) only [ldv_at hpad]
  refine st_80007570 O.live ?_
  refine st_80007574 O.live ?_
  simp only [VsaIris.ra]
  refine trim_run O ⟨F'.of_regs ?_ ?_ ?_ ?_, H', hle, hpres, T.disj, hframe, ?_, ?_, ?_, ?_⟩
    (fun R' M' F h8 D => st_80007578 O.live (free_epi O F D.heap D.pres D.frame)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [T.s0]; rfl
  · rfl
  · exact T.s0

/-- The numbers of a free predecessor `p` of `x = p + psz` (size `sz`): where
`p` and its bin nodes lie. -/
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
  have HH := h.heap.heap
  obtain ⟨hal, _⟩ := HH.aligned
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest := by simp
  have hxm : (⟨x, sz, true⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest := by simp
  have hpb := HH.walk.chunk_bounds _ hpm; have hxb := HH.walk.chunk_bounds _ hxm
  have hp16 := hal _ hpm
  have hps := walk_sizes HH.walk _ hpm; have hxs := walk_sizes HH.walk _ hxm
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := h.heap.top_room
  have hpend := P.pend
  simp only at hpb hxb hp16 hps hxs
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
  obtain ⟨hpp16, hpnode⟩ := HH.node P.i0 P.i1 hpredm
  obtain ⟨hsp16, hsnode⟩ := HH.node P.i0 P.i1 hsuccm
  have bP : (p = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest, c.addr = p) :=
    .inr ⟨_, hpm, rfl⟩
  have bX : (x = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest, c.addr = x) :=
    .inr ⟨_, hxm, rfl⟩
  have hloc : ∀ z, (z = binAt i ∨ ∃ cx ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest,
      cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins i) →
      0x8001ad20 ≤ z ∧ z + 32 ≤ C.top0 := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i P.i1; have := HH.walk.le; have hi0 := P.i0
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  unfold heapStart heapEnd at *
  exact ⟨hp16, hpb.1, hps.1, hps.2, hxs.1, hxs.2, by omega, by omega,
    hpp16, hsp16, (hloc _ hpnode).1, (hloc _ hsnode).1, (hloc _ hpnode).2, (hloc _ hsnode).2,
    HH.bnd_ne_node P.i1 hsnode bP 16 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hsnode bX 16 (by omega) (by omega),
    HH.bnd_ne_node P.i1 hpnode bP 8 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hpnode bX 8 (by omega) (by omega),
    h.heap.node_foot P.i0 P.i1 hpredm, h.heap.node_foot P.i0 P.i1 hsuccm⟩

/-- The machine memory after unlinking the free predecessor `p` agrees with
the coalesced virtual heap `b2Mem` off `p`'s header. -/
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

/-- **The top merge** (`0x80007534`): a chunk `x` whose successor is the top
absorbs a free predecessor, if any, and becomes the top (`top_tail`). -/
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
  refine st_80007534 O.live ?_
  have hsum : (R 15 + R 13).toNat = brkv - x := by rw [BitVec.toNat_add, ha5, ha3]; omega
  refine st_80007538 O.live (fun h1 => ?_) (fun h0 => ?_)
  · -- the predecessor in use: `x` itself becomes the top
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
  -- a free predecessor `p`: unlink it and absorb `x`
  have hpf : hdr0 % 2 = 0 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false, ne_eq, Decidable.not_not] at h0
    rw [h0] at ht1; simp at ht1; omega
  obtain ⟨cs₀, p, psz, i, pre, post, predP, succP, P⟩ := pv_of_heap Hd K.hdr hpf
  have hsp := P.split
  subst hsp
  have G := PvGeo.of_heap Hd P
  have hpend := P.pend
  subst hpend
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi := G.pphi; have hsphi := G.sphi; have hppf := G.ppfoot; have hspf := G.spfoot
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ [⟨p + psz, sz, true⟩] := by simp
  have hff := foot_free Hd.heap hpm rfl
  simp only at hff
  have hpsl := Vsa.Sim.read64_lt _ _ _ P.foot
  have hsl := Vsa.Sim.read64_lt _ _ _ P.fd
  have hpl := Vsa.Sim.read64_lt _ _ _ P.bk
  have ha1 := D.a1
  -- the footer word below `x`
  have hEx : (R 11 + sign_extend (m := 64) (0xff0#12)).toNat = p + psz := by
    sx_norm; rw [BitVec.toNat_add, ha1, ← K.addr]; simp; omega
  refine st_8000753c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEx]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEx]; exact O.foot hff.2
  rw [hEx, ldv_at P.foot _ rfl]
  refine st_80007540 O.live ?_
  have hEp : (R 14 - BitVec.ofNat 64 psz).toNat = p := by
    rw [BitVec.toNat_sub, ha4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpsl]; omega
  have hEpf : (R 14 - BitVec.ofNat 64 psz + sign_extend (m := 64) (0x010#12)).toNat = p + 16 := by
    sx_norm; rw [BitVec.toNat_add, hEp]; simp; omega
  have hEpb : (R 14 - BitVec.ofNat 64 psz + sign_extend (m := 64) (0x018#12)).toNat = p + 24 := by
    sx_norm; rw [BitVec.toNat_add, hEp]; simp; omega
  refine st_80007544 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEpf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEpf]; exact O.foot (fun k hk => hff.1 k (by omega))
  rw [hEpf, ldv_at P.fd _ rfl]
  refine st_80007548 O.live ?_
  refine st_8000754c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEpb]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEpb]; exact O.foot (fun k hk => by
      have := hff.1 (8 + k) (by omega); rwa [show p + 16 + (8 + k) = p + 24 + k by omega] at this)
  rw [hEpb, ldv_at P.bk _ rfl]
  have eS : (BitVec.ofNat 64 succP + sign_extend (m := 64) (0x018#12)).toNat = succP + 24 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]; simp; omega
  have eP : (BitVec.ofNat 64 predP + sign_extend (m := 64) (0x010#12)).toNat = predP + 16 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]; simp; omega
  have fS : ∀ k, k < 8 → vsaFoot C.H (succP + 24 + k) := fun k hk => by
    have := hspf (24 + k) (by omega) (by omega); rwa [show succP + (24 + k) = succP + 24 + k by omega] at this
  have fP : ∀ k, k < 8 → vsaFoot C.H (predP + 16 + k) := fun k hk => by
    have := hppf (16 + k) (by omega) (by omega); rwa [show predP + (16 + k) = predP + 16 + k by omega] at this
  have o1 := off_stack_of D.heap.disj fS
  have o2 := off_stack_of D.heap.disj fP
  refine st_80007550 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [eS]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [eS]; exact O.foot fS
  rw [eS]
  refine st_80007554 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [eP]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [eP]; exact O.foot fP
  rw [eP]
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
    pv_agree G K.hdr hv1 hv2,
    fun a ha => writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha)), Hp.disj,
    frame_store (win_foot fP) (frame_store (win_foot fS) Hp.frame), ?_, ?_, ?_, ?_⟩ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · exact D.s0
  · exact D.a7
  · exact hEp
  · rw [BitVec.toNat_add, hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpsl]; omega

/-- **`_free_r`** (`0x80007350`, a non-NULL block): the prologue, the
dispatch on the top (`0x80007398`), and every path to the epilogue. -/
theorem free_body {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (E : FEntry C q R) (Hp : FHeap C C.Mt0 q n brkv chunks bins) :
    AW C.live C.S C.Q 0x80007350#64 R C.Mt0 :=
  free_pro O E Hp fun _ _ _ _ _ _ D => st_80007398 O.live
    (fun h => free_top O D (by
      have := congrArg BitVec.toNat h; rw [D.a6, D.a2] at this; omega))
    (fun h => free_nt O D (fun he => h (BitVec.eq_of_toNat_eq (by rw [D.a6, D.a2]; omega)))
      fun _ _ _ _ _ _ _ N => free_split O N)

end VsaIris.VsaHeap
