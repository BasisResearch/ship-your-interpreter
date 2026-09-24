import VsaIris.Vsa.ReallocMal

/-!
# `_realloc_r` into a free successor

A free chunk after the old one, together big enough, is unlinked from its
bin (`0x80005400`) and absorbed (`PHeapAt.unlink`, then `PHeapAt.absorb`);
the tail records the merged size and marks the next header.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A free chunk's place in its bin: bin `i` is `pre ++ v :: post`, between
`pred` and `succ`, with its links. -/
structure FreeBinAt (m : Mem) (bins : Nat → List Nat) (v i : Nat) (pre post : List Nat)
    (pred succ : Nat) : Prop where
  i0 : 0 < i
  i1 : i < numBins
  bin : bins i = pre ++ v :: post
  hpred : (binAt i :: pre).getLast? = some pred
  hsucc : (post ++ [binAt i]).head? = some succ
  fd : read64 m (v + 16) = some succ
  bk : read64 m (v + 24) = some pred

theorem free_bin_at {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) {c : Chunk} (hc : c ∈ chunks)
    (hf : c.inuse = false) : ∃ i pre post pred succ, FreeBinAt m bins c.addr i pre post pred succ := by
  have HH := h.heap.heap
  obtain ⟨i, hi0, hi, hm, _⟩ := HH.free_binned c hc hf
  obtain ⟨pre, post, hbin⟩ := List.append_of_mem hm
  obtain ⟨pred, hpred⟩ : ∃ q, (binAt i :: pre).getLast? = some q := ⟨_, List.getLast?_cons⟩
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt i]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  rw [hbin] at hring
  exact ⟨i, pre, post, pred, succ, hi0, hi, hbin, hpred, hsucc, (ring_member hring hpred hsucc).1,
    (ring_member hring hpred hsucc).2⟩

theorem FreeBinAt.pred_node {m : Mem} {bins : Nat → List Nat} {v i : Nat} {pre post : List Nat}
    {pred succ : Nat} (F : FreeBinAt m bins v i pre post pred succ) : pred = binAt i ∨ pred ∈ bins i := by
  have := List.mem_of_getLast? F.hpred
  rcases List.mem_cons.mp this with h1 | h1
  · exact .inl h1
  · exact .inr (by rw [F.bin]; exact List.mem_append_left _ h1)

theorem FreeBinAt.succ_node {m : Mem} {bins : Nat → List Nat} {v i : Nat} {pre post : List Nat}
    {pred succ : Nat} (F : FreeBinAt m bins v i pre post pred succ) : succ = binAt i ∨ succ ∈ bins i := by
  have := List.mem_of_head? F.hsucc
  rcases List.mem_append.mp this with h1 | h1
  · exact .inr (by rw [F.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
  · exact .inl (List.mem_singleton.mp h1)

/-- `reflag` at the end of one chunk keeps every chunk that ends elsewhere. -/
theorem map_reflag_other {q : Nat} {b : Bool} {cs : List Chunk} (h : ∀ c ∈ cs, c.addr + c.size ≠ q) :
    cs.map (reflag q b) = cs := by
  conv => rhs; rw [← List.map_id cs]
  refine List.map_congr_left fun c hc => ?_
  unfold reflag; rw [if_neg (h c hc)]; rfl

/-- **Into a free successor** (`0x80005400`): the chunk `N` after `X` is free
and `S + ns` holds the request; unlink `N` and go to the tail with `X` of
size `S + ns`. -/
theorem realloc_next {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks)
    (hfit : nb ≤ S + ns) (h16 : (R 16).toNat = X + S) (h17 : (R 17).toNat = S + ns) :
    AW C.live C.S C.Q 0x80005400#64 R Mt := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hXb := HH.walk.chunk_bounds _ hXm; have hNb := HH.walk.chunk_bounds _ hN
  have hx16 := HH.aligned.1 _ hXm; have hS16 := (walk_sizes HH.walk _ hXm).1
  have hns16 := (walk_sizes HH.walk _ hN).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := HB.top_room
  simp only at hXb hNb hx16 hS16 hns16
  unfold heapStart heapEnd at *
  -- the chunk list around `X` and `N`
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  obtain ⟨cs₃, rfl⟩ : ∃ cs₃, cs₂ = ⟨X + S, ns, false⟩ :: cs₃ := by
    rcases hnext with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
    · simp only at he; omega
    · have hdm : d ∈ chunks := by rw [hsp, h1]; simp
      have := HH.chunk_eq hdm hN (by simp only at h2 ⊢; omega)
      exact ⟨cs₃, by rw [h1, this]⟩
  -- `N`'s bin links and the header after it
  obtain ⟨i, pre, post, pred, succ, FB⟩ := free_bin_at Hp.heap hN rfl
  simp only at FB
  have hpn := FB.pred_node; have hsn := FB.succ_node
  obtain ⟨hp16, hpnode⟩ := HH.node FB.i0 FB.i1 hpn
  obtain ⟨hs16, hsnode⟩ := HH.node FB.i0 FB.i1 hsn
  have hpf := Hp.heap.heap.node_foot FB.i0 FB.i1 hpn
  have hsf := Hp.heap.heap.node_foot FB.i0 FB.i1 hsn
  have hbX : X = C.top0 ∨ ∃ c ∈ chunks, c.addr = X := .inr ⟨_, hXm, rfl⟩
  have hbE : X + S + ns = C.top0 ∨ ∃ c ∈ chunks, c.addr = X + S + ns := by
    have := HH.end_bnd hN; simpa using this
  have nX16s := HH.bnd_ne_node FB.i1 hsnode hbX 16 (by omega) (by omega)
  have nE16s := HH.bnd_ne_node FB.i1 hsnode hbE 16 (by omega) (by omega)
  have nE8p := HH.bnd_ne_node FB.i1 hpnode hbE 8 (by omega) (by omega)
  have nE16p := HH.bnd_ne_node FB.i1 hpnode hbE 16 (by omega) (by omega)
  have hloc : ∀ z, (z = binAt i ∨ ∃ cx ∈ chunks, cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins i) →
      0x8001ad20 ≤ z ∧ z + 32 ≤ C.top0 := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i FB.i1; have := HH.walk.le; have := FB.i0
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  obtain ⟨hplo, hphi⟩ := hloc _ hpnode
  obtain ⟨hslo, hshi⟩ := hloc _ hsnode
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hNf := (foot_free HB hN rfl).1
  simp only at hNf
  have hfd := FB.fd; have hbk := FB.bk
  have hpl := Vsa.Sim.read64_lt _ _ _ hbk
  have hsl := Vsa.Sim.read64_lt _ _ _ hfd
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have eB : (R 16 + sign_extend (m := 64) (0x018#12)).toNat = X + S + 24 := by
    rw [n24, addr_add h16 24 (by omega)]
  have eF : (R 16 + sign_extend (m := 64) (0x010#12)).toNat = X + S + 16 := by
    rw [n16, addr_add h16 16 (by omega)]
  have fB : ∀ k, k < 8 → vsaFoot C.H (X + S + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hNf (8 + k) (by omega); rwa [show X + S + 16 + (8 + k) = X + S + 24 + k by omega] at this)
  have fF : ∀ k, k < 8 → vsaFoot C.H (X + S + 16 + k) := fun k hk => vsaFoot_cons_sub _ (hNf k (by omega))
  have fS : ∀ k, k < 8 → vsaFoot C.H (succ + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hsf (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  have fP : ∀ k, k < 8 → vsaFoot C.H (pred + 16 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hpf (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  refine st_80005400 O.live (by rw [eB]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [eB]; exact O.foot fB) ?_
  rw [eB, ldv_at hbk _ rfl]
  refine st_80005404 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; exact O.foot fF) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eF, ldv_at hfd _ rfl]
  refine st_80005408 O.live ?_
  have hvP : (BitVec.ofNat 64 pred).toNat = pred := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hvS : (BitVec.ofNat 64 succ).toNat = succ := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  have eS : (BitVec.ofNat 64 succ + sign_extend (m := 64) (0x018#12)).toNat = succ + 24 := by
    rw [n24, addr_add hvS 24 (by omega)]
  have eP : (BitVec.ofNat 64 pred + sign_extend (m := 64) (0x010#12)).toNat = pred + 16 := by
    rw [n16, addr_add hvP 16 (by omega)]
  have oS := off_stack_of D.heap.disj fS
  have oP := off_stack_of D.heap.disj fP
  refine st_8000540c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]; exact O.foot fS) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS]
  refine st_80005410 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]; exact O.foot fP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eP]
  generalize hM2 : writeLog (writeLog Mt [(succ + 24, 8, BitVec.ofNat 64 pred)])
    [(pred + 16, 8, BitVec.ofNat 64 succ)] = M2
  have hM2o : ∀ a, ¬ (succ + 24 ≤ a ∧ a < succ + 32) → ¬ (pred + 16 ≤ a ∧ a < pred + 24) →
      M2[a]? = Mt[a]? := fun a h1 h2 => by
    rw [← hM2, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  -- the headers of `X` and after `N`
  have hXr := D.hdr; have hXs := D.hsz; have hXl := D.hlow
  have hw2 := HH.walk
  rw [hsp] at hw2
  obtain ⟨⟨hNN, hNNr, hNNp⟩, hnext2⟩ := walk_next_of (cs₁ := cs₁ ++ [⟨X, S, true⟩]) (by simpa using hw2)
  simp only at hNNr hNNp
  have hNNe : hNN % 2 = 0 := by unfold prevInuse at hNNp; simp at hNNp; omega
  have hNNl : hNN % 4 < 2 := by
    rcases hnext2 with ⟨he, _⟩ | ⟨d, cs₄, h1, h2⟩
    · exfalso; have ht := HH.top_header; have hts := HH.top_size; simp only at he
      rw [← he, hNNr] at ht; cases ht; rw [← he] at hts; omega
    · have hdm : d ∈ chunks := by rw [hsp, h1]; simp
      obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d hdm
      simp only at h2; rw [h2, hNNr] at hd0r; cases hd0r; exact hd0l
  have hNNlt := Vsa.Sim.read64_lt _ _ _ hNNr
  -- the unlinked heap, with the header after `N` marked
  have hvN : (BitVec.ofNat 64 (hNN + 1)).toNat = hNN + 1 := by rw [BitVec.toNat_ofNat]; omega
  generalize hW1 : writeLog M2 [(X + S + ns + 8, 8, BitVec.ofNat 64 (hNN + 1))] = W1
  have hW1o : ∀ a, ¬ (X + S + ns + 8 ≤ a ∧ a < X + S + ns + 16) → W1[a]? = M2[a]? := fun a h => by
    have ho : OutL [(X + S + ns + 8, 8, BitVec.ofNat 64 (hNN + 1))] a := ⟨by simp only; omega, trivial⟩
    rw [← hW1, writeLog_out _ _ _ ho]
  have H0 := Hp.heap
  rw [hsp] at H0
  obtain ⟨mid, Wa, Wb⟩ := (show ChunkWalk Mt heapStart C.top0 (cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    from hw).append_inv
  have HXw := walkHead Wb
  have hmid : X = mid := HXw.addr
  subst hmid
  have HNw := walkHead HXw.rest
  simp only at HNw
  have hWab := Wa.chunk_bounds
  have hWcb := HNw.rest.chunk_bounds
  have H1 := H0.unlink (m' := W1) FB.i0 FB.i1 FB.bin (c := ⟨X + S, ns, false⟩) (by simp) rfl FB.hpred
    FB.hsucc (hd' := hNN + 1) ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left
  · show read64 W1 (pred + 16) = some succ
    rw [← hW1, rd_miss (by omega), ← hM2, read64_store_hit, hvS]
  · show read64 W1 (succ + 24) = some pred
    rw [← hW1, rd_miss (by omega), ← hM2, rd_miss (by omega), read64_store_hit, hvP]
  · show read64 W1 (X + S + ns + 8) = some (hNN + 1)
    rw [← hW1, read64_store_hit, hvN]
  · intro hd hdr; simp only at hdr; rw [hNNr] at hdr; cases hdr
    exact ⟨by unfold chunkSize; omega, by omega⟩
  · unfold prevInuse; simp; omega
  · intro a ha hT
    unfold TakeW at hT
    simp only at hT
    rw [hW1o a (by omega), hM2o a (by omega) (by omega)]
  have hmap : (cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃).map (reflag (X + S + ns) true) =
      cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, true⟩ :: cs₃ := by
    rw [List.map_append, List.map_cons, List.map_cons,
      map_reflag_other (fun c hc => by have := hWab c hc; have := hXb.2.2; omega),
      map_reflag_other (fun c hc => by have := hWcb c hc; simp only at this; omega)]
    simp only [reflag, ite_self, ite_true]
  rw [hmap] at H1
  -- `X` absorbs `N`, and the block grows
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  have hv : (BitVec.ofNat 64 (S + ns + hdr0 % 2)).toNat = S + ns + hdr0 % 2 := by
    rw [BitVec.toNat_ofNat]; omega
  generalize hV : writeLog W1 [(X + 8, 8, BitVec.ofNat 64 (S + ns + hdr0 % 2))] = V
  have hVo : ∀ w, ¬ (X + 8 ≤ w ∧ w < X + 16) → V[w]? = W1[w]? := fun w hw => by
    have ho : OutL [(X + 8, 8, BitVec.ofNat 64 (S + ns + hdr0 % 2))] w := ⟨by simp only; omega, trivial⟩
    rw [← hV, writeLog_out _ _ _ ho]
  have hM2X : read64 M2 (X + 8) = some hdr0 := by
    rw [← hM2, rd_miss (by omega), rd_miss (by omega)]; exact hXr
  have hW1X : read64 W1 (X + 8) = some hdr0 := by rw [← hW1, rd_miss (by omega)]; exact hM2X
  have hno : ∀ e ∈ (B.p, B.nOld) :: C.H, e.1 ≠ X + S + 16 := fun e he heq => by
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he he
    have := HH.chunk_eq hc0 hN (by simp only; omega)
    rw [this] at hu; cases hu
  have Ha := H1.absorb (m' := V) (x := X) (a := S) (b := ns) (h' := S + ns + hdr0 % 2) hno
    (by rw [← hV, read64_store_hit, hv]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      rw [hW1X] at hr; cases hr; unfold prevInuse; rw [show (S + ns + hdr0 % 2) % 2 = hdr0 % 2 by omega])
    (fun w _ hw _ => hVo w hw)
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [D.nbok.eq]; unfold physSize; omega
  have Hr := Ha.reblock (c := ⟨X, S + ns, true⟩) (by simp) rfl D.addr (n' := C.n.toNat)
    (by simp only; omega)
  rw [← D.addr] at Hr
  have hM2N : read64 M2 (X + S + ns + 8) = some hNN := by
    rw [← hM2, rd_miss (by omega), rd_miss (by omega)]; exact hNNr
  have hfoot : ∀ w, vsaFoot C.H w → w < C.s.toNat - 256 ∨ C.s.toNat ≤ w := fun w hw =>
    Classical.byContradiction fun hc => D.heap.disj w (by unfold mHead; omega) (by omega) hw
  have F2 : RFrame C R M2 := by
    rw [← hM2]
    have a1 := hfoot _ (fS 0 (by omega)); have a2 := hfoot _ (fS 7 (by omega))
    have a3 := hfoot _ (fP 0 (by omega)); have a4 := hfoot _ (fP 7 (by omega))
    have hsl := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hsl
    exact (D.frame.store (a := succ + 24) (w := 8) (by omega)).store (a := pred + 16) (w := 8) (by omega)
  have hdata2 : ∀ k, k < B.nOld → M2[X + 16 + k]? = some (B.old (B.p + k)) := by
    intro k hk
    have hb := D.addr
    have hsz8 : B.nOld + 8 ≤ S := by
      obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
      have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; omega)
      subst this; simpa using hc0n
    have hnf : ¬ vsaFoot ((B.p, B.nOld) :: C.H) (B.p + k) := fun hf => by
      rcases hf with hg | ⟨_, _, h3⟩
      · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
      · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
    have hS1 : ¬ (succ + 24 ≤ B.p + k ∧ B.p + k < succ + 32) := fun h => hnf (by
      have := hsf (B.p + k - succ) (by omega) (by omega)
      rwa [show succ + (B.p + k - succ) = B.p + k by omega] at this)
    have hP1 : ¬ (pred + 16 ≤ B.p + k ∧ B.p + k < pred + 24) := fun h => hnf (by
      have := hpf (B.p + k - pred) (by omega) (by omega)
      rwa [show pred + (B.p + k - pred) = B.p + k by omega] at this)
    rw [show X + 16 + k = B.p + k by omega, hM2o _ hS1 hP1]
    exact Hp.data k hk
  refine realloc_tail O (V := V) (X := X) (S := S + ns) (nb := nb) (cs₁ := cs₁) (cs₂ := cs₃)
    ⟨F2.of_regs ?_ ?_ ?_, Hr, by rw [D.addr]; exact Hp.starts, by omega, D.nbok, hfit,
      ⟨hdr0, hM2X, by rw [← hV, read64_store_hit, hv]⟩,
      ⟨hNN, by rw [show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact hM2N, by
        rw [show hNN / 2 * 2 + 1 = hNN + 1 by omega, ← hV, rd_miss (by omega),
          show X + (S + ns) + 8 = X + S + ns + 8 by omega, ← hW1, read64_store_hit, hvN]⟩,
      fun w _ hw hw' => by rw [hVo w hw, hW1o w (by omega)],
      fun a ha => by rw [← hM2]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha)),
      Hp.disj, Hp.disjD, hdata2, by have := Hp.grow; omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [D.s0]
  · exact D.s1
  · exact D.a2
  · rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      addr_add h17 0 (by omega)]; rfl
  · exact D.a5

end VsaIris.VsaHeap
