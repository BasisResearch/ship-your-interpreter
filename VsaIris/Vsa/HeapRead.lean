import VsaIris.Vsa.HeapAlg

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.MallocFast

theorem read64_keep {m m' : Mem} {a : Nat} (h : ∀ k, k < 8 → m'[a + k]? = m[a + k]?) :
    read64 m' a = read64 m a :=
  read64_agreeP (P := fun b => m'[b]? = m[b]?) (fun _ hb => hb) h

theorem binAt_geo (j : Nat) (hj : j < numBins) :
    binAt j % 16 = 0 ∧ 0x8001ad10 ≤ binAt j ∧ binAt j + 32 ≤ 0x8001b520 := by
  unfold binAt avAddr; unfold numBins at hj; omega

section Rd

variable {m m' : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
  {bins : Nat → List Nat} {U : Nat → Prop}

theorem _root_.Vsa.Sim.DlHeap.HeapAt.member (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins)
    {j q : Nat} (hj0 : 0 < j) (hj : j < numBins) (hq : q ∈ bins j) :
    ∃ c ∈ chunks, c.addr = q ∧ c.inuse = false := by
  obtain ⟨c, hc, h1, h2, _⟩ := h.bin_free j q hj0 hj hq
  exact ⟨c, hc, h1, h2⟩

theorem BlockHeapAt.node_foot (B : BlockHeapAt m H top brkv chunks bins)
    {j x : Nat} (hj0 : 0 < j) (hj : j < numBins) (hx : x = binAt j ∨ x ∈ bins j) :
    ∀ k, 16 ≤ k → k < 32 → vsaFoot H (x + k) := by
  intro k hk1 hk2
  rcases hx with rfl | hx
  · have := binAt_geo j hj
    exact .inl (.inl ⟨by omega, by omega⟩)
  · obtain ⟨cx, hcx, rfl, hf⟩ := B.heap.member hj0 hj hx
    have := (foot_free B hcx hf).1 (k - 16) (by omega)
    rwa [show cx.addr + 16 + (k - 16) = cx.addr + k by omega] at this

theorem rd_keep (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {a : Nat}
    (hf : ∀ k, k < 8 → vsaFoot H (a + k)) (hu : ∀ w, U w → w < a ∨ a + 8 ≤ w) :
    read64 m' a = read64 m a :=
  read64_keep fun k hk => hag _ (hf k hk) fun h => by have := hu _ h; omega

theorem BlockHeapAt.keep_fd (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {j x : Nat} (hj0 : 0 < j) (hj : j < numBins)
    (hx : x = binAt j ∨ x ∈ bins j) (hu : ∀ w, U w → w < x + 16 ∨ x + 24 ≤ w) :
    fdOf m' x = fdOf m x :=
  rd_keep hag (fun k hk => by
    have := B.node_foot hj0 hj hx (16 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this) hu

theorem BlockHeapAt.keep_bk (B : BlockHeapAt m H top brkv chunks bins)
    (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?) {j x : Nat} (hj0 : 0 < j) (hj : j < numBins)
    (hx : x = binAt j ∨ x ∈ bins j) (hu : ∀ w, U w → w < x + 24 ∨ x + 32 ≤ w) :
    bkOf m' x = bkOf m x :=
  rd_keep hag (fun k hk => by
    have := B.node_foot hj0 hj hx (24 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this) hu

theorem _root_.Vsa.Sim.DlHeap.HeapAt.keep_scal {R : Nat × Nat → Prop}
    (h : HeapAt m H R top brkv chunks bins) (hag : ∀ w, vsaFoot H w → ¬ U w → m'[w]? = m[w]?)
    (hG : ∀ w, allocGlobal w → U w → w < 0x8001b520 ∧ (w < topAddr ∨ topAddr + 8 ≤ w)) :
    read64 m' sbrkBaseAddr = some heapStart ∧ read64 m' brkAddr = some brkv ∧
    read64 m' topPadAddr = some 0 ∧ (read64 m' maxSbrkedAddr).isSome ∧
    (read64 m' mallinfoAddr).isSome ∧ read64 m' topAddr = some top := by
  have K : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → (0x8001b520 ≤ a ∨ a = topAddr) →
      read64 m' a = read64 m a := fun a hg ha => read64_keep fun k hk =>
    hag _ (.inl (hg k hk)) fun hu => by have := hG _ (hg k hk) hu; unfold topAddr avAddr at *; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K _ (fun k hk => .inr (.inr (.inl ⟨by unfold sbrkBaseAddr; omega, by unfold sbrkBaseAddr; omega⟩)))
      (by unfold sbrkBaseAddr; omega)]; exact h.sbrk_base
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold brkAddr; omega, by unfold brkAddr; omega⟩))))
      (by unfold brkAddr; omega)]; exact h.brk
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold topPadAddr; omega, by unfold topPadAddr; omega⟩))))
      (by unfold topPadAddr; omega)]; exact h.top_pad
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inl ⟨by unfold maxSbrkedAddr; omega,
      by unfold maxSbrkedAddr; omega⟩)))) (by unfold maxSbrkedAddr; omega)]; exact h.max_sbrked
  · rw [K _ (fun k hk => .inr (.inr (.inr (.inr (.inr ⟨by unfold mallinfoAddr; omega,
      by unfold mallinfoAddr; omega⟩))))) (by unfold mallinfoAddr; omega)]; exact h.mallinfo
  · rw [K _ (fun k hk => .inl ⟨by unfold topAddr avAddr; omega, by unfold topAddr avAddr; omega⟩)
      (.inr rfl)]; exact h.top_ptr

end Rd

theorem pred_mem {b pred : Nat} {pre L : List Nat} (hs : ∀ x ∈ pre, x ∈ L)
    (h : (b :: pre).getLast? = some pred) : pred = b ∨ pred ∈ L :=
  (List.mem_cons.mp (List.mem_of_getLast? h)).imp_right (hs _)

theorem succ_mem {b succ : Nat} {post L : List Nat} (hs : ∀ x ∈ post, x ∈ L)
    (h : (post ++ [b]).head? = some succ) : succ = b ∨ succ ∈ L := by
  rcases List.mem_append.mp (List.mem_of_head? h) with h1 | h1
  · exact .inr (hs _ h1)
  · exact .inl (List.mem_singleton.mp h1)

theorem seg_pairs {hd pred succ : Nat} {pre post ys zs : List Nat}
    (hnd : (pre ++ post).Nodup) (hne : ∀ x ∈ pre ++ post, x ≠ hd)
    (hys : hd :: pre = ys ++ [pred]) (hzs : post ++ [hd] = succ :: zs) :
    ∀ a b, [a, b] <:+: ys ++ [pred] ∨ [a, b] <:+: succ :: zs →
      (a = hd ∨ a ∈ pre ++ post) ∧ a ≠ pred ∧ (b = hd ∨ b ∈ pre ++ post) ∧ b ≠ succ := by
  intro a b hab
  have hndpre : (hd :: pre).Nodup :=
    List.nodup_cons.2 ⟨fun hm => hne _ (List.mem_append_left _ hm) rfl, (List.nodup_append.mp hnd).1⟩
  have hndpost : (post ++ [hd]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_append.mp hnd).2.1, by simp, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton.mp hy]
    exact hne x (List.mem_append_right _ hx)
  have hdisj : ∀ x ∈ pre, ∀ y ∈ post, x ≠ y := fun x hx y hy =>
    (List.nodup_append.mp hnd).2.2 x hx y hy
  have hpm : pred = hd ∨ pred ∈ pre := List.mem_cons.mp (hys ▸ List.mem_append_right _ (List.mem_singleton_self _))
  have hsm : succ ∈ post ++ [hd] := hzs ▸ List.mem_cons_self
  rcases hab with hab | hab
  · rw [← hys] at hab
    have ⟨ha, hb⟩ := pair_mem hab
    have hane : a ≠ pred := pair_ne_last (hys ▸ hab) (hys ▸ hndpre)
    have hbne : b ≠ hd := pair_ne_head hab hndpre
    have hbpre : b ∈ pre := (List.mem_cons.mp hb).resolve_left hbne
    refine ⟨(List.mem_cons.mp ha).imp_right (List.mem_append_left _), hane,
      .inr (List.mem_append_left _ hbpre), fun hbs => ?_⟩
    rcases List.mem_append.mp (hbs ▸ hsm) with h1 | h1
    · exact hdisj b hbpre b h1 rfl
    · exact hbne (List.mem_singleton.mp h1)
  · rw [← hzs] at hab
    have ⟨ha, hb⟩ := pair_mem hab
    have hbne : b ≠ succ := pair_ne_head (hzs ▸ hab) (hzs ▸ hndpost)
    have hane : a ≠ hd := pair_ne_last hab hndpost
    have hapost : a ∈ post :=
      (List.mem_append.mp ha).resolve_right fun h => hane (List.mem_singleton.mp h)
    refine ⟨.inr (List.mem_append_right _ hapost), fun hap => ?_, ?_, hbne⟩
    · rcases hap ▸ hpm with h1 | h1
      · exact hane h1
      · exact hdisj a h1 a hapost rfl
    · rcases List.mem_append.mp hb with h1 | h1
      · exact .inr (List.mem_append_right _ h1)
      · exact .inl (List.mem_singleton.mp h1)

theorem binList_keep {m m' : Mem} {i : Nat} {L : List Nat} (hold : BinList m i L)
    (hfd : ∀ x, (x = binAt i ∨ x ∈ L) → fdOf m' x = fdOf m x)
    (hbk : ∀ x, (x = binAt i ∨ x ∈ L) → bkOf m' x = bkOf m x) : BinList m' i L := by
  rw [binList_iff_ring] at hold ⊢
  refine ⟨Links.transport hold.1 fun a b hab => ?_, hold.2⟩
  have hn : ∀ y ∈ binAt i :: L ++ [binAt i], y = binAt i ∨ y ∈ L := by
    intro y hy
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with h1 | h1 | h1 <;> simp [h1]
  exact ⟨hfd a (hn a (pair_mem hab).1), hbk b (hn b (pair_mem hab).2)⟩

theorem binList_remove {m m' : Mem} {i v pred succ : Nat} {L pre post : List Nat}
    (hold : BinList m i L) (hL : L = pre ++ v :: post) (hnd : L.Nodup)
    (hpred : (binAt i :: pre).getLast? = some pred) (hsucc : (post ++ [binAt i]).head? = some succ)
    (h1 : fdOf m' pred = some succ) (h2 : bkOf m' succ = some pred)
    (hfd : ∀ x, (x = binAt i ∨ x ∈ L) → x ≠ pred → fdOf m' x = fdOf m x)
    (hbk : ∀ x, (x = binAt i ∨ x ∈ L) → x ≠ succ → bkOf m' x = bkOf m x) :
    BinList m' i (pre ++ post) := by
  subst hL
  rw [binList_iff_ring] at hold ⊢
  have hsub : ∀ x, x ∈ pre ++ post → x ∈ pre ++ v :: post := by
    intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  have hne : ∀ x ∈ pre ++ post, x ≠ binAt i := fun x hx => hold.2 x (hsub x hx)
  refine ⟨?_, hne⟩
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hpred
  obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.1 hsucc
  have hold := hold.1
  unfold Ring at hold ⊢
  rw [show binAt i :: (pre ++ v :: post) ++ [binAt i] = (binAt i :: pre) ++ v :: (post ++ [binAt i])
    by simp, hys, hzs, List.append_assoc] at hold
  rw [show binAt i :: (pre ++ post) ++ [binAt i] = (binAt i :: pre) ++ (post ++ [binAt i])
    by simp, hys, hzs, List.append_assoc]
  refine links_unlink hold h1 h2 fun a b hab => ?_
  obtain ⟨ha, hap, hb, hbs⟩ := seg_pairs ((List.nodup_append.mpr ⟨(List.nodup_append.mp hnd).1,
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2, fun x hx y hy =>
      (List.nodup_append.mp hnd).2.2 x hx y (List.mem_cons_of_mem _ hy)⟩)) hne hys hzs a b hab
  exact ⟨hfd a (ha.imp_right (hsub a)) hap, hbk b (hb.imp_right (hsub b)) hbs⟩

theorem binList_insert {m m' : Mem} {i v pred succ : Nat} {L pre post : List Nat}
    (hold : BinList m i L) (hL : L = pre ++ post) (hnd : L.Nodup) (hv : v ≠ binAt i)
    (hpred : (binAt i :: pre).getLast? = some pred) (hsucc : (post ++ [binAt i]).head? = some succ)
    (h1 : fdOf m' pred = some v) (h2 : bkOf m' v = some pred) (h3 : fdOf m' v = some succ)
    (h4 : bkOf m' succ = some v)
    (hfd : ∀ x, (x = binAt i ∨ x ∈ L) → x ≠ pred → fdOf m' x = fdOf m x)
    (hbk : ∀ x, (x = binAt i ∨ x ∈ L) → x ≠ succ → bkOf m' x = bkOf m x) :
    BinList m' i (pre ++ v :: post) := by
  subst hL
  rw [binList_iff_ring] at hold ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hpred
    obtain ⟨zs, hzs⟩ := List.head?_eq_some_iff.1 hsucc
    have hr := hold.1
    unfold Ring at hr ⊢
    rw [show binAt i :: (pre ++ post) ++ [binAt i] = (binAt i :: pre) ++ (post ++ [binAt i])
      by simp, hys, hzs, List.append_assoc] at hr
    rw [show binAt i :: (pre ++ v :: post) ++ [binAt i] = (binAt i :: pre) ++ v :: (post ++ [binAt i])
      by simp, hys, hzs, List.append_assoc]
    refine links_link hr h1 h2 h3 h4 fun a b hab => ?_
    obtain ⟨ha, hap, hb, hbs⟩ := seg_pairs hnd hold.2 hys hzs a b hab
    exact ⟨hfd a ha hap, hbk b hb hbs⟩
  · simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hold.2 x (List.mem_append_left _ hx)
    · exact hv
    · exact hold.2 x (List.mem_append_right _ hx)

end VsaIris.VsaHeap
