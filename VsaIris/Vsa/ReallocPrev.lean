import VsaIris.Vsa.ReallocTop

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

structure PVKeep (R R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = R 2
  t1 : R' 6 = R 6
  s1 : R' 9 = R 9
  a3 : R' 13 = R 13
  a5 : R' 15 = R 15
  a6 : R' 16 = R 16
  a7 : R' 17 = R 17
  s2 : R' 18 = R 18
  s3 : R' 19 = R 19

macro "pv_keep" h:term : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;>
  first | exact ($h).sp | exact ($h).t1 | exact ($h).s1 | exact ($h).a3 | exact ($h).a5 |
    exact ($h).a6 | exact ($h).a7 | exact ($h).s2 | exact ($h).s3))


theorem pvA_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x80005648#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x80005630#64 R (copyW M0 d s j) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  rgn_step hlive at 0x80005648
  cp_norm
  exact hk _ (by pv_keep K)

theorem pvA_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = d)
    (h12 : (R 12).toNat = L) (h10 : (R 10).toNat = 72)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x80005648#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005604#64 R (copyW M0 d s 0) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 8).toNat = s + 8 * j →
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x80005630#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvA_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
  rgn_step hlive at 0x8000560c
  refine (step% st 0x8000560c) hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · exact tail 0 _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  rgn_step hlive at 0x80005624
  cp_norm
  refine (step% st 0x80005624) hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12, BitVec.reduceToNat] at hc'
  · rgn_step hlive at 0x800057b8
    cp_norm
    refine (step% st 0x800057b8) hlive (fun hc'' => ?_) (fun hc'' => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc''
    · have hL72 : L = 72 := by rw [← h12, hc'']; exact h10
      rgn_step hlive at 0x80005630
      cp_norm
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
    · have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by rw [h12, h10, h]))
        omega
      rgn_step hlive at 0x80005630
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  · rgn_step hlive at 0x80005630
    exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))

end Copy

theorem node_off_inuse {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {i x : Nat} (hi : i < numBins)
    (hx : x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i)
    {c : Chunk} (hc : c ∈ chunks) (hu : c.inuse = true) :
    ∀ a, c.addr ≤ a → a < c.addr + c.size + 8 → a < x + 16 ∨ x + 32 ≤ a := by
  intro a h1 h2
  have hcb := (h.walk.chunk_bounds c hc).1
  unfold heapStart at hcb
  rcases hx with rfl | ⟨cx, hcx, rfl, hf, _⟩
  · have := binAt_geo i hi; omega
  · rcases h.walk.chunk_sep cx hcx c hc with rfl | h3 | h3
    · rw [hu] at hf; cases hf
    all_goals have := (walk_sizes h.walk cx hcx).2; omega

theorem copyW_agreeOn {m1 m2 : Mem} {d s : Nat} {Pr : Nat → Prop}
    (h : ∀ a, Pr a → m1[a]? = m2[a]?) :
    ∀ {k : Nat}, (∀ i, i < 8 * k → Pr (s + i)) →
      ∀ a, Pr a → (copyW m1 d s k)[a]? = (copyW m2 d s k)[a]?
  | 0, _, a, ha => h a ha
  | k + 1, hs, a, ha => by
    have IH := copyW_agreeOn (m1 := m1) (m2 := m2) (d := d) (s := s) h (k := k)
      (fun i hi => hs i (by omega))
    rw [copyW_succ, copyW_succ, ldv_congr (m1 := copyW m1 d s k) (m2 := copyW m2 d s k) fun j hj =>
      IH _ (by have := hs (8 * k + j) (by omega); rwa [show s + (8 * k + j) = s + 8 * k + j by omega] at this)]
    exact wl1_congr fun hout => IH a ha

abbrev coalW (W : Mem) (P ps S' hxv hdr0 predP succP : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog W
    [(predP + 16, 8, BitVec.ofNat 64 succP)]) [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(P + ps + 8, 8, BitVec.ofNat 64 (hxv ||| 1))]) [(P + 8, 8, BitVec.ofNat 64 (ps + S' + 1))])
    [(P + ps + 8, 8, BitVec.ofNat 64 hdr0)]

theorem pv_agreeW {C : MCtx} {Mt W : Mem} {P ps S' hxv hdr0 predP succP : Nat}
    (G : PvGeo C P ps S' predP succP) (hxM : read64 Mt (P + ps + 8) = some hdr0)
    (hag : ∀ a, ¬ (P + ps + 8 ≤ a ∧ a < P + ps + 16) →
      ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mt[a]? = W[a]?)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, ¬ (P + 8 ≤ w0 ∧ w0 < P + 16) → ¬ (P + ps + S' + 8 ≤ w0 ∧ w0 < P + ps + S' + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (coalW W P ps S' hxv hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have hdlt := Vsa.Sim.read64_lt _ _ _ hxM
  intro w0 h1' h2'
  refine agree_of_words (P := fun x => ¬ (P + 8 ≤ x ∧ x < P + 16) ∧
      ¬ (P + ps + S' + 8 ≤ x ∧ x < P + ps + S' + 16))
    [succP + 24, predP + 16, P + ps + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨h1', h2'⟩
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
      · rw [rd_miss (by omega), rd_miss (by omega)]; exact hxM
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out]
    · exact hag x (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

structure PvIn (C : MCtx) (B : RB) (Mt W : Mem) (brkv : Nat) (cs₀ rest : List Chunk)
    (bins : Nat → List Nat) (P ps S' L hdr0 hxv hn nb i : Nat) (pre post : List Nat)
    (predP succP : Nat) : Prop where
  heap : PHeapAt W ((B.p, B.nOld) :: C.H) C.top0 brkv
    ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest) bins
  starts : Starts ((B.p, B.nOld) :: C.H)
  addr : P + ps + 16 = B.p
  pv : FPv W (cs₀ ++ [⟨P, ps, false⟩]) bins (P + ps) cs₀ P ps i pre post predP succP
  xW : read64 W (P + ps + 8) = some hxv
  xM : read64 Mt (P + ps + 8) = some hdr0
  nM : read64 Mt (P + ps + S' + 8) = some hn
  nW : read64 W (P + ps + S' + 8) = some (hn / 2 * 2 + 1)
  agree : ∀ a, ¬ (P + ps + 8 ≤ a ∧ a < P + ps + 16) →
    ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mt[a]? = W[a]?
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  grow : B.nOld < C.n.toNat
  nbok : NbOK C.n nb
  fit : nb ≤ ps + S'
  L8 : L % 8 = 0
  Lold : B.nOld ≤ L
  Lle : L + 8 ≤ S'

theorem pvG_rt {C : MCtx} {B : RB} (O : ROK C B) {Mt W : Mem} {brkv : Nat}
    {cs₀ rest : List Chunk} {bins : Nat → List Nat} {P ps S' L hdr0 hxv hn nb i : Nat}
    {pre post : List Nat} {predP succP : Nat}
    (I : PvIn C B Mt W brkv cs₀ rest bins P ps S' L hdr0 hxv hn nb i pre post predP succP)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (P + ps + 16) (L / 8))[a]?)
    (h8 : (R' 8).toNat = P + 16) (h9 : R' 9 = reentV) (h12 : (R' 12).toNat = P)
    (h14 : (R' 14).toNat = ps + S') (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005414#64 R' Mc := by
  have H0 := I.heap
  have HH := H0.heap.heap
  have PV := I.pv
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S' predP succP := PvGeo.of_heap (C := C') H0 PV
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have hxend : P + ps + S' ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have haddr := I.addr
  have hnb := I.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hL8 := I.L8; have hLo := I.Lold; have hLe := I.Lle; have hfit := I.fit

  have hXm : (⟨P + ps, S', true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest := by
    simp
  have hbE : P + ps + S' = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest,
      c.addr = P + ps + S' := by have := HH.end_bnd hXm; simpa using this
  have hpm : predP = binAt i ∨ predP ∈ bins i := by
    have := List.mem_of_getLast? PV.hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [PV.bin]; exact List.mem_append_left _ h1)
  have hsm : succP = binAt i ∨ succP ∈ bins i := by
    have := List.mem_of_head? PV.hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [PV.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨_, hpnode⟩ := HH.node PV.i0 PV.i1 hpm
  obtain ⟨_, hsnode⟩ := HH.node PV.i0 PV.i1 hsm
  have nE8 := HH.bnd_ne_node PV.i1 hpnode hbE 8 (by omega) (by omega)
  have nE16 := HH.bnd_ne_node PV.i1 hsnode hbE 16 (by omega) (by omega)

  have Hd := H0.drop
  simp only [List.append_assoc, List.singleton_append] at Hd
  have hst := I.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact haddr⟩)
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 W (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have hPodd := PV.prev hP hPr
  have hPM : read64 Mt (P + 8) = some hP := by
    rw [read64_keep (m := W) fun k hk => I.agree _ (by omega) (by omega)]; exact hPr
  have Hc := Hd.coalPrev (cs₂ := rest) (b := S') hnoX PV.i0 PV.i1 PV.bin PV.hpred PV.hsucc I.xW
    (h' := ps + S' + 1) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      have := PV.prev h0 hr; unfold prevInuse; rw [show (ps + S' + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hPm : (⟨P, ps + S', true⟩ : Chunk) ∈ cs₀ ++ ⟨P, ps + S', true⟩ :: rest := by simp
  have Ha := Hc.addBlock (q := P + 16) (n := ps + S' - 8) hPm rfl rfl (by simp only; omega)
  generalize hV : copyW (coalW W P ps S' hxv hdr0 predP succP) (P + 16) (P + ps + 16) (L / 8) = V
  have hLw : 8 * (L / 8) = L := by omega
  have HV : PHeapAt V ((P + 16, ps + S' - 8) :: C.H) C.top0 brkv (cs₀ ++ ⟨P, ps + S', true⟩ :: rest)
      (updBins bins i (pre ++ post)) := by
    refine Ha.transport_read fun a ha => ?_
    rw [← hV]
    refine (copyW_out ?_).symm
    rcases ha.1 with hg | ⟨_, _, h3⟩
    · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
    · have := h3 _ List.mem_cons_self; unfold InExt at this; simp only at this; omega
  have Hr := HV.reblock (c := ⟨P, ps + S', true⟩) hPm rfl rfl (n' := C.n.toNat) (by simp only; omega)

  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  generalize hM1 : writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(predP + 16, 8, BitVec.ofNat 64 succP)] = M1 at hMc
  have hag1 : ∀ w, ¬ (P + 8 ≤ w ∧ w < P + 16) → ¬ (P + ps + S' + 8 ≤ w ∧ w < P + ps + S' + 16) →
      M1[w]? = (coalW W P ps S' hxv hdr0 predP succP)[w]? :=
    fun w h1 h2 => by rw [← hM1]; exact pv_agreeW G I.xM I.agree hv1 hv2 w h1 h2
  have hM1o : ∀ a, ¬ (succP + 24 ≤ a ∧ a < succP + 32) → ¬ (predP + 16 ≤ a ∧ a < predP + 24) →
      M1[a]? = Mt[a]? := fun a h1 h2 => by
    rw [← hM1, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a := fun a ha => by
    have hlo := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
    have := offStack_pt I.disj ha; omega
  have HdX : PHeapAt W C.H C.top0 brkv ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest) bins :=
    H0.drop
  have hsrcF : ∀ k, k < S' - 8 → vsaFoot C.H (P + ps + 16 + k) := fun k hk =>
    HdX.payload_foot hXm hnoX _ (by simp only; omega) (by simp only; omega)
  have hpresM1 : ∀ a, vsaFoot C.H a → (M1[a]?).isSome := fun a ha => by
    rw [← hM1]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (I.pres a ha))
  have hMcF : ∀ a, vsaFoot C.H a →
      Mc[a]? = (copyW M1 (P + 16) (P + ps + 16) (L / 8))[a]? := fun a ha => hMc a (hstk a ha)
  have hcpy : ∀ a, ¬ (P + 8 ≤ a ∧ a < P + 16) → ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) →
      (copyW M1 (P + 16) (P + ps + 16) (L / 8))[a]? = V[a]? := fun a h1 h2 => by
    rw [← hV]
    exact copyW_agreeOn (Pr := fun a => ¬ (P + 8 ≤ a ∧ a < P + 16) ∧
        ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16)) (fun a ha => hag1 a ha.1 ha.2)
      (fun i hi => ⟨by omega, by omega⟩) a ⟨h1, h2⟩

  have hnd : ∀ a, P + ps ≤ a → a < P + ps + S' + 8 → M1[a]? = Mt[a]? := fun a h1 h2 =>
    hM1o a (by have := node_off_inuse HH PV.i1 hsnode hXm rfl a h1 h2; omega)
      (by have := node_off_inuse HH PV.i1 hpnode hXm rfl a h1 h2; omega)
  have hnh : ∀ k, k < 8 → vsaFoot C.H (P + ps + S' + 8 + k) := foot_header HdX.heap hbE
  clear hbE hpnode hsnode hpm hsm
  have hStarts : Starts ((P + 16, C.n.toNat) :: C.H) := by
    refine Starts.cons hst.2 fun e he heq => ?_
    have he' : e ∈ (B.p, B.nOld) :: C.H := List.mem_cons_of_mem _ he
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he' he'
    have := HH.chunk_eq hc0 (show (⟨P, ps, false⟩ : Chunk) ∈
      (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest by simp) (by simp only; omega)
    rw [this] at hu; cases hu
  have hPspan : ∀ a, P + 8 ≤ a → a < P + ps + S' + 8 → vsaFoot C.H a := fun a h1 h2 => by
    by_cases ha : a < P + ps + 16
    · exact foot_free_span HdX.heap (c := ⟨P, ps, false⟩) (by simp) rfl a h1 ha
    · exact hsrcF (a - (P + ps + 16)) (by omega) |> fun h => by
        rwa [show P + ps + 16 + (a - (P + ps + 16)) = a by omega] at h
  have hMcV : ∀ a, vsaFoot C.H a → ¬ (P + 8 ≤ a ∧ a < P + 16) →
      ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mc[a]? = V[a]? :=
    fun a h1 h2 h3 => (hMcF a h1).trans (hcpy a h2 h3)
  have hVn : read64 V (P + ps + S' + 8) = some (hn / 2 * 2 + 1) := by
    rw [← hV, read64_keep (m := coalW W P ps S' hxv hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rd_log [I.nW]
  have hMn : read64 Mc (P + ps + S' + 8) = some hn := by
    rw [read64_keep (m := Mt) fun k hk => by
      rw [hMcF _ (hnh k hk), copyW_out (by omega), hM1o _ (by omega) (by omega)]]
    exact I.nM
  refine realloc_tail O (V := V) (X := P) (S := ps + S') (nb := nb) (cs₁ := cs₀) (cs₂ := rest)
    ⟨F, Hr, hStarts, by omega, I.nbok, I.fit, ⟨hP, ?_, ?_⟩, ⟨hn, ?_, ?_⟩, fun w hw h1 h2 => ?_,
      fun a ha => ?_, I.disj, I.disjD, fun k hk => ?_, by have := I.grow; omega, h8, h9, h12, h14, h15⟩
  · rw [read64_keep (m := Mt) fun k hk => ?_]
    · exact hPM
    rw [hMcF _ (hPspan _ (by omega) (by omega)), copyW_out (by omega), hM1o _ (by omega) (by omega)]
  · rw [← hV, read64_keep (m := coalW W P ps S' hxv hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hPodd]
  · rw [show P + (ps + S') + 8 = P + ps + S' + 8 by omega]; exact hMn
  · rw [show P + (ps + S') + 8 = P + ps + S' + 8 by omega]; exact hVn
  · exact hMcV w (vsaFoot_of_cons hw) h1 (by omega)
  · rw [hMcF a ha]; exact copyW_present (hpresM1 a ha)
  · rw [hMcF _ (hPspan _ (by omega) (by omega)),
      copyW_spec (.inl (by omega)) (fun i hi => hpresM1 _ (hsrcF i (by omega))) k (by omega),
      hnd _ (by omega) (by omega), show P + ps + 16 + k = B.p + k by omega]
    exact I.data k hk

theorem pvX_rt {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h8 : (R' 8).toNat = P + 16) (h9 : R' 9 = reentV) (h12 : (R' 12).toNat = P)
    (h14 : (R' 14).toNat = ps + S) (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005414#64 R' Mc := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  have hpend := PV.pend
  subst hpend
  have hXm : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest := by
    simp
  have hS := walk_sizes HH.walk _ hXm
  simp only at hS
  obtain ⟨⟨hn, hnr, hnp⟩, _⟩ := walk_next_of (cs₁ := cs₀ ++ [⟨P, ps, false⟩]) HH.walk
  simp only at hnr hnp
  have hnodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by have := D.addr; simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  exact pvG_rt O (W := Mt) (hxv := hdr0)
    { heap := H0, starts := Hp.starts, addr := D.addr, pv := PV, xW := D.hdr, xM := D.hdr,
      nM := hnr, nW := by rw [hnr]; congr 1; omega, agree := fun _ _ _ => rfl, pres := Hp.pres,
      disj := Hp.disj, disjD := Hp.disjD, data := Hp.data, grow := Hp.grow, nbok := D.nbok,
      fit := hfit, L8 := by omega, Lold := by omega, Lle := by omega }
    F hMc h8 h9 h12 h14 h15

theorem RFrame.agree {C : MCtx} {R : Nat → BitVec 64} {M M' : Mem} (F : RFrame C R M)
    (h : ∀ a, C.s.toNat - 64 + 40 ≤ a → a < C.s.toNat - 64 + 64 → M'[a]? = M[a]?) :
    RFrame C R M' where
  sp := F.sp
  s0 := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.s0
  s1 := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.s1
  ra := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.ra
  s2 := F.s2
  s3 := F.s3

theorem pvX_join {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h13 : (R' 13).toNat = P + 16) (h9 : R' 9 = reentV) (h6 : (R' 6).toNat = P)
    (h17 : (R' 17).toNat = ps + S) (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005648#64 R' Mc := by
  rgn_run O.live at 0x80005414
  refine pvX_rt O D hsp PV hfit (F.of_regs ?_ ?_ ?_) hMc ?_ ?_ ?_ ?_ ?_ <;> carry_close

theorem pv_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h13 : (R 13).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 17).toNat = (R 17).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x80005648#64 R' Mc) :
    AW C.live C.S C.Q 0x80005710#64 R M1 := by
  have rk := O.toWOK.stackRgn
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hn := A.n32; have hn8 := A.n8
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [F.sp]; exact sp64_toNat O.spA
  have e : ∀ c, c < 32 → (R 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c :=
    fun c hc => addr_add hs2 c (by omega)
  have hcp : ∀ (m : Mem) a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat →
      ldv .ld (copyW m d s (n / 8)) a = ldv .ld m a :=
    fun m a h1 h2 => ldv_congr fun k hk => copyW_out (by omega)
  rgn_run O.live at 0x800069c4
  refine memmove_fwd A O.live (by carry_close [h13]) (by carry_close [h8]) (by carry_close [h12])
    (by carry_close) fun R' hK => ?_
  carry_norm
  have hR2 : R' 2 = R 2 := hK.sp
  have hs2' : (R' 2).toNat = C.s.toNat - 64 := hR2 ▸ hs2
  rgn_run O.live at 0x80005648
  simp (disch := omega) only [hR2, e, hs2, hcp, ldv_store_hit, ldv_ld_miss]
  generalize hW : writeLog _ [_] = W
  have hWo : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → W[a]? = M1[a]? := fun a ha => by
    rw [← hW, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ <;>
    try carry_close [hR2, hK.s2, hK.s3, hK.s1]
  · rw [copyW_out (by omega), hWo a (by omega)]
  · exact copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) hWo
      (fun i hi => by omega) a ha

theorem pv_span {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ rest : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest) (hX : X = P + ps) :
    ∀ a, P + 8 ≤ a → a < X + S + 8 → vsaFoot C.H a := by
  subst hX
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HdX : PHeapAt Mt C.H C.top0 brkv ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest) bins :=
    H0.drop
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact D.addr⟩)
  intro a h1 h2
  by_cases ha : a < P + ps + 16
  · exact foot_free_span HdX.heap (c := ⟨P, ps, false⟩) (by simp) rfl a h1 ha
  · exact HdX.payload_foot (c := ⟨P + ps, S, true⟩) (by simp) hnoX a (by simp only; omega)
      (by simp only; omega)

theorem realloc_pvX {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S) (h6 : (R 6).toNat = P) (h17 : (R 17).toNat = ps + S) :
    AW C.live C.S C.Q 0x800055e4#64 R Mt := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have G : PvGeo { C with H := (B.p, B.nOld) :: C.H } P ps S predP succP := PvGeo.of_heap H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D hsp hpend
  subst hpend
  open_fields G; clear G_sP G_sX G_pP G_pX
  have hlo := O.spA.lo; have hhi := O.spA.hi; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have rX : Rgn (vsaFoot C.H) (P + 8) (ps + S) := ⟨fun k hk => hspan _ (by omega) (by omega)⟩
  have rS : Rgn (vsaFoot C.H) (succP + 16) 16 := Rgn.lower (x := (B.p, B.nOld)) ⟨fun k hk => by
    have := G.spfoot (16 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this⟩
  have rP : Rgn (vsaFoot C.H) (predP + 16) 16 := Rgn.lower (x := (B.p, B.nOld)) ⟨fun k hk => by
    have := G.ppfoot (16 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this⟩
  have ha4 := D.a4; have hs0 := D.s0; have hs1 := D.s1; have ha5 := D.a5
  rgn_run O.live at 0x800055ec
  rgn_ld [PV.bk, PV.fd]
  rgn_run O.live at 0x80005600
  rw [show (BitVec.ofNat 64 succP + 24#64).toNat = succP + 24 by rgn_arith,
    show (BitVec.ofNat 64 predP + 16#64).toNat = predP + 16 by rgn_arith]
  have eL : (R 14 + 18446744073709551608#64).toNat = S - 8 := by rgn_arith
  have oX := rX.offStack Hp.disj (by omega); have oS := rS.offStack Hp.disj (by omega)
  have oP := rP.offStack Hp.disj (by omega); unfold mHead at oX oS oP
  have eF : (R 6 + 16#64).toNat = P + 16 := by rgn_arith
  have F1 : RFrame C R (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
      [(predP + 16, 8, BitVec.ofNat 64 succP)]) :=
    (D.frame.store (by omega)).store (by omega)
  have A : CPArgs C.S (P + 16) (P + ps + 16) (S - 8) :=
    { n8 := by omega, d8 := by omega, s8 := by omega, ov := .inl (by omega),
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))),
      dS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))) }
  refine (step% st 0x80005600) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, eL, BitVec.reduceToNat] at hc ⊢
  · refine pv_mm O { A with n32 := by omega } (F1.of_regs ?_ ?_ ?_) (by omega) (by omega) ?_ ?_ ?_
      (fun R' Mc F' hMc g13 g6 g15 g17 g9 => pvX_join O D hsp PV hfit F' hMc ?_ ?_ ?_ ?_ ?_) <;>
      simp only [*, upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · refine pvA_inline A O.live (by omega) rfl ?_ ?_ ?_ ?_ ?_
      fun R' ⟨k2, k6, k9, k13, k15, k16, k17, k18, k19⟩ => pvX_join O D hsp PV hfit
        ((F1.of_regs ?_ ?_ ?_).agree fun a h1 h2 => copyW_out (by omega)) (fun a _ => rfl) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [*, upd_apply, Nat.reduceEqDiff, ite_true, ite_false, BitVec.reduceToNat]
