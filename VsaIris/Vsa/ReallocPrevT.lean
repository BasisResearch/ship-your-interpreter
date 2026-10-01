import VsaIris.Vsa.ReallocPrevN

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem pvT_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x80005574#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x8000555c#64 R (copyW M0 d s j) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  rgn_step hlive at 0x80005574
  cp_norm
  exact hk _ (by pv_keep K)

theorem pvT_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = d)
    (h12 : (R 12).toNat = L)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x80005574#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005530#64 R (copyW M0 d s 0) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 8).toNat = s + 8 * j →
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x8000555c#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvT_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
  rgn_step hlive at 0x80005538
  refine (step% st 0x80005538) hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · exact tail 0 _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  rgn_step hlive at 0x80005550
  cp_norm
  refine (step% st 0x80005550) hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12, BitVec.reduceToNat] at hc'
  · rgn_step hlive at 0x80005878
    cp_norm
    refine (step% st 0x80005878) hlive (fun hc'' => ?_) (fun hc'' => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc''
    · have hL72 : L = 72 := by rw [← h12, hc'']; rfl
      rgn_step hlive at 0x8000555c
      cp_norm
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
    · have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by rw [h12, h]; rfl))
        omega
      rgn_step hlive at 0x8000555c
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  · rgn_step hlive at 0x8000555c
    exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))

end Copy

theorem pvT_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h13 : (R 13).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 16).toNat = (R 16).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x80005574#64 R' Mc) :
    AW C.live C.S C.Q 0x80005818#64 R M1 := by
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [F.sp]; exact sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hn := A.n32; have hn8 := A.n8; have sr := O.stackRgn
  have cpo : ∀ (W : Mem) a, C.s.toNat - 64 ≤ a → a < C.s.toNat → (copyW W d s (n / 8))[a]? = W[a]? :=
    fun _ a h1 h2 => copyW_out (by omega)
  have ldc : ∀ (W : Mem) a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat →
      ldv .ld (copyW W d s (n / 8)) a = ldv .ld W a :=
    fun W a h1 h2 => ldv_congr fun k hk => cpo W _ (by omega) (by omega)
  rgn_step O.live at 0x800069c4
  rw [show (R 2 + sign_extend (m := 64) (0x018#12)).toNat = C.s.toNat - 64 + 24 by rgn_arith,
    show (R 2 + sign_extend (m := 64) (0x010#12)).toNat = C.s.toNat - 64 + 16 by rgn_arith,
    show (R 2 + sign_extend (m := 64) (0x008#12)).toNat = C.s.toNat - 64 + 8 by rgn_arith,
    show (R 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 + 0 by rgn_arith]
  refine memmove_fwd A O.live (by rgn_arith) (by rgn_arith) (by rgn_arith)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide) fun R' hK => ?_
  have hs2' : (R' 2).toNat = C.s.toNat - 64 := by rw [hK.sp]; rgn_arith
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rgn_step O.live at 0x80005574
  rw [show (R' 2 + sign_extend (m := 64) (0x018#12)).toNat = C.s.toNat - 64 + 24 by rgn_arith,
    show (R' 2 + sign_extend (m := 64) (0x010#12)).toNat = C.s.toNat - 64 + 16 by rgn_arith,
    show (R' 2 + sign_extend (m := 64) (0x008#12)).toNat = C.s.toNat - 64 + 8 by rgn_arith,
    show (R' 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 + 0 by rgn_arith]
  simp (disch := omega) only [ldc, ldv_store_hit, ldv_ld_miss]
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_)
    (copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) (fun a ha => ?_)
      fun i hi => by omega) ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [hK.sp, hK.s1, hK.s2, hK.s3, upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals (try rw [cpo _ a (by omega) (by omega)])
  all_goals rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega

theorem pv_agree_self {C : MCtx} {Mt : Mem} {P ps S hdr0 predP succP : Nat}
    (G : PvGeo C P ps S predP succP) (hdr : read64 Mt (P + ps + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, ¬ (P + 8 ≤ w0 ∧ w0 < P + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (coalW Mt P ps S hdr0 hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have e1 := Nat.mod_eq_of_lt (h1 ▸ v1.isLt); have e2 := Nat.mod_eq_of_lt (h2 ▸ v2.isLt)
  have e3 := Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr)
  intro w0 h1'
  refine agree_of_words (P := fun x => ¬ (P + 8 ≤ x ∧ x < P + 16))
    [succP + 24, predP + 16, P + ps + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 h1'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact ⟨predP, by rd_log [h1], by rd_log [BitVec.toNat_ofNat, e1]⟩
    · exact ⟨succP, by rd_log [h2], by rd_log [BitVec.toNat_ofNat, e2]⟩
    · exact ⟨hdr0, by rd_log [hdr], by rd_log [BitVec.toNat_ofNat, e3]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out] <;> simp only [OutL, and_true] <;> omega

structure PvTRet (C : MCtx) (B : RB) (Mf : Mem) (P nb brkv : Nat) (cs₀ : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mf ((P + 16, C.n.toNat) :: C.H) (P + nb) brkv (cs₀ ++ [⟨P, nb, true⟩]) bins
  starts : Starts ((P + 16, C.n.toNat) :: C.H)
  top_le : P + nb ≤ C.top0 + physSize C.n.toNat
  pres : ∀ a, vsaFoot C.H a → (Mf[a]?).isSome
  data : ∀ k, k < B.nOld → Mf[P + 16 + k]? = some (B.old (B.p + k))
  align : (P + 16) % 16 = 0

theorem pvT_heap {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨X, S, true⟩])
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hXt : X + S = C.top0) (hroom : nb + 32 ≤ ps + S + (brkv - C.top0))
    {Mc : Mem}
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    {vT vH vS vP : BitVec 64} (hvT : vT.toNat = P + nb)
    (hvH : vH.toNat = ps + S + (brkv - C.top0) - nb + 1) (hvP : vP.toNat = nb + 1) :
    PvTRet C B (writeLog (writeLog (writeLog (writeLog Mc [(0x8001ad20, 8, vT)])
      [(P + nb + 8, 8, vH)]) [(C.s.toNat - 64, 8, vS)]) [(P + 8, 8, vP)]) P nb brkv cs₀
      (updBins bins i (pre ++ post)) := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') (rest := []) H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D (rest := []) hsp hpend
  subst hpend
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have haddr := D.addr
  have hnb := D.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 ∧ 32 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hlt := D.lt
  have hbrk := HH.brk_le; have hroom0 := H0.heap.top_room
  unfold heapEnd at hbrk
  obtain ⟨ts, rfl⟩ : ∃ ts, brkv = C.top0 + ts := ⟨brkv - C.top0, by omega⟩
  rw [Nat.add_sub_cancel_left] at hroom hvH
  have hlo := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hdisj := Hp.disjD
  unfold allocHeadroom at hdisj
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 512 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => hdisj a (by omega) (by omega) ha

  have hXm : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
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

  have hnd : ∀ a, P + ps ≤ a → a < P + ps + S + 8 →
      (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)])[a]? = Mt[a]? := fun a h1 h2 => by
    have n1 := node_off_inuse HH PV.i1 hsnode hXm rfl a h1 h2
    have n2 := node_off_inuse HH PV.i1 hpnode hXm rfl a h1 h2
    rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  clear hpnode hsnode hpm hsm

  have Hd := H0.drop
  simp only [List.append_assoc, List.singleton_append] at Hd
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact haddr⟩)
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 Mt (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have Hc := Hd.coalPrev (cs₂ := []) (b := S) hnoX PV.i0 PV.i1 PV.bin PV.hpred PV.hsucc D.hdr
    (h' := ps + S + 1) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      have := PV.prev h0 hr; unfold prevInuse; rw [show (ps + S + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hPm : (⟨P, ps + S, true⟩ : Chunk) ∈ cs₀ ++ [⟨P, ps + S, true⟩] := by simp
  have Ha := Hc.addBlock (q := P + 16) (n := S - 8) hPm rfl rfl (by simp only; omega)
  generalize hV : copyW (coalW Mt P ps S hdr0 hdr0 predP succP) (P + 16) (P + ps + 16) ((S - 8) / 8) = V
  have hLw : 8 * ((S - 8) / 8) = S - 8 := by omega
  have HV : PHeapAt V ((P + 16, S - 8) :: C.H) C.top0 (C.top0 + ts) (cs₀ ++ [⟨P, ps + S, true⟩])
      (updBins bins i (pre ++ post)) := by
    refine Ha.transport_read fun a ha => ?_
    rw [← hV]
    refine (copyW_out ?_).symm
    rcases ha.1 with hg | ⟨_, _, h3⟩
    · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
    · have := h3 _ List.mem_cons_self; unfold InExt at this; simp only at this; omega
  have hVP : read64 V (P + 8) = some (ps + S + 1) := by
    rw [← hV, read64_keep (m := coalW Mt P ps S hdr0 hdr0 predP succP) fun k hk => copyW_out (by omega),
      rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hPno : ∀ e ∈ C.H, e.1 ≠ P + 16 := fun e he heq => by
    have he' : e ∈ (B.p, B.nOld) :: C.H := List.mem_cons_of_mem _ he
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he' he'
    have := HH.chunk_eq hc0 (show (⟨P, ps, false⟩ : Chunk) ∈
      (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] by simp) (by simp only; omega)
    rw [this] at hu; cases hu
  have HcH := Hc.heap.heap
  have hfit : ∀ e ∈ (P + 16, S - 8) :: C.H, P + 16 ≤ e.1 → e.1 + e.2 ≤ P + (ps + S) + 8 →
      e.1 + e.2 ≤ P + nb + 8 := by
    intro e he h1 h2
    rcases List.mem_cons.mp he with rfl | he
    · simp only; omega
    obtain ⟨c, hc, _, hca, hcn⟩ := HcH.exact e he he
    rcases HcH.walk.chunk_sep c hc _ hPm with rfl | h3 | h3
    · exact absurd (by simp only at hca; omega) (hPno e he)
    · simp only at h3; omega
    · have := HcH.walk.chunk_bounds c hc; simp only at h3 this; omega
  generalize hV3 : writeLog (writeLog (writeLog V [(0x8001ad20, 8, vT)]) [(P + nb + 8, 8, vH)])
    [(P + 8, 8, vP)] = V3
  have HG := HV.setTop (m' := V3) (x := P) (a := ps + S) (a' := nb) hnbv.2.1 hnbv.2.2 (by omega)
    (h' := nb + 1) (by rw [← hV3, read64_store_hit, hvP]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      rw [hVP] at hr; cases hr; unfold prevInuse
      rw [show (nb + 1) % 2 = 1 by omega, show (ps + S + 1) % 2 = 1 by omega])
    (by rw [← hV3]; unfold topAddr avAddr; rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, hvT])
    (by rw [← hV3, rd_miss (by omega), read64_store_hit, hvH]; congr 1; omega)
    (fun w hw h1 h2 h3 => by
      unfold topAddr avAddr at h2
      rw [← hV3, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega)
    hfit
  have Hr2 := HG.reblock (c := ⟨P, nb, true⟩) (by simp) rfl rfl (n' := C.n.toNat) (by simp only; omega)

  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  generalize hM1 : writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(predP + 16, 8, BitVec.ofNat 64 succP)] = M1 at hMc hnd
  have hag1 : ∀ w, ¬ (P + 8 ≤ w ∧ w < P + 16) → M1[w]? = (coalW Mt P ps S hdr0 hdr0 predP succP)[w]? :=
    fun w h => by rw [← hM1]; exact pv_agree_self G D.hdr hv1 hv2 w h
  have hMV : ∀ a, vsaFoot C.H a → ¬ (P + 8 ≤ a ∧ a < P + 16) → Mc[a]? = V[a]? := fun a ha h => by
    rw [hMc a (by have := hstk a ha; omega), ← hV]
    exact copyW_agreeOn (Pr := fun a => ¬ (P + 8 ≤ a ∧ a < P + 16)) (fun a h => hag1 a h)
      (fun i hi => by omega) a h
  have hpres1 : ∀ a, vsaFoot C.H a → (M1[a]?).isSome := fun a ha => by
    rw [← hM1]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha))
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  refine ⟨Hr2.transport_read fun a ha => ?_, Starts.cons hst.2 hPno, by omega, fun a ha => ?_,
    fun k hk => ?_, by omega⟩
  · have hf : vsaFoot C.H a := vsaFoot_of_cons ha.1
    rw [← hV3]
    refine wl1_congr fun _ => ?_
    have ho : OutL [(C.s.toNat - 64, 8, vS)] a := ⟨by have := hstk a hf; simp only; omega, trivial⟩
    rw [writeLog_out _ _ _ ho]
    exact wl1_congr fun _ => wl1_congr fun _ => (hMV a hf (by omega)).symm
  · refine writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ ?_)))
    rw [hMc a (by have := hstk a ha; omega)]
    exact copyW_present (hpres1 a ha)
  · have hf := hspan (P + 16 + k) (by omega) (by omega)
    have := hstk _ hf
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · rw [hMc _ (by omega), copyW_spec (.inl (by omega))
        (fun i hi => hpres1 _ (hspan _ (by omega) (by omega))) k (by omega),
        hnd _ (by omega) (by omega), show P + ps + 16 + k = B.p + k by omega]
      exact Hp.data k hk
    all_goals simp only [OutL, and_true]; omega

theorem pvT_fin {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨X, S, true⟩])
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hXt : X + S = C.top0) (hroom : nb + 32 ≤ ps + S + (brkv - C.top0))
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h6 : (R' 6).toNat = P) (h15 : (R' 15).toNat = nb)
    (h16 : (R' 16).toNat = ps + S + (brkv - C.top0)) (h13 : (R' 13).toNat = P + 16) :
    AW C.live C.S C.Q 0x80005574#64 R' Mc := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') (rest := []) H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D (rest := []) hsp hpend
  subst hpend
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact D.addr⟩)
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16
  have sP := G.sP; have pP := G.pP
  have hnb := D.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 ∧ 32 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hbrk := HH.brk_le; have hroom0 := H0.heap.top_room
  unfold heapEnd at hbrk
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hs2 : (R' 2).toNat = C.s.toNat - 64 := by rw [F.sp]; exact sp64_toNat O.spA
  have rX : Rgn (vsaFoot C.H) (P + 8) (ps + S) := ⟨fun k hk => hspan _ (by omega) (by omega)⟩
  have rN : Rgn (vsaFoot C.H) (P + nb + 8) 8 := ⟨fun k hk => by
    refine .inr ⟨by show heapStart ≤ _; unfold heapStart; omega,
      by show _ < heapEnd; unfold heapEnd; omega, fun e he hin => ?_⟩
    obtain ⟨c, hc, hu, hca, hcn⟩ := HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    have hPm' : (⟨P, ps, false⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
    have hXm' : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
    have hcb := HH.walk.chunk_bounds c hc
    unfold InExt at hin
    rcases HH.walk.chunk_sep c hc _ hXm' with rfl | h1 | h1
    · exact hnoX e he (by simp only at hca; omega)
    · rcases HH.walk.chunk_sep c hc _ hPm' with rfl | h2 | h2
      · cases hu
      · simp only at h2; omega
      · simp only at h1 h2; omega
    · simp only at h1 hcb; omega⟩
  have rG := globRgn C.H; have sr := O.stackRgn
  have oX := rX.offStack Hp.disj (by omega); have oN := rN.offStack Hp.disj (by omega)
  have oG := rG.offStack Hp.disj (by omega); unfold mHead at oX oN oG
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 Mt (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have hPodd := PV.prev hP hPr
  have hPlt := Vsa.Sim.read64_lt _ _ _ hPr
  have hPc : read64 Mc (P + 8) = some hP := by
    rw [read64_keep (m := Mt) fun k hk => ?_]
    · exact hPr
    rw [hMc _ (by omega), copyW_out (by omega), writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  rgn_step O.live at 0x80005580
  simp only [BitVec.reduceAppend, sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend, BitVec.reduceAdd]
  rgn_step O.live at 0x80005590
  rgn_ld [hPc]
  rgn_run O.live at 0x8000544c
  rw [show (2147593504#64).toNat = 0x8001ad20 from rfl, hs2,
    show (R' 6 + R' 15 + 8#64).toNat = P + nb + 8 by rgn_arith, show (R' 6 + 8#64).toNat = P + 8 by rgn_arith]
  have hvH : (R' 16 - R' 15 ||| 1#64).toNat = ps + S + (brkv - C.top0) - nb + 1 := by
    have ht16 := HH.aligned.2; have hbp := H0.brk_page
    rw [or1_toNat', BitVec.toNat_sub, h16, h15]; omega
  have hvP : (BitVec.ofNat 64 hP &&& 1#64 ||| R' 15).toNat = nb + 1 := by
    rw [BitVec.toNat_or, and1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPlt, hPodd, h15,
      Nat.or_comm, nat_or1]; omega
  have Rt := pvT_heap O D hsp PV hXt hroom hMc (vT := R' 6 + R' 15) (vS := R' 13) (by rgn_arith) hvH hvP
  refine repi O (((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).of_regs
    rfl rfl rfl) fun R'' hR h10 => O.ok R'' _ ?_
  have hp : (R'' 10).toNat = P + 16 := by rw [h10]; exact h13
  refine ⟨hR, ?_, ?_, ⟨P + nb, brkv, cs₀ ++ [⟨P, nb, true⟩], updBins bins i (pre ++ post), ?_, Rt.top_le⟩, Rt.pres,
    fun k hk => ?_⟩ <;> try rw [hp]
  · exact Rt.heap.fresh_of_block Rt.starts
  · exact Rt.align
  · exact Rt.heap
  · exact Rt.data k hk

theorem realloc_pvT {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨X, S, true⟩])
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hXt : X + S = C.top0) (hroom : nb + 32 ≤ ps + S + (brkv - C.top0)) (h6 : (R 6).toNat = P)
    (h16 : (R 16).toNat = ps + S + (brkv - C.top0)) :
    AW C.live C.S C.Q 0x80005510#64 R Mt := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') (rest := []) H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D (rest := []) hsp hpend
  subst hpend
  open_fields G
  have hxend : P + ps + S ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have hlo := O.spA.lo; have hhi := O.spA.hi; have h14 := D.a4
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have rX : Rgn (vsaFoot C.H) (P + 8) (ps + S) := ⟨fun k hk => hspan _ (by omega) (by omega)⟩
  have rS : Rgn (vsaFoot C.H) (succP + 16) 16 := Rgn.lower (x := (B.p, B.nOld))
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.spfoot _ (by omega) (by omega)⟩
  have rP : Rgn (vsaFoot C.H) (predP + 16) 16 := Rgn.lower (x := (B.p, B.nOld))
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.ppfoot _ (by omega) (by omega)⟩
  have oX := rX.offStack Hp.disj (by omega); have oS := rS.offStack Hp.disj (by omega)
  have oP := rP.offStack Hp.disj (by omega); unfold mHead at oX oS oP
  rgn_step O.live at 0x80005520
  rgn_ld [PV.bk, PV.fd]
  rgn_step O.live at 0x8000552c
  rw [show (BitVec.ofNat 64 succP + sign_extend (m := 64) (0x018#12)).toNat = succP + 24 by rgn_arith,
    show (BitVec.ofNat 64 predP + sign_extend (m := 64) (0x010#12)).toNat = predP + 16 by rgn_arith]
  have eL : (R 14 + sign_extend (m := 64) (0xff8#12)).toNat = S - 8 := by rgn_arith
  have eF : (R 6 + sign_extend (m := 64) (0x010#12)).toNat = P + 16 := by rgn_arith
  have e72 : (0#64 + sign_extend (m := 64) (0x048#12)).toNat = 72 := rfl
  have F1 : RFrame C R (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
      [(predP + 16, 8, BitVec.ofNat 64 succP)]) :=
    (D.frame.store (by omega)).store (by omega)
  have A : CPArgs C.S (P + 16) (P + ps + 16) (S - 8) :=
    { n8 := by omega, d8 := by omega, s8 := by omega, ov := .inl (by omega),
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))),
      dS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))) }
  refine (step% st 0x8000552c) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, eL, e72] at hc ⊢
  · exact pvT_mm O { A with n32 := by omega } (F1.of_regs rfl rfl rfl) (by omega) (by omega) eF D.s0 eL
      fun R' Mc F' hMc g13 g6 g15 g16 g9 => pvT_fin O D hsp PV hXt hroom F' hMc (g6.trans h6)
        (g15.trans D.a5) (g16.trans h16) (g13.trans eF)
  · exact pvT_inline A O.live (by omega) rfl D.s0 h6 eF eL fun R' K => pvT_fin O D hsp PV hXt hroom
      ((F1.of_regs K.sp K.s2 K.s3).agree fun a h1 h2 => copyW_out (by omega)) (fun a _ => rfl)
      ((congrArg _ K.t1).trans h6) ((congrArg _ K.a5).trans D.a5) ((congrArg _ K.a6).trans h16)
      ((congrArg _ K.a3).trans eF)

end VsaIris.VsaHeap
