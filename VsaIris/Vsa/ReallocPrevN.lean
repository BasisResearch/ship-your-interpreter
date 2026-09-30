import VsaIris.Vsa.ReallocPrev

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem pvN_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x800056e0#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x800056c8#64 R (copyW M0 d s j) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  rgn_step hlive at 0x800056e0
  cp_norm
  exact hk _ (by pv_keep K)

theorem pvN_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h16 : (R 16).toNat = d)
    (h12 : (R 12).toNat = L)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x800056e0#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x8000569c#64 R (copyW M0 d s 0) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 8).toNat = s + 8 * j →
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x800056c8#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvN_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
  rgn_step hlive at 0x800056a4
  refine (step% st 0x800056a4) hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · exact tail 0 _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  rgn_step hlive at 0x800056bc
  cp_norm
  refine (step% st 0x800056bc) hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12, BitVec.reduceToNat] at hc'
  · rgn_step hlive at 0x80005808
    cp_norm
    refine (step% st 0x80005808) hlive (fun hc'' => ?_) (fun hc'' => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc''
    · have hL72 : L = 72 := by rw [← h12, hc'']; rfl
      rgn_step hlive at 0x800056c8
      cp_norm
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
    · have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by rw [h12, h]; rfl))
        omega
      rgn_step hlive at 0x800056c8
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))
  · rgn_step hlive at 0x800056c8
    exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by pv_keep (PVKeep.refl R))

end Copy

theorem pvN_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h16 : (R 16).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 16).toNat = (R 16).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x800056e0#64 R' Mc) :
    AW C.live C.S C.Q 0x80005778#64 R M1 := by
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
  refine memmove_fwd A O.live ?_ ?_ ?_ ?_ fun R' hK => ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact h16
  · exact h8
  · exact h12
  · decide
  have hR2 : R' 2 = R 2 := hK.sp
  have hs2' : (R' 2).toNat = C.s.toNat - 64 := hR2 ▸ hs2
  rgn_run O.live at 0x800056e0
  simp (disch := omega) only [hR2, e, hs2, hcp, ldv_store_hit, ldv_ld_miss]
  generalize hW : writeLog _ [_] = W
  have hWo : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → W[a]? = M1[a]? := fun a ha => by
    rw [← hW, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hR2
  · exact hK.s2
  · exact hK.s3
  · rw [copyW_out (by omega), hWo a (by omega)]
  · exact copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) hWo
      (fun i hi => by omega) a ha
  · exact hK.s1

theorem pvN_join {C : MCtx} {B : RB} (O : ROK C B) {Mt W : Mem} {brkv : Nat}
    {cs₀ rest : List Chunk} {bins : Nat → List Nat} {P ps S' L hdr0 hxv hn nb i : Nat}
    {pre post : List Nat} {predP succP : Nat}
    (I : PvIn C B Mt W brkv cs₀ rest bins P ps S' L hdr0 hxv hn nb i pre post predP succP)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (P + ps + 16) (L / 8))[a]?)
    (h16 : (R' 16).toNat = P + 16) (h9 : R' 9 = reentV) (h6 : (R' 6).toNat = P)
    (h13 : (R' 13).toNat = ps + S') (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x800056e0#64 R' Mc := by
  rgn_run O.live at 0x80005414
  refine pvG_rt O I (F.of_regs ?_ ?_ ?_) hMc ?_ ?_ ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;> assumption

theorem pvXN_P {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ cs₃ : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    (hpf : hdr0 % 2 = 0) {bins' : Nat → List Nat} {V : Mem} {hNN pred succ : Nat}
    (N : NAbs C B Mt V brkv (cs₀ ++ [⟨P, ps, false⟩]) cs₃ bins' X S ns hdr0 hNN pred succ)
    (hfit : nb ≤ ps + (S + ns)) {R' : Nat → BitVec 64} (F : RFrame C R' Mt)
    (h6 : (R' 6).toNat = P) (h8 : (R' 8).toNat = X + 16) (h9 : R' 9 = reentV)
    (h12 : (R' 12).toNat = S - 8) (h13 : (R' 13).toNat = ps + (S + ns)) (h15 : (R' 15).toNat = nb)
    (h17 : (R' 17).toNat = 72) :
    AW C.live C.S C.Q 0x80005684#64 R' (unlinkM Mt pred succ) := by
  have Hp := D.heap
  have hS := walk_sizes Hp.heap.heap.heap.walk _ D.mem
  have hSn := walk_sizes N.heap.heap.heap.walk ⟨X, S + ns, true⟩ (by simp)
  simp only at hS hSn
  have hlo := O.spA.lo; have hhi := O.spA.hi; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  obtain ⟨cs₀', p, psz, i, pre, post, predP, succP, PV⟩ := pv_of_heap
    (C := { C with H := (B.p, B.nOld) :: C.H }) (cs₁ := cs₀ ++ [⟨P, ps, false⟩]) (rest := cs₃)
    N.heap N.xW (by omega)
  obtain ⟨hc0, hcP⟩ := List.append_inj' PV.split (by rfl)
  simp only [List.cons.injEq, Chunk.mk.injEq, and_true] at hcP
  obtain ⟨rfl, rfl⟩ := hcP
  subst hc0
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D hsp hpend
  subst hpend
  have G : PvGeo { C with H := (B.p, B.nOld) :: C.H } P ps (S + ns) predP succP :=
    PvGeo.of_heap N.heap PV
  open_fields G; clear G_sP G_sX G_pP G_pX
  have rX : Rgn (vsaFoot C.H) (P + 8) (ps + S) := ⟨fun k hk => hspan _ (by omega) (by omega)⟩
  have rS : Rgn (vsaFoot C.H) (succP + 16) 16 := Rgn.lower (x := (B.p, B.nOld)) ⟨fun k hk => by
    have := G.spfoot (16 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this⟩
  have rP : Rgn (vsaFoot C.H) (predP + 16) 16 := Rgn.lower (x := (B.p, B.nOld)) ⟨fun k hk => by
    have := G.ppfoot (16 + k) (by omega) (by omega); rwa [← Nat.add_assoc] at this⟩
  have hbk : read64 (unlinkM Mt pred succ) (P + 24) = some predP := by
    rw [read64_keep (m := V) fun k hk => N.agree _ (by omega) (by omega)]; exact PV.bk
  have hfd : read64 (unlinkM Mt pred succ) (P + 16) = some succP := by
    rw [read64_keep (m := V) fun k hk => N.agree _ (by omega) (by omega)]; exact PV.fd
  rgn_run O.live at 0x8000568c
  rgn_ld [hbk, hfd]
  rgn_run O.live at 0x80005698
  rw [show (BitVec.ofNat 64 succP + 24#64).toNat = succP + 24 by rgn_arith,
    show (BitVec.ofNat 64 predP + 16#64).toNat = predP + 16 by rgn_arith]
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := Hp.heap.heap.heap.exact _ List.mem_cons_self List.mem_cons_self
    have := Hp.heap.heap.heap.chunk_eq hc0 D.mem (by have := D.addr; simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  have I : PvIn C B (unlinkM Mt pred succ) V brkv cs₀ cs₃ bins' P ps (S + ns)
      (S - 8) hdr0 (S + ns + hdr0 % 2) hNN nb i pre post predP succP :=
    { heap := N.heap, starts := Hp.starts, addr := D.addr, pv := PV, xW := N.xW, xM := N.xM,
      nM := by rw [show P + ps + (S + ns) + 8 = P + ps + S + ns + 8 by omega]; exact N.nM,
      nW := by rw [show P + ps + (S + ns) + 8 = P + ps + S + ns + 8 by omega]; exact N.nW,
      agree := fun a h1 h2 => N.agree a h1 (by omega), pres := N.pres, disj := Hp.disj,
      disjD := Hp.disjD, data := N.data, grow := Hp.grow, nbok := D.nbok, fit := hfit,
      L8 := by omega, Lold := by omega, Lle := by omega }
  have oX := rX.offStack Hp.disj (by omega); have oS := rS.offStack Hp.disj (by omega)
  have oP := rP.offStack Hp.disj (by omega); unfold mHead at oX oS oP
  have eF : (R' 6 + 16#64).toNat = P + 16 := by rgn_arith
  have F1 : RFrame C R' (unlinkM (unlinkM Mt pred succ) predP succP) :=
    ((N.frame R' F).store (by omega)).store (by omega)
  have A : CPArgs C.S (P + 16) (P + ps + 16) (S - 8) :=
    { n8 := by omega, d8 := by omega, s8 := by omega, ov := .inl (by omega),
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))),
      dS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))) }
  refine (step% st 0x80005698) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc ⊢ <;> rw [h17, h12] at hc
  · refine pvN_mm O { A with n32 := by omega } (F1.of_regs ?_ ?_ ?_) (by omega) (by omega) ?_ ?_ ?_
      (fun R'' Mc F' hMc g13 g6 g15 g16 g9 => pvN_join O I F' hMc ?_ ?_ ?_ ?_ ?_) <;>
      simp only [*, upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · refine pvN_inline A O.live (by omega) rfl ?_ ?_ ?_ ?_
      fun R'' ⟨k2, k6, k9, k13, k15, k16, k17, k18, k19⟩ => pvN_join O I
        ((F1.of_regs ?_ ?_ ?_).agree fun a h1 h2 => copyW_out (by omega)) (fun a _ => rfl) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [*, upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

theorem realloc_pvXN {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ cs₃ : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    (hpf : hdr0 % 2 = 0) {iN : Nat} {preN postN : List Nat} {pred succ : Nat}
    (FB : FreeBinAt Mt bins (X + S) iN preN postN pred succ)
    (hfit : nb ≤ ps + (S + ns)) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = ps + (S + ns))
    (h16 : (R 16).toNat = X + S) :
    AW C.live C.S C.Q 0x8000566c#64 R Mt := by
  have Hp := D.heap
  have hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
  have Xk := (Hp.heap.heap.chunkK D.mem).lower; have Nk := (Hp.heap.heap.chunkK hN).lower
  have Nf := (Hp.heap.heap.freeSpan hN rfl).lower
  open_fields Xk; open_fields Nk; simp only at Nf
  have Pk := (Hp.heap.heap.nodeK FB.i0 FB.i1 FB.pred_node).lower
  have Sk := (Hp.heap.heap.nodeK FB.i0 FB.i1 FB.succ_node).lower
  open_fields Pk; open_fields Sk
  have hpl := Vsa.Sim.read64_lt _ _ _ FB.bk; have hsl := Vsa.Sim.read64_lt _ _ _ FB.fd
  have ha4 := D.a4
  rgn_run O.live at 0x80005674
  rgn_ld [FB.bk, FB.fd]
  rgn_run O.live at 0x80005684
  rw [show (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 by rgn_arith,
    show (BitVec.ofNat 64 pred + 16#64).toNat = pred + 16 by rgn_arith]
  obtain ⟨V, hNN, N⟩ := next_absorb O D hsp FB
  refine pvXN_P O D hsp hpf N hfit (D.frame.of_regs ?_ ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact h6
  · exact D.s0
  · exact D.s1
  · rgn_arith
  · exact h13
  · exact D.a5
  · rfl

end VsaIris.VsaHeap
