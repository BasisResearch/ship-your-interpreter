import VsaIris.Vsa.ReallocMove
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}


theorem mal_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R : Nat → BitVec 64} {j : Nat} (h14 : (R 14).toNat = s + 8 * j) (h15 : (R 15).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L)
    (hk : ∀ R', (∀ x, x ≠ 12 → x ≠ 14 → R' x = R x) →
      AW live S Q 0x800053c0#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x800053a8#64 R (copyW M0 d s j) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  rgn_step hlive at 0x800053c0
  cp_norm
  exact hk _ fun x h12 h14 => by simp only [upd_apply, h12, h14, ite_false]


macro "cp_keep" h:term : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;>
  first | exact ($h).sp | exact ($h).s0 | exact ($h).s1 | exact ($h).a0 | exact ($h).a2 |
    exact ($h).a3 | exact ($h).a5 | exact ($h).s2 | exact ($h).s3))

theorem mal_inline {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h10 : (R 10).toNat = d) (h12 : (R 12).toNat = L)
    (h15 : (R 15).toNat = 72)
    (hk : ∀ R', R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 13 = R 13 → R' 18 = R 18 → R' 19 = R 19 →
      AW live S Q 0x800053c0#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005398#64 R (copyW M0 d s 0) := by
  have rs : ARgn S s L := ⟨⟨A.sS⟩, A.slo, A.shi⟩; have rd : ARgn S d L := ⟨⟨A.dS⟩, A.dlo, A.dhi⟩
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 14).toNat = s + 8 * j →
      (R' 15).toNat = d + 8 * j → (∀ x ∈ [2, 8, 9, 13, 18, 19], R' x = R x) →
      AW live S Q 0x800053a8#64 R' (copyW M0 d s j) := fun j R' hj g14 g15 g =>
    mal_tail3 A hlive g14 g15 (by omega) fun R'' hR => by
      have e : ∀ x ∈ [2, 8, 9, 13, 18, 19], R'' x = R x := fun x hx => by
        rw [hR x (by rintro rfl; simp at hx) (by rintro rfl; simp at hx), g x hx]
      rw [hj]
      exact hk R'' (e 2 (by simp)) (e 8 (by simp)) (e 9 (by simp)) (e 13 (by simp)) (e 18 (by simp))
        (e 19 (by simp))
  rgn_step hlive at 0x8000539c
  refine (step% st 0x8000539c) hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · rgn_step hlive at 0x800055d4
    cp_norm
    refine (step% st 0x800055d4) hlive (fun hc' => ?_) (fun hc' => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12, BitVec.reduceToNat] at hc'
    · rgn_step hlive at 0x80005700
      cp_norm
      refine (step% st 0x80005700) hlive (fun hc'' => ?_) (fun hc'' => ?_) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc''
      · have hL72 : L = 72 := by rw [← h12, hc'', h15]
        rgn_step hlive at 0x800053a8
        cp_norm
        exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by simp [upd_apply])
      · have hL56 : L = 56 := by
          have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by rw [h12, h15, h]))
          omega
        rgn_step hlive at 0x800053a8
        exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by simp [upd_apply])
    · rgn_step hlive at 0x800053a8
      exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by simp [upd_apply])
  · rgn_step hlive at 0x800053a8
    exact tail _ _ (by omega) (by rgn_arith) (by rgn_arith) (by simp [upd_apply])

end Copy

theorem mal_copy {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} {d s S : Nat}
    (A : CPArgs C.S d s (S - 8)) (hS32 : 32 ≤ S) (hS16 : S % 16 = 0)
    (hslotD : C.s.toNat - 64 + 8 ≤ d ∨ d + (S - 8) ≤ C.s.toNat - 64)
    (hslotS : C.s.toNat - 64 + 8 ≤ s ∨ s + (S - 8) ≤ C.s.toNat - 64)
    (h8 : (R 8).toNat = s) (h10 : (R 10).toNat = d) (h14 : (R 14).toNat = S) (h13 : R 13 = R 10)
    (hsp : R 2 = C.s + 18446744073709551552#64)
    (hk : ∀ R' Mc, R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 13 = R 13 → R' 18 = R 18 →
      R' 19 = R 19 →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) → Mc[a]? = (copyW Mt d s ((S - 8) / 8))[a]?) →
      AW C.live C.S C.Q 0x800053c0#64 R' Mc) :
    AW C.live C.S C.Q 0x8000538c#64 R Mt := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have St := O.toWOK.stackRgn
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [hsp]; exact hs64
  have hL : ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat = S - 8 := by rgn_arith
  rgn_step O.live at 0x80005394
  refine (step% st 0x80005394) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hL] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x048#12) : BitVec 64).toNat = 72 from rfl] at hc
  · have AM : MMArgs C.S d s (S - 8) := { A with n32 := by omega }
    rgn_run O.live at 0x800069c4
    rw [hs2]
    refine memmove_fwd AM O.live (by rgn_arith) (by rgn_arith) (by rgn_arith)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide) fun R' hK => ?_
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have hslot : read64 (copyW (writeLog Mt [(C.s.toNat - 64, 8, R 10)]) d s ((S - 8) / 8))
        (C.s.toNat - 64) = some (R 10).toNat := by
      rw [read64_keep (m := writeLog Mt [(C.s.toNat - 64, 8, R 10)]) fun k hk => copyW_out (by omega),
        read64_store_hit]
    have h2' : (R' 2).toNat = C.s.toNat - 64 := by rw [hK.sp]; rgn_arith
    rgn_run O.live at 0x800053c0
    rgn_ld [hslot]
    refine hk _ _ hK.sp hK.s0 hK.s1 ?_ hK.s2 hK.s3 fun a ha => copyW_agree (fun a ha => ?_) (by omega) a ha
    · simp only [upd_apply, ite_true]
      rw [h13]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 10).isLt])
    · have ho : OutL [(C.s.toNat - 64, 8, R 10)] a := ⟨by simp only; omega, trivial⟩
      rw [writeLog_out _ _ _ ho]
  ·
    have hLs : S - 8 = 24 ∨ S - 8 = 40 ∨ S - 8 = 56 ∨ S - 8 = 72 := by omega
    exact mal_inline A O.live hLs (by rgn_arith) (by rgn_arith) (by rgn_arith) (by rgn_arith)
      fun R' g2 g8 g9 g13 g18 g19 => hk R' _ g2 g8 g9 g13 g18 g19 fun _ _ => rfl

theorem repi3 {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → R' 10 = R 13 → AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x800053dc#64 R Mt :=
  repi_core O ((step% st 0x800053dc) O.live) ((step% st 0x800053e0) O.live) ((step% st 0x800053e4) O.live) ((step% st 0x800053e8) O.live)
    ((step% st 0x800053ec) O.live) ((step% st 0x800053f0) O.live) F hfin

theorem mal_free {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mc : Mem}
    {p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mc) (h8 : (R 8).toNat = B.p) (h9 : R 9 = reentV) (h13 : (R 13).toNat = p')
    (hp16 : p' % 16 = 0)
    (hheap : PHeapAt Mc ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) top brkv chunks bins)
    (hst : Starts ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H))
    (htop : top ≤ C.top0 + physSize C.n.toNat)
    (hpres : ∀ a, vsaFoot C.H a → (Mc[a]?).isSome)
    (hdisjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hdata : ∀ k, k < B.nOld → Mc[p' + k]? = some (B.old (B.p + k))) (hold : B.nOld ≤ C.n.toNat) :
    AW C.live C.S C.Q 0x800053c0#64 R Mc := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := F.sp
  have St := O.toWOK.stackRgn
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [hsp]; exact hs64
  have hblk : ∀ k, k < C.n.toNat → vsaFoot C.H (p' + k) ∧ ¬ vsaFoot ((p', C.n.toNat) :: C.H) (p' + k) := by
    have hst' : Starts ((p', C.n.toNat) :: C.H) := by
      unfold Starts at *
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
      exact ⟨hst.1.2, hst.2.2⟩
    have Hd : PHeapAt Mc ((p', C.n.toNat) :: C.H) top brkv chunks bins :=
      (hheap.perm (H' := (B.p, B.nOld) :: (p', C.n.toNat) :: C.H) mem_swap).drop
    intro k hk
    refine ⟨Hd.block_foot hst' k hk, fun hf => ?_⟩
    rcases hf with hg | ⟨_, _, h3⟩
    · have := Hd.fresh_of_block hst'
      obtain ⟨_, hlo', hhi', _⟩ := this.block
      have := allocGlobal_off_arena _ hg
      change heapStart ≤ p' at hlo'
      change p' + C.n.toNat ≤ heapEnd at hhi'
      unfold heapStart heapEnd at *; omega
    · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
  rgn_run O.live at 0x80007350
  rw [hs2]
  generalize hM2 : writeLog Mc [(C.s.toNat - 64, 8, R 13)] = M2
  have hM2o : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) → M2[a]? = Mc[a]? := fun a ha => by
    have ho : OutL [(C.s.toNat - 64, 8, R 13)] a := ⟨by simp only; omega, trivial⟩
    rw [← hM2, writeLog_out _ _ _ ho]
  have hfoot : ∀ a, vsaFoot C.H a → (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) := fun a ha =>
    Classical.byContradiction fun hc => hdisjD a (by unfold allocHeadroom; omega) (by omega) ha
  have H2 : PHeapAt M2 ((B.p, B.nOld) :: (p', C.n.toNat) :: C.H) top brkv chunks bins :=
    (hheap.perm mem_swap).transport_read fun a ha => (hM2o a (hfoot a (vsaFoot_cons_sub a
      (vsaFoot_cons_sub a (vsaFoot_perm mem_swap ha.1))))).symm
  refine rcall_free O (link := 0x800053d0#64) (by decide) (fun a ha => vsaFoot_cons_sub a ha) ?_ ?_ ?_ ?_
    H2 hst.swap (fun a ha => by rw [← hM2]; exact writeLog_present _ _ _ (hpres a (vsaFoot_cons_sub a ha)))
    hdisjD (fun R' Mt' g1 g2 g8 g9 g18 g19 hfh hfp hfr => ?_) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hsp
  · first | exact h9 | (rw [h9]; rfl)
  · rgn_arith
  obtain ⟨top', brkv', chunks', bins', H3, htop'⟩ := hfh
  have hkeep : ∀ a, ((C.s.toNat - 64 ≤ a ∧ a < C.s.toNat) ∨ ¬ vsaFoot ((p', C.n.toNat) :: C.H) a ∧
      vsaFoot C.H a) → Mt'[a]? = M2[a]? := by
    intro a ha
    refine hfr a fun hw => ?_
    rcases hw with hf | ⟨h1, h2⟩
    · rcases ha with ⟨h1, h2⟩ | ⟨hn, _⟩
      · exact hdisjD a (by unfold allocHeadroom; omega) h2 (vsaFoot_cons_sub a hf)
      · exact hn hf
    · rw [hs64] at h1 h2
      rcases ha with ⟨h3, _⟩ | ⟨_, hf⟩
      · omega
      · exact hdisjD a (win64_le h1) (by omega) hf
  have hslot : ∀ a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat → read64 Mt' a = read64 M2 a :=
    fun a h1 h2 => read64_keep fun k hk => hkeep _ (.inl ⟨by omega, by omega⟩)
  have hsl : read64 Mt' (C.s.toNat - 64) = some (R 13).toNat := by
    rw [hslot _ (by omega) (by omega), ← hM2, read64_store_hit]
  have h2' : (R' 2).toNat = C.s.toNat - 64 := by rw [g2]; rgn_arith
  rgn_run O.live at 0x800053dc
  rgn_ld [hsl]
  have F' : RFrame C R' Mt' := by
    refine ⟨g2.trans hsp, ?_, ?_, ?_, g18.trans F.s2, g19.trans F.s3⟩
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.s0
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.s1
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.ra
  have hst' : Starts ((p', C.n.toNat) :: C.H) := by
    unfold Starts at *
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
    exact ⟨hst.1.2, hst.2.2⟩
  refine repi3 O (F'.of_regs ?_ ?_ ?_) fun R'' hR h10 => O.ok R'' Mt' ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have hp : (R'' 10).toNat = p' := by
    rw [h10]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 13).isLt, h13]
  refine ⟨hR, ?_, ?_, ⟨top', brkv', chunks', bins', ?_, by omega⟩, fun a ha => ?_, fun k hk => ?_⟩ <;>
    try rw [hp]
  · exact H3.fresh_of_block hst'
  · exact hp16
  · exact H3
  · by_cases hf : vsaFoot ((p', C.n.toNat) :: C.H) a
    · exact hfp a hf
    · rw [hkeep a (.inr ⟨hf, ha⟩), ← hM2]; exact writeLog_present _ _ _ (hpres a ha)
  · obtain ⟨hf, hn⟩ := hblk k (by omega)
    rw [hkeep _ (.inr ⟨hn, hf⟩), hM2o _ (hfoot _ hf)]
    exact hdata k hk

structure RMal (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt : Mem) (X S nb p' top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  frame : RFrame C R Mt
  spNb : read64 Mt (C.s.toNat - 64) = some nb
  spX : read64 Mt (C.s.toNat - 64 + 8) = some X
  spS : read64 Mt (C.s.toNat - 64 + 16) = some S
  heap : PHeapAt Mt ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) top brkv chunks bins
  top_le : top ≤ C.top0 + physSize C.n.toNat
  fresh : FreshAt ((B.p, B.nOld) :: C.H) p' C.n.toNat
  align : p' % 16 = 0
  keepX : (⟨X, S, true⟩ : Chunk) ∈ chunks
  addr : X + 16 = B.p
  starts : Starts ((B.p, B.nOld) :: C.H)
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  nbok : NbOK C.n nb
  nb31 : nb < 2 ^ 31
  lt : S < nb
  grow : B.nOld < C.n.toNat
  s0 : (R 8).toNat = X + 16
  s1 : R 9 = reentV
  a0 : (R 10).toNat = p'

theorem RMal.of_regs {C : MCtx} {B : RB} {R R' : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) (h2 : R' 2 = R 2) (h8 : R' 8 = R 8)
    (h9 : R' 9 = R 9) (h10 : R' 10 = R 10) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) :
    RMal C B R' Mt X S nb p' top brkv chunks bins :=
  { M with frame := M.frame.of_regs h2 h18 h19, s0 := h8 ▸ M.s0, s1 := h9 ▸ M.s1, a0 := h10 ▸ M.a0 }

theorem RMal.starts2 {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem} {X S nb p' top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (M : RMal C B R Mt X S nb p' top brkv chunks bins) :
    Starts ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) :=
  M.starts.cons M.fresh.start

theorem mal_merge {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) (hp' : p' = X + S + 16)
    (h12 : (R 12).toNat = X) (h14 : (R 14).toNat = S) (h15 : (R 15).toNat = nb) :
    AW C.live C.S C.Q 0x800055b0#64 R Mt := by
  have HB := M.heap.heap
  obtain ⟨cN, hcN, huN, hcNa, hcNn⟩ := HB.heap.exact _ List.mem_cons_self List.mem_cons_self
  obtain ⟨Na, ns, Ni⟩ := cN
  simp only at huN hcNa hcNn
  subst huN
  obtain rfl : Na = X + S := by omega
  obtain ⟨cs₁, cs₃, hsp⟩ := HB.next_eq M.keepX hcN rfl
  have Xk := HB.chunkK M.keepX; have Nk := (HB.chunkK hcN).lower.lower
  open_fields Xk; open_fields Nk
  obtain ⟨hX, hXr, hXs, hXl⟩ := Xk_hdrv; obtain ⟨hN, hNr, hNs, hNl⟩ := Nk_hdrv
  obtain ⟨hn, hnr, hnp⟩ := Nk_nhdrv
  have hNlt := Vsa.Sim.read64_lt _ _ _ hNr; have ha0 := M.a0
  rgn_run O.live at 0x80005414
  rgn_ld [hNr]
  have hns : (BitVec.ofNat 64 hN &&& 18446744073709551612#64).toNat = ns := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNlt, ← hNs]; rfl
  have hv : (BitVec.ofNat 64 (S + ns + hX % 2)).toNat = S + ns + hX % 2 := by
    rw [BitVec.toNat_ofNat]; omega
  have H0 := M.heap
  rw [hsp] at H0
  have Ha := H0.drop.absorb_permit (x := X) (a := S) (b := ns) (h' := S + ns + hX % 2)
    (m' := writeLog Mt [(X + 8, 8, BitVec.ofNat 64 (S + ns + hX % 2))])
    (fun e he heq => M.fresh.start e he (by rw [heq, hp'])) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      rw [hXr] at hr; cases hr; unfold prevInuse; rw [show (S + ns + hX % 2) % 2 = hX % 2 by omega])
    (Realises.of_log (by wl_win; exact .inl (.inl ⟨by omega, by omega⟩)) (by rd_log [hv]) trivial)
  have Hr := Ha.reblock (c := ⟨X, S + ns, true⟩) (by simp) rfl M.addr (n' := C.n.toNat)
    (by simp only; omega)
  rw [← M.addr] at Hr
  have hnodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
  have hnb := M.nbok.eq
  refine realloc_tail O (X := X) (S := S + ns) (nb := nb) (cs₁ := cs₁) (cs₂ := cs₃)
    ⟨M.frame.of_regs ?_ ?_ ?_, Hr, by rw [M.addr]; exact M.starts, M.top_le, M.nbok,
      by rw [hnb]; unfold physSize; omega, ⟨hX, hXr, by simp (disch := omega) only [read64_hit_eq]; rw [hv]⟩,
      ⟨hn, by rw [show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact hnr, by
        rw [show hn / 2 * 2 + 1 = hn by omega, rd_miss (by omega),
          show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact hnr⟩,
      fun w _ hw _ => (writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩).symm, M.pres, M.disj,
      M.disjD, by rw [M.addr]; exact M.data, by have := M.grow; omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [M.s0]
  · exact M.s1
  · exact h12
  · rw [BitVec.toNat_add, h14, hns, Nat.mod_eq_of_lt (by omega)]
  · exact h15

theorem mal_null {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    (F : RFrame C R Mt) (h10 : R 10 = 0#64)
    (hheap : ∃ top brkv chunks bins, PHeapAt Mt ((B.p, B.nOld) :: C.H) top brkv chunks bins)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hdata : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k)))
    (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x80005364#64 R Mt := by
  have hlo := O.spA.lo; have hhi := O.spA.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have St := O.toWOK.stackRgn
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [F.sp]; exact sp64_toNat O.spA
  rgn_step O.live at 0x80005374
  refine (step% st 0x80005374) O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
  · sx_run [12] O.live at 0x800054c4
    refine repi0 O (F.of_regs ?_ ?_ ?_) fun R' hR h13 => O.null R' Mt ⟨hR, ?_, hheap, hpres, hdata, hst⟩ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
    rw [h13]; rfl
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10

theorem mal_ok {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) :
    AW C.live C.S C.Q 0x80005364#64 R Mt := by
  have HH := M.heap.heap.heap
  have hlo := O.spA.lo; have hhi := O.spA.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := M.frame.sp
  have St := O.toWOK.stackRgn
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [hsp]; exact sp64_toNat O.spA
  rgn_run O.live at 0x80005374
  rgn_ld [M.spNb, M.spX, M.spS]
  clear St
  have hXm := M.keepX
  have Xk := (M.heap.heap.chunkK hXm).lower.lower
  open_fields Xk; clear Xk_next Xk_nhdr
  obtain ⟨hX, hXr, hXs, hXl⟩ := Xk_hdrv
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  obtain ⟨_, hp'lo, hp'hi, hp'dj⟩ := M.fresh.block
  change heapStart ≤ p' at hp'lo
  change p' + C.n.toNat ≤ heapEnd at hp'hi
  unfold heapStart at hp'lo; unfold heapEnd at hp'hi
  have hnb := M.nbok.eq
  have hnblt : nb < 2 ^ 64 := by have := M.nb31; omega
  have h8 := M.s0; have h10 := M.a0
  refine (step% st 0x80005374) O.live (fun hc => absurd hc ?_) (fun _ => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    intro h0; have := congrArg BitVec.toNat h0; rw [M.a0] at this; simp at this; omega
  rgn_run O.live at 0x80005388
  rgn_ld [hXr]
  have hS' : (BitVec.ofNat 64 hX &&& 18446744073709551614#64).toNat = S := by
    rw [toNat_and_m2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hXlt]
    unfold chunkSize at hXs; omega
  have hXv : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; omega
  have hN : (R 10 + 18446744073709551600#64).toNat = p' - 16 := by rgn_arith
  refine (step% st 0x80005388) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · have hm : X + S = p' - 16 := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, hXv, hS', hN, Nat.mod_eq_of_lt (by omega)] at this; exact this
    exact mal_merge O (M.of_regs rfl rfl rfl rfl rfl rfl) (by omega) (by rgn_arith) (by rgn_arith)
      (by rgn_arith)
  have hne : X + S ≠ p' - 16 := fun h => hc (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, hXv, hS', hN, Nat.mod_eq_of_lt (by omega)]; exact h))
  have hst2 := M.starts2
  have hstN : Starts ((p', C.n.toNat) :: C.H) := by
    unfold Starts at *
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
    exact ⟨hst2.1.2, hst2.2.2⟩
  have HN : PHeapAt Mt ((p', C.n.toNat) :: C.H) top brkv chunks bins := (M.heap.perm mem_swap).drop
  have HO : PHeapAt Mt C.H top brkv chunks bins := M.heap.drop.drop
  have hnoX : ∀ e ∈ C.H, e.1 ≠ X + 16 := by
    have := M.starts; unfold Starts at this; rw [List.map_cons, List.nodup_cons] at this
    exact fun e he heq => this.1 (List.mem_map.2 ⟨e, he, by rw [heq, M.addr]⟩)
  have rS : Rgn (vsaFoot C.H) (X + 16) (S - 8) :=
    ⟨fun k hk => HO.payload_foot hXm hnoX _ (by simp only; omega) (by simp only; omega)⟩
  have rD : Rgn (vsaFoot C.H) p' C.n.toNat := ⟨HN.block_foot hstN⟩
  have hSn : S - 8 < C.n.toNat := by rw [hnb] at M; have := M.lt; unfold physSize at this; omega
  obtain ⟨cN, hcN, _, hcNa, hcNn⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
  simp only at hcNa hcNn
  have hNb := HH.walk.chunk_bounds cN hcN
  have hov : p' ≤ X + 16 ∨ X + 16 + (S - 8) ≤ p' := by
    rcases HH.walk.chunk_sep cN hcN _ hXm with rfl | h3 | h3
    · exfalso; have := M.addr
      exact M.fresh.start (B.p, B.nOld) List.mem_cons_self (by simp only at hcNa ⊢; omega)
    · left; simp only at h3; omega
    · right; simp only at h3; omega
  have oS := rS.offStack M.disj (by omega); have oD := rD.offStack M.disj (by omega)
  unfold mHead at oS oD
  have A : CPArgs C.S p' (X + 16) (S - 8) :=
    { n8 := by omega, d8 := by have := M.align; omega, s8 := by omega, ov := hov,
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (rS.byte k hk)),
      dS := fun k hk => O.own _ (.inl (rD.byte k (by omega))) }
  refine mal_copy O A (by omega) Xk_sz16 (by omega) (by omega) (by rgn_arith) (by rgn_arith) (by rgn_arith)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hsp)
    fun R' Mc g2 g8 g9 g13 g18 g19 hMc => ?_
  have hL8 : 8 * ((S - 8) / 8) = S - 8 := by omega
  have hMcF : ∀ a, vsaFoot C.H a → Mc[a]? = (copyW Mt p' (X + 16) ((S - 8) / 8))[a]? := fun a ha =>
    hMc a (by have := offStack_pt M.disj ha; omega)
  have hMcS : ∀ a, C.s.toNat - 64 + 8 ≤ a → a < C.s.toNat → Mc[a]? = Mt[a]? := fun a h1 h2 => by
    rw [hMc a (by omega), copyW_out (by omega)]
  have hslot : ∀ a, C.s.toNat - 64 + 8 ≤ a → a + 8 ≤ C.s.toNat → read64 Mc a = read64 Mt a :=
    fun a h1 h2 => read64_keep fun k hk => hMcS _ (by omega) (by omega)
  have F := M.frame
  have hblk : ∀ a, vsaFoot ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) a → ¬ (p' ≤ a ∧ a < p' + (S - 8)) :=
    fun a ha hin => by
      rcases ha with hg | ⟨_, _, h3⟩
      · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
      · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
  refine mal_free O (brkv := brkv) (chunks := chunks) (bins := bins)
    ⟨g2.trans hsp, ?_, ?_, ?_, g18.trans F.s2, g19.trans F.s3⟩ (by rw [g8]; exact M.s0.trans M.addr)
    (g9.trans M.s1) (by rw [g13]; exact M.a0) M.align ?_ M.starts2 M.top_le ?_ M.disjD ?_
    (by have := M.grow; omega)
  · rw [hslot _ (by omega) (by omega)]; exact F.s0
  · rw [hslot _ (by omega) (by omega)]; exact F.s1
  · rw [hslot _ (by omega) (by omega)]; exact F.ra
  · refine M.heap.transport_read fun a ha => ?_
    have hf := vsaFoot_cons_sub a (vsaFoot_cons_sub a ha.1)
    rw [hMcF a hf, copyW_out (by have := hblk a ha.1; omega)]
  · intro a ha; rw [hMcF a ha]; exact copyW_present (M.pres a ha)
  · intro k hk
    have hk' : k < C.n.toNat := by have := M.grow; omega
    have hold := M.grow
    have hS8 : B.nOld + 8 ≤ S := by
      obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact (B.p, B.nOld) (List.mem_cons_of_mem _ List.mem_cons_self)
        (List.mem_cons_of_mem _ List.mem_cons_self)
      have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; have := M.addr; omega)
      subst this; simpa using hc0n
    rw [hMcF _ (rD.byte k hk'), copyW_spec (by rw [hL8]; exact hov)
      (fun i hi => M.pres _ (rS.byte i (by omega))) k (by omega),
      show X + 16 + k = B.p + k by rw [M.addr]]
    exact M.data k hk

theorem realloc_mal {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) :
    AW C.live C.S C.Q 0x80005350#64 R Mt := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := D.frame.sp
  have St := O.toWOK.stackRgn
  have hs2 : (R 2).toNat = C.s.toNat - 64 := by rw [hsp]; exact hs64
  rgn_run O.live at 0x800047a8
  rw [show (R 2 + 16#64).toNat = C.s.toNat - 64 + 16 by rgn_arith,
    show (R 2 + 8#64).toNat = C.s.toNat - 64 + 8 by rgn_arith, hs2]
  have Hp := ((D.heap.store_stack (a := C.s.toNat - 64 + 16) (w := 8) (v := R 14) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 8) (w := 8) (v := R 12) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64) (w := 8) (v := R 15) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog Mt [(C.s.toNat - 64 + 16, 8, R 14)])
    [(C.s.toNat - 64 + 8, 8, R 12)]) [(C.s.toNat - 64, 8, R 15)] = M1 at Hp ⊢
  have hrd : ∀ a, a + 8 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ a → read64 M1 a = read64 Mt a := fun a ha => by
    rw [← hM1, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)]
  have hX8 : read64 M1 (B.p - 8) = some hdr0 := by
    have := D.addr; have := D.hdr
    rw [hrd _ (by
      have hf := foot_header D.heap.heap.heap (.inr ⟨_, D.mem, rfl⟩)
      have := off_stack_of D.heap.disj fun k hk => vsaFoot_cons_sub _ (hf k hk)
      simp only at this; omega), show B.p - 8 = X + 8 by omega]
    exact D.hdr

  have hwin : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat → ¬ MWin ((B.p, B.nOld) :: C.H)
      (C.s + 18446744073709551552#64) a := fun a h1 h2 hw => by
    rcases hw with hf | ⟨h3, h4⟩
    · exact D.heap.disj a (by unfold mHead; omega) h2 (vsaFoot_cons_sub a hf)
    · rw [hs64] at h4; omega
  have hFr : ∀ (Mt' : Mem), (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat → read64 Mt' a = read64 M1 a :=
    fun Mt' hf a h1 h2 => read64_keep fun k hk => hf _ (hwin _ (by omega) (by omega))

  have hbA : ∀ k, k < B.nOld → heapStart ≤ B.p + k ∧ B.p + k < heapEnd := by
    obtain ⟨c, hc, _, h8, h9⟩ := D.heap.heap.heap.heap.live _ List.mem_cons_self
    have := D.heap.heap.heap.heap.walk.chunk_bounds c hc
    have := D.heap.heap.heap.heap.brk_le; have := D.heap.heap.heap.heap.top_le
    have := D.heap.heap.heap.top_room
    simp only at h8 h9; intro k hk; unfold heapStart heapEnd at *; omega
  have hblkw : ∀ k, k < B.nOld → ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) (B.p + k) :=
    fun k hk hw => by
      obtain ⟨hA1, hA2⟩ := hbA k hk
      rcases hw with hf' | ⟨h3, h4⟩
      · rcases hf' with hg | ⟨_, _, h5⟩
        · have := allocGlobal_off_arena _ hg; omega
        · exact h5 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
      · rw [hs64] at h3 h4
        exact D.heap.disjD _ (win64_le h3) (by omega) (D.heap.blk k hk)
  have hbd : ∀ k, k < B.nOld → M1[B.p + k]? = some (B.old (B.p + k)) := fun k hk => by
    exact Hp.data k hk
  have hsl : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ a, vsaFoot C.H a → ¬ vsaFoot ((B.p, B.nOld) :: C.H) a →
      (Mt'[a]?).isSome ∧ ∀ k, k < B.nOld → Mt'[B.p + k]? = some (B.old (B.p + k)) :=
    fun Mt' hf a ha hna => ⟨by
      rw [hf a fun hw => ?_]
      · exact Hp.pres a ha
      rcases hw with hf' | ⟨h3, h4⟩
      · exact hna hf'
      · rw [hs64] at h3 h4; exact D.heap.disjD _ (win64_le h3) (by omega) ha,
      fun k hk => by rw [hf _ (hblkw k hk)]; exact hbd k hk⟩
  have hpres' : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → (∀ a, vsaFoot ((B.p, B.nOld) :: C.H) a → (Mt'[a]?).isSome) →
      ∀ a, vsaFoot C.H a → (Mt'[a]?).isSome := fun Mt' hf hp a ha => by
    by_cases h : vsaFoot ((B.p, B.nOld) :: C.H) a
    · exact hp a h
    · exact (hsl Mt' hf a ha h).1
  have hdata' : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ k, k < B.nOld → Mt'[B.p + k]? = some (B.old (B.p + k)) :=
    fun Mt' hf k hk => by rw [hf _ (hblkw k hk)]; exact hbd k hk
  have hF : ∀ (R' : Nat → BitVec 64) (Mt' : Mem), R' 2 = R 2 → R' 18 = R 18 → R' 19 = R 19 →
      (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a → Mt'[a]? = M1[a]?) →
      RFrame C R' Mt' := fun R' Mt' g2 g18 g19 hf => by
    have F := D.frame
    refine ⟨g2.trans hsp, ?_, ?_, ?_, g18.trans F.s2, g19.trans F.s3⟩ <;>
      rw [hFr Mt' hf _ (by omega) (by omega), ← hM1, rd_miss (by omega), rd_miss (by omega),
        rd_miss (by omega)]
    · exact F.s0
    · exact F.s1
    · exact F.ra
  refine rcall_malloc O (n := C.n) (link := 0x80005364#64) (by decide) (fun a ha => vsaFoot_cons_sub a ha) ?_ ?_ ?_ ?_
    Hp.heap (fun a ha => Hp.pres a (vsaFoot_cons_sub a ha)) D.heap.disjD
    (fun R' Mt' g1 g2 g8 g9 g18 g19 hfr hal' hheap' hpres'' hframe' => ?_)
    (fun R' Mt' g1 g2 g8 g9 g18 g19 h10 hheap' hpres'' hframe' hst => ?_) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hsp
  · first | exact D.s1 | (rw [D.s1]; rfl)
  · exact D.a1
  ·
    obtain ⟨top', brkv', chunks', bins', H', htop', hkeep⟩ := hheap'
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at g2 g8 g9 g18 g19
    have F' := hF R' Mt' g2 g18 g19 hframe'
    have hkX : (⟨X, S, true⟩ : Chunk) ∈ chunks' := by
      have := hkeep (B.p, B.nOld) List.mem_cons_self hdr0 hX8
      have ha := D.addr; have hs := D.hsz
      simp only at this
      rwa [show B.p - 16 = X by omega, hs] at this
    refine mal_ok O (X := X) (S := S) (nb := nb) (p' := (R' 10).toNat)
      ⟨F', ?_, ?_, ?_, H', by omega, hfr, hal', hkX, D.addr, D.heap.starts, hpres' Mt' hframe' hpres'',
        D.heap.disj, D.heap.disjD, hdata' Mt' hframe', D.nbok, D.nb31, D.lt, D.heap.grow, ?_, ?_, rfl⟩
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1, read64_store_hit, D.a5]
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1, rd_miss (by omega), read64_store_hit, D.a2]
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1, rd_miss (by omega), rd_miss (by omega),
        read64_store_hit, D.a4]
    · rw [g8, D.s0]
    · rw [g9, D.s1]
  ·
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at g2 g8 g9 g18 g19
    exact mal_null O (hF R' Mt' g2 g18 g19 hframe') h10 hheap' (hpres' Mt' hframe' hpres'')
      (hdata' Mt' hframe') hst

end VsaIris.VsaHeap
