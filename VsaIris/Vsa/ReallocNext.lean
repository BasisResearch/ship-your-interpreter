import VsaIris.Vsa.ReallocMal
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

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

theorem map_reflag_other {q : Nat} {b : Bool} {cs : List Chunk} (h : ∀ c ∈ cs, c.addr + c.size ≠ q) :
    cs.map (reflag q b) = cs := by
  conv => rhs; rw [← List.map_id cs]
  refine List.map_congr_left fun c hc => ?_
  unfold reflag; rw [if_neg (h c hc)]; rfl

abbrev unlinkM (m : Mem) (pred succ : Nat) : Mem :=
  writeLog (writeLog m [(succ + 24, 8, BitVec.ofNat 64 pred)]) [(pred + 16, 8, BitVec.ofNat 64 succ)]

structure NAbs (C : MCtx) (B : RB) (Mt V : Mem) (brkv : Nat) (cs₁ cs₃ : List Chunk)
    (bins : Nat → List Nat) (X S ns hdr0 hNN pred succ : Nat) : Prop where
  heap : PHeapAt V ((B.p, B.nOld) :: C.H) C.top0 brkv (cs₁ ++ ⟨X, S + ns, true⟩ :: cs₃) bins
  xM : read64 (unlinkM Mt pred succ) (X + 8) = some hdr0
  xW : read64 V (X + 8) = some (S + ns + hdr0 % 2)
  nM : read64 (unlinkM Mt pred succ) (X + S + ns + 8) = some hNN
  nW : read64 V (X + S + ns + 8) = some (hNN / 2 * 2 + 1)
  agree : ∀ a, ¬ (X + 8 ≤ a ∧ a < X + 16) → ¬ (X + S + ns + 8 ≤ a ∧ a < X + S + ns + 16) →
    (unlinkM Mt pred succ)[a]? = V[a]?
  pres : ∀ a, vsaFoot C.H a → ((unlinkM Mt pred succ)[a]?).isSome
  data : ∀ k, k < B.nOld → (unlinkM Mt pred succ)[B.p + k]? = some (B.old (B.p + k))
  frame : ∀ R', RFrame C R' Mt → RFrame C R' (unlinkM Mt pred succ)

theorem next_absorb {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₁ cs₃ : List Chunk}
    (hsp : chunks = cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    {i : Nat} {pre post : List Nat} {pred succ : Nat}
    (FB : FreeBinAt Mt bins (X + S) i pre post pred succ) :
    ∃ V hNN, NAbs C B Mt V brkv cs₁ cs₃ (updBins bins i (pre ++ post)) X S ns hdr0 hNN pred succ := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
  have SX : ChunkSec Mt ((B.p, B.nOld) :: C.H) C.top0 brkv chunks X S true := HB.sec D.mem
  have SN : FreeSec Mt ((B.p, B.nOld) :: C.H) C.top0 brkv chunks (X + S) ns := HB.freeSec hN
  sec_arith SX; sec_arith SN.toChunkSec
  have P := HB.nodeSec FB.i0 FB.i1 FB.pred_node
  have Q := HB.nodeSec FB.i0 FB.i1 FB.succ_node
  have := P.lo; have := P.hi; have := P.al; have := Q.lo; have := Q.hi; have := Q.al
  have hbX : X = C.top0 ∨ ∃ c ∈ chunks, c.addr = X := .inr ⟨_, D.mem, rfl⟩
  have nX16s := Q.bnd _ hbX 16 (by omega) (by omega)
  have nE16s := Q.bnd _ SN.next 16 (by omega) (by omega)
  have nE8p := P.bnd _ SN.next 8 (by omega) (by omega)
  have nE16p := P.bnd _ SN.next 16 (by omega) (by omega)
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hfd := FB.fd; have hbk := FB.bk
  have hpl := Vsa.Sim.read64_lt _ _ _ hbk
  have hsl := Vsa.Sim.read64_lt _ _ _ hfd
  have hvP : (BitVec.ofNat 64 pred).toNat = pred := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hvS : (BitVec.ofNat 64 succ).toNat = succ := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  have hXr := D.hdr; have hXs := D.hsz; have hXl := D.hlow
  obtain ⟨hNN, hNNr, hNNp⟩ := SN.nhdr
  have hNNe : hNN % 2 = 0 := by unfold prevInuse at hNNp; simp at hNNp; omega
  have hNNl : hNN % 4 < 2 := by
    rcases SN.next with he | ⟨d, hdm, h2⟩
    · exfalso; have ht := HH.top_header; have hts := HH.top_size
      rw [← he, hNNr] at ht; cases ht; rw [← he] at hts; omega
    · obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d hdm
      rw [h2, hNNr] at hd0r; cases hd0r; exact hd0l
  have hNNlt := Vsa.Sim.read64_lt _ _ _ hNNr
  have hvN : (BitVec.ofNat 64 (hNN + 1)).toNat = hNN + 1 := by rw [BitVec.toNat_ofNat]; omega
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  have hv : (BitVec.ofNat 64 (S + ns + hdr0 % 2)).toNat = S + ns + hdr0 % 2 := by
    rw [BitVec.toNat_ofNat]; omega
  have H0 := Hp.heap
  rw [hsp] at H0
  have H1 := H0.unlink_permit FB.i0 FB.i1 FB.bin (c := ⟨X + S, ns, false⟩) (by simp) rfl FB.hpred
    FB.hsucc (hd' := hNN + 1)
    (m' := writeLog (unlinkM Mt pred succ) [(X + S + ns + 8, 8, BitVec.ofNat 64 (hNN + 1))])
    (fun hd hdr => by
      simp only at hdr; rw [hNNr] at hdr; cases hdr; exact ⟨by unfold chunkSize; omega, by omega⟩)
    (by unfold prevInuse; simp; omega)
    (Realises.of_log (by wl_win <;> exact .inl (by unfold TakeW; omega))
      (by rd_log [hvS, hvP, hvN]) (by rd_log))
  obtain ⟨mid, Wa, Wb⟩ := (show ChunkWalk Mt heapStart C.top0 (cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    from hsp ▸ HH.walk).append_inv
  have HXw := walkHead Wb
  have hmid : X = mid := HXw.addr
  subst hmid
  have HNw := walkHead HXw.rest
  have hWab := Wa.chunk_bounds
  have hWcb := HNw.rest.chunk_bounds
  have hmap : (cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃).map (reflag (X + S + ns) true) =
      cs₁ ++ ⟨X, S, true⟩ :: ⟨X + S, ns, true⟩ :: cs₃ := by
    rw [List.map_append, List.map_cons, List.map_cons,
      map_reflag_other (fun c hc => by have := hWab c hc; omega),
      map_reflag_other (fun c hc => by have := hWcb c hc; simp only at this; omega)]
    simp only [reflag, ite_self, ite_true]
  rw [hmap] at H1
  have hno : ∀ e ∈ (B.p, B.nOld) :: C.H, e.1 ≠ X + S + 16 := fun e he heq => by
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he he
    have := HH.chunk_eq hc0 hN (by simp only; omega)
    rw [this] at hu; cases hu
  have Ha := H1.absorb_permit (x := X) (a := S) (b := ns) hno (h' := S + ns + hdr0 % 2)
    (m' := writeLog (writeLog (unlinkM Mt pred succ) [(X + S + ns + 8, 8, BitVec.ofNat 64 (hNN + 1))])
      [(X + 8, 8, BitVec.ofNat 64 (S + ns + hdr0 % 2))])
    (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      simp (disch := omega) only [read64_miss] at hr
      rw [hXr] at hr; cases hr; unfold prevInuse; rw [show (S + ns + hdr0 % 2) % 2 = hdr0 % 2 by omega])
    (Realises.of_log (by wl_win <;> exact .inl (.inl ⟨by omega, by omega⟩)) (by rd_log [hv]) trivial)
  have hfoot : ∀ w, vsaFoot C.H w → w < C.s.toNat - 256 ∨ C.s.toNat ≤ w := fun w hw =>
    Classical.byContradiction fun hc => D.heap.disj w (by unfold mHead; omega) (by omega) hw
  refine ⟨_, hNN, Ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [read64_miss]; exact hXr
  · simp (disch := omega) only [read64_hit_eq]; rw [hv]
  · simp (disch := omega) only [read64_miss]; exact hNNr
  · rw [show hNN / 2 * 2 + 1 = hNN + 1 by omega]
    simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hvN]
  · intro a h1 h2; symm
    rw [writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩, writeLog_out _ [_] _ ⟨by simp only; omega, trivial⟩]
  · intro a ha; exact writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha))
  · intro k hk
    have hsz8 : B.nOld + 8 ≤ S := by
      obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
      have := HH.chunk_eq hc0 D.mem (by simp only at hc0a ⊢; have := D.addr; omega)
      subst this; simpa using hc0n
    have hb := D.addr
    have hnf : ¬ vsaFoot ((B.p, B.nOld) :: C.H) (B.p + k) := fun hf => by
      rcases hf with hg | ⟨_, _, h3⟩
      · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
      · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
    rw [writeLog_out _ [_] _ ⟨by
        simp only; refine Classical.byContradiction fun hc => hnf ?_
        have := P.fd (B.p + k - (pred + 16)) (by omega)
        rwa [show pred + 16 + (B.p + k - (pred + 16)) = B.p + k by omega] at this, trivial⟩,
      writeLog_out _ [_] _ ⟨by
        simp only; refine Classical.byContradiction fun hc => hnf ?_
        have := Q.bk (B.p + k - (succ + 24)) (by omega)
        rwa [show succ + 24 + (B.p + k - (succ + 24)) = B.p + k by omega] at this, trivial⟩]
    exact Hp.data k hk
  · intro R' F
    have a1 := hfoot _ (vsaFoot_cons_sub _ (Q.bk 0 (by omega)))
    have a2 := hfoot _ (vsaFoot_cons_sub _ (Q.bk 7 (by omega)))
    have a3 := hfoot _ (vsaFoot_cons_sub _ (P.fd 0 (by omega)))
    have a4 := hfoot _ (vsaFoot_cons_sub _ (P.fd 7 (by omega)))
    exact (F.store (a := succ + 24) (w := 8) (by omega)).store (a := pred + 16) (w := 8) (by omega)

theorem realloc_next {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) (hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks)
    (hfit : nb ≤ S + ns) (h16 : (R 16).toNat = X + S) (h17 : (R 17).toNat = S + ns) :
    AW C.live C.S C.Q 0x80005400#64 R Mt := by
  have Hp := D.heap
  have SX : ChunkSec Mt ((B.p, B.nOld) :: C.H) C.top0 brkv chunks X S true := Hp.heap.heap.sec D.mem
  have SN : FreeSec Mt ((B.p, B.nOld) :: C.H) C.top0 brkv chunks (X + S) ns := Hp.heap.heap.freeSec hN
  sec_arith SX; sec_arith SN.toChunkSec
  obtain ⟨cs₁, cs₃, hsp⟩ := Hp.heap.heap.next_eq D.mem hN rfl
  obtain ⟨i, pre, post, pred, succ, FB⟩ := free_bin_at Hp.heap hN rfl
  simp only at FB
  have P := Hp.heap.heap.nodeSec FB.i0 FB.i1 FB.pred_node
  have Q := Hp.heap.heap.nodeSec FB.i0 FB.i1 FB.succ_node
  have := P.lo; have := P.hi; have := P.al; have := Q.lo; have := Q.hi; have := Q.al
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hfd := FB.fd; have hbk := FB.bk
  have hpl := Vsa.Sim.read64_lt _ _ _ hbk
  have hsl := Vsa.Sim.read64_lt _ _ _ hfd
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have eB : (R 16 + sign_extend (m := 64) (0x018#12)).toNat = X + S + 24 := by
    rw [n24, addr_add h16 24 (by omega)]
  have eF : (R 16 + sign_extend (m := 64) (0x010#12)).toNat = X + S + 16 := by
    rw [n16, addr_add h16 16 (by omega)]
  have fB : ∀ k, k < 8 → vsaFoot C.H (X + S + 24 + k) :=
    fun k hk => vsaFoot_cons_sub _ (SN.body _ (by omega) (by omega))
  have fF : ∀ k, k < 8 → vsaFoot C.H (X + S + 16 + k) :=
    fun k hk => vsaFoot_cons_sub _ (SN.body _ (by omega) (by omega))
  have fS : ∀ k, k < 8 → vsaFoot C.H (succ + 24 + k) := fun k hk => vsaFoot_cons_sub _ (Q.bk k hk)
  have fP : ∀ k, k < 8 → vsaFoot C.H (pred + 16 + k) := fun k hk => vsaFoot_cons_sub _ (P.fd k hk)
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
  obtain ⟨V, hNN, N⟩ := next_absorb O D hsp FB
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [D.nbok.eq]; unfold physSize; omega
  have Hr := N.heap.reblock (c := ⟨X, S + ns, true⟩) (by simp) rfl D.addr (n' := C.n.toNat)
    (by simp only; omega)
  rw [← D.addr] at Hr
  refine realloc_tail O (V := V) (X := X) (S := S + ns) (nb := nb) (cs₁ := cs₁) (cs₂ := cs₃)
    ⟨(N.frame R D.frame).of_regs ?_ ?_ ?_, Hr, by rw [D.addr]; exact Hp.starts, by omega, D.nbok, hfit,
      ⟨hdr0, N.xM, N.xW⟩,
      ⟨hNN, by rw [show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact N.nM,
        by rw [show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact N.nW⟩,
      fun w _ hw hw' => N.agree w hw (by omega), N.pres, Hp.disj, Hp.disjD,
      fun k hk => by rw [show X + 16 + k = B.p + k by have := D.addr; omega]; exact N.data k hk,
      by have := Hp.grow; omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [D.s0]
  · exact D.s1
  · exact D.a2
  · rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      addr_add h17 0 (by omega)]; rfl
  · exact D.a5

end VsaIris.VsaHeap
