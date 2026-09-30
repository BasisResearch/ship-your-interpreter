import VsaIris.Vsa.FreeLarge
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure FNt (C : MCtx) (R : Nat → BitVec 64) (Mt Mt1 : Mem) (brkv : Nat) (cs₁ cs₃ : List Chunk)
    (d : Chunk) (bins : Nat → List Nat) (x sz hdr0 hnn : Nat) (w : BitVec 64) : Prop where
  frame : FFrame C R Mt1
  mem : Mt1 = writeLog Mt [(x + sz + 8, 8, w)]
  wv : w.toNat = d.size
  heap : PHeapAt Mt C.H C.top0 brkv (cs₁ ++ ⟨x, sz, true⟩ :: d :: cs₃) bins
  hno : ∀ e ∈ C.H, e.1 ≠ x + 16
  starts : Starts C.H
  daddr : d.addr = x + sz
  hdr : read64 Mt (x + 8) = some hdr0
  hsz : chunkSize hdr0 = sz
  hlow : hdr0 % 4 < 2
  nnr : read64 Mt (x + sz + d.size + 8) = some hnn
  nnf : prevInuse hnn = d.inuse
  pres : ∀ a, vsaFoot C.H a → (Mt1[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt1[a]? = C.Mt0[a]?
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a1 : (R 11).toNat = x + 16
  a2 : (R 12).toNat = x + sz
  a3 : (R 13).toNat = d.size
  a4 : (R 14).toNat = x
  a5 : (R 15).toNat = sz
  a0 : (R 10).toNat = hdr0
  t1 : (R 6).toNat = hdr0 % 2
  a6 : (R 16).toNat = hnn % 2

theorem free_nt {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {x sz hdr0 nh : Nat}
    (D : FDec C R Mt q n brkv chunks bins x sz hdr0 nh) (hnt : x + sz ≠ C.top0)
    (hk : ∀ R' Mt1 cs₁ cs₃ d hnn w, FNt C R' Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w →
      AW C.live C.S C.Q 0x800073ac#64 R' Mt1) :
    AW C.live C.S C.Q 0x8000739c#64 R Mt := by
  have Hp := D.heap; have K := D.chunk
  obtain ⟨cs₁, d, cs₃, hsplit, hda⟩ := Hp.heap.heap.next K.mem hnt
  simp only at hda
  have hdm : d ∈ chunks := by rw [hsplit]; simp
  have X := (Hp.heap.heap.chunkK K.mem).lower; have Dk := (Hp.heap.heap.chunkK hdm).lower
  open_fields X; open_fields Dk
  obtain ⟨hdh, hdhr, hdhs, _⟩ := Dk.hdrv
  rw [hda, K.next] at hdhr
  obtain rfl : nh = hdh := Option.some.inj hdhr
  obtain ⟨hnn, hnnr, hnnf⟩ := Dk.nhdrv
  have hoN := X_nhdr.offStack Hp.disj (by decide)
  have ha2 := D.a2; have ha3 := D.a3
  unfold mHead at hoN
  rgn_run O.live at 0x800073ac
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  refine hk _ _ cs₁ cs₃ d hnn (R 13) ⟨(D.frame.store (by rgn_arith)).of_regs ?_ ?_ ?_ ?_,
    by rw [show (R 12 + 8#64).toNat = x + sz + 8 by rgn_arith], by rw [ha3]; exact hdhs, hsplit ▸ Hp.heap.drop,
    fun e he heq => hst.1 (List.mem_map.2 ⟨e, he, by rw [heq, K.addr]⟩), hst.2, hda, K.hdr, K.hsz,
    K.hlow, hda ▸ hnnr, hnnf, pres_log _ Hp.pres, Hp.disj, frame_log (by log_in) Hp.frame,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact D.s0
  · exact D.a7
  · rw [D.a1, ← K.addr]
  · exact ha2
  · rw [ha3, hdhs]
  · exact D.a4
  · exact D.a5
  · exact D.a0
  · exact D.t1
  · rw [ldv_at hnnr _ (by rgn_arith), BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hnnr),
      show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

structure FNtGeo (C : MCtx) (Mt : Mem) (d : Chunk) (x sz : Nat) : Prop where
  x16 : x % 16 = 0
  xlo : 0x8001c170 ≤ x
  sz16 : sz % 16 = 0
  sz32 : 32 ≤ sz
  d16 : (x + sz) % 16 = 0
  dsz16 : d.size % 16 = 0
  dsz32 : 32 ≤ d.size
  dend : x + sz + d.size ≤ C.top0
  top : C.top0 + 16 ≤ heapEnd
  dhdr : ∃ hd, read64 Mt (x + sz + 8) = some hd ∧ chunkSize hd = d.size ∧ hd % 4 < 2
  xfoot : ∀ a, x + 8 ≤ a → a < x + sz + 8 → vsaFoot C.H a
  hfoot : ∀ k, k < 8 → vsaFoot C.H (x + 8 + k)
  nfoot : ∀ k, k < 8 → vsaFoot C.H (x + sz + 8 + k)

theorem FNt.geo {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₁ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) : FNtGeo C Mt d x sz := by
  have HH := N.heap.heap.heap
  have hX : (⟨x, sz, true⟩ : Chunk) ∈ cs₁ ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hD : d ∈ cs₁ ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hXb := HH.walk.chunk_bounds _ hX
  have hDb := HH.walk.chunk_bounds _ hD
  obtain ⟨hal, _⟩ := HH.aligned
  have hx16 := hal _ hX; have hd16 := hal _ hD
  have hs := walk_sizes HH.walk _ hX; have hds := walk_sizes HH.walk _ hD
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := N.heap.heap.top_room
  simp only at hXb hx16 hs
  rw [N.daddr] at hd16 hDb
  obtain ⟨hd, hdr, hds', hdl⟩ := walk_header HH.walk d hD
  rw [N.daddr] at hdr
  unfold heapStart at hXb
  exact ⟨hx16, hXb.1, hs.1, hs.2, hd16, hds.1, hds.2, hDb.2.1, by omega, ⟨hd, hdr, hds', hdl⟩,
    fun a h1 h2 => foot_of_chunk N.heap hX N.hno h1 h2,
    foot_header N.heap.heap (.inr ⟨_, hX, rfl⟩),
    by rw [← N.daddr]; exact foot_header N.heap.heap (.inr ⟨_, hD, rfl⟩)⟩

theorem free_b1a {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₁ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hprev : hdr0 % 2 = 1)
    (hdin : d.inuse = true) :
    AW C.live C.S C.Q 0x80007484#64 R Mt1 := by
  have G := N.geo
  open_fields G
  have rX : Rgn (vsaFoot C.H) (x + 8) sz := ⟨fun k hk => G.xfoot _ (by omega) (by omega)⟩
  have oX := rX.offStack N.disj (by omega); unfold mHead at oX
  unfold heapEnd at G_top
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨hd0, hd0r, hd0s, _⟩ := G.dhdr
  have ha1 := N.a1; have ha2 := N.a2; have ha0 := N.a0
  have hdrlt := Vsa.Sim.read64_lt _ _ _ N.hdr
  rgn_run O.live at 0x80007490
  rw [show (R 11 + 18446744073709551608#64).toNat = x + 8 by rgn_arith, ha2]
  have hor : (hdr0 ||| 1) = hdr0 := by
    have h1 : (hdr0 ||| 1) / 2 = hdr0 / 2 := by
      have := Nat.or_div_two_pow (a := hdr0) (b := 1) (n := 1); simpa using this
    have h2 : (hdr0 ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
    have := Nat.div_add_mod (hdr0 ||| 1) 2; have := Nat.div_add_mod hdr0 2
    omega
  have hval : (R 10 ||| 1#64).toNat = hdr0 := by rw [BitVec.toNat_or, ha0]; simpa using hor
  generalize hMp : writeLog (writeLog Mt1 [(x + 8, 8, R 10 ||| 1#64)]) [(x + sz, 8, R 15)] = Mp
  have hM1 := N.mem
  have B : FBin C Mp Mt x sz C.top0 brkv cs₁ (d :: cs₃) bins := by
    refine ⟨⟨N.heap, Nat.le_refl _, N.hno, fun h0 hh0 => ?_, fun d' hd' => ?_, by omega,
      ?_, ?_, fun hd hr => ?_⟩, ?_, N.disj, ?_⟩
    · rw [N.hdr] at hh0; cases hh0; exact hprev
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd'; rw [← hd']; exact hdin
    · intro w0 hw0 hr0
      refine agree_of_words (P := fun a => vsaFoot C.H a ∧ ¬ (x + sz ≤ a ∧ a < x + sz + 16)) [x + 8]
        (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨hw0, hr0⟩
      · simp only [List.mem_singleton] at hw'; subst hw'
        refine ⟨hdr0, ?_, N.hdr⟩
        rw [← hMp, rd_miss (by omega), read64_store_hit, hval]
      · simp only [List.mem_singleton, forall_eq] at hout
        have := ha.2
        rw [← hMp, hM1, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
    · rw [← hMp, read64_store_hit, N.a5]
    · rw [hd0r] at hr; cases hr
      refine ⟨d.size, ?_, by unfold chunkSize at hd0s ⊢; omega, by omega,
        by unfold prevInuse; simp; omega⟩
      rw [← hMp, rd_miss (by omega), rd_miss (by omega), hM1, read64_store_hit, N.wv]
    · rw [← hMp]; exact pres_log _ (pres_log _ N.pres)
    · rw [← hMp, writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) N.frameM
  refine free_bin2 O (hMp ▸ ((N.frame.store (a := x + 8) (w := 8) (by omega)).store (a := x + sz)
    (w := 8) (by omega)).of_regs ?_ ?_ ?_ ?_) B ?_ ?_ ?_ <;>
    (try simp only [upd_apply, Nat.reduceEqDiff, ite_false])
  · exact N.a7
  · exact N.a4
  · exact N.a5

/-- The `fd`/`bk` link words of a bin-ring node, from its foot fact. -/
theorem linkRgn_FreePaths {H : List (Nat × Nat)} {z : Nat}
    (h : ∀ k, 16 ≤ k → k < 32 → vsaFoot H (z + k)) : Rgn (vsaFoot H) (z + 16) 16 :=
  ⟨fun k hk => by rw [Nat.add_assoc]; exact h _ (by omega) (by omega)⟩

/-- The span of an in-use chunk whose payload holds no live extent (the chunk being freed). -/
theorem chunkRgn_FreePaths {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) {X S : Nat}
    (hX : (⟨X, S, true⟩ : Chunk) ∈ chunks) (hno : ∀ e ∈ H, e.1 ≠ X + 16) : Rgn (vsaFoot H) (X + 8) S :=
  ⟨fun k hk => foot_of_chunk h hX hno (by omega) (by omega)⟩

structure FFwdMem (C : MCtx) (Mc Mv : Mem) (brkv : Nat) (cs cs' : List Chunk)
    (bins : Nat → List Nat) (Y a b : Nat) : Prop where
  heap : PHeapAt Mv C.H C.top0 brkv (cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: cs') bins
  hno : ∀ e ∈ C.H, e.1 ≠ Y + 16
  prev : ∀ h0, read64 Mv (Y + 8) = some h0 → h0 % 2 = 1
  agree : ∀ w, vsaFoot C.H w → ¬ (Y + 8 ≤ w ∧ w < Y + 16) → ¬ (Y + a + 8 ≤ w ∧ w < Y + a + 16) →
    Mc[w]? = Mv[w]?
  nxh : read64 Mc (Y + a + 8) = some b
  pres : ∀ x, vsaFoot C.H x → (Mc[x]?).isSome
  disj : ∀ x, C.s.toNat - mHead ≤ x → x < C.s.toNat → ¬ vsaFoot C.H x
  frameM : ∀ x, ¬ MWin C.H C.s x → Mc[x]? = C.Mt0[x]?

structure FFwd (C : MCtx) (R : Nat → BitVec 64) (Mc Mv : Mem) (brkv : Nat) (cs cs' : List Chunk)
    (bins : Nat → List Nat) (Y a b : Nat) : Prop extends FFwdMem C Mc Mv brkv cs cs' bins Y a b where
  frame : FFrame C R Mc
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = Y
  a5 : (R 15).toNat = a + b
  a2 : (R 12).toNat = Y + a
  a0 : (R 10).toNat = binAt 1

structure FwdNx (Mv : Mem) (top : Nat) (cs' : List Chunk) (bins : Nat → List Nat) (Y a b : Nat)
    (i : Nat) (pre post : List Nat) (d' : Chunk) (cs'' : List Chunk) (hdn : Nat) : Prop where
  i0 : 0 < i
  i1 : i < numBins
  bin : bins i = pre ++ (Y + a) :: post
  tail : cs' = d' :: cs''
  daddr : d'.addr = Y + a + b
  dinuse : d'.inuse = true
  not_top : Y + a + b ≠ top
  dhdr : read64 Mv (Y + a + b + 8) = some hdn
  dlow : hdn % 4 < 2
  dflag : prevInuse hdn = false

theorem FFwdMem.nx {C : MCtx} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwdMem C Mc Mv brkv cs cs' bins Y a b) :
    ∃ i pre post d' cs'' hdn, FwdNx Mv C.top0 cs' bins Y a b i pre post d' cs'' hdn := by
  have HH := V.heap.heap.heap
  have hN : (⟨Y + a, b, false⟩ : Chunk) ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: cs' := by simp
  obtain ⟨i, hi0, hi, hm, _⟩ := HH.free_binned _ hN rfl
  simp only at hm
  obtain ⟨pre, post, hbin⟩ := List.append_of_mem hm
  have hw : ChunkWalk Mv heapStart C.top0 ((cs ++ [⟨Y, a, true⟩]) ++ ⟨Y + a, b, false⟩ :: cs') := by
    simpa using HH.walk
  have HH' : HeapAt Mv C.H (fun e => e ∈ C.H) C.top0 brkv ((cs ++ [⟨Y, a, true⟩]) ++ ⟨Y + a, b, false⟩ :: cs') bins := by
    simpa using HH
  have NB := HH'.freeNbrs
  obtain ⟨⟨hdn, hdnr, hdnf⟩, hnext⟩ := walk_next_of hw
  simp only at hdnr hdnf
  obtain ⟨d', cs'', rfl, hda⟩ : ∃ d' cs'', cs' = d' :: cs'' ∧ d'.addr = Y + a + b := by
    rcases hnext with ⟨he, _⟩ | ⟨d', cs'', h1, h2⟩
    · exact absurd he NB.not_top
    · exact ⟨d', cs'', h1, h2⟩
  have hdm : d' ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'' := by simp
  obtain ⟨hd0, hd0r, _, hd0l⟩ := walk_header HH.walk d' hdm
  rw [hda, hdnr] at hd0r
  obtain rfl : hdn = hd0 := Option.some.inj hd0r
  exact ⟨i, pre, post, d', cs'', hdn, hi0, hi, hbin, rfl, hda, NB.next d' rfl, NB.not_top, hdnr,
    hd0l, hdnf⟩

structure FwdGeo (C : MCtx) (Y a b pred succ : Nat) : Prop where
  Y16 : Y % 16 = 0
  a16 : a % 16 = 0
  a32 : 32 ≤ a
  b16 : b % 16 = 0
  b32 : 32 ≤ b
  Ylo : 0x8001c170 ≤ Y
  dend : Y + a + b + 32 ≤ C.top0
  top : C.top0 + 16 ≤ 0x87800000
  p16 : pred % 16 = 0
  s16 : succ % 16 = 0
  plo : 0x8001ad20 ≤ pred
  slo : 0x8001ad20 ≤ succ
  phi : pred + 32 ≤ C.top0
  shi : succ + 32 ≤ C.top0
  sY : Y ≠ succ + 16
  sN : Y + a ≠ succ + 16
  sD : Y + a + b ≠ succ + 16
  pD : Y + a + b ≠ pred + 16
  pY : Y ≠ pred + 8
  pN : Y + a ≠ pred + 8
  pfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (pred + k)
  sfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (succ + k)
  dfoot : ∀ k, k < 8 → vsaFoot C.H (Y + a + b + 8 + k)

theorem FwdNx.geo {C : MCtx} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwdMem C Mc Mv brkv cs cs' bins Y a b)
    {i : Nat} {pre post : List Nat} {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv C.top0 cs' bins Y a b i pre post d' cs'' hdn) {pred succ : Nat}
    (hpred : (binAt i :: pre).getLast? = some pred) (hsucc : (post ++ [binAt i]).head? = some succ) :
    FwdGeo C Y a b pred succ := by
  obtain ⟨hi0, hi, hbin, htail, hda, hdin, hnt, hdnr, hdnl, hdnf⟩ := X
  subst htail
  have HH := V.heap.heap.heap
  obtain ⟨hal, htop16⟩ := HH.aligned
  have hX : (⟨Y, a, true⟩ : Chunk) ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'' := by simp
  have hN : (⟨Y + a, b, false⟩ : Chunk) ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'' := by simp
  have hdm : d' ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'' := by simp
  have hXb := HH.walk.chunk_bounds _ hX; have hDb := HH.walk.chunk_bounds _ hdm
  have hY16 := hal _ hX
  have ha := walk_sizes HH.walk _ hX; have hb := walk_sizes HH.walk _ hN
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := V.heap.heap.top_room
  rw [hda] at hDb
  have hpredm : pred = binAt i ∨ pred ∈ bins i := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  have hsuccm : succ = binAt i ∨ succ ∈ bins i := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hbin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hp16, hpnode⟩ := HH.node hi0 hi hpredm
  obtain ⟨hs16, hsnode⟩ := HH.node hi0 hi hsuccm
  have bY : (Y = C.top0 ∨ ∃ c ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'', c.addr = Y) :=
    .inr ⟨_, hX, rfl⟩
  have bN : (Y + a = C.top0 ∨ ∃ c ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'', c.addr = Y + a) :=
    .inr ⟨_, hN, rfl⟩
  have bD : (Y + a + b = C.top0 ∨ ∃ c ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'', c.addr = Y + a + b) :=
    .inr ⟨_, hdm, hda⟩
  have hloc : ∀ z, (z = binAt i ∨ ∃ cx ∈ cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: d' :: cs'',
      cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins i) → 0x8001ad20 ≤ z ∧ z + 32 ≤ C.top0 := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i hi; have := HH.walk.le; unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  simp only at hXb hY16 ha hb hDb
  unfold heapStart heapEnd at *
  exact ⟨hY16, ha.1, ha.2, hb.1, hb.2, hXb.1, by have := hDb.2.2; omega, by omega, hp16, hs16,
    (hloc _ hpnode).1, (hloc _ hsnode).1, (hloc _ hpnode).2, (hloc _ hsnode).2,
    HH.bnd_ne_node hi hsnode bY 16 (by omega) (by omega), HH.bnd_ne_node hi hsnode bN 16 (by omega) (by omega),
    HH.bnd_ne_node hi hsnode bD 16 (by omega) (by omega), HH.bnd_ne_node hi hpnode bD 16 (by omega) (by omega),
    HH.bnd_ne_node hi hpnode bY 8 (by omega) (by omega), HH.bnd_ne_node hi hpnode bN 8 (by omega) (by omega),
    V.heap.heap.node_foot hi0 hi hpredm, V.heap.heap.node_foot hi0 hi hsuccm, foot_header V.heap.heap bD⟩

theorem fwd_agree {C : MCtx} {Mc Mv : Mem} {Y a b pred succ hdn : Nat} (G : FwdGeo C Y a b pred succ)
    (hag : ∀ w, vsaFoot C.H w → ¬ (Y + 8 ≤ w ∧ w < Y + 16) → ¬ (Y + a + 8 ≤ w ∧ w < Y + a + 16) →
      Mc[w]? = Mv[w]?) (hnxh : read64 Mc (Y + a + 8) = some b)
    {v1 v2 v3 v4 : BitVec 64} (h1 : v1.toNat = pred) (h2 : v2.toNat = succ)
    (h3 : v3.toNat = a + b + 1) :
    ∀ w, vsaFoot C.H w → ¬ (Y + (a + b) ≤ w ∧ w < Y + (a + b) + 16) →
      (writeLog (writeLog (writeLog (writeLog Mc [(succ + 24, 8, v1)]) [(pred + 16, 8, v2)])
        [(Y + 8, 8, v3)]) [(Y + a + b, 8, v4)])[w]? =
      (writeLog (writeLog (writeLog (writeLog (writeLog Mv
        [(pred + 16, 8, BitVec.ofNat 64 succ)]) [(succ + 24, 8, BitVec.ofNat 64 pred)])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 (hdn ||| 1))]) [(Y + 8, 8, BitVec.ofNat 64 (a + b + 1))])
        [(Y + a + 8, 8, BitVec.ofNat 64 b)])[w]? := by
  open_fields G
  have hpv : pred < 2 ^ 64 := by omega
  have hsv : succ < 2 ^ 64 := by omega
  intro w0 hw0 hr0
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (Y + (a + b) ≤ x ∧ x < Y + (a + b) + 16))
    [succ + 24, pred + 16, Y + 8, Y + a + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, hr0⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact ⟨pred, by rd_log [h1], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpv]⟩
    · exact ⟨succ, by rd_log [h2], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv]⟩
    · exact ⟨a + b + 1, by rd_log [h3],
        by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a + b + 1 < 2 ^ 64)]⟩
    · exact ⟨b, by rd_log [hnxh], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact hag x hx1 (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

theorem fwd_fbin {C : MCtx} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwdMem C Mc Mv brkv cs cs' bins Y a b)
    {i : Nat} {pre post : List Nat} {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv C.top0 cs' bins Y a b i pre post d' cs'' hdn) {pred succ : Nat}
    (hpred : (binAt i :: pre).getLast? = some pred) (hsucc : (post ++ [binAt i]).head? = some succ)
    {v1 v2 v3 v4 : BitVec 64} (h1 : v1.toNat = pred) (h2 : v2.toNat = succ)
    (h3 : v3.toNat = a + b + 1) (h4 : v4.toNat = a + b) :
    FBin C (writeLog (writeLog (writeLog (writeLog Mc [(succ + 24, 8, v1)]) [(pred + 16, 8, v2)])
      [(Y + 8, 8, v3)]) [(Y + a + b, 8, v4)])
      (writeLog (writeLog (writeLog (writeLog (writeLog Mv
        [(pred + 16, 8, BitVec.ofNat 64 succ)]) [(succ + 24, 8, BitVec.ofNat 64 pred)])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 (hdn ||| 1))]) [(Y + 8, 8, BitVec.ofNat 64 (a + b + 1))])
        [(Y + a + 8, 8, BitVec.ofNat 64 b)])
      Y (a + b) C.top0 brkv cs cs' (updBins bins i (pre ++ post)) := by
  have G := X.geo V hpred hsucc
  obtain ⟨hi0, hi, hbin, htail, hda, hdin, hnt, hdnr, hdnl, hdnf⟩ := X
  open_fields G
  have hY8 : ∀ h0, read64 Mv (Y + 8) = some h0 → prevInuse (a + b + 1) = prevInuse h0 := by
    intro h0 hr
    have := V.prev h0 hr
    unfold prevInuse; rw [show (a + b + 1) % 2 = 1 by omega, this]
  have hcs : chunkSize (a + b + 1) = a + b := by unfold chunkSize; omega
  have hcl : (a + b + 1) % 4 < 2 := by omega
  have HP := V.heap.coalNext hi0 hi hbin hpred hsucc hdnr hcs hcl hY8 (BitVec.ofNat 64 b)
  subst htail
  have rY := chunkRgn_FreePaths HP (X := Y) (S := a + b) (by simp) V.hno
  have rP := linkRgn_FreePaths G.pfoot; have rS := linkRgn_FreePaths G.sfoot
  refine ⟨⟨HP, Nat.le_refl _, V.hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega,
    fwd_agree G V.agree V.nxh h1 h2 h3, ?_, fun hd hr => ?_⟩,
    pres_log _ (pres_log _ (pres_log _ (pres_log _ V.pres))), V.disj, ?_⟩
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd0; rw [← hd0]; exact hdin
  · rw [show Y + (a + b) = Y + a + b from (Nat.add_assoc _ _ _).symm, read64_store_hit, h4]
  · rw [show Y + (a + b) + 8 = Y + a + b + 8 by omega, rd_miss (by omega), rd_miss (by omega),
      read64_store_hit] at hr
    cases hr
    rw [show Y + (a + b) + 8 = Y + a + b + 8 by omega]
    have hdlt := Vsa.Sim.read64_lt _ _ _ hdnr
    have h1' : (hdn ||| 1) / 2 = hdn / 2 := by
      have := Nat.or_div_two_pow (a := hdn) (b := 1) (n := 1); simpa using this
    have h2' : (hdn ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
    have := Nat.div_add_mod (hdn ||| 1) 2
    refine ⟨hdn, ?_, ?_, hdnl, hdnf⟩
    · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
        read64_keep (fun k hk => V.agree _ (G.dfoot k hk) (by omega) (by omega))]
      exact hdnr
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      unfold chunkSize; omega
  · simp only [writeLog_nest, List.cons_append, List.nil_append]; exact frame_log (by log_in) V.frameM

theorem FwdNx.lr {Mv : Mem} {top : Nat} {cs' : List Chunk} {bins : Nat → List Nat} {Y a b : Nat}
    {pre post : List Nat} {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv top cs' bins Y a b 1 pre post d' cs'' hdn) (hrem : (bins 1).length ≤ 1) :
    pre = [] ∧ post = [] := by
  have := X.bin
  rw [this] at hrem
  simp at hrem
  exact ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩

theorem fwd_lr_core {C : MCtx} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwdMem C Mc Mv brkv cs cs' bins Y a b)
    {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv C.top0 cs' bins Y a b 1 [] [] d' cs'' hdn) :
    FBinCore C
      (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mv
        [(binAt 1 + 16, 8, BitVec.ofNat 64 (binAt 1))]) [(binAt 1 + 24, 8, BitVec.ofNat 64 (binAt 1))])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 (hdn ||| 1))]) [(Y + 8, 8, BitVec.ofNat 64 (a + b + 1))])
        [(Y + a + 8, 8, BitVec.ofNat 64 b)]) [(Y + a + b, 8, BitVec.ofNat 64 (a + b))])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 hdn)])
      (writeLog (writeLog (writeLog (writeLog (writeLog Mv
        [(binAt 1 + 16, 8, BitVec.ofNat 64 (binAt 1))]) [(binAt 1 + 24, 8, BitVec.ofNat 64 (binAt 1))])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 (hdn ||| 1))]) [(Y + 8, 8, BitVec.ofNat 64 (a + b + 1))])
        [(Y + a + 8, 8, BitVec.ofNat 64 b)])
      Y (a + b) C.top0 brkv cs cs' (updBins bins 1 []) := by
  have G := X.geo V (pred := binAt 1) (succ := binAt 1) rfl rfl
  obtain ⟨hi0, hi, hbin, htail, hda, hdin, hnt, hdnr, hdnl, hdnf⟩ := X
  have hY16 := G.Y16; have ha16 := G.a16; have ha32 := G.a32; have hb16 := G.b16; have hb32 := G.b32
  have hYlo := G.Ylo; have hdend := G.dend; have htop := G.top
  have hY8 : ∀ h0, read64 Mv (Y + 8) = some h0 → prevInuse (a + b + 1) = prevInuse h0 := by
    intro h0 hr
    have := V.prev h0 hr
    unfold prevInuse; rw [show (a + b + 1) % 2 = 1 by omega, this]
  have hcs : chunkSize (a + b + 1) = a + b := by unfold chunkSize; omega
  have hcl : (a + b + 1) % 4 < 2 := by omega
  have HP := V.heap.coalNext hi0 hi hbin rfl rfl hdnr hcs hcl hY8 (BitVec.ofNat 64 b)
  simp only [List.nil_append] at HP
  subst htail
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdnr
  have h1' : (hdn ||| 1) / 2 = hdn / 2 := by
    have := Nat.or_div_two_pow (a := hdn) (b := 1) (n := 1); simpa using this
  have h2' : (hdn ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
  have := Nat.div_add_mod (hdn ||| 1) 2
  refine ⟨HP, Nat.le_refl _, V.hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega, fun w hw hr => ?_,
    ?_, fun hd hr => ?_⟩
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd0; rw [← hd0]; exact hdin
  · rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · rw [show Y + (a + b) = Y + a + b by omega, rd_miss (by omega), read64_store_hit,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [show Y + (a + b) + 8 = Y + a + b + 8 by omega, rd_miss (by omega), rd_miss (by omega),
      read64_store_hit] at hr
    cases hr
    refine ⟨hdn, ?_, ?_, hdnl, hdnf⟩
    · rw [show Y + (a + b) + 8 = Y + a + b + 8 by omega, read64_store_hit, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hdlt]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      unfold chunkSize; omega

theorem fwd_lr_agree {C : MCtx} {Mc Mv : Mem} {Y a b hdn : Nat} (G : FwdGeo C Y a b (binAt 1) (binAt 1))
    (hag : ∀ w, vsaFoot C.H w → ¬ (Y + 8 ≤ w ∧ w < Y + 16) → ¬ (Y + a + 8 ≤ w ∧ w < Y + a + 16) →
      Mc[w]? = Mv[w]?) (hnxh : read64 Mc (Y + a + 8) = some b)
    {v1 v2 v3 v4 : BitVec 64} (h3 : v3.toNat = a + b + 1) :
    ∀ w, vsaFoot C.H w → ¬ RelW Y (a + b) (binAt 1) (binAt 1) w →
      (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mc
        [(binAt 1 + 24, 8, v1)]) [(binAt 1 + 16, 8, v1)]) [(Y + 24, 8, v2)]) [(Y + 16, 8, v2)])
        [(Y + 8, 8, v3)]) [(Y + a + b, 8, v4)])[w]? =
      (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mv
        [(binAt 1 + 16, 8, BitVec.ofNat 64 (binAt 1))]) [(binAt 1 + 24, 8, BitVec.ofNat 64 (binAt 1))])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 (hdn ||| 1))]) [(Y + 8, 8, BitVec.ofNat 64 (a + b + 1))])
        [(Y + a + 8, 8, BitVec.ofNat 64 b)]) [(Y + a + b, 8, BitVec.ofNat 64 (a + b))])
        [(Y + a + b + 8, 8, BitVec.ofNat 64 hdn)])[w]? := by
  have hY16 := G.Y16; have ha16 := G.a16; have ha32 := G.a32; have hb16 := G.b16; have hb32 := G.b32
  have hYlo := G.Ylo; have hdend := G.dend; have htop := G.top
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  unfold binAt avAddr at hg1 ⊢
  intro w0 hw0 hr0
  unfold RelW binblocksAddr at hr0
  unfold avAddr at hr0
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (Y + 16 ≤ x ∧ x < Y + 32) ∧
      ¬ (0x8001ad10 + 16 * 1 + 16 ≤ x ∧ x < 0x8001ad10 + 16 * 1 + 32) ∧ ¬ (Y + (a + b) ≤ x ∧ x < Y + (a + b) + 16))
    [Y + 8, Y + a + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, by omega, by omega, by omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl
    · exact ⟨a + b + 1, by rd_log [h3],
        by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a + b + 1 < 2 ^ 64)]⟩
    · exact ⟨b, by rd_log [hnxh], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact hag x hx1 (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

theorem fwd_lr_done {C : MCtx} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwdMem C Mc Mv brkv cs cs' bins Y a b)
    {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv C.top0 cs' bins Y a b 1 [] [] d' cs'' hdn)
    {v1 v2 v3 v4 : BitVec 64} (h1 : v1.toNat = Y) (h2 : v2.toNat = binAt 1)
    (h3 : v3.toNat = a + b + 1) (h4 : v4.toNat = a + b) :
    FDone C (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mc
        [(binAt 1 + 24, 8, v1)]) [(binAt 1 + 16, 8, v1)]) [(Y + 24, 8, v2)]) [(Y + 16, 8, v2)])
        [(Y + 8, 8, v3)]) [(Y + a + b, 8, v4)]) := by
  have G := X.geo V (pred := binAt 1) (succ := binAt 1) rfl rfl
  have K := fwd_lr_core V X
  have hY16 := G.Y16; have ha16 := G.a16; have ha32 := G.a32; have hb16 := G.b16; have hb32 := G.b32
  have hYlo := G.Ylo; have hdend := G.dend; have htop := G.top
  have hb1 : binAt 1 = 2147593504 := rfl
  have HH := V.heap.heap.heap
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mv binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hdnr := X.dhdr
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdnr
  have rY := chunkRgn_FreePaths K.heap (X := Y) (S := a + b) (by simp) V.hno
  have rG := globRgn C.H
  refine fb_release K (j := 1) (pre' := []) (post' := []) (pred := binAt 1) (succ := binAt 1)
    (bb' := bb) (by decide) (by unfold numBins; decide) (fun h => absurd h (by decide))
    (fun _ => by simp [updBins]) (by simp [updBins]) rfl rfl ?_ ?_ ?_ ?_ ?_ (V.heap.bb_lt bb hbb)
    (fun h => absurd h (by decide)) ?_ (fwd_lr_agree G V.agree V.nxh h3) ?_
    (pres_log _ (pres_log _ (pres_log _ (pres_log _ (pres_log _ (pres_log _ V.pres)))))) ?_
  · show read64 _ (Y + 16) = _; rd_log [h2]
  · show read64 _ (Y + 24) = _; rd_log [h2]
  · show read64 _ (binAt 1 + 16) = _; rd_log [h1]
  · show read64 _ (binAt 1 + 24) = _; rd_log [h1]
  · have hA : binblocksAddr = 0x8001ad18 := rfl
    rw [hA, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), read64_keep (fun k hk => V.agree _
        (.inl (.inl ⟨by omega, by omega⟩)) (by omega) (by omega)), ← hA]
    exact hbb
  · intro bb0 hbb0 k hk
    have hA : binblocksAddr = 0x8001ad18 := rfl
    rw [hA, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), ← hA, hbb] at hbb0
    cases hbb0; exact hk
  · intro w h1' h2'
    refine agree_of_words (P := fun x => Y + (a + b) ≤ x ∧ x < Y + (a + b) + 16)
      [Y + a + b, Y + a + b + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w ⟨h1', h2'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact ⟨a + b, by rd_log [h4],
          by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a + b < 2 ^ 64)]⟩
      · refine ⟨hdn, ?_, by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]⟩
        rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
          rd_miss (by omega), rd_miss (by omega),
          read64_keep (fun k hk => V.agree _ (G.dfoot k hk) (by omega) (by omega))]
        exact hdnr
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
      obtain ⟨hx1, hx2⟩ := hx
      omega
  · simp only [writeLog_nest, List.cons_append, List.nil_append]; exact frame_log (by log_in) V.frameM

theorem free_fwd {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat}
    {cs cs' : List Chunk} {bins : Nat → List Nat} {Y a b : Nat}
    (V : FFwd C R Mc Mv brkv cs cs' bins Y a b) :
    AW C.live C.S C.Q 0x80007458#64 R Mc := by
  obtain ⟨i, pre, post, d', cs'', hdn, X⟩ := V.toFFwdMem.nx
  have HH := V.heap.heap.heap
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt i :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt i]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have G := X.geo V.toFFwdMem hpred hsucc
  have hi0 := X.i0; have hi := X.i1
  open_fields G; clear G_sY G_sN G_sD G_pD G_pY G_pN
  have hring := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  rw [X.bin] at hring
  have rY := chunkRgn_FreePaths V.heap (X := Y) (S := a) (by simp) V.hno
  have rN : Rgn (vsaFoot C.H) (Y + a + 8) (b + 8) :=
    V.heap.heap.freeSpan (c := ⟨Y + a, b, false⟩) (by simp) rfl
  have rP := linkRgn_FreePaths G.pfoot; have rS := linkRgn_FreePaths G.sfoot; have rG := globRgn C.H
  have hfd' : read64 Mc (Y + a + 16) = some succ := by
    rw [read64_keep (fun k hk => V.agree _ (rN.mem (by omega) (by omega)) (by omega) (by omega))]
    exact (ring_member hring hpred hsucc).1
  have hbk' : read64 Mc (Y + a + 24) = some pred := by
    rw [read64_keep (fun k hk => V.agree _ (rN.mem (by omega) (by omega)) (by omega) (by omega))]
    exact (ring_member hring hpred hsucc).2
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have ha2 := V.a2; have ha4 := V.a4; have ha5 := V.a5; have ha0 := V.a0
  have ha7 : (R 17).toNat = 2147593488 := by rw [V.a7]; rfl
  have hsv := Vsa.Sim.read64_lt _ _ _ hfd'; have hpv := Vsa.Sim.read64_lt _ _ _ hbk'
  have hb1 : binAt 1 = 2147593504 := rfl
  have o1 := rY.offStack V.disj (by omega); have o2 := rN.offStack V.disj (by omega)
  have o3 := rP.offStack V.disj (by omega); have o4 := rS.offStack V.disj (by omega)
  have o5 := rG.offStack V.disj (by omega); unfold mHead at o1 o2 o3 o4 o5
  have hv3 : (R 15 ||| 1#64).toNat = a + b + 1 := or1_toNat ha5 (by omega)
  rgn_run O.live at 0x8000745c
  rgn_ld [hfd']
  rgn_run O.live at 0x80007464
  refine st_80007464 O.live (fun heq => ?_) (fun hne => ?_)
  · have hs1 : succ = binAt 1 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv, ha0] at this; exact this
    have hi1 : i = 1 := by
      have hsm : succ = binAt i ∨ succ ∈ bins i := by
        have := List.mem_of_head? hsucc
        rcases List.mem_append.mp this with h1 | h1
        · exact .inr (by rw [X.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
        · exact .inl (List.mem_singleton.mp h1)
      rcases hsm with h | h
      · rw [hs1] at h; unfold binAt at h; omega
      · obtain ⟨c, hc, hca, _⟩ := HH.member hi0 hi h
        have := (HH.walk.chunk_bounds c hc).1; unfold heapStart at this; rw [hca, hs1, hb1] at this; omega
    subst hi1
    obtain ⟨rfl, rfl⟩ := X.lr HH.remainder
    rgn_run O.live at 0x80007434
    rw [show (R 17 + 40#64).toNat = binAt 1 + 24 by rgn_arith,
      show (R 17 + 32#64).toNat = binAt 1 + 16 by rgn_arith,
      show (R 14 + 24#64).toNat = Y + 24 by rgn_arith, show (R 14 + 16#64).toNat = Y + 16 by rgn_arith,
      show (R 14 + 8#64).toNat = Y + 8 by rgn_arith, show (R 14 + R 15).toNat = Y + a + b by rgn_arith]
    have D := fwd_lr_done V.toFFwdMem X ha4 ha0 hv3 ha5
    exact free_epi O ((((((V.frame.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)).store (by omega) |>.of_regs rfl rfl rfl rfl) D.heap D.pres D.frame
  · have B := fwd_fbin V.toFFwdMem X hpred hsucc (v1 := BitVec.ofNat 64 pred) (v2 := BitVec.ofNat 64 succ)
      (BitVec.toNat_ofNat .. ▸ Nat.mod_eq_of_lt hpv) (BitVec.toNat_ofNat .. ▸ Nat.mod_eq_of_lt hsv)
      hv3 ha5
    rgn_run O.live at 0x8000746c
    rgn_ld [hbk']
    rgn_run O.live at 0x800073e8
    rw [show (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 by rgn_arith,
      show (BitVec.ofNat 64 pred + 16#64).toNat = pred + 16 by rgn_arith,
      show (R 14 + 8#64).toNat = Y + 8 by rgn_arith, show (R 14 + R 15).toNat = Y + a + b by rgn_arith]
    exact free_bin O ((((V.frame.store (by omega)).store (by omega)).store (by omega)).store (by omega)
      |>.of_regs rfl rfl rfl rfl) B V.a7 ha4 ha5

theorem free_b1b {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₁ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hprev : hdr0 % 2 = 1)
    (hdfree : d.inuse = false) :
    AW C.live C.S C.Q 0x8000744c#64 R Mt1 := by
  have G := N.geo
  obtain ⟨da, ds, di⟩ := d
  have hda := N.daddr
  simp only at hda hdfree
  subst hda hdfree
  open_fields G; unfold heapEnd at G_top
  have hM1 := N.mem; have ha5 := N.a5; have ha3 := N.a3
  simp only at G_dsz32 G_dend ha3
  rgn_run O.live at 0x80007458
  refine free_fwd O ⟨⟨N.heap, N.hno, fun h0 hr => ?_, fun w0 hw0 h1 h2 => ?_,
    ?_, N.pres, N.disj, N.frameM⟩, N.frame.of_regs rfl rfl rfl rfl, N.a7, N.a4, by rgn_arith, N.a2, rfl⟩
  · rw [N.hdr] at hr; cases hr; exact hprev
  · rw [hM1, writeLog_out]; simp only [OutL, and_true]; omega
  · rw [hM1, read64_store_hit, N.wv]

structure FPv (Mt : Mem) (cs₁ : List Chunk) (bins : Nat → List Nat) (x : Nat) (cs₀ : List Chunk)
    (p psz i : Nat) (pre post : List Nat) (predP succP : Nat) : Prop where
  split : cs₁ = cs₀ ++ [⟨p, psz, false⟩]
  pend : p + psz = x
  i0 : 0 < i
  i1 : i < numBins
  bin : bins i = pre ++ p :: post
  hpred : (binAt i :: pre).getLast? = some predP
  hsucc : (post ++ [binAt i]).head? = some succP
  foot : read64 Mt x = some psz
  fd : read64 Mt (p + 16) = some succP
  bk : read64 Mt (p + 24) = some predP
  prev : ∀ h0, read64 Mt (p + 8) = some h0 → h0 % 2 = 1

theorem pv_of_heap {C : MCtx} {Mt : Mem} {brkv : Nat} {cs₁ rest : List Chunk}
    {bins : Nat → List Nat} {x sz hdr0 : Nat}
    (h : PHeapAt Mt C.H C.top0 brkv (cs₁ ++ ⟨x, sz, true⟩ :: rest) bins)
    (hdr : read64 Mt (x + 8) = some hdr0) (hpf : hdr0 % 2 = 0) :
    ∃ cs₀ p psz i pre post predP succP, FPv Mt cs₁ bins x cs₀ p psz i pre post predP succP := by
  have HH := h.heap.heap

  obtain ⟨cs₀, c, hc⟩ : ∃ cs₀ c, cs₁ = cs₀ ++ [c] := by
    rcases List.eq_nil_or_concat cs₁ with rfl | ⟨cs₀, c, rfl⟩
    · exfalso
      have hv : x = heapStart := by
        have := (walkHead (by simpa using HH.walk)).addr; exact this
      have := HH.first_prev
      rw [← hv, hdr] at this
      simp only [Option.any, beq_iff_eq] at this; omega
    · exact ⟨cs₀, c, List.concat_eq_append ..⟩
  subst hc
  have hw := HH.walk
  simp only [List.append_assoc, List.singleton_append] at hw
  obtain ⟨⟨h, hr, hp⟩, hn⟩ := walk_next_of hw
  have hca : c.addr + c.size = x := by
    rcases hn with ⟨_, h1⟩ | ⟨d', cs', h1, h2⟩
    · cases h1
    · simp only [List.cons.injEq] at h1; rw [← h2, ← h1.1]
  rw [hca, hdr] at hr
  cases hr
  have hcf : c.inuse = false := by
    rw [← hp]; unfold prevInuse; simp; omega
  obtain ⟨p, psz, ci⟩ := c
  simp only at hca hcf
  subst hcf
  have hcm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: rest := by simp
  obtain ⟨i, hi0, hi, hm, _⟩ := HH.free_binned _ hcm rfl
  simp only at hm
  obtain ⟨pre, post, hbin⟩ := List.append_of_mem hm
  obtain ⟨predP, hpred⟩ : ∃ q, (binAt i :: pre).getLast? = some q := ⟨_, List.getLast?_cons⟩
  obtain ⟨succP, hsucc⟩ : ∃ q, (post ++ [binAt i]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  rw [hbin] at hring
  have hft := HH.footer _ hcm rfl
  simp only at hft
  rw [hca] at hft
  have HH' : HeapAt Mt C.H (fun e => e ∈ C.H) C.top0 brkv (cs₀ ++ ⟨p, psz, false⟩ :: ⟨x, sz, true⟩ :: rest) bins := by
    simpa using HH
  exact ⟨cs₀, p, psz, i, pre, post, predP, succP, rfl, hca, hi0, hi, hbin, hpred, hsucc, hft,
    (ring_member hring hpred hsucc).1, (ring_member hring hpred hsucc).2, HH'.freeNbrs.prev⟩

theorem FNt.pv {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₁ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hpf : hdr0 % 2 = 0) :
    ∃ cs₀ p psz i pre post predP succP, FPv Mt cs₁ bins x cs₀ p psz i pre post predP succP :=
  pv_of_heap N.heap N.hdr hpf

structure FB2 (C : MCtx) (R : Nat → BitVec 64) (Mt Mt1 : Mem) (brkv : Nat) (cs₀ cs₃ : List Chunk)
    (d : Chunk) (bins : Nat → List Nat) (x sz hdr0 hnn : Nat) (w : BitVec 64)
    (p psz i : Nat) (pre post : List Nat) (predP succP : Nat) : Prop where
  frame : FFrame C R Mt1
  mem : Mt1 = writeLog Mt [(x + sz + 8, 8, w)]
  wv : w.toNat = d.size
  heap : PHeapAt Mt C.H C.top0 brkv ((cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃) bins
  hno : ∀ e ∈ C.H, e.1 ≠ x + 16
  daddr : d.addr = x + sz
  hdr : read64 Mt (x + 8) = some hdr0
  hsz : chunkSize hdr0 = sz
  hlow : hdr0 % 4 < 2
  nnr : read64 Mt (x + sz + d.size + 8) = some hnn
  nnf : prevInuse hnn = d.inuse
  pv : FPv Mt (cs₀ ++ [⟨p, psz, false⟩]) bins x cs₀ p psz i pre post predP succP
  pres : ∀ a, vsaFoot C.H a → (Mt1[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frameM : ∀ a, ¬ MWin C.H C.s a → Mt1[a]? = C.Mt0[a]?
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = p
  a5 : (R 15).toNat = sz + psz
  a1 : (R 11).toNat = succP
  a0 : (R 10).toNat = binAt 1
  a2 : (R 12).toNat = x + sz
  a3 : (R 13).toNat = d.size
  a6 : (R 16).toNat = hnn % 2

theorem free_b2 {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₁ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hpf : hdr0 % 2 = 0)
    (hnl : ∀ R' cs₀ p psz i pre post predP succP, i ≠ 1 →
      FB2 C R' Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP →
      AW C.live C.S C.Q 0x800073cc#64 R' Mt1)
    (hlr : ∀ R' cs₀ p psz, FB2 C R' Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz 1 [] [] (binAt 1) (binAt 1) →
      AW C.live C.S C.Q 0x80007508#64 R' Mt1) :
    AW C.live C.S C.Q 0x800073b0#64 R Mt1 := by
  obtain ⟨cs₀, p, psz, i, pre, post, predP, succP, P⟩ := N.pv hpf
  have HH := N.heap.heap.heap
  obtain rfl := P.split
  suffices hB : ∀ R', FB2 C R' Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP →
      AW C.live C.S C.Q 0x800073c8#64 R' Mt1 by
    have G := N.geo
    open_fields G; unfold heapEnd at G_top
    have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by
      simp
    have rPv := N.heap.heap.freeSpan hpm rfl; have hps := (N.heap.heap.chunkK hpm).sz32
    have hpend := P.pend; simp only at rPv hps
    have hfoot : read64 Mt1 x = some psz := by rw [N.mem, rd_miss (by omega)]; exact P.foot
    have hfd : read64 Mt1 (p + 16) = some succP := by rw [N.mem, rd_miss (by omega)]; exact P.fd
    have hpflt := Vsa.Sim.read64_lt _ _ _ hfoot; have hsflt := Vsa.Sim.read64_lt _ _ _ hfd
    have ha1 := N.a1; have ha4 := N.a4; have ha5 := N.a5
    rgn_run O.live at 0x800073b4
    rgn_ld [hfoot]
    have hEp : (R 14 - BitVec.ofNat 64 psz).toNat = p := by
      rw [BitVec.toNat_sub, ha4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpflt]; omega
    rgn_run O.live at 0x800073c4
    rgn_ld [hfd]
    rgn_run O.live at 0x800073c8
    exact hB _ ⟨N.frame.of_regs rfl rfl rfl rfl, N.mem, N.wv, N.heap, N.hno, N.daddr, N.hdr, N.hsz, N.hlow,
      N.nnr, N.nnf, P, N.pres, N.disj, N.frameM, N.a7, hEp, by rgn_arith, by rgn_arith, rfl, N.a2, N.a3, N.a6⟩
  intro R' B
  have hb1 : binAt 1 = 2147593504 := rfl
  have hnil : i = 1 → pre = [] ∧ post = [] := by
    rintro rfl
    have hrem := HH.remainder
    rw [P.bin] at hrem; simp at hrem
    exact ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
  refine st_800073c8 O.live (fun heq => ?_) (fun hne => ?_)
  · have hs1 : succP = binAt 1 := by
      have e1 := B.a1; have e0 := B.a0
      rw [heq] at e1; rw [e1] at e0; exact e0
    have hi1 : i = 1 := by
      have hsm : succP = binAt i ∨ succP ∈ bins i := by
        have := List.mem_of_head? P.hsucc
        rcases List.mem_append.mp this with h1 | h1
        · exact .inr (by rw [P.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
        · exact .inl (List.mem_singleton.mp h1)
      rcases hsm with h | h
      · rw [hs1] at h; unfold binAt at h; omega
      · obtain ⟨c, hc, hca, _⟩ := HH.member P.i0 P.i1 h
        have := (HH.walk.chunk_bounds c hc).1; unfold heapStart at this; rw [hca, hs1, hb1] at this; omega
    subst hi1
    obtain ⟨rfl, rfl⟩ := hnil rfl
    have hp1 : predP = binAt 1 := by have := P.hpred; simp at this; exact this.symm
    subst hp1 hs1
    exact hlr _ cs₀ p psz B
  · refine hnl _ cs₀ p psz i pre post predP succP (fun he => hne ?_) B
    subst he; obtain ⟨rfl, rfl⟩ := hnil rfl
    have e1 := B.a1; have e0 := B.a0
    apply BitVec.eq_of_toNat_eq; rw [e1, e0]; have := P.hsucc; simp at this; exact this.symm

structure B2Geo (C : MCtx) (p psz sz dsz predP succP : Nat) : Prop where
  p16 : p % 16 = 0
  plo : 0x8001c170 ≤ p
  psz16 : psz % 16 = 0
  psz32 : 32 ≤ psz
  sz16 : sz % 16 = 0
  sz32 : 32 ≤ sz
  dsz16 : dsz % 16 = 0
  dsz32 : 32 ≤ dsz
  dend : p + psz + sz + dsz ≤ C.top0
  top : C.top0 + 16 ≤ 0x87800000
  pp16 : predP % 16 = 0
  sp16 : succP % 16 = 0
  pplo : 0x8001ad20 ≤ predP
  splo : 0x8001ad20 ≤ succP
  pphi : predP + 32 ≤ C.top0
  sphi : succP + 32 ≤ C.top0
  sP : p ≠ succP + 16
  sX : p + psz ≠ succP + 16
  sD : p + psz + sz ≠ succP + 16
  pD : p + psz + sz ≠ predP + 16
  pP : p ≠ predP + 8
  pX : p + psz ≠ predP + 8
  ppfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (predP + k)
  spfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot C.H (succP + k)

theorem FB2.geo {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP) :
    B2Geo C p psz sz d.size predP succP := by
  have HH := B.heap.heap.heap
  have P := B.pv
  obtain ⟨hal, _⟩ := HH.aligned
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hxm : (⟨x, sz, true⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hdm : d ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hpb := HH.walk.chunk_bounds _ hpm; have hdb := HH.walk.chunk_bounds _ hdm
  have hp16 := hal _ hpm
  have hps := walk_sizes HH.walk _ hpm; have hxs := walk_sizes HH.walk _ hxm
  have hds := walk_sizes HH.walk _ hdm
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := B.heap.heap.top_room
  have hpend := P.pend
  have hda := B.daddr
  simp only at hpb hp16 hps hxs
  rw [hda] at hdb
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
  have bP : (p = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃, c.addr = p) :=
    .inr ⟨_, hpm, rfl⟩
  have bX : (x = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃, c.addr = x) :=
    .inr ⟨_, hxm, rfl⟩
  have bD : (x + sz = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃, c.addr = x + sz) :=
    .inr ⟨_, hdm, hda⟩
  have hloc : ∀ z, (z = binAt i ∨ ∃ cx ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃,
      cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins i) →
      0x8001ad20 ≤ z ∧ z + 32 ≤ C.top0 := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i P.i1; have := HH.walk.le; have hi0 := P.i0
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  unfold heapStart heapEnd at *
  exact ⟨hp16, hpb.1, hps.1, hps.2, hxs.1, hxs.2, hds.1, hds.2, by have := hdb.2.1; omega, by omega,
    hpp16, hsp16, (hloc _ hpnode).1, (hloc _ hsnode).1, (hloc _ hpnode).2, (hloc _ hsnode).2,
    HH.bnd_ne_node P.i1 hsnode bP 16 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hsnode bX 16 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hsnode bD 16 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hpnode bD 16 (by omega) (by omega),
    HH.bnd_ne_node P.i1 hpnode bP 8 (by omega) (by omega),
    by rw [hpend]; exact HH.bnd_ne_node P.i1 hpnode bX 8 (by omega) (by omega),
    B.heap.heap.node_foot P.i0 P.i1 hpredm, B.heap.heap.node_foot P.i0 P.i1 hsuccm⟩

abbrev b2Mem (Mt : Mem) (p psz sz hdr0 predP succP : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog Mt
    [(predP + 16, 8, BitVec.ofNat 64 succP)]) [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(p + psz + 8, 8, BitVec.ofNat 64 (hdr0 ||| 1))]) [(p + 8, 8, BitVec.ofNat 64 (psz + sz + 1))])
    [(p + psz + 8, 8, BitVec.ofNat 64 hdr0)]

theorem FB2.coal {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP) :
    PHeapAt (b2Mem Mt p psz sz hdr0 predP succP) C.H C.top0 brkv
      (cs₀ ++ ⟨p, psz + sz, true⟩ :: d :: cs₃) (updBins bins i (pre ++ post)) := by
  have G := B.geo
  have P := B.pv
  have hpend := P.pend
  subst hpend
  have h := B.heap
  simp only [List.append_assoc, List.singleton_append] at h
  have hps := G.psz16; have hss := G.sz16
  exact h.coalPrev B.hno P.i0 P.i1 P.bin P.hpred P.hsucc B.hdr (h' := psz + sz + 1)
    (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by have := P.prev h0 hr; unfold prevInuse; rw [show (psz + sz + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)

theorem b2_agree {C : MCtx} {Mt Mt1 : Mem} {p psz sz dsz hdr0 predP succP : Nat} {w : BitVec 64}
    (G : B2Geo C p psz sz dsz predP succP) (hM1 : Mt1 = writeLog Mt [(p + psz + sz + 8, 8, w)])
    (hdr : read64 Mt (p + psz + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, vsaFoot C.H w0 → ¬ (p + 8 ≤ w0 ∧ w0 < p + 16) → ¬ (p + psz + sz + 8 ≤ w0 ∧ w0 < p + psz + sz + 16) →
      (writeLog (writeLog Mt1 [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (b2Mem Mt p psz sz hdr0 predP succP)[w0]? := by
  open_fields G
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hpv : predP < 2 ^ 64 := by omega
  have hsv : succP < 2 ^ 64 := by omega
  subst hM1
  intro w0 hw0 h1' h2'
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (p + 8 ≤ x ∧ x < p + 16) ∧
      ¬ (p + psz + sz + 8 ≤ x ∧ x < p + psz + sz + 16))
    [succP + 24, predP + 16, p + psz + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, h1', h2'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact ⟨predP, by rd_log [h1], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpv]⟩
    · exact ⟨succP, by rd_log [h2], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv]⟩
    · exact ⟨hdr0, by rd_log [hdr], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega

theorem FB2.hnoP {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP) :
    ∀ e ∈ C.H, e.1 ≠ p + 16 := by
  have HH := B.heap.heap.heap
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  intro e he heq
  obtain ⟨c, hc, hu, h1, _⟩ := HH.exact e he he
  have := HH.chunk_eq hc hpm (by simp only; omega)
  rw [this] at hu; cases hu

theorem b2_fbin {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP)
    (hdin : d.inuse = true) {v1 v2 v3 v4 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP)
    (h3 : v3.toNat = psz + sz + 1) (h4 : v4.toNat = psz + sz) :
    FBin C (writeLog (writeLog (writeLog (writeLog Mt1 [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])
      [(p + 8, 8, v3)]) [(p + psz + sz, 8, v4)])
      (b2Mem Mt p psz sz hdr0 predP succP) p (psz + sz) C.top0 brkv cs₀ (d :: cs₃)
      (updBins bins i (pre ++ post)) := by
  have G := B.geo
  have P := B.pv
  have hpend := P.pend
  subst hpend
  have HP := B.coal
  have hA := b2_agree G B.mem B.hdr h1 h2
  open_fields G
  have HH := B.heap.heap.heap
  have hdm : d ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨p + psz, sz, true⟩ :: d :: cs₃ := by simp
  obtain ⟨hd0, hd0r, hd0s, hd0l⟩ := walk_header HH.walk d hdm
  rw [B.daddr] at hd0r
  have hno := B.hnoP
  have rP := chunkRgn_FreePaths HP (X := p) (S := psz + sz) (by simp) hno
  have rPP := linkRgn_FreePaths G.ppfoot; have rSP := linkRgn_FreePaths G.spfoot
  have hM1 := B.mem
  refine ⟨⟨HP, Nat.le_refl _, hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega, fun w0 hw0 hr0 => ?_,
    ?_, fun hd hr => ?_⟩, pres_log _ (pres_log _ (pres_log _ (pres_log _ B.pres))), B.disj, ?_⟩
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd0; rw [← hd0]; exact hdin
  · refine agree_of_words (P := fun a => vsaFoot C.H a ∧ ¬ (p + (psz + sz) ≤ a ∧ a < p + (psz + sz) + 16))
      [p + 8] (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨hw0, hr0⟩
    · simp only [List.mem_singleton] at hw'; subst hw'
      exact ⟨psz + sz + 1, by rd_log [h3],
        by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : psz + sz + 1 < 2 ^ 64)]⟩
    · simp only [List.mem_singleton, forall_eq] at hout
      obtain ⟨ha1, ha2⟩ := ha
      rw [writeLog_out, writeLog_out]
      · exact hA a ha1 (by omega) (by omega)
      all_goals simp only [OutL, and_true]; omega
  · rw [show p + (psz + sz) = p + psz + sz by omega, read64_store_hit, h4]
  · rw [show p + (psz + sz) + 8 = p + psz + sz + 8 by omega, rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)] at hr
    rw [hd0r] at hr; cases hr
    refine ⟨w.toNat, ?_, by rw [B.wv, hd0s]; unfold chunkSize; omega, by rw [B.wv]; omega,
      by rw [B.wv]; unfold prevInuse; simp; omega⟩
    rw [show p + (psz + sz) + 8 = p + psz + sz + 8 by omega, rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), hM1, read64_store_hit]
  · simp only [writeLog_nest, List.cons_append, List.nil_append]; exact frame_log (by log_in) B.frameM

theorem free_b2nl {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₀ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz i : Nat} {pre post : List Nat} {predP succP : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP) :
    AW C.live C.S C.Q 0x800073cc#64 R Mt1 := by
  have G := B.geo
  have P := B.pv
  have hpend := P.pend
  subst hpend
  have hM1 := B.mem; have hno := B.hnoP; have HP := B.coal
  open_fields G
  have rP : Rgn (vsaFoot C.H) (p + 8) (psz + sz) :=
    ⟨fun k hk => foot_of_chunk HP (X := p) (S := psz + sz) (by simp) hno (by omega) (by omega)⟩
  have rPP : Rgn (vsaFoot C.H) (predP + 16) 16 :=
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.ppfoot _ (by omega) (by omega)⟩
  have rSP : Rgn (vsaFoot C.H) (succP + 16) 16 :=
    ⟨fun k hk => by rw [Nat.add_assoc]; exact G.spfoot _ (by omega) (by omega)⟩
  have o1 := rSP.offStack B.disj (by decide); have o2 := rPP.offStack B.disj (by decide)
  have o3 := rP.offStack B.disj (by omega)
  have hbk : read64 Mt1 (p + 24) = some predP := by rw [hM1, rd_miss (by omega)]; exact P.bk
  have hpv := Vsa.Sim.read64_lt _ _ _ hbk
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo; unfold mHead at o1 o2 o3
  have ha4 := B.a4; have ha1 := B.a1; have ha5 := B.a5; have ha2 := B.a2; have ha3 := B.a3
  rgn_run O.live at 0x800073d0
  rgn_ld [hbk]
  rgn_run O.live at 0x800073d8
  rw [show (R 11 + 24#64).toNat = succP + 24 by rgn_arith,
    show (BitVec.ofNat 64 predP + 16#64).toNat = predP + 16 by rgn_arith]
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpv]
  have F2 := (B.frame.store (a := succP + 24) (w := 8) (v := BitVec.ofNat 64 predP) (by omega)).store
    (a := predP + 16) (w := 8) (v := R 11) (by omega)
  have hA := b2_agree (C := C) (Mt1 := Mt1) (dsz := d.size) (w := w) G hM1 B.hdr hv1 ha1
  refine (step% st 0x800073d8) O.live (fun hz => ?_) (fun hnz => ?_)
  · have hdf : d.inuse = false := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hz
      have h0 := congrArg BitVec.toNat hz; rw [B.a6] at h0
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at h0
      rw [← B.nnf]; unfold prevInuse; rw [h0]; rfl
    obtain ⟨da, ds, di⟩ := d
    have hda := B.daddr
    simp only at hda hdf
    subst hda hdf
    simp only at hA G_dend G_dsz16 G_dsz32 ha3 HP
    rgn_run O.live at 0x80007458
    refine free_fwd O (Y := p) (a := psz + sz) (b := ds) ⟨⟨
      by rw [show p + (psz + sz) = p + psz + sz by omega]; exact HP, hno, fun h0 hr => ?_,
      fun w0 hw0 h1' h2' => hA w0 hw0 h1' (by omega), ?_, pres_log _ (pres_log _ B.pres), B.disj,
      by simp only [writeLog_nest, List.cons_append, List.nil_append]
         exact frame_log (by log_in) B.frameM⟩,
      F2.of_regs ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [rd_miss (by omega), read64_store_hit] at hr
      cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    · rw [show p + (psz + sz) + 8 = p + psz + sz + 8 by omega, rd_miss (by omega), rd_miss (by omega),
        hM1, read64_store_hit, B.wv]
    · exact B.a7
    · exact ha4
    · rw [BitVec.toNat_add, ha5, ha3]; unfold heapEnd at *; omega
    · rw [ha2]; omega
    · exact B.a0
  · have hdin : d.inuse = true := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hnz
      have hh : hnn % 2 ≠ 0 := fun h0 => hnz (BitVec.eq_of_toNat_eq (by rw [B.a6, h0]; rfl))
      rw [← B.nnf]; unfold prevInuse; rw [show hnn % 2 = 1 by omega]; rfl
    rgn_run O.live at 0x800073e8
    rw [show (R 14 + 8#64).toNat = p + 8 by rgn_arith, ha2]
    have hv3 : (R 15 ||| 1#64).toNat = psz + sz + 1 := by
      rw [BitVec.toNat_or, ha5]
      have h1' : (sz + psz ||| 1) / 2 = (sz + psz) / 2 := by
        have := Nat.or_div_two_pow (a := sz + psz) (b := 1) (n := 1); simpa using this
      have h2' : (sz + psz ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
      have := Nat.div_add_mod (sz + psz ||| 1) 2
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    exact free_bin O ((F2.store (by omega)).store (by omega) |>.of_regs
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]) (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]) (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]))
      (b2_fbin B hdin hv1 ha1 hv3 (by rw [ha5]; omega))
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact B.a7)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact ha4)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [ha5]; omega)

theorem FB2.lr_links {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64} {p psz : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz 1 [] [] (binAt 1) (binAt 1)) :
    read64 Mt (binAt 1 + 16) = some p ∧ read64 Mt (binAt 1 + 24) = some p := by
  have HH := B.heap.heap.heap
  have hring := (binList_iff_ring.1 (HH.bins_list 1 (by decide) (by unfold numBins; decide))).1
  rw [B.pv.bin] at hring
  exact ⟨ring_fd_head hring (f := p) (by simp), ring_bk_head hring (l := p) (by simp)⟩

theorem lr_a_done {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64} {p psz : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz 1 [] [] (binAt 1) (binAt 1))
    (hdin : d.inuse = true) {v3 v4 : BitVec 64} (h3 : v3.toNat = psz + sz + 1)
    (h4 : v4.toNat = psz + sz) :
    FDone C (writeLog (writeLog Mt1 [(p + 8, 8, v3)]) [(p + psz + sz, 8, v4)]) := by
  have G := B.geo
  have P := B.pv
  have hpend := P.pend
  subst hpend
  open_fields G
  have hb1 : binAt 1 = 2147593504 := rfl
  have HH := B.heap.heap.heap
  have hdm : d ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨p + psz, sz, true⟩ :: d :: cs₃ := by simp
  obtain ⟨hd0, hd0r, hd0s, hd0l⟩ := walk_header HH.walk d hdm
  rw [B.daddr] at hd0r
  have hM1 := B.mem
  have hno := B.hnoP
  have HP := B.coal
  obtain ⟨hfd1, hbk1⟩ := B.lr_links
  have hwlt : w.toNat < 2 ^ 64 := w.isLt

  have K : FBinCore C (writeLog (writeLog (b2Mem Mt p psz sz hdr0 (binAt 1) (binAt 1))
      [(p + (psz + sz), 8, BitVec.ofNat 64 (psz + sz))]) [(p + (psz + sz) + 8, 8, w)])
      (b2Mem Mt p psz sz hdr0 (binAt 1) (binAt 1)) p (psz + sz) C.top0 brkv cs₀ (d :: cs₃)
      (updBins bins 1 ([] ++ [])) := by
    refine ⟨HP, Nat.le_refl _, hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega,
      fun w0 hw0 hr0 => ?_, ?_, fun hd hr => ?_⟩
    · rw [rd_miss (by omega), read64_store_hit] at hr
      cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd0; rw [← hd0]; exact hdin
    · rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
    · rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [show p + (psz + sz) + 8 = p + psz + sz + 8 by omega, rd_miss (by omega), rd_miss (by omega),
        rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)] at hr
      rw [hd0r] at hr; cases hr
      refine ⟨w.toNat, read64_store_hit _ _ _, by rw [B.wv, hd0s]; unfold chunkSize; omega,
        by rw [B.wv]; omega, by rw [B.wv]; unfold prevInuse; simp; omega⟩
  have rP := chunkRgn_FreePaths HP (X := p) (S := psz + sz) (by simp) hno
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mt binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 HH.binblocks_present
  have hA : binblocksAddr = 0x8001ad18 := rfl
  refine fb_release K (j := 1) (pre' := []) (post' := []) (pred := binAt 1) (succ := binAt 1) (bb' := bb)
    (by decide) (by unfold numBins; decide) (fun h => absurd h (by decide)) (fun _ => by simp [updBins])
    (by simp [updBins]) rfl rfl ?_ ?_ ?_ ?_ ?_ (B.heap.bb_lt bb hbb) (fun h => absurd h (by decide)) ?_ ?_ ?_
    (pres_log _ (pres_log _ B.pres)) ?_
  · show read64 _ (p + 16) = _; rw [hM1]; rd_log [P.fd]
  · show read64 _ (p + 24) = _; rw [hM1]; rd_log [P.bk]
  · show read64 _ (binAt 1 + 16) = _; rw [hM1]; rd_log [hfd1]
  · show read64 _ (binAt 1 + 24) = _; rw [hM1]; rd_log [hbk1]
  · rw [hA, rd_miss (by omega), rd_miss (by omega), hM1, rd_miss (by omega), ← hA]; exact hbb
  · intro bb0 hbb0 k hk
    rw [hA, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), ← hA, hbb] at hbb0
    cases hbb0; exact hk
  · intro w0 hw0 hr0
    unfold RelW at hr0
    refine agree_of_words (P := fun a => vsaFoot C.H a ∧ ¬ RelW p (psz + sz) (binAt 1) (binAt 1) a)
      [p + 8, p + psz + 8] (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨hw0, by unfold RelW; exact hr0⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact ⟨psz + sz + 1, by rd_log [h3],
          by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : psz + sz + 1 < 2 ^ 64)]⟩
      · exact ⟨hdr0, by rw [hM1]; rd_log [B.hdr],
          by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ B.hdr)]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
      obtain ⟨ha1, ha2⟩ := ha
      unfold RelW binblocksAddr avAddr at ha2
      rw [hM1, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
        writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · intro w0 h1' h2'
    refine agree_of_words (P := fun a => p + (psz + sz) ≤ a ∧ a < p + (psz + sz) + 16)
      [p + psz + sz, p + psz + sz + 8] (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨h1', h2'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact ⟨psz + sz, by rd_log [h4],
          by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : psz + sz < 2 ^ 64)]⟩
      · exact ⟨w.toNat, by rw [hM1]; rd_log, by rd_log⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
      obtain ⟨ha1, ha2⟩ := ha
      omega
  · rw [writeLog_nest]; exact frame_log (L := [_, _]) (by log_in) B.frameM

abbrev lrMem (Mt1 : Mem) : Mem :=
  writeLog (writeLog Mt1 [(binAt 1 + 16, 8, BitVec.ofNat 64 (binAt 1))])
    [(binAt 1 + 24, 8, BitVec.ofNat 64 (binAt 1))]

theorem lr_b_mem {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {bins : Nat → List Nat} {sz hdr0 hnn : Nat} {w : BitVec 64} {p psz ds : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ ⟨p + psz + sz, ds, false⟩ bins (p + psz) sz hdr0 hnn w p psz 1 [] []
      (binAt 1) (binAt 1)) :
    FFwdMem C (lrMem Mt1) (b2Mem Mt p psz sz hdr0 (binAt 1) (binAt 1)) brkv cs₀ cs₃
      (updBins bins 1 ([] ++ [])) p (psz + sz) ds := by
  have G := B.geo
  obtain ⟨hp16, hplo, hps16, hps32, hs16, hs32, hd16, hd32, hdend, htop, hpp16, hsp16, hpplo, hsplo,
    hpphi, hsphi, sP, sX, sD, pD, pP, pX, hppf, hspf⟩ := G
  simp only at hd16 hd32 hdend
  have hb1 : binAt 1 = 2147593504 := rfl
  have hM1 := B.mem
  have HP := B.coal
  try simp only at HP
  have hdlt := Vsa.Sim.read64_lt _ _ _ B.hdr
  have eb : (BitVec.ofNat 64 (binAt 1)).toNat = binAt 1 := rfl
  refine ⟨by rw [show p + (psz + sz) = p + psz + sz by omega]; exact HP, B.hnoP, fun h0 hr => ?_,
    fun w0 hw0 h1' h2' => ?_, ?_, pres_log _ (pres_log _ B.pres), B.disj, ?_⟩
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · refine agree_of_words (P := fun a => vsaFoot C.H a ∧ ¬ (p + 8 ≤ a ∧ a < p + 16) ∧
        ¬ (p + (psz + sz) + 8 ≤ a ∧ a < p + (psz + sz) + 16))
      [binAt 1 + 16, binAt 1 + 24, p + psz + 8] (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨hw0, h1', h2'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact ⟨binAt 1, by rd_log [eb], by rd_log [eb]⟩
      · exact ⟨binAt 1, by rd_log [eb], by rd_log [eb]⟩
      · exact ⟨hdr0, by rw [hM1]; rd_log [B.hdr], by rd_log [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
      obtain ⟨ha1, ha2, ha3⟩ := ha
      rw [hM1, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
        writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · rw [show p + (psz + sz) + 8 = p + psz + sz + 8 by omega, rd_miss (by omega), rd_miss (by omega),
      hM1, read64_store_hit, B.wv]
  · have rG := globRgn C.H; clear sP sX sD pD pP pX; unfold lrMem; rw [writeLog_nest]
    exact frame_log (L := [_, _]) (by log_in) B.frameM

theorem lr_b_done {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₀ cs₃ : List Chunk}
    {bins : Nat → List Nat} {sz hdr0 hnn : Nat} {w : BitVec 64} {p psz ds : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ ⟨p + psz + sz, ds, false⟩ bins (p + psz) sz hdr0 hnn w p psz 1 [] []
      (binAt 1) (binAt 1))
    {predD succD : Nat} (hbkD : read64 Mt (p + psz + sz + 24) = some predD)
    (hfdD : read64 Mt (p + psz + sz + 16) = some succD)
    {v1 v2 v3 v4 : BitVec 64} (h1 : v1.toNat = predD) (h2 : v2.toNat = succD)
    (h3 : v3.toNat = psz + sz + ds + 1) (h4 : v4.toNat = psz + sz + ds) :
    FDone C (writeLog (writeLog (writeLog (writeLog Mt1 [(succD + 24, 8, v1)]) [(predD + 16, 8, v2)])
      [(p + 8, 8, v3)]) [(p + (psz + sz) + ds, 8, v4)]) := by
  have VM := lr_b_mem B
  have G2 := B.geo
  have P := B.pv
  obtain ⟨hp16, hplo, hps16, hps32, hs16, hs32, hd16, hd32, hdend, htop, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _⟩ := G2
  simp only at hd16 hd32 hdend
  obtain ⟨iD, preD, postD, d', cs'', hdn, X⟩ := VM.nx
  obtain ⟨pred', hpred⟩ : ∃ q, (binAt iD :: preD).getLast? = some q := ⟨_, List.getLast?_cons⟩
  obtain ⟨succ', hsucc⟩ : ∃ q, (postD ++ [binAt iD]).head? = some q := by
    rcases postD with _ | ⟨z, zs⟩ <;> simp
  have G := X.geo VM hpred hsucc
  have HH := VM.heap.heap.heap
  have hiD : iD ≠ 1 := by
    intro he; have := X.bin; rw [he] at this; simp [updBins] at this
  have hring := (binList_iff_ring.1 (HH.bins_list iD X.i0 X.i1)).1
  rw [X.bin] at hring
  have hM2 : ∀ o, o = 16 ∨ o = 24 → read64 (b2Mem Mt p psz sz hdr0 (binAt 1) (binAt 1)) (p + (psz + sz) + o) =
      read64 Mt (p + psz + sz + o) := by
    have hb1 : binAt 1 = 2147593504 := rfl
    rintro o (rfl | rfl) <;>
    rw [show p + (psz + sz) = p + psz + sz by omega, rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)]
  have e1 : succ' = succD := by
    have := (ring_member hring hpred hsucc).1
    simp only [fdOf] at this
    rw [hM2 16 (.inl rfl), hfdD] at this; exact (Option.some.inj this).symm
  have e2 : pred' = predD := by
    have := (ring_member hring hpred hsucc).2
    simp only [bkOf] at this
    rw [hM2 24 (.inr rfl), hbkD] at this; exact (Option.some.inj this).symm
  subst e1 e2
  have FB := fwd_fbin VM X hpred hsucc h1 h2 h3 h4
  obtain ⟨hY16, ha16, ha32, hb16, hb32, hYlo, hdend', htop', hp16', hs16', hplo', hslo', hphi', hshi',
    sY, sN, sD, pD, pY, pN, hppf, hspf, hdf⟩ := G
  have hb1 : binAt 1 = 2147593504 := rfl

  have hnode : ∀ z, (z = binAt iD ∨ z ∈ updBins bins 1 ([] ++ []) iD) → z ≠ p ∧ z ≠ binAt 1 := by
    rintro z (rfl | hz)
    · have := binAt_geo iD X.i1
      refine ⟨by unfold binAt avAddr at *; omega, fun he => hiD ?_⟩
      unfold binAt avAddr at he; omega
    · obtain ⟨c, hc, hca, hcf⟩ := HH.member X.i0 X.i1 hz
      have := (HH.walk.chunk_bounds c hc).1; unfold heapStart at this
      refine ⟨fun he => ?_, by rw [← hca, hb1]; omega⟩
      have hpm : (⟨p, psz + sz, true⟩ : Chunk) ∈ cs₀ ++ ⟨p, psz + sz, true⟩ :: ⟨p + (psz + sz), ds, false⟩ :: cs₃ := by simp
      have := HH.chunk_eq hc hpm (by rw [hca, he])
      rw [this] at hcf; cases hcf
  have hpredm : pred' = binAt iD ∨ pred' ∈ updBins bins 1 ([] ++ []) iD := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [X.bin]; exact List.mem_append_left _ h1)
  have hsuccm : succ' = binAt iD ∨ succ' ∈ updBins bins 1 ([] ++ []) iD := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [X.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hPp, hPb⟩ := hnode _ hpredm
  obtain ⟨hSp, hSb⟩ := hnode _ hsuccm
  have hM1 := B.mem
  obtain ⟨hfd1, hbk1⟩ := B.lr_links
  have hdnr := X.dhdr
  have hdn' : read64 Mt1 (p + (psz + sz) + ds + 8) = some hdn := by
    rw [hM1, rd_miss (by omega)]
    rw [show p + (psz + sz) + ds + 8 = p + (psz + sz) + ds + 8 from rfl] at hdnr
    rw [← hdnr, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega)]
  obtain ⟨bb, hbb⟩ : ∃ bb, read64 Mt binblocksAddr = some bb :=
    Option.isSome_iff_exists.1 B.heap.heap.heap.binblocks_present
  have hA : binblocksAddr = 0x8001ad18 := rfl
  have rP := chunkRgn_FreePaths FB.heap (X := p) (S := psz + sz + ds) (by simp) FB.hno
  have rF := linkRgn_FreePaths hspf; have rB := linkRgn_FreePaths hppf
  refine fb_release FB.toFBinCore (j := 1) (pre' := []) (post' := []) (pred := binAt 1) (succ := binAt 1)
    (bb' := bb) (by decide) (by unfold numBins; decide) (fun h => absurd h (by decide))
    (fun _ => by rw [updBins_other _ _ (Ne.symm hiD), updBins_same]; rfl)
    (by rw [updBins_other _ _ (Ne.symm hiD), updBins_same]) rfl rfl ?_ ?_ ?_ ?_ ?_
    (B.heap.bb_lt bb hbb) (fun h => absurd h (by decide)) ?_ ?_ ?_
    (pres_log _ (pres_log _ (pres_log _ (pres_log _ B.pres)))) ?_
  · show read64 _ (p + 16) = _; rw [hM1]; rd_log [B.pv.fd]
  · show read64 _ (p + 24) = _; rw [hM1]; rd_log [B.pv.bk]
  · show read64 _ (binAt 1 + 16) = _; rw [hM1]; rd_log [hfd1]
  · show read64 _ (binAt 1 + 24) = _; rw [hM1]; rd_log [hbk1]
  · rw [hA, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), hM1,
      rd_miss (by omega), ← hA]; exact hbb
  · intro bb0 hbb0 k hk
    rw [hA, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), rd_miss (by omega), ← hA, hbb] at hbb0
    cases hbb0; exact hk
  · intro w0 hw0 hr0
    unfold RelW binblocksAddr avAddr at hr0
    exact wl1_congr fun _ => wl1_congr fun _ => wl1_congr fun _ => wl1_congr fun _ => by
      rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · intro w0 h1' h2'
    exact wl1_congr fun _ => wl1_congr fun _ => wl1_congr fun _ => wl1_congr fun _ => by
      rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · clear sY sN sD pD pY pN
    simp only [writeLog_nest, List.cons_append, List.nil_append]; exact frame_log (by log_in) B.frameM

structure FreeLinks (H : List (Nat × Nat)) (top : Nat) (m : Mem) (c : Nat) (fd bk : Nat) : Prop where
  fdr : read64 m (c + 16) = some fd
  bkr : read64 m (c + 24) = some bk
  fd16 : fd % 16 = 0
  bk16 : bk % 16 = 0
  fdlo : 0x8001ad20 ≤ fd
  bklo : 0x8001ad20 ≤ bk
  fdhi : fd + 32 ≤ top
  bkhi : bk + 32 ≤ top
  fdfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot H (fd + k)
  bkfoot : ∀ k, 16 ≤ k → k < 32 → vsaFoot H (bk + k)

theorem free_links {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) {c : Chunk} (hc : c ∈ chunks)
    (hf : c.inuse = false) : ∃ fd bk, FreeLinks H top m c.addr fd bk := by
  have HH := h.heap.heap
  obtain ⟨i, hi0, hi, hm, _⟩ := HH.free_binned c hc hf
  obtain ⟨pre, post, hbin⟩ := List.append_of_mem hm
  obtain ⟨pred, hpred⟩ : ∃ q, (binAt i :: pre).getLast? = some q := ⟨_, List.getLast?_cons⟩
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt i]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have hring := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  rw [hbin] at hring
  have hpm : pred = binAt i ∨ pred ∈ bins i := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hbin]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt i ∨ succ ∈ bins i := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hbin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨hp16, hpnode⟩ := HH.node hi0 hi hpm
  obtain ⟨hs16, hsnode⟩ := HH.node hi0 hi hsm
  have hloc : ∀ z, (z = binAt i ∨ ∃ cx ∈ chunks, cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins i) →
      0x8001ad20 ≤ z ∧ z + 32 ≤ top := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo i hi; have := HH.walk.le; unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  exact ⟨succ, pred, (ring_member hring hpred hsucc).1, (ring_member hring hpred hsucc).2, hs16, hp16,
    (hloc _ hsnode).1, (hloc _ hpnode).1, (hloc _ hsnode).2, (hloc _ hpnode).2,
    h.heap.node_foot hi0 hi hsm, h.heap.node_foot hi0 hi hpm⟩

theorem free_b2lr {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₀ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    {p psz : Nat}
    (B : FB2 C R Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz 1 [] [] (binAt 1) (binAt 1)) :
    AW C.live C.S C.Q 0x80007508#64 R Mt1 := by
  have G := B.geo
  have P := B.pv
  have hpend := P.pend
  subst hpend
  open_fields G; clear G_sP G_sX G_sD G_pD G_pP G_pX
  have hM1 := B.mem; have hno := B.hnoP; have HP := B.coal
  have rP := chunkRgn_FreePaths HP (X := p) (S := psz + sz) (by simp) hno
  have oP := rP.offStack B.disj (by omega)
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo; unfold mHead at oP
  have ha4 := B.a4; have ha5 := B.a5; have ha2 := B.a2; have ha3 := B.a3
  refine st_80007508 O.live (fun hnz => ?_) (fun hz => ?_)
  · have hdin : d.inuse = true := by
      have hh : hnn % 2 ≠ 0 := fun h0 => hnz (BitVec.eq_of_toNat_eq (by rw [B.a6, h0]; rfl))
      rw [← B.nnf]; unfold prevInuse; rw [show hnn % 2 = 1 by omega]; rfl
    rgn_run O.live at 0x80007434
    rw [show (R 14 + 8#64).toNat = p + 8 by rgn_arith, ha2]
    have D := lr_a_done B hdin (v3 := R 15 ||| 1#64) (v4 := R 15) (by rw [or1_toNat ha5 (by omega)]; omega)
      (by rw [ha5]; omega)
    exact free_epi O ((B.frame.store (by omega)).store (by omega) |>.of_regs rfl rfl rfl rfl)
      D.heap D.pres D.frame
  · have hdf : d.inuse = false := by
      simp only [ne_eq, Decidable.not_not] at hz
      have h0 := congrArg BitVec.toNat hz; rw [B.a6] at h0
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at h0
      rw [← B.nnf]; unfold prevInuse; rw [h0]; rfl
    obtain ⟨da, ds, di⟩ := d
    have hda := B.daddr
    simp only at hda hdf G_dsz16 G_dsz32 G_dend ha3
    subst hda hdf
    have hdm : (⟨p + psz + sz, ds, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++
        ⟨p + psz, sz, true⟩ :: ⟨p + psz + sz, ds, false⟩ :: cs₃ := by simp
    obtain ⟨succD, predD, L⟩ := free_links B.heap hdm rfl
    open_fields L
    have rD := B.heap.heap.freeSpan hdm rfl; simp only at rD
    have rF := linkRgn_FreePaths L.fdfoot; have rB := linkRgn_FreePaths L.bkfoot
    have o1 := rD.offStack B.disj (by omega); have o2 := rF.offStack B.disj (by omega)
    have o3 := rB.offStack B.disj (by omega); unfold mHead at o1 o2 o3
    have hsv := Vsa.Sim.read64_lt _ _ _ L_fdr; have hpv := Vsa.Sim.read64_lt _ _ _ L_bkr
    have hfd' : read64 Mt1 (p + psz + sz + 16) = some succD := by rw [hM1, rd_miss (by omega)]; exact L_fdr
    have hbk' : read64 Mt1 (p + psz + sz + 24) = some predD := by rw [hM1, rd_miss (by omega)]; exact L_bkr
    rgn_run O.live at 0x80007514
    rgn_ld [hbk', hfd']
    rgn_run O.live at 0x80007434
    have hT : (R 13 + R 15).toNat = psz + sz + ds := by rgn_arith
    rw [show (BitVec.ofNat 64 succD + 24#64).toNat = succD + 24 by rgn_arith,
      show (BitVec.ofNat 64 predD + 16#64).toNat = predD + 16 by rgn_arith,
      show (R 14 + 8#64).toNat = p + 8 by rgn_arith,
      show (R 14 + (R 13 + R 15)).toNat = p + (psz + sz) + ds by rgn_arith]
    have D := lr_b_done B L_bkr L_fdr (v1 := BitVec.ofNat 64 predD) (v2 := BitVec.ofNat 64 succD)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpv]) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv])
      (or1_toNat hT (by omega)) hT
    exact free_epi O ((((B.frame.store (by omega)).store (by omega)).store (by omega)).store (by omega)
      |>.of_regs rfl rfl rfl rfl) D.heap D.pres D.frame

theorem free_split {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₁ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) :
    AW C.live C.S C.Q 0x800073ac#64 R Mt1 := by
  have ht1 := N.t1; have ha6 := N.a6
  refine (step% st 0x800073ac) O.live (fun hp => ?_) (fun hp => ?_)
  · have hprev : hdr0 % 2 = 1 := by
      have : hdr0 % 2 ≠ 0 := fun h0 => hp (BitVec.eq_of_toNat_eq (by rw [ht1, h0]; rfl))
      omega
    refine (step% st 0x80007448) O.live (fun hn => ?_) (fun hn => ?_)
    · have hdin : d.inuse = true := by
        have hh : hnn % 2 ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by rw [ha6, h0]; rfl))
        rw [← N.nnf]; unfold prevInuse; rw [show hnn % 2 = 1 by omega]; rfl
      exact free_b1a O N hprev hdin
    · have hdf : d.inuse = false := by
        simp only [ne_eq, Decidable.not_not] at hn
        have h0 := congrArg BitVec.toNat hn; rw [ha6] at h0
        rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at h0
        rw [← N.nnf]; unfold prevInuse; rw [h0]; rfl
      exact free_b1b O N hprev hdf
  · have hpf : hdr0 % 2 = 0 := by
      simp only [ne_eq, Decidable.not_not] at hp
      have h0 := congrArg BitVec.toNat hp; rw [ht1] at h0; exact h0
    exact free_b2 O N hpf (fun R' _ _ _ _ _ _ _ _ _ B => free_b2nl O B) (fun R' _ _ _ B => free_b2lr O B)

end VsaIris.VsaHeap
