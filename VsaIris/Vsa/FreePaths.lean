import VsaIris.Vsa.FreeLarge

/-!
# `_free_r`'s paths below the top

A chunk whose successor is not the top: the successor's header loses
`PREV_INUSE` (`0x8000739c`), and the header after it says whether the
successor is free (`FNt`). The chunk then coalesces with a free predecessor,
a free successor, both or neither, and goes to a bin — or, when a neighbour
is the last remainder, stays in or takes over bin 1.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The state at `0x800073ac`: the chunk `x` (size `sz`, header `hdr0`) with
the chunk `d` after it, whose header now reads its size alone (`Mt1`), and
the header `hnn` after `d` giving `d`'s flag; the heap without the block at
the memory before that store (`Mt`). -/
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

/-- **Below the top** (`0x8000739c`): clear the successor's `PREV_INUSE` and
read the header after it. -/
theorem free_nt {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {x sz hdr0 nh : Nat}
    (D : FDec C R Mt q n brkv chunks bins x sz hdr0 nh) (hnt : x + sz ≠ C.top0)
    (hk : ∀ R' Mt1 cs₁ cs₃ d hnn w, FNt C R' Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w →
      AW C.live C.S C.Q 0x800073ac#64 R' Mt1) :
    AW C.live C.S C.Q 0x8000739c#64 R Mt := by
  have Hp := D.heap
  have HH := Hp.heap.heap.heap
  have K := D.chunk
  obtain ⟨hal, htop16⟩ := HH.aligned
  obtain ⟨cs₁, cs₂, hsplit⟩ := List.append_of_mem K.mem
  have hw := HH.walk
  rw [hsplit] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  obtain ⟨d, cs₃, rfl, hda⟩ : ∃ d cs₃, cs₂ = d :: cs₃ ∧ d.addr = x + sz := by
    rcases hnext with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
    · exact absurd he hnt
    · exact ⟨d, cs₃, h1, h2⟩
  have hdm : d ∈ chunks := by rw [hsplit]; simp
  obtain ⟨hdh, hdhr, hdhs, _⟩ := walk_header HH.walk d hdm
  rw [hda, K.next] at hdhr
  obtain rfl : nh = hdh := Option.some.inj hdhr
  obtain ⟨hnn, hnnr, hnnf⟩ := (HH.headers hdm).2
  rw [hda] at hnnr
  have hdb := HH.walk.chunk_bounds d hdm
  have hXb := HH.walk.chunk_bounds _ K.mem
  have hbrk := HH.brk_le; have htle := HH.top_le
  simp only at hXb
  unfold heapStart heapEnd at *
  have hx16 := hal _ K.mem
  have hd16 := hal d hdm
  simp only at hx16
  rw [hda] at hd16 hdb
  have hsz16 := (walk_sizes HH.walk _ K.mem).1
  have hdsz16 := (walk_sizes HH.walk d hdm).1
  simp only at hsz16
  have ha2 := D.a2; have ha3 := D.a3
  have hnf := fun k hk => vsaFoot_of_cons (foot_header Hp.heap.heap (HH.end_bnd K.mem) k hk)
  simp only at hnf
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hEn : (R 12 + sign_extend (m := 64) (0x008#12)).toNat = x + sz + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha2]; simp; omega
  refine st_8000739c O.live ?_ ?_ ?_
  · rw [hEn]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hEn]; exact O.foot hnf
  rw [hEn]
  refine st_800073a0 O.live ?_
  have hEnn : (R 12 + R 13 + sign_extend (m := 64) (0x008#12)).toNat = x + sz + d.size + 8 := by
    sx_norm; rw [BitVec.toNat_add, BitVec.toNat_add, ha2, ha3, hdhs]; simp; omega
  have hnnF := fun k hk => vsaFoot_of_cons (foot_header Hp.heap.heap (HH.end_bnd hdm) k hk)
  rw [hda] at hnnF
  have hnnr' : read64 (writeLog Mt [(x + sz + 8, 8, R 13)]) (x + sz + d.size + 8) = some hnn := by
    rw [read64_store_miss _ _ (by omega)]; exact hnnr
  refine st_800073a4 O.live ?_ ?_ ?_
  · simp only [upd_apply, ite_true]; rw [hEnn]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · simp only [upd_apply, ite_true]; rw [hEnn]; exact O.foot hnnF
  simp only [upd_apply, ite_true]
  rw [hEnn, ldv_at hnnr' _ rfl]
  refine st_800073a8 O.live ?_
  have hnnlt := Vsa.Sim.read64_lt _ _ _ hnnr
  have hoN : x + sz + 8 + 8 ≤ C.s.toNat - mHead ∨ C.s.toNat ≤ x + sz + 8 := by
    refine Classical.byContradiction fun hc => ?_
    have hk : (if x + sz + 8 ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - (x + sz + 8)) < 8 := by
      split <;> omega
    exact Hp.disj _ (by split <;> omega) (by unfold mHead at *; split <;> omega) (hnf _ hk)
  unfold mHead at hoN
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have Hd := Hp.heap.drop
  rw [hsplit] at Hd
  refine hk _ _ cs₁ cs₃ d hnn (R 13) ⟨(D.frame.store (by omega)).of_regs ?_ ?_ ?_ ?_, rfl,
    by rw [ha3]; exact hdhs, Hd, fun e he heq => hst.1 (List.mem_map.2 ⟨e, he, by rw [heq, K.addr]⟩),
    hst.2, hda, K.hdr, K.hsz, K.hlow, hnnr, hnnf, fun a ha => writeLog_present _ _ _ (Hp.pres a ha),
    Hp.disj, frame_store (win_foot hnf) Hp.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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
  · sx_norm
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnnlt,
      show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- Facts every path below the top reads off `FNt`: the geometry of `x` and
`d`, and `d`'s header. -/
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

/-- A footprint doubleword lies wholly below or above the stack window. -/
theorem off_stack_of {C : MCtx} {a : Nat}
    (hd : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hf : ∀ k, k < 8 → vsaFoot C.H (a + k)) : a + 8 ≤ C.s.toNat - 256 ∨ C.s.toNat ≤ a := by
  refine Classical.byContradiction fun hc => ?_
  have hk : (if a ≥ C.s.toNat - mHead then 0 else C.s.toNat - mHead - a) < 8 := by
    unfold mHead; split <;> omega
  exact hd _ (by unfold mHead at *; split <;> omega) (by unfold mHead at *; split <;> omega) (hf _ hk)

/-- **Both neighbours in use** (`0x80007484`): `x`'s header keeps its
`PREV_INUSE`, its footer is written, and it goes to its bin. -/
theorem free_b1a {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat}
    {cs₁ cs₃ : List Chunk} {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hprev : hdr0 % 2 = 1)
    (hdin : d.inuse = true) :
    AW C.live C.S C.Q 0x80007484#64 R Mt1 := by
  have G := N.geo
  have hx16 := G.x16; have hxlo := G.xlo; have hs16 := G.sz16; have hs32 := G.sz32
  have hdend := G.dend; have htop := G.top; have hds32 := G.dsz32
  unfold heapEnd at htop
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨hd0, hd0r, hd0s, _⟩ := G.dhdr
  have ha1 := N.a1; have ha2 := N.a2; have ha0 := N.a0
  have hdrlt := Vsa.Sim.read64_lt _ _ _ N.hdr
  have hor : (hdr0 ||| 1) = hdr0 := by
    have h1 : (hdr0 ||| 1) / 2 = hdr0 / 2 := by
      have := Nat.or_div_two_pow (a := hdr0) (b := 1) (n := 1); simpa using this
    have h2 : (hdr0 ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
    have := Nat.div_add_mod (hdr0 ||| 1) 2; have := Nat.div_add_mod hdr0 2
    omega
  refine st_80007484 O.live ?_
  have hE8 : (R 11 + sign_extend (m := 64) (0xff8#12)).toNat = x + 8 := by
    sx_norm; rw [BitVec.toNat_add, ha1]; simp; omega
  have hEn : (R 12 + sign_extend (m := 64) (0x000#12)).toNat = x + sz := by
    sx_norm; rw [ha2]
  have hof := off_stack_of N.disj G.hfoot
  have hoF := off_stack_of (a := x + sz) N.disj (fun k hk => G.xfoot _ (by omega) (by omega))
  refine st_80007488 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hE8]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hE8]; exact O.foot G.hfoot
  rw [hE8]
  refine st_8000748c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEn]; unfold StOK Vsa.Sim.tohostAddr; omega
  · rw [hEn]; exact O.foot (fun k hk => G.xfoot _ (by omega) (by omega))
  rw [hEn]
  have hval : (R 10 ||| sign_extend (m := 64) (0x001#12)).toNat = hdr0 := by
    sx_norm; rw [BitVec.toNat_or, ha0]; simpa using hor
  generalize hMp : writeLog (writeLog Mt1 [(x + 8, 8, R 10 ||| sign_extend (m := 64) (0x001#12))])
    [(x + sz, 8, R 15)] = Mp
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
      have hds16 := G.dsz16
      refine ⟨d.size, ?_, by unfold chunkSize at hd0s ⊢; omega, by omega,
        by unfold prevInuse; simp; omega⟩
      rw [← hMp, rd_miss (by omega), rd_miss (by omega), hM1, read64_store_hit, N.wv]
    · intro a ha
      rw [← hMp]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (N.pres a ha))
    · rw [← hMp]
      exact frame_store (fun b h1 h2 => .inl (G.xfoot b (by omega) (by omega)))
        (frame_store (win_foot G.hfoot) N.frameM)
  have F : FFrame C (upd R 10 (R 10 ||| sign_extend (m := 64) (0x001#12))) Mp := by
    rw [← hMp]
    exact ((N.frame.store (a := x + 8) (w := 8) (by omega)).store (a := x + sz) (w := 8)
      (by omega)).of_regs (upd_other _ _ (by decide)) (upd_other _ _ (by decide))
      (upd_other _ _ (by decide)) (upd_other _ _ (by decide))
  exact free_bin2 O F B (by rw [upd_other _ _ (by decide)]; exact N.a7)
    (by rw [upd_other _ _ (by decide)]; exact N.a4) (by rw [upd_other _ _ (by decide)]; exact N.a5)

/-- The state at the forward coalescing (`0x80007458`): the machine memory
`Mc` and a virtual heap `Mv` in which `Y` (size `a`) is in use and followed
by the free chunk `Y + a` (size `b`); they agree but on `Y`'s header and the
free chunk's, which the machine left holding its size. -/
structure FFwd (C : MCtx) (R : Nat → BitVec 64) (Mc Mv : Mem) (brkv : Nat) (cs cs' : List Chunk)
    (bins : Nat → List Nat) (Y a b : Nat) : Prop where
  frame : FFrame C R Mc
  heap : PHeapAt Mv C.H C.top0 brkv (cs ++ ⟨Y, a, true⟩ :: ⟨Y + a, b, false⟩ :: cs') bins
  hno : ∀ e ∈ C.H, e.1 ≠ Y + 16
  prev : ∀ h0, read64 Mv (Y + 8) = some h0 → h0 % 2 = 1
  agree : ∀ w, vsaFoot C.H w → ¬ (Y + 8 ≤ w ∧ w < Y + 16) → ¬ (Y + a + 8 ≤ w ∧ w < Y + a + 16) →
    Mc[w]? = Mv[w]?
  nxh : read64 Mc (Y + a + 8) = some b
  pres : ∀ x, vsaFoot C.H x → (Mc[x]?).isSome
  disj : ∀ x, C.s.toNat - mHead ≤ x → x < C.s.toNat → ¬ vsaFoot C.H x
  frameM : ∀ x, ¬ MWin C.H C.s x → Mc[x]? = C.Mt0[x]?
  a7 : R 17 = 0x8001ad10#64
  a4 : (R 14).toNat = Y
  a5 : (R 15).toNat = a + b
  a2 : (R 12).toNat = Y + a
  a0 : (R 10).toNat = binAt 1

/-- The free chunk at the forward coalescing: on its bin, followed by an in-use
chunk that is not the top. -/
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

theorem FFwd.nx {C : MCtx} {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwd C R Mc Mv brkv cs cs' bins Y a b) :
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

/-- The numbers of a forward coalescing: alignment, sizes, and where the
unlink's nodes lie relative to the chunk boundaries. -/
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

theorem FwdNx.geo {C : MCtx} {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwd C R Mc Mv brkv cs cs' bins Y a b)
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

/-- The machine memory and the coalesced virtual heap agree off the merged
chunk's footer and the next header. -/
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
  obtain ⟨hY16, ha16, ha32, hb16, hb32, hYlo, hdend, htop, hp16, hs16, hplo, hslo, hphi, hshi,
    sY, sN, sD, pD, pY, pN, _, _, _⟩ := G
  intro w0 hw0 hr0
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (Y + (a + b) ≤ x ∧ x < Y + (a + b) + 16))
    [succ + 24, pred + 16, Y + 8, Y + a + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, hr0⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · refine ⟨pred, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit, h1]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨succ, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, h2]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
          read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨a + b + 1, ?_, ?_⟩
      · rw [rd_miss (by omega), read64_store_hit, h3]
      · rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨b, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)]
        exact hnxh
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact hag x hx1 (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

/-- **The heap for the insertion after a forward coalescing.** The machine's
unlink of the free chunk and `Y`'s header and footer give an insertion state
over the virtual heap in which `Y` absorbed it (`PHeapAt.coalNext`). -/
theorem fwd_fbin {C : MCtx} {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwd C R Mc Mv brkv cs cs' bins Y a b)
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
  have hY16 := G.Y16; have ha16 := G.a16; have ha32 := G.a32; have hb16 := G.b16; have hb32 := G.b32
  have hYlo := G.Ylo; have hdend := G.dend; have htop := G.top; have hphi := G.phi; have hshi := G.shi
  have hp16 := G.p16; have hs16 := G.s16; have hplo := G.plo; have hslo := G.slo
  have sY := G.sY; have sN := G.sN; have sD := G.sD; have pD := G.pD; have pY := G.pY; have pN := G.pN
  have hY8 : ∀ h0, read64 Mv (Y + 8) = some h0 → prevInuse (a + b + 1) = prevInuse h0 := by
    intro h0 hr
    have := V.prev h0 hr
    unfold prevInuse; rw [show (a + b + 1) % 2 = 1 by omega, this]
  have hcs : chunkSize (a + b + 1) = a + b := by unfold chunkSize; omega
  have hcl : (a + b + 1) % 4 < 2 := by omega
  have HP := V.heap.coalNext hi0 hi hbin hpred hsucc hdnr hcs hcl hY8 (BitVec.ofNat 64 b)
  subst htail
  have hYfoot : ∀ x, Y + 8 ≤ x → x < Y + (a + b) + 8 → vsaFoot C.H x :=
    fun x h1 h2 => foot_of_chunk HP (by simp) V.hno h1 h2
  refine ⟨⟨HP, Nat.le_refl _, V.hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega,
    fwd_agree G V.agree V.nxh h1 h2 h3, ?_, fun hd hr => ?_⟩, fun x hx => ?_, V.disj, ?_⟩
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
  · exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (V.pres x hx))))
  · refine frame_store (fun x h1 h2 => .inl (hYfoot x (by omega) (by omega)))
      (frame_store (fun x h1 h2 => .inl (hYfoot x (by omega) (by omega)))
        (frame_store (fun x h1 h2 => .inl (by
          have := G.pfoot (x - pred) (by omega) (by omega); rwa [show pred + (x - pred) = x by omega] at this))
          (frame_store (fun x h1 h2 => .inl (by
            have := G.sfoot (x - succ) (by omega) (by omega); rwa [show succ + (x - succ) = x by omega] at this))
            V.frameM)))

/-- The free chunk at the forward coalescing, when it is the last remainder:
bin 1 holds it alone. -/
theorem FwdNx.lr {Mv : Mem} {top : Nat} {cs' : List Chunk} {bins : Nat → List Nat} {Y a b : Nat}
    {pre post : List Nat} {d' : Chunk} {cs'' : List Chunk} {hdn : Nat}
    (X : FwdNx Mv top cs' bins Y a b 1 pre post d' cs'' hdn) (hrem : (bins 1).length ≤ 1) :
    pre = [] ∧ post = [] := by
  have := X.bin
  rw [this] at hrem
  simp at hrem
  exact ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩

/-- **The insertion state of a forward coalescing into the last remainder**,
over a virtual memory: the coalesced heap with the footer and the original
next header. -/
theorem fwd_lr_core {C : MCtx} {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwd C R Mc Mv brkv cs cs' bins Y a b)
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

/-- The machine's stores at `0x800075d0` agree with the virtual insertion
state off the release's words. -/
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
    · refine ⟨a + b + 1, ?_, ?_⟩
      · rw [rd_miss (by omega), read64_store_hit, h3]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨b, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
          rd_miss (by omega), rd_miss (by omega)]
        exact hnxh
      · rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · exact hag x hx1 (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

/-- **A forward coalescing into the last remainder** (`0x800075d0`): `Y`
replaces the free chunk as bin 1's only member; the heap is done. -/
theorem fwd_lr_done {C : MCtx} {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat} {cs cs' : List Chunk}
    {bins : Nat → List Nat} {Y a b : Nat} (V : FFwd C R Mc Mv brkv cs cs' bins Y a b)
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
  have hYf : ∀ x, Y + 8 ≤ x → x < Y + (a + b) + 8 → vsaFoot C.H x :=
    fun x h1 h2 => foot_of_chunk K.heap (by simp) V.hno h1 h2
  refine fb_release K (j := 1) (pre' := []) (post' := []) (pred := binAt 1) (succ := binAt 1)
    (bb' := bb) (by decide) (by unfold numBins; decide) (fun h => absurd h (by decide))
    (fun _ => by simp [updBins]) (by simp [updBins]) rfl rfl ?_ ?_ ?_ ?_ ?_ (V.heap.bb_lt bb hbb)
    (fun h => absurd h (by decide)) ?_ (fwd_lr_agree G V.agree V.nxh h3) ?_ ?_ ?_
  · show read64 _ (Y + 16) = _
    rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, h2]
  · show read64 _ (Y + 24) = _
    rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit, h2]
  · show read64 _ (binAt 1 + 16) = _
    unfold binAt avAddr
    rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      read64_store_hit, h1]
  · show read64 _ (binAt 1 + 24) = _
    unfold binAt avAddr
    rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega), read64_store_hit, h1]
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
      · refine ⟨a + b, ?_, ?_⟩
        · rw [read64_store_hit, h4]
        · rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · refine ⟨hdn, ?_, ?_⟩
        · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
            rd_miss (by omega), rd_miss (by omega),
            read64_keep (fun k hk => V.agree _ (G.dfoot k hk) (by omega) (by omega))]
          exact hdnr
        · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
      obtain ⟨hx1, hx2⟩ := hx
      omega
  · intro x hx
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _ (V.pres x hx))))))
  · refine frame_store (fun x h1 h2 => .inl (hYf x (by omega) (by omega)))
      (frame_store (fun x h1 h2 => .inl (hYf x (by omega) (by omega)))
        (frame_store (fun x h1 h2 => .inl (hYf x (by omega) (by omega)))
          (frame_store (fun x h1 h2 => .inl (hYf x (by omega) (by omega)))
            (frame_store (fun x h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩)))
              (frame_store (fun x h1 h2 => .inl (.inl (.inl ⟨by omega, by omega⟩))) V.frameM)))))

/-- **The forward coalescing** (`0x80007458`): `Y` absorbs the free chunk after
it. A last remainder is replaced in bin 1 (`0x800075d0`); otherwise the free
chunk is unlinked and the merged chunk goes to its bin (`0x800073e8`). -/
theorem free_fwd {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mc Mv : Mem} {brkv : Nat}
    {cs cs' : List Chunk} {bins : Nat → List Nat} {Y a b : Nat}
    (V : FFwd C R Mc Mv brkv cs cs' bins Y a b) :
    AW C.live C.S C.Q 0x80007458#64 R Mc := by
  obtain ⟨i, pre, post, d', cs'', hdn, X⟩ := V.nx
  have HH := V.heap.heap.heap
  obtain ⟨pred, hpred⟩ : ∃ p, (binAt i :: pre).getLast? = some p := ⟨_, List.getLast?_cons⟩
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt i]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have G := X.geo V hpred hsucc
  have hi0 := X.i0; have hi := X.i1
  have hY16 := G.Y16; have ha16 := G.a16; have ha32 := G.a32; have hb16 := G.b16; have hb32 := G.b32
  have hYlo := G.Ylo; have hdend := G.dend; have htop := G.top
  have hp16 := G.p16; have hs16 := G.s16; have hplo := G.plo; have hslo := G.slo
  have hphi := G.phi; have hshi := G.shi
  have hring := (binList_iff_ring.1 (HH.bins_list i hi0 hi)).1
  rw [X.bin] at hring
  have hfdN := (ring_member hring hpred hsucc).1
  have hbkN := (ring_member hring hpred hsucc).2
  have hvm : Y + a ∈ bins i := by rw [X.bin]; exact List.mem_append_right _ List.mem_cons_self
  have hnf := V.heap.heap.node_foot hi0 hi (.inr hvm)
  have hfd' : read64 Mc (Y + a + 16) = some succ := by
    rw [read64_keep (fun k hk => V.agree _ (by
      have := hnf (16 + k) (by omega) (by omega); rwa [show Y + a + (16 + k) = Y + a + 16 + k by omega] at this)
      (by omega) (by omega))]
    exact hfdN
  have hbk' : read64 Mc (Y + a + 24) = some pred := by
    rw [read64_keep (fun k hk => V.agree _ (by
      have := hnf (24 + k) (by omega) (by omega); rwa [show Y + a + (24 + k) = Y + a + 24 + k by omega] at this)
      (by omega) (by omega))]
    exact hbkN
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have ha2 := V.a2; have ha4 := V.a4; have ha5 := V.a5; have ha0 := V.a0
  have hE16 : (R 12 + sign_extend (m := 64) (0x010#12)).toNat = Y + a + 16 := by
    sx_norm; rw [BitVec.toNat_add, ha2]; simp; omega
  have hE24 : (R 12 + sign_extend (m := 64) (0x018#12)).toNat = Y + a + 24 := by
    sx_norm; rw [BitVec.toNat_add, ha2]; simp; omega
  refine st_80007458 O.live ?_ ?_ ?_
  · rw [hE16]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hE16]; exact O.foot (fun k hk => by
      have := hnf (16 + k) (by omega) (by omega); rwa [show Y + a + (16 + k) = Y + a + 16 + k by omega] at this)
  rw [ldv_at hfd' _ hE16]
  refine st_8000745c O.live ?_
  refine st_80007460 O.live ?_
  have hsv : succ < 2 ^ 64 := by omega
  have hb1 : binAt 1 = 2147593504 := rfl
  -- is the free chunk the last remainder?
  have hlr : succ = binAt 1 ↔ i = 1 := by
    have hsm : succ = binAt i ∨ succ ∈ bins i := by
      have := List.mem_of_head? hsucc
      rcases List.mem_append.mp this with h1 | h1
      · exact .inr (by rw [X.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
      · exact .inl (List.mem_singleton.mp h1)
    constructor
    · intro he
      rcases hsm with h | h
      · rw [he] at h; unfold binAt at h; omega
      · obtain ⟨c, hc, hca, _⟩ := HH.member hi0 hi h
        have := (HH.walk.chunk_bounds c hc).1; unfold heapStart at this; rw [hca, he, hb1] at this; omega
    · intro he; subst he
      obtain ⟨rfl, rfl⟩ := X.lr HH.remainder
      simpa using hsucc.symm
  refine st_80007464 O.live (fun heq => ?_) (fun hne => ?_)
  · -- the last remainder: take over bin 1
    have hs1 : succ = binAt 1 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv, ha0] at this; exact this
    have hi1 : i = 1 := hlr.1 hs1
    subst hi1
    obtain ⟨rfl, rfl⟩ := X.lr HH.remainder
    have K := fwd_lr_core V X
    have hYf : ∀ x, Y + 8 ≤ x → x < Y + (a + b) + 8 → vsaFoot C.H x :=
      fun x h1 h2 => foot_of_chunk K.heap (by simp) V.hno h1 h2
    have ha7 := V.a7
    have e40 : (R 17 + sign_extend (m := 64) (0x028#12)).toNat = binAt 1 + 24 := by rw [ha7]; rfl
    have e32 : (R 17 + sign_extend (m := 64) (0x020#12)).toNat = binAt 1 + 16 := by rw [ha7]; rfl
    have eY24 : (R 14 + sign_extend (m := 64) (0x018#12)).toNat = Y + 24 := by
      sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
    have eY16 : (R 14 + sign_extend (m := 64) (0x010#12)).toNat = Y + 16 := by
      sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
    have eY8 : (R 14 + sign_extend (m := 64) (0x008#12)).toNat = Y + 8 := by
      sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
    have eN : (R 14 + R 15 + sign_extend (m := 64) (0x000#12)).toNat = Y + a + b := by
      sx_norm; rw [BitVec.toNat_add, ha4, ha5]; simp; omega
    have hglob : ∀ o, 16 ≤ o → o < 32 → ∀ k, k < 8 → vsaFoot C.H (binAt 1 + o + k - k + k) := by
      intro o h1 h2 k hk; exact .inl (.inl ⟨by rw [hb1]; omega, by rw [hb1]; omega⟩)
    refine st_800075d0 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [e40, hb1]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [e40]; exact O.foot (fun k hk => .inl (.inl ⟨by rw [hb1]; omega, by rw [hb1]; omega⟩))
    rw [e40]
    refine st_800075d4 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [e32, hb1]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [e32]; exact O.foot (fun k hk => .inl (.inl ⟨by rw [hb1]; omega, by rw [hb1]; omega⟩))
    rw [e32]
    refine st_800075d8 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [eY24]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eY24]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eY24]
    refine st_800075dc O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [eY16]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eY16]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eY16]
    refine st_800075e0 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [eY8]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eY8]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eY8]
    refine st_800075e4 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [eN]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eN]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eN]
    refine st_800075e8 O.live ?_
    have hv3 : (R 15 ||| sign_extend (m := 64) (0x001#12)).toNat = a + b + 1 := by
      sx_norm
      rw [BitVec.toNat_or, ha5]
      have h1' : (a + b ||| 1) / 2 = (a + b) / 2 := by
        have := Nat.or_div_two_pow (a := a + b) (b := 1) (n := 1); simpa using this
      have h2' : (a + b ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
      have := Nat.div_add_mod (a + b ||| 1) 2
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    have D := fwd_lr_done V X ha4 ha0 hv3 ha5
    have F := V.frame
    have o1 := off_stack_of (a := binAt 1 + 24) V.disj (fun k hk => .inl (.inl ⟨by rw [hb1]; omega, by rw [hb1]; omega⟩))
    have o2 := off_stack_of (a := binAt 1 + 16) V.disj (fun k hk => .inl (.inl ⟨by rw [hb1]; omega, by rw [hb1]; omega⟩))
    have o3 := off_stack_of (a := Y + 24) V.disj (fun k hk => hYf _ (by omega) (by omega))
    have o4 := off_stack_of (a := Y + 16) V.disj (fun k hk => hYf _ (by omega) (by omega))
    have o5 := off_stack_of (a := Y + 8) V.disj (fun k hk => hYf _ (by omega) (by omega))
    have o6 := off_stack_of (a := Y + a + b) V.disj (fun k hk => hYf _ (by omega) (by omega))
    exact free_epi O ((((((F.store (by omega)).store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega) |>.of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]) (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])) D.heap D.pres D.frame
  · -- an ordinary free chunk: unlink it and insert the merged chunk
    have hs1 : succ ≠ binAt 1 := by
      intro he; apply hne
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv, ha0, he]
    have hpv : pred < 2 ^ 64 := by omega
    have hv3 : (R 15 ||| sign_extend (m := 64) (0x001#12)).toNat = a + b + 1 := by
      sx_norm
      rw [BitVec.toNat_or, ha5]
      have h1' : (a + b ||| 1) / 2 = (a + b) / 2 := by
        have := Nat.or_div_two_pow (a := a + b) (b := 1) (n := 1); simpa using this
      have h2' : (a + b ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.2 (.inr rfl)
      have := Nat.div_add_mod (a + b ||| 1) 2
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    have B := fwd_fbin V X hpred hsucc (v1 := BitVec.ofNat 64 pred) (v2 := BitVec.ofNat 64 succ)
      (BitVec.toNat_ofNat .. ▸ Nat.mod_eq_of_lt hpv) (BitVec.toNat_ofNat .. ▸ Nat.mod_eq_of_lt hsv)
      hv3 ha5
    have hYf : ∀ x, Y + 8 ≤ x → x < Y + (a + b) + 8 → vsaFoot C.H x :=
      fun x h1 h2 => B.foot_chunk h1 h2
    refine st_80007468 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [hE24]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · rw [hE24]; exact O.foot (fun k hk => by
        have := hnf (24 + k) (by omega) (by omega); rwa [show Y + a + (24 + k) = Y + a + 24 + k by omega] at this)
    rw [ldv_at hbk' _ hE24]
    have eS : (BitVec.ofNat 64 succ + sign_extend (m := 64) (0x018#12)).toNat = succ + 24 := by
      sx_norm; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsv]; simp; omega
    have eP : (BitVec.ofNat 64 pred + sign_extend (m := 64) (0x010#12)).toNat = pred + 16 := by
      sx_norm; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpv]; simp; omega
    have eY8 : (R 14 + sign_extend (m := 64) (0x008#12)).toNat = Y + 8 := by
      sx_norm; rw [BitVec.toNat_add, ha4]; simp; omega
    have eN : (R 14 + R 15 + sign_extend (m := 64) (0x000#12)).toNat = Y + a + b := by
      sx_norm; rw [BitVec.toNat_add, ha4, ha5]; simp; omega
    have hsf := G.sfoot; have hpf := G.pfoot
    refine st_8000746c O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [eS]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eS]; exact O.foot (fun k hk => by
        have := hsf (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
    rw [eS]
    refine st_80007470 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [eP]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eP]; exact O.foot (fun k hk => by
        have := hpf (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
    rw [eP]
    refine st_80007474 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [eY8]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eY8]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eY8]
    refine st_80007478 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [eN]; unfold StOK Vsa.Sim.tohostAddr; omega
    · rw [eN]; exact O.foot (fun k hk => hYf _ (by omega) (by omega))
    rw [eN]
    refine st_8000747c O.live ?_
    have o1 := off_stack_of (a := succ + 24) V.disj (fun k hk => by
      have := hsf (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
    have o2 := off_stack_of (a := pred + 16) V.disj (fun k hk => by
      have := hpf (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
    have o3 := off_stack_of (a := Y + 8) V.disj (fun k hk => hYf _ (by omega) (by omega))
    have o4 := off_stack_of (a := Y + a + b) V.disj (fun k hk => hYf _ (by omega) (by omega))
    exact free_bin O ((((V.frame.store (by omega)).store (by omega)).store (by omega)).store (by omega)
      |>.of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]) (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])) B
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact V.a7)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact ha4)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact ha5)

/-- **Predecessor in use, successor free** (`0x8000744c`): `x` absorbs its
successor (`free_fwd`). -/
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
  have hs := G.dsz32; have hsz := G.sz32; have hx16 := G.x16; have hs16 := G.sz16
  have hdend := G.dend; have htop := G.top
  simp only at hs hdend
  have hM1 := N.mem
  refine st_8000744c O.live ?_
  refine st_80007450 O.live ?_
  refine st_80007454 O.live ?_
  refine free_fwd O ⟨N.frame.of_regs rfl rfl rfl rfl, N.heap, N.hno, fun h0 hr => ?_, fun w0 hw0 h1 h2 => ?_,
    ?_, N.pres, N.disj, N.frameM, ?_, ?_, ?_, ?_, ?_⟩
  · rw [N.hdr] at hr; cases hr; exact hprev
  · rw [hM1, writeLog_out]; simp only [OutL, and_true]; omega
  · rw [hM1, read64_store_hit, N.wv]
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.a7
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.a4
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.toNat_add, N.a5, N.a3]; simp only; unfold heapEnd at htop; omega
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact N.a2
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rfl

/-- The free predecessor `p` of `x` (size `psz`): last of `cs₁`, on bin `i`
between `predP` and `succP`, its header with `PREV_INUSE`, its footer read at
`x`. -/
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

theorem FNt.pv {C : MCtx} {R : Nat → BitVec 64} {Mt Mt1 : Mem} {brkv : Nat} {cs₁ cs₃ : List Chunk}
    {d : Chunk} {bins : Nat → List Nat} {x sz hdr0 hnn : Nat} {w : BitVec 64}
    (N : FNt C R Mt Mt1 brkv cs₁ cs₃ d bins x sz hdr0 hnn w) (hpf : hdr0 % 2 = 0) :
    ∃ cs₀ p psz i pre post predP succP, FPv Mt cs₁ bins x cs₀ p psz i pre post predP succP := by
  have HH := N.heap.heap.heap
  -- `x` is not the first chunk: its header lacks `PREV_INUSE`
  obtain ⟨cs₀, c, hc⟩ : ∃ cs₀ c, cs₁ = cs₀ ++ [c] := by
    rcases List.eq_nil_or_concat cs₁ with rfl | ⟨cs₀, c, rfl⟩
    · exfalso
      have hv : x = heapStart := by
        have := (walkHead (by simpa using HH.walk)).addr; exact this
      have := HH.first_prev
      rw [← hv, N.hdr] at this
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
  rw [hca, N.hdr] at hr
  cases hr
  have hcf : c.inuse = false := by
    rw [← hp]; unfold prevInuse; simp; omega
  obtain ⟨p, psz, ci⟩ := c
  simp only at hca hcf
  subst hcf
  have hcm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
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
  have HH' : HeapAt Mt C.H (fun e => e ∈ C.H) C.top0 brkv (cs₀ ++ ⟨p, psz, false⟩ :: ⟨x, sz, true⟩ :: d :: cs₃) bins := by
    simpa using HH
  exact ⟨cs₀, p, psz, i, pre, post, predP, succP, rfl, hca, hi0, hi, hbin, hpred, hsucc, hft,
    (ring_member hring hpred hsucc).1, (ring_member hring hpred hsucc).2, HH'.freeNbrs.prev⟩

/-- The state after reading the free predecessor (`0x800073c8`): the memory
facts of `FNt` with `cs₁` split at `p`, and `p` in `a4`, the combined size
in `a5`, `p`'s `fd` in `a1`, bin 1's header in `a0`. -/
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

/-- **The free predecessor** (`0x800073b0`): read its size from `x`'s
footer word and its `fd`; the last remainder stays in bin 1 (`0x80007508`),
any other predecessor is unlinked (`0x800073cc`). -/
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
  have G := N.geo
  have HH := N.heap.heap.heap
  have hsplit := P.split
  subst hsplit
  have hx16 := G.x16; have hxlo := G.xlo; have hs16 := G.sz16; have hs32 := G.sz32
  have hdend := G.dend; have htop := G.top
  unfold heapEnd at htop
  have hpm : (⟨p, psz, false⟩ : Chunk) ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨x, sz, true⟩ :: d :: cs₃ := by simp
  have hpb := HH.walk.chunk_bounds _ hpm
  have hp16 := HH.aligned.1 _ hpm
  simp only at hpb hp16
  unfold heapStart at hpb
  have hpend := P.pend
  have hM1 := N.mem
  have hfoot : read64 Mt1 x = some psz := by
    rw [hM1, rd_miss (by omega)]; exact P.foot
  have hfd : read64 Mt1 (p + 16) = some succP := by
    rw [hM1, rd_miss (by omega)]; exact P.fd
  have hpflt := Vsa.Sim.read64_lt _ _ _ hfoot
  have hsflt := Vsa.Sim.read64_lt _ _ _ hfd
  have hxf : ∀ k, k < 8 → vsaFoot C.H (x + k) := fun k hk => by
    have := foot_free N.heap.heap hpm rfl; simp only at this
    rw [← hpend]; exact this.2 k hk
  have hpf16 : ∀ k, k < 16 → vsaFoot C.H (p + 16 + k) := fun k hk => by
    have := foot_free N.heap.heap hpm rfl; simp only at this; exact this.1 k hk
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have ha1 := N.a1; have ha4 := N.a4; have ha5 := N.a5
  have hEx : (R 11 + sign_extend (m := 64) (0xff0#12)).toNat = x := by
    sx_norm; rw [BitVec.toNat_add, ha1]; simp; omega
  refine st_800073b0 O.live ?_ ?_ ?_
  · rw [hEx]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEx]; exact O.foot hxf
  rw [hEx, ldv_at hfoot _ rfl]
  refine st_800073b4 O.live ?_
  refine st_800073b8 O.live ?_
  refine st_800073bc O.live ?_
  have hEp : (R 14 - BitVec.ofNat 64 psz).toNat = p := by
    rw [BitVec.toNat_sub, ha4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpflt]; omega
  have hEpf : (R 14 - BitVec.ofNat 64 psz + sign_extend (m := 64) (0x010#12)).toNat = p + 16 := by
    sx_norm; rw [BitVec.toNat_add, hEp]; simp; omega
  refine st_800073c0 O.live ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [hEpf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEpf]; exact O.foot (fun k hk => hpf16 k (by omega))
  rw [hEpf, ldv_at hfd _ rfl]
  refine st_800073c4 O.live ?_
  have hb1 : binAt 1 = 2147593504 := rfl
  have hA0 : (0x800073b4#64 + sign_extend (m := 64) ((0x00014#20) +++ (0x000#12)) +
      sign_extend (m := 64) (0x96c#12)).toNat = binAt 1 := by rfl
  have hi0 := P.i0; have hi := P.i1
  -- is the predecessor the last remainder?
  have hsm : succP = binAt i ∨ succP ∈ bins i := by
    have := List.mem_of_head? P.hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [P.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  have hLR : succP = binAt 1 ↔ i = 1 := by
    constructor
    · intro he
      rcases hsm with h | h
      · rw [he] at h; unfold binAt at h; omega
      · obtain ⟨c, hc, hca, _⟩ := HH.member hi0 hi h
        have := (HH.walk.chunk_bounds c hc).1; unfold heapStart at this; rw [hca, he, hb1] at this; omega
    · intro he; subst he
      have hrem := HH.remainder
      rw [P.bin] at hrem; simp at hrem
      have h1 : pre = [] := List.length_eq_zero_iff.1 (by omega)
      have h2 : post = [] := List.length_eq_zero_iff.1 (by omega)
      subst h1 h2
      have := P.hsucc; simp at this; exact this.symm
  have Fr := N.frame
  have hbase : ∀ R' : Nat → BitVec 64, (∀ x, x ≠ 6 → x ≠ 10 → x ≠ 11 → x ≠ 14 → x ≠ 15 → R' x = R x) →
      (R' 14).toNat = p → (R' 15).toNat = sz + psz → (R' 11).toNat = succP → (R' 10).toNat = binAt 1 →
      FB2 C R' Mt Mt1 brkv cs₀ cs₃ d bins x sz hdr0 hnn w p psz i pre post predP succP := by
    intro R' hk h14 h15 h11 h10
    have e := fun y (h1 : y ≠ 6) h2 h3 h4 h5 => hk y h1 h2 h3 h4 h5
    exact ⟨Fr.of_regs (e 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (e 9 (by decide) (by decide) (by decide) (by decide) (by decide))
      (e 18 (by decide) (by decide) (by decide) (by decide) (by decide))
      (e 19 (by decide) (by decide) (by decide) (by decide) (by decide)), N.mem, N.wv, N.heap, N.hno,
      N.daddr, N.hdr, N.hsz, N.hlow, N.nnr, N.nnf, P, N.pres, N.disj, N.frameM,
      by rw [e 17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact N.a7, h14, h15, h11, h10,
      by rw [e 12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact N.a2,
      by rw [e 13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact N.a3,
      by rw [e 16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact N.a6⟩
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hregs : ∀ y, y ≠ 6 → y ≠ 10 → y ≠ 11 → y ≠ 14 → y ≠ 15 →
      (upd (upd (upd (upd (upd (upd R 6 (BitVec.ofNat 64 psz)) 10
        (0x800073b4#64 + sign_extend (m := 64) ((0x00014#20) +++ (0x000#12)))) 10
        (0x800073b4#64 + sign_extend (m := 64) ((0x00014#20) +++ (0x000#12)) + sign_extend (m := 64) (0x96c#12)))
        14 (R 14 - BitVec.ofNat 64 psz)) 11 (BitVec.ofNat 64 succP)) 15 (R 15 + BitVec.ofNat 64 psz)) y = R y :=
    fun y h6 h10 h11 h14 h15 => by simp only [upd_apply, h6, h10, h11, h14, h15, ite_false]
  have B := hbase _ hregs
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hEp)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [BitVec.toNat_add, ha5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpflt]; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsflt])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hA0)
  refine st_800073c8 O.live (fun heq => ?_) (fun hne => ?_)
  · have hs1 : succP = binAt 1 := by
      have e1 := B.a1; have e0 := B.a0
      rw [heq] at e1; rw [e1] at e0; exact e0
    have hi1 := hLR.1 hs1
    subst hi1
    have hrem := HH.remainder
    rw [P.bin] at hrem; simp at hrem
    have h1 : pre = [] := List.length_eq_zero_iff.1 (by omega)
    have h2 : post = [] := List.length_eq_zero_iff.1 (by omega)
    subst h1 h2
    have hp1 : predP = binAt 1 := by have := P.hpred; simp at this; exact this.symm
    subst hp1 hs1
    exact hlr _ cs₀ p psz B
  · refine hnl _ cs₀ p psz i pre post predP succP (fun he => hne ?_) B
    have e1 := B.a1; have e0 := B.a0
    apply BitVec.eq_of_toNat_eq; rw [e1, e0]; exact hLR.2 he

/-- The numbers of a backward coalescing: `p`, `x = p + psz` and the chunk
`d` after `x`, and where `p`'s bin nodes lie. -/
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

/-- The virtual heap in which the free predecessor `p` absorbed `x`
(`PHeapAt.coalPrev`): `p` unlinked, its header recording `psz + sz`, and
`x`'s header as the machine leaves it. -/
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

/-- The machine memory after unlinking `p` agrees with the coalesced virtual
heap off `p`'s header and the words `excl` excludes. -/
theorem b2_agree {C : MCtx} {Mt Mt1 : Mem} {p psz sz dsz hdr0 predP succP : Nat} {w : BitVec 64}
    (G : B2Geo C p psz sz dsz predP succP) (hM1 : Mt1 = writeLog Mt [(p + psz + sz + 8, 8, w)])
    (hdr : read64 Mt (p + psz + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, vsaFoot C.H w0 → ¬ (p + 8 ≤ w0 ∧ w0 < p + 16) → ¬ (p + psz + sz + 8 ≤ w0 ∧ w0 < p + psz + sz + 16) →
      (writeLog (writeLog Mt1 [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (b2Mem Mt p psz sz hdr0 predP succP)[w0]? := by
  obtain ⟨hp16, hplo, hps16, hps32, hs16, hs32, hd16, hd32, hdend, htop, hpp16, hsp16, hpplo, hsplo,
    hpphi, hsphi, sP, sX, sD, pD, pP, pX, _, _⟩ := G
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  intro w0 hw0 h1' h2'
  refine agree_of_words (P := fun x => vsaFoot C.H x ∧ ¬ (p + 8 ≤ x ∧ x < p + 16) ∧
      ¬ (p + psz + sz + 8 ≤ x ∧ x < p + psz + sz + 16))
    [succP + 24, predP + 16, p + psz + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨hw0, h1', h2'⟩
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
      · rw [rd_miss (by omega), rd_miss (by omega), hM1, rd_miss (by omega)]; exact hdr
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [hM1, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega

/-- No live block starts in the free predecessor. -/
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

/-- **The insertion state after a backward coalescing with an in-use
successor** (`0x800073dc`): the machine's unlink of `p`, its header and
footer, over the virtual heap in which `p` absorbed `x`. -/
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
  obtain ⟨hp16, hplo, hps16, hps32, hs16, hs32, hd16, hd32, hdend, htop, hpp16, hsp16, hpplo, hsplo,
    hpphi, hsphi, sP, sX, sD, pD, pP, pX, hppf, hspf⟩ := G
  have HH := B.heap.heap.heap
  have hdm : d ∈ (cs₀ ++ [⟨p, psz, false⟩]) ++ ⟨p + psz, sz, true⟩ :: d :: cs₃ := by simp
  obtain ⟨hd0, hd0r, hd0s, hd0l⟩ := walk_header HH.walk d hdm
  rw [B.daddr] at hd0r
  have hno := B.hnoP
  have hPf : ∀ a, p + 8 ≤ a → a < p + (psz + sz) + 8 → vsaFoot C.H a :=
    fun a h1 h2 => foot_of_chunk HP (by simp) hno h1 h2
  have hM1 := B.mem
  refine ⟨⟨HP, Nat.le_refl _, hno, fun h0 hr => ?_, fun d0 hd0 => ?_, by omega, fun w0 hw0 hr0 => ?_,
    ?_, fun hd hr => ?_⟩, fun a ha => ?_, B.disj, ?_⟩
  · rw [rd_miss (by omega), read64_store_hit] at hr
    cases hr; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd0; rw [← hd0]; exact hdin
  · refine agree_of_words (P := fun a => vsaFoot C.H a ∧ ¬ (p + (psz + sz) ≤ a ∧ a < p + (psz + sz) + 16))
      [p + 8] (fun w' hw' => ?_) (fun a ha hout => ?_) w0 ⟨hw0, hr0⟩
    · simp only [List.mem_singleton] at hw'; subst hw'
      refine ⟨psz + sz + 1, ?_, ?_⟩
      · rw [rd_miss (by omega), read64_store_hit, h3]
      · rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
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
  · exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (B.pres a ha))))
  · refine frame_store (fun a h1 h2 => .inl (hPf a (by omega) (by omega)))
      (frame_store (fun a h1 h2 => .inl (hPf a (by omega) (by omega)))
        (frame_store (fun a h1 h2 => .inl (by
          have := hppf (a - predP) (by omega) (by omega); rwa [show predP + (a - predP) = a by omega] at this))
          (frame_store (fun a h1 h2 => .inl (by
            have := hspf (a - succP) (by omega) (by omega); rwa [show succP + (a - succP) = a by omega] at this))
            B.frameM)))

end VsaIris.VsaHeap