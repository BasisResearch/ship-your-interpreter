import VsaIris.Interp.EnvDefineSpans
import VsaIris.Interp.EnvDefineCalls
import VsaIris.Interp.DefineCost
import VsaIris.Stack
import VsaIris.Interp.ProofEnvSet

/-!
# `env_define`'s arms, at the Iris level

The constants of one call (`DefCall`), what its entry guarantees
(`DefCall.OK`), and the additive pair of continuations it ends in (`defK`:
the return, or the out-of-memory abort). The two sinks every path reaches:
`def_ret` (the epilogue, then the return) and `def_oom` (the out-of-memory
arm `0x80002bd0`, parked for the abort).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- The constants of one `env_define` call: entry `sp`, return address, the
name and value pointers, the name and value, the callee-saved words, and the
value slot's bytes at the entry. -/
structure DefCall where
  s : BitVec 64
  r : BitVec 64
  pn : BitVec 64
  vp : BitVec 64
  x : String
  v : Value
  saved : List (Nat × BitVec 64)
  so : Nat → BitVec 8

/-- What the entry guarantees about a call's constants. -/
structure DefCall.OK (C : DefCall) : Prop where
  sp : EnvSp C.s envDefineNeed
  slot : SlotWin C.vp.toNat
  ra : C.r.toNat % 4 = 0
  saved : C.saved.map Prod.fst = defineSaved
  sep : C.vp.toNat + 24 ≤ C.s.toNat - envDefineNeed ∨ C.s.toNat ≤ C.vp.toNat

theorem DefCall.OK.s64 {C : DefCall} (h : C.OK) : htifLo + 16 + 64 ≤ C.s.toNat := by
  have := h.sp.lo; unfold envDefineNeed at this; omega

theorem DefCall.OK.sepStk {C : DefCall} (h : C.OK) :
    C.vp.toNat + 24 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ C.vp.toNat := by
  have := h.sep; unfold envDefineNeed at this; omega

/-- The state inside frame `G` (image `img`, `n` bindings) between spans:
`s2` the name, `s5` the value pointer, `s4` the frame, `s3` the count, `s6`
the names array. -/
structure DefFrame (C : DefCall) (G : FrameGeom) (n : Nat) (img : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  stack : DefStack C.s.toNat C.r (pairVal C.saved) R Mt
  name : R 18 = C.pn
  vp : R 21 = C.vp
  env : (R 20).toNat = G.e
  cnt : R 19 = BitVec.ofNat 64 n
  arr : R 22 = BitVec.ofNat 64 G.pn
  lay : FrameLayout (imgM Mt) G n
  img : ∀ a, frameS G a → imgM Mt a = img a
  sepOut : ∀ a, frameS G a → a < C.vp.toNat ∨ C.vp.toNat + 24 ≤ a
  sepStk : ∀ a, frameS G a → a < C.s.toNat - 64 ∨ C.s.toNat ≤ a
  slot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a

/-- The frame state reads only `sp` and `s2-s6`. -/
theorem DefFrame.regs {C : DefCall} {G : FrameGeom} {n : Nat} {img : Nat → BitVec 8}
    {R R' : Nat → BitVec 64} {Mt : Mem} (h : DefFrame C G n img R Mt) (hs : 64 ≤ C.s.toNat)
    (hk : ∀ k, k = 2 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R' k = R k) :
    DefFrame C G n img R' Mt :=
  { h with
    stack := h.stack.congr (hk 2 (by omega)) (fun _ _ _ => rfl) hs
    name := (hk 18 (by omega)).trans h.name
    vp := (hk 21 (by omega)).trans h.vp
    env := by rw [hk 20 (by omega)]; exact h.env
    cnt := (hk 19 (by omega)).trans h.cnt
    arr := (hk 22 (by omega)).trans h.arr }

/-- `env_define`'s name loop (`0x80002ab0`): the name in `s2`, the count in `s3`. -/
def defLoop (live : Nat → Prop) (hl : ∀ p ∈ envText, live p.1) : ScanLoop live where
  scan := 0x80002ab0#64
  jal := 0x80002ab8
  jcode := [0xef#8, 0x40#8, 0x80#8, 0x3e#8]
  hit := 0x80002ac0#64
  tail := 0x80002b14#64
  nameR := 18
  cntR := 19
  cntOK := by decide
  jexec := jalx_80002ab8 live fun p hp => hl _ (env_code_80002ab8 p hp)
  jtext := env_code_80002ab8
  jal4 := by decide
  sLoad := def_load hl
  sCmp := def_cmp hl

/-- `DefFrame` is the name loop's invariant. -/
theorem defFrame_scanInv {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) (C : DefCall)
    {G : FrameGeom} {n : Nat} {img : Nat → BitVec 8} (hs : 64 ≤ C.s.toNat) :
    ScanInv (defLoop live hl) G n img C.pn (DefFrame C G n img) where
  lay h := h.lay
  img h := h.img
  name h := h.name
  regs h hk := h.regs hs fun k hk' => by
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hk _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A frame with room for one more binding (`n < cap`, and `cap` already the
canonical cap of `n + 1`): `FrameLayout` before the append's count bump. -/
structure AppLayout (img : Nat → BitVec 8) (G : FrameGeom) (n : Nat) : Prop where
  e_ne : G.e ≠ 0
  sblk : G.sblk.1 ≤ G.e ∧ G.e + 32 ≤ G.sblk.1 + G.sblk.2
  count : imgLE img G.e 4 = n
  cap : imgLE img (G.e + 4) 4 = G.cap
  names : imgLE img (G.e + 8) 8 = G.pn
  vals : imgLE img (G.e + 16) 8 = G.pv
  parent : imgLE img (G.e + 24) 8 = G.par
  room : n < G.cap
  arrays : G.nblk = (G.pn, 8 * G.cap) ∧ G.vblk = (G.pv, 24 * G.cap)
  disjoint : G.blocks.Pairwise ExtDisj
  win : ∀ b ∈ G.blocks, BlockWin b
  e_align : G.e % 8 = 0
  cap_next : G.cap = capFor (n + 1)

/-- A full-cap-free frame is ready for the append as it is. -/
theorem FrameLayout.appLayout {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) (hne : G.cap ≠ n) : AppLayout img G n := by
  have hle := h.count_le
  have hpos : 0 < G.cap := by omega
  rcases growthCost_eq n with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
  · exact absurd (h.cap_canon.trans h1) hne
  · exact { h with
      room := by omega
      arrays := h.arrays hpos
      cap_next := h.cap_canon.trans h2.symm }

/-- **After the append's count bump** the layout is a frame's again. -/
theorem AppLayout.bump {img img' : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) (hcnt : imgLE img' G.e 4 = n + 1)
    (hag : ∀ a, G.e + 4 ≤ a → a < G.e + 32 → img' a = img a) : FrameLayout img' G (n + 1) := by
  have e : ∀ o w, 4 ≤ o → o + w ≤ 32 → imgLE img' (G.e + o) w = imgLE img (G.e + o) w :=
    fun o w h4 how => imgLE_congr fun k hk => hag _ (by omega) (by omega)
  have hpos : 0 < G.cap := by have := h.room; omega
  exact { h with
    count := hcnt
    cap := by rw [e 4 4 (by omega) (by omega)]; exact h.cap
    names := by rw [e 8 8 (by omega) (by omega)]; exact h.names
    vals := by rw [e 16 8 (by omega) (by omega)]; exact h.vals
    parent := by rw [e 24 8 (by omega) (by omega)]; exact h.parent
    count_le := h.room
    empty := fun h0 => absurd h0 (by omega)
    arrays := fun _ => h.arrays
    cap_canon := h.cap_next }

/-- Two disjoint nonempty extents are apart. -/
theorem extDisj_apart {b b' : Nat × Nat} (h : ExtDisj b b') (h1 : 0 < b.2) (h2 : 0 < b'.2) :
    b.1 + b.2 ≤ b'.1 ∨ b'.1 + b'.2 ≤ b.1 :=
  interval_apart h1 h2 fun c hc1 hc2 => by
    by_cases hb : InExt b c
    · exact absurd ⟨hc1, hc2⟩ (h c hb)
    · unfold InExt at hb; omega

/-- A C string's bytes moved to `p'`. -/
theorem CStrImg.shift {img : Nat → BitVec 8} {p p' : Nat} {x : String} (h : CStrImg img p x) :
    CStrImg (fun a => img (a - p' + p)) p' x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [show p' + i - p' + p = p + i by omega]; exact h1 i hi
  · simp only [show p' + x.toList.length - p' + p = p + x.toList.length by omega]; exact h2

theorem AppLayout.envWin {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) : EnvWin G.e := by
  have hw := h.win G.sblk (by simp [FrameGeom.blocks])
  have hsb := h.sblk
  have := hw.lo; have := hw.hi; have := hw.htif
  exact ⟨by omega, by omega, by omega, h.e_align⟩

theorem AppLayout.blocks_eq {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) : G.blocks = [G.sblk, G.nblk, G.vblk] := by
  have := h.room
  simp [FrameGeom.blocks, show G.cap ≠ 0 by omega]

theorem AppLayout.nwin {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) : BlockWin G.nblk :=
  h.win _ (by rw [h.blocks_eq]; simp)

theorem AppLayout.vwin {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) : BlockWin G.vblk :=
  h.win _ (by rw [h.blocks_eq]; simp)

/-- The three blocks of a frame with arrays are pairwise apart. -/
theorem AppLayout.apart {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : AppLayout img G n) :
    ExtDisj G.sblk G.nblk ∧ ExtDisj G.sblk G.vblk ∧ ExtDisj G.nblk G.vblk := by
  have hd := h.disjoint
  rw [h.blocks_eq] at hd
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hd
  exact ⟨hd.1.1, hd.1.2, hd.2.1⟩

/-- An image read at a shifted place. -/
theorem imgLE_shift {img img' : Nat → BitVec 8} {a a' : Nat} :
    ∀ {n : Nat}, (∀ i, i < n → img' (a' + i) = img (a + i)) → imgLE img' a' n = imgLE img a n
  | 0, _ => rfl
  | n + 1, h => by
    unfold imgLE
    rw [show img' a' = img a by simpa using h 0 (by omega),
      imgLE_shift (a := a + 1) (a' := a' + 1) (n := n) (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show a' + (i + 1) = a' + 1 + i by omega, show a + (i + 1) = a + 1 + i by omega]
          at this)]

theorem imgW_shift {img img' : Nat → BitVec 8} {a a' : Nat}
    (h : ∀ i, i < 8 → img' (a' + i) = img (a + i)) : imgW img' a' = imgW img a := by
  unfold imgW; rw [imgLE_shift h]

section Bindings

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
/-- A string's image, its window, and its read-only bytes. -/
theorem strAt_parts {p : Nat} {x : String} :
    strAt (GF := GF) p x ⊢ ∃ img, ⌜CStrImg img p x ∧ StrWin p x.toList.length⌝ ∗
      roImg (InExt (p, x.toList.length + 1)) img := by
  iintro H; unfold strAt; iexact H

/-- A value's meaning at a shifted place. -/
theorem valImg_shift (N : NativeAddrs) {img img' : Nat → BitVec 8} {a a' : Nat} (v : Value)
    (h : ∀ o, o < 24 → img' (a' + o) = img (a + o)) :
    valImg (GF := GF) N img' a' v = valImg N img a v := by
  have w : ∀ o, o + 8 ≤ 24 → imgW img' (a' + o) = imgW img (a + o) := fun o ho =>
    imgW_shift fun i hi => by
      have := h (o + i) (by omega)
      rwa [show a' + (o + i) = a' + o + i by omega, show a + (o + i) = a + o + i by omega] at this
  unfold valImg
  rw [show a' = a' + 0 from rfl, show a = a + 0 from rfl, w 0 (by omega), w 8 (by omega),
    w 16 (by omega)]

/-- **The bindings at relocated arrays**: every name word and value's bytes
agree. -/
theorem bindings_move (N : NativeAddrs) {img img' : Nat → BitVec 8} {pn pv pn' pv' : Nat}
    {vars : List (String × Value)}
    (hn : ∀ k, k < vars.length → ∀ o, o < 8 → img' (pn' + 8 * k + o) = img (pn + 8 * k + o))
    (hv : ∀ k, k < vars.length → ∀ o, o < 24 → img' (pv' + 24 * k + o) = img (pv + 24 * k + o)) :
    bindings (GF := GF) N img pn pv vars ⊢ bindings N img' pn' pv' vars := by
  iintro #Hb
  unfold bindings
  iapply sepL_of_all
  imodintro
  iintro %q %hq
  obtain ⟨p, k⟩ := q
  rw [List.mem_zipIdx_iff_getElem?] at hq
  have hk : k < vars.length := by
    have := List.getElem?_eq_some_iff.1 hq; simpa using this.1
  have hp : p = vars[k] := by rw [List.getElem?_eq_getElem hk] at hq; exact (Option.some.inj hq).symm
  subst hp
  ihave ⟨#Hname, #Hval⟩ := sepL_zipIdx_get _ vars hk $$ Hb
  dsimp only
  rw [imgLE_shift (hn k hk), valImg_shift N _ (hv k hk)]
  iframe Hname Hval

/-- **One more binding** at the end: its name word and value. -/
theorem bindings_snoc (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat)
    (vars : List (String × Value)) (x : String) (v : Value) :
    bindings (GF := GF) N img pn pv vars ∗
        strAt (imgLE img (pn + 8 * vars.length) 8) x ∗ valImg N img (pv + 24 * vars.length) v ⊢
      bindings N img pn pv (vars ++ [(x, v)]) := by
  iintro ⟨#Hb, #Hx, #Hv⟩
  unfold bindings
  rw [List.zipIdx_append]
  iapply (sepL_append _ _ _).2
  iframe Hb
  simp only [List.zipIdx_singleton, Nat.zero_add, sepL_cons, sepL_nil]
  iframe Hx Hv

end Bindings

section Sinks

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- The registers the abort hands over clobbered: all but `sp`. -/
abbrev oomRegs : List Nat := VsaIris.ra :: 10 :: retClob ++ defineSaved

/-- **The pair of continuations** an `env_define` path ends in, with the
final regime `ρ` and store `st'`. -/
def defK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (C : DefCall) (ρ : Regime) (st' : Store) : IProp GF :=
  iprop((VsaIris.PC ↦ᵣ C.r -∗ VsaIris.ra ↦ᵣ C.r -∗
      (VsaIris.sp ↦ᵣ C.s ∗ clobbered (10 :: retClob) ∗ savedOwn C.saved ∗
        stackScratch C.s envDefineNeed ∗ valAt N C.vp.toNat C.v ∗ heapStore N ρ st') -∗ Wp.W Φ) ∧
    ((⌜ρ = .uncounted⌝ ∗ oomAt 0x80002bd0#64 (C.s - 64#64) C.s envDefineNeed oomRegs ∗
      valAt N C.vp.toNat C.v) -∗ Wp.W Φ))

omit I in
theorem toNat_s64 {C : DefCall} (hC : C.OK) : (C.s - 64#64).toNat = C.s.toNat - 64 :=
  toNat_sub_frame (by have := hC.s64; simp; omega)

omit I in
/-- The entry stack as the 64-byte frame and the callees' scratch below it. -/
theorem def_stack_split {C : DefCall} (hC : C.OK) :
    stackScratch (GF := GF) C.s envDefineNeed ⊢
      stackScratch (C.s - 64#64) allocHeadroom ∗ blockOwn (C.s.toNat - 64) 64 := by
  iintro H
  ihave ⟨H1, H2⟩ := stackScratch_frame (s := C.s) (f := 64#64) (n := envDefineNeed)
    (by have := hC.sp.lo; unfold envDefineNeed allocHeadroom at *; omega)
    (by unfold envDefineNeed allocHeadroom; decide) $$ H
  rw [show envDefineNeed - (64#64 : BitVec 64).toNat = allocHeadroom from rfl, toNat_s64 hC,
    show (64#64 : BitVec 64).toNat = 64 from rfl]
  iframe H1 H2

omit I in
/-- The inverse of `def_stack_split`. -/
theorem def_stack_join {C : DefCall} (hC : C.OK) :
    stackScratch (GF := GF) (C.s - 64#64) allocHeadroom ∗ blockOwn (C.s.toNat - 64) 64 ⊢
      stackScratch C.s envDefineNeed := by
  iintro ⟨H1, H2⟩
  iapply stackScratch_unframe (s := C.s) (f := 64#64) (n := envDefineNeed)
    (by have := hC.sp.lo; unfold envDefineNeed allocHeadroom at *; omega)
    (by unfold envDefineNeed allocHeadroom; decide)
  rw [show envDefineNeed - (64#64 : BitVec 64).toNat = allocHeadroom from rfl, toNat_s64 hC,
    show (64#64 : BitVec 64).toNat = 64 from rfl]
  iframe H1 H2

/-- The slot's bytes and the entry meaning give back `valAt`. -/
theorem def_valAt (N : NativeAddrs) {C : DefCall} {Mt : Mem}
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    ownSet (GF := GF) (InExt (C.vp.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      valImg N C.so C.vp.toNat C.v ⊢ valAt N C.vp.toNat C.v := by
  iintro ⟨Hout, #Hv⟩
  unfold valAt
  iexists (imgM Mt)
  iframe Hout
  rw [valImg_agree N C.v fun o ho => hslot _ (by omega) (by omega)]
  iexact Hv

/-- **The return**: the epilogue `0x80002aec` from the frame, then the return
continuation. -/
theorem def_ret (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1) (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime}
    {st' : Store} {R : Nat → BitVec 64} {Mt : Mem}
    (hstk : DefStack C.s.toNat C.r (pairVal C.saved) R Mt)
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ valImg N C.so C.vp.toNat C.v ∗
      VsaIris.PC ↦ᵣ 0x80002aec#64 ∗ regsOf gprs R ∗
      ownSet (baseS C.s.toNat C.vp.toNat) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗ heapStore N ρ st' ∗ defK Wp Φ N C ρ st'
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hgp, #Hv, Hpc, HR, HB, Hscr, Hhs, HK⟩
  have hs := hC.s64
  iapply wp_span Wp (def_epi hl (S := baseS C.s.toNat C.vp.toNat) hs hC.sp.hi hC.ra hstk
    (fun a h1 h2 => .inl ⟨h1, h2⟩))
  iframe Ht Hgp Hpc HR HB
  iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, hret⟩ Hpc HR HB
  have hperm : (([(VsaIris.ra, C.r), (VsaIris.sp, C.s)] ++ C.saved).map Prod.fst ++
      (10 :: retClob)).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hC.saved]; decide
  have hfix : ∀ p ∈ [(VsaIris.ra, C.r), (VsaIris.sp, C.s)] ++ C.saved, R1 p.1 = p.2 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hret.ra
      · show R1 2 = C.s
        rw [hret.sp]; exact BitVec.eq_of_toNat_eq (by simp)
    · rw [hret.saved p.1 (by rw [← hC.saved]; exact List.mem_map_of_mem hp),
        pairVal_of_mem C.saved (by rw [hC.saved]; decide) p hp]
  ihave ⟨Hfix, Hcl⟩ := regsOf_exit gprs _ (10 :: retClob) hperm R1 hfix $$ HR
  unfold savedOwn
  ihave ⟨H2, Hsv⟩ := (sepL_append _ _ _).1 $$ Hfix
  simp only [sepL_cons, sepL_nil]
  icases H2 with ⟨Hra, Hsp, -⟩
  ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt1) (by omega) hC.sepStk $$ HB
  unfold defK
  ihave Kret := and_elim_l $$ HK
  iapply Kret $$ Hpc Hra
  unfold savedOwn
  iframe Hsp Hcl Hsv Hhs
  isplitl [Hscr Hstk]
  · iapply def_stack_join hC; iframe Hscr Hstk
  iapply def_valAt N hslot; iframe Hout Hv

/-- **The out-of-memory arm** `0x80002bd0`: parked for the abort, uncounted. -/
theorem def_oom (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime} {st' : Store}
    {R : Nat → BitVec 64} {Mt : Mem} {H : List (Nat × Nat)} (hρ : ρ = .uncounted)
    (h2 : (R 2).toNat = C.s.toNat - 64)
    (hslot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a) :
    valImg N C.so C.vp.toNat C.v ∗ VsaIris.PC ↦ᵣ 0x80002bd0#64 ∗ regsOf gprs R ∗
      ownSet (baseS C.s.toNat C.vp.toNat) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB .uncounted H ∗ defK Wp Φ N C ρ st'
    ⊢ Wp.W Φ := by
  iintro ⟨#Hv, Hpc, HR, HB, Hscr, Hh, HK⟩
  have hs := hC.s64
  have hperm : ([(VsaIris.sp, C.s - 64#64)].map Prod.fst ++ oomRegs).Perm gprs := by
    simp only [List.map_cons, List.map_nil]; decide
  ihave ⟨Hsp, Hcl⟩ := regsOf_exit gprs _ _ hperm R (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    show R 2 = C.s - 64#64
    apply BitVec.eq_of_toNat_eq; rw [h2, toNat_s64 hC]) $$ HR
  unfold savedOwn
  simp only [sepL_cons, sepL_nil]
  icases Hsp with ⟨Hsp, -⟩
  ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt) (by omega) hC.sepStk $$ HB
  unfold defK
  ihave Kab := and_elim_r $$ HK
  iapply Kab
  isplitl []
  · ipureintro; exact hρ
  isplitl [Hpc Hsp Hcl Hscr Hstk Hh]
  · unfold oomAt
    iframe Hpc Hsp Hcl
    isplitl [Hscr Hstk]
    · iapply def_stack_join hC; iframe Hscr Hstk
    iexists H; iexact Hh
  iapply def_valAt N hslot; iframe Hout Hv

/-- A frame's bindings are unique (`StoreInvariant`). -/
theorem frame_unique {st : Store} {fa : Addr} {f : Frame} (hinv : Vsa.Sim.StoreInvariant st)
    (hf : st.frames[fa]? = some f) : FrameNamesUnique f.vars := by
  have hfalt : fa < st.frames.size := by
    rcases Nat.lt_or_ge fa st.frames.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hf
  have hfa : st.frames[fa] = f := by simpa [Array.getElem?_eq_getElem hfalt] using hf
  have := hinv.unique fa hfalt; rwa [hfa] at this

/-- `Store.define` at a bound name replaces its first (only) binding. -/
theorem define_hit_frames {st : Store} {fa : Addr} {f : Frame} {x : String} {v v0 : Value}
    {j : Nat} (hinv : Vsa.Sim.StoreInvariant st) (hf : st.frames[fa]? = some f)
    (hj : f.vars[j]? = some (x, v0)) :
    (st.define fa x v).frames.toList = st.frames.toList.set fa { f with vars := f.vars.set j (x, v) } := by
  have hany : f.vars.any (·.1 == x) := by
    rw [List.any_eq_true]
    exact ⟨(x, v0), List.mem_of_getElem? hj, by simp⟩
  rw [define_frames_toList hf]
  unfold defineFrame
  rw [if_pos hany, map_replace_eq_set hj (frame_unique hinv hf)]

theorem Regime.plus_zero (ρ : Regime) : ρ.plus 0 = ρ := by cases ρ <;> rfl

/-- **The hit** `0x80002ac0`: write `vals[j] := *v`, close the frame at
`st.define`, return. -/
theorem def_hit (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1) (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime}
    {st : Store} {fa : Addr} {f : Frame} {G : FrameGeom} {img : Nat → BitVec 8} {j : Nat}
    {v0 : Value} {R : Nat → BitVec 64} {Mt : Mem} {H B₁ B₂ : List (Nat × Nat)}
    (hF : DefFrame C G f.vars.length img R Mt) (h8 : R 8 = BitVec.ofNat 64 j)
    (hj : f.vars[j]? = some (C.x, v0)) (hf : st.frames[fa]? = some f)
    (hinv : Vsa.Sim.StoreInvariant st) (hdisj : ∀ a, frameS G a → ¬ baseS C.s.toNat C.vp.toNat a)
    (hBH : ∀ b ∈ B₁ ++ G.blocks ++ B₂, b ∈ H) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ valImg N C.so C.vp.toNat C.v ∗
      VsaIris.PC ↦ᵣ 0x80002ac0#64 ∗ regsOf gprs R ∗
      ownSet (getS C.s.toNat C.vp.toNat G) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB ρ H ∗
      bindings N img G.pn G.pv f.vars ∗ parentAt f.parent G.par ∗ frameAt fa G.e ∗
      frameCloser N st fa B₁ B₂ ∗ defK Wp Φ N C ρ (st.define fa C.x C.v)
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hgp, #Hv, Hpc, HR, HS, Hscr, Hh, #Hb, #Hp, #HGe, Hclose, HK⟩
  have hlt : j < f.vars.length := by
    rcases Nat.lt_or_ge j f.vars.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hj
  have hvj : f.vars[j] = (C.x, v0) := by simpa [List.getElem?_eq_getElem hlt] using hj
  obtain ⟨hcap, -, -, hv1, hv2, -, hvw⟩ := hF.lay.slot hlt
  have hs64 : 64 ≤ C.s.toNat := by have := hC.s64; unfold htifLo at this; omega
  have hstkv : G.pv + 24 * j + 24 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ G.pv + 24 * j := by
    have := interval_apart (a := G.pv + 24 * j) (n := 24) (b := C.s.toNat - 64) (m := 64)
      (by omega) (by omega) fun c h1 h2 => by
        rcases Nat.lt_or_ge c (G.pv + 24 * j) with h | h
        · exact .inl h
        · rcases Nat.lt_or_ge c (G.pv + 24 * j + 24) with h' | h'
          · have := hF.sepStk c (by
              unfold frameS InExt; exact .inr ⟨hcap, .inr ⟨by omega, by omega⟩⟩)
            omega
          · exact .inr h'
    omega
  have hwo : 0x80000000 ≤ C.vp.toNat ∧ C.vp.toNat + 24 ≤ 0x100000000 ∧
      htifLo + 16 ≤ C.vp.toNat ∧ C.vp.toNat % 8 = 0 :=
    ⟨hC.slot.lo, hC.slot.hi, hC.slot.htif, hC.slot.align⟩
  have h21 : (R 21).toNat = C.vp.toNat := by rw [hF.vp]
  iapply wp_span Wp (def_write hl (s := C.s.toNat) (G := G) hF.lay hlt h8 hF.env h21 hwo)
  iframe Ht Hgp Hpc HR HS
  iintro %pc1 %R1 %Mt1 %⟨rfl, hco, hk1⟩ Hpc HR HS
  have hslotw := copyOut_slot (fo := C.so) hF.lay hlt hF.sepOut hF.slot hco
  ihave ⟨HB, Hst⟩ := frame_write_close N (st := st) (st' := st.define fa C.x C.v) (fa := fa)
    (f := f) (img := img) (B₁ := B₁) (B₂ := B₂) (x := C.x) (v := C.v) hdisj hF.lay hF.img
    hF.sepOut hF.slot hco hlt (by rw [hvj])
    ⟨rfl, define_hit_frames hinv hf hj, hinv.define st fa C.x C.v⟩ $$ [HS Hclose]
  · iframe HS Hb Hp HGe Hclose Hv
  have hstk1 : DefStack C.s.toNat C.r (pairVal C.saved) R1 Mt1 :=
    hF.stack.congr (hk1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a h1 h2 => hco.frame a (by
        rcases hstkv with h | h
        · right; omega
        · left; omega)) (by have := hC.s64; omega)
  iapply def_ret Wp hl N hC hstk1 (fun a h1 h2 => by
    have := hslotw (a - C.vp.toNat) (by omega)
    rwa [show C.vp.toNat + (a - C.vp.toNat) = a by omega] at this)
  iframe Ht Hgp Hv Hpc HR HB Hscr HK
  unfold heapStore
  iexists H, (B₁ ++ G.blocks ++ B₂)
  iframe Hh Hst
  ipureintro; exact hBH

/-- The callees' `sp` discipline at `env_define`'s frame. -/
theorem def_spOK {C : DefCall} (hC : C.OK) {R : Nat → BitVec 64}
    (h2 : (R 2).toNat = C.s.toNat - 64) : SpOKA (R 2) := by
  have := hC.sp.lo; have := hC.sp.hi; have := hC.sp.align
  unfold envDefineNeed allocHeadroom htifLo at *
  exact ⟨by rw [h2]; unfold Vsa.Sim.tohostAddr allocHeadroom; omega, by rw [h2]; omega,
    by rw [h2]; omega⟩

theorem def_sp {C : DefCall} (hC : C.OK) {R : Nat → BitVec 64}
    (h2 : (R 2).toNat = C.s.toNat - 64) : R 2 = C.s - 64#64 :=
  BitVec.eq_of_toNat_eq (by rw [h2, toNat_s64 hC])

/-- The state at the append (`0x80002b1c`): geometry `G'` with room for one
more binding, whose first `n` slots hold frame `G`'s (image `img`). -/
structure AppReady (C : DefCall) (G G' : FrameGeom) (n : Nat) (img : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  stack : DefStack C.s.toNat C.r (pairVal C.saved) R Mt
  name : R 18 = C.pn
  vp : R 21 = C.vp
  env : (R 20).toNat = G'.e
  lay : AppLayout (imgM Mt) G' n
  e : G'.e = G.e
  par : G'.par = G.par
  oldNames : ∀ k, k < n → ∀ o, o < 8 → imgM Mt (G'.pn + 8 * k + o) = img (G.pn + 8 * k + o)
  oldVals : ∀ k, k < n → ∀ o, o < 24 → imgM Mt (G'.pv + 24 * k + o) = img (G.pv + 24 * k + o)
  sepOut : ∀ a, frameS G' a → a < C.vp.toNat ∨ C.vp.toNat + 24 ≤ a
  sepStk : ∀ a, frameS G' a → a < C.s.toNat - 64 ∨ C.s.toNat ≤ a
  slot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a

/-- **The append** `0x80002b1c`: copy the name (`strlen`, `malloc`,
`memcpy`), store the new binding, bump the count, return; or abort when
`malloc` returns NULL. -/
theorem def_append (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1) (A : AllocSpecs live) (N : NativeAddrs) {C : DefCall}
    (hC : C.OK) {ρ : Regime} {st : Store} {fa : Addr} {f : Frame} {G G' : FrameGeom}
    {img : Nat → BitVec 8} {R : Nat → BitVec 64} {Mt : Mem} {H B₁ B₂ : List (Nat × Nat)}
    (hR : AppReady C G G' f.vars.length img R Mt) (hf : st.frames[fa]? = some f)
    (hinv : Vsa.Sim.StoreInvariant st) (hmiss : ¬ f.vars.any (·.1 == C.x))
    (hdisj : ∀ a, frameS G' a → ¬ baseS C.s.toNat C.vp.toNat a)
    (hBH : ∀ b ∈ B₁ ++ G'.blocks ++ B₂, b ∈ H) :
    textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ strlenSpec Wp ∗ memcpySpec Wp ∗
      strAt C.pn.toNat C.x ∗ valImg N C.so C.vp.toNat C.v ∗
      VsaIris.PC ↦ᵣ 0x80002b1c#64 ∗ regsOf gprs R ∗
      ownSet (getS C.s.toNat C.vp.toNat G') (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus (nameCopyCost C.x)) H ∗
      bindings N img G.pn G.pv f.vars ∗ parentAt f.parent G.par ∗ frameAt fa G.e ∗
      frameCloser N st fa B₁ B₂ ∗ defK Wp Φ N C ρ (st.define fa C.x C.v)
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hat, #Hgp, #Hsl, #Hmc, #Hx, #Hv, Hpc, HR, HS, Hscr, Hh, #Hb, #Hp, #HGe, Hclose, HK⟩
  have hs64 : 64 ≤ C.s.toNat := by have := hC.s64; unfold htifLo at this; omega
  have h2 : (R 2).toNat = C.s.toNat - 64 := hR.stack.sp
  ihave ⟨%ximg, %⟨hcs, hsw⟩, #Hro⟩ := strAt_parts $$ Hx
  have hlenx : C.x.length = C.x.toList.length := String.length_toList.symm
  have hxw := hsw.hi
  -- `a0 := name`, `strlen`
  iapply wp_span Wp (def_app1 hl (S := getS C.s.toNat C.vp.toNat G') (R := R) (Mt := Mt))
  iframe Ht Hgp Hpc HR HS
  iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, h10, hk1⟩ Hpc HR HS
  iapply wp_call_strlen Wp (i := 0x80002b20)
    (jalx_80002b20 live fun p hp => hl _ (env_code_80002b20 p hp)) (by decide) (R := R1) (x := C.x)
  isplitl []
  · iapply instrAt_of_text env_code_80002b20 $$ Ht
  iframe Hsl Hpc HR
  isplitl []
  · rw [h10, hR.name]; iexact Hx
  iintro %R2 %⟨hlen, -, hk2⟩ Hpc HR
  rw [show BitVec.ofNat 64 (0x80002b20 + 4) = 0x80002b24#64 from rfl]
  -- `s0 := a0 := len + 1`, `malloc`
  iapply wp_span Wp (def_app2 hl (S := getS C.s.toNat C.vp.toNat G') (R := R2) (Mt := Mt1))
  iframe Ht Hgp Hpc HR HS
  iintro %pc3 %R3 %Mt3 %⟨rfl, rfl, h8, h10', hk3⟩ Hpc HR HS
  have e2 : ∀ k, k = 2 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R3 k = R k :=
    fun k hk => by
      have ha : k ≠ 8 ∧ k ≠ 10 ∧ k ∉ VsaIris.ra :: strKs := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hk3 k ha.1 ha.2.1, hk2 k ha.2.2, hk1 k ha.2.1]
  have h32 : (R3 2).toNat = C.s.toNat - 64 := by rw [e2 2 (by omega)]; exact h2
  have hn1 : (R3 10).toNat = C.x.length + 1 := by
    have : C.x.length < 2 ^ 32 := by omega
    rw [h10', hlen, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [← def_sp hC h32]
  iapply wp_call_malloc A Wp (i := 0x80002b2c) (R := R3)
    (jalx_80002b2c live fun p hp => hl _ (env_code_80002b2c p hp)) (by decide) ρ H
    (nameCopyCost C.x) (by rw [hn1]; exact ⟨by omega, Nat.le_refl _⟩) (def_spOK hC h32)
  isplitl []
  · iapply instrAt_of_text env_code_80002b2c $$ Ht
  iframe Hat Hgp Hpc HR Hscr Hh
  iintro %R4 %p %⟨h10p, -, hk4⟩ Hpc HR Hscr Hres
  rw [show BitVec.ofNat 64 (0x80002b2c + 4) = 0x80002b30#64 from rfl, hn1]
  have e4 : ∀ k, k = 2 ∨ k = 8 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 →
      R4 k = R3 k := fun k hk => hk4 k (by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  -- `s1 := a0`; NULL aborts
  iapply wp_span Wp (def_app3 hl (S := getS C.s.toNat C.vp.toNat G') (R := R4) (Mt := Mt3))
  iframe Ht Hgp Hpc HR HS
  iintro %pc5 %R5 %Mt5 %⟨rfl, h9, hcase⟩ Hpc HR HS
  unfold mallocRes
  rcases hcase with ⟨hp0, rfl, hk5⟩ | ⟨hp0, rfl, h12, h11, hk5⟩
  · -- NULL: out of memory
    icases Hres with (⟨%⟨-, hρ⟩, Hh⟩ | ⟨%⟨hfr, -⟩, -, -⟩)
    · subst hρ
      ihave ⟨HB, -⟩ := get_split (img := imgM Mt5) hdisj (fun _ _ => rfl) $$ HS
      iapply def_oom Wp N hC (st' := st.define fa C.x C.v) (H := H) (R := R5) (Mt := Mt5) rfl
        (by rw [hk5 2 (by decide), e4 2 (by omega)]; exact h32) hR.slot
      rw [def_sp hC h32]
      iframe Hv Hpc HR HB Hscr Hh HK
    · exfalso; exact hfr.nonzero (by rw [← h10p, hp0]; rfl)
  icases Hres with (⟨%⟨hp0', -⟩, -⟩ | ⟨%⟨hfr, hal⟩, Hh, Hblk⟩)
  · exfalso; exact hp0 (h10p.trans hp0')
  -- `memcpy` the name into the fresh block
  obtain ⟨-, hplo, hphi, -⟩ := hfr.destruct
  have hplo' : Vsa.Sim.DlHeap.heapStart ≤ p.toNat := hplo
  have hphi' : p.toNat + (C.x.length + 1) ≤ Vsa.Sim.DlHeap.heapEnd := hphi
  unfold Vsa.Sim.DlHeap.heapStart at hplo'; unfold Vsa.Sim.DlHeap.heapEnd at hphi'
  have e5 : ∀ k, k = 2 ∨ k = 8 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R5 k = R4 k :=
    fun k hk => hk5 k (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hp10 : (R5 10).toNat = p.toNat := by
    rw [hk5 10 (by decide) (by decide) (by decide), h10p]
  have hpn11 : R5 11 = C.pn := by rw [h11, e4 18 (by omega), e2 18 (by omega), hR.name]
  have h12' : R5 12 = BitVec.ofNat 64 (C.x.length + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [h12, e4 8 (by omega), h8, ← hn1, h10']; simp
  rw [← hlenx] at hsw
  have hxw' := hsw.hi
  have hxlo := hsw.lo
  have hxht := hsw.htif
  iapply wp_call_memcpy Wp (i := 0x80002b40)
    (jalx_80002b40 live fun p hp => hl _ (env_code_80002b40 p hp)) (by decide) (R := R5)
    (n := C.x.length + 1) (img := ximg) h12'
    ⟨by rw [hp10]; omega, by rw [hp10]; omega, by rw [hp10]; unfold htifLo; omega⟩
    ⟨by rw [hpn11]; omega, by rw [hpn11]; omega, by rw [hpn11]; unfold htifLo at hxht ⊢; omega⟩
  isplitl []
  · iapply instrAt_of_text env_code_80002b40 $$ Ht
  iframe Hmc Hpc HR
  isplitl [Hblk]
  · rw [hp10]; iexact Hblk
  isplitl []
  · rw [hpn11, hlenx]; iexact Hro
  iintro %R6 %⟨h10c, -, hk6⟩ Hpc HR Hcopy
  rw [show BitVec.ofNat 64 (0x80002b40 + 4) = 0x80002b44#64 from rfl, hp10, hpn11]
  -- the copy is the name, read-only from now on
  iapply Wp.fupd
  imod strAt_of_owned (p := p.toNat) (s := C.x) (hcs.shift (p' := p.toNat))
    ⟨by omega, by rw [← hlenx]; omega, by unfold htifLo; omega⟩
    $$ [Hcopy] with #Hnew
  · rw [← hlenx]; iexact Hcopy
  imodintro
  -- the stores: `names[n] := copy`, `vals[n] := *v`, `count := n + 1`
  have e6 : ∀ k, k = 2 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R6 k = R k := fun k hk => by
    have ha : k ∉ VsaIris.ra :: strKs := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hk6 k ha, e5 k (by omega), e4 k (by omega), e2 k (by omega)]
  have h69 : R6 9 = p := by
    rw [hk6 9 (by decide), h9, h10p]
  have hlay := hR.lay
  have hroom := hlay.room
  obtain ⟨hna, hva⟩ := hlay.arrays
  obtain ⟨dsn, dsv, dnv⟩ := hlay.apart
  have hnw := hlay.nwin
  have hvw := hlay.vwin
  rw [hna] at hnw dsn dnv
  rw [hva] at hvw dsv dnv
  have := hnw.lo; have := hnw.hi; have := hnw.htif; have := hnw.align
  have := hvw.lo; have := hvw.hi; have := hvw.htif; have := hvw.align
  simp only at *
  have hsb := hlay.sblk
  have hcap0 : 0 < G'.cap := by omega
  have dsn' := extDisj_apart dsn (by omega) (by simp only; omega)
  have dsv' := extDisj_apart dsv (by omega) (by simp only; omega)
  have dnv' := extDisj_apart dnv (by simp only; omega) (by simp only; omega)
  simp only at dsn' dsv' dnv'
  have hsl := hC.slot
  have := hsl.lo; have := hsl.hi; have := hsl.htif; have := hsl.align
  iapply wp_span Wp (def_app4 hl (S := getS C.s.toNat C.vp.toNat G') (R := R6) (Mt := Mt5)
    (n := f.vars.length) hlay.envWin (by rw [e6 20 (by omega)]; exact hR.env)
    (by rw [e6 21 (by omega), hR.vp]) hlay.count (by omega) hlay.names hlay.vals
    ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
    ⟨hsl.lo, hsl.hi, hsl.htif, hsl.align⟩ (by omega) (by omega) (by omega) (fun a ha => by
      unfold getS baseS frameS
      simp only [InExt] at ha
      rcases ha with ha | ha | ha | ha
      · right; left; unfold InExt; omega
      · right; right; refine ⟨by omega, .inl ?_⟩; rw [hna]; unfold InExt; simp only; omega
      · right; right; refine ⟨by omega, .inr ?_⟩; rw [hva]; unfold InExt; simp only; omega
      · left; right; omega))
  iframe Ht Hgp Hpc HR HS
  iintro %pc7 %R7 %Mt7 %⟨rfl, hout, hk7⟩ Hpc HR HS
  -- the frame after the append
  have hoffS : ∀ a, G'.sblk.1 ≤ a → a < G'.sblk.1 + G'.sblk.2 → ¬ InExt (G'.pn + 8 * f.vars.length, 8) a ∧
      ¬ InExt (G'.pv + 24 * f.vars.length, 24) a := fun a h1 h2 => by
    unfold InExt; constructor <;> omega
  have hlay' : FrameLayout (imgM Mt7) G' (f.vars.length + 1) :=
    hlay.bump hout.cnt fun a h1 h2 => hout.frame a (hoffS a (by omega) (by omega)).1
      (hoffS a (by omega) (by omega)).2 (by unfold InExt; omega)
  ihave ⟨HB, HF⟩ := get_split (img := imgM Mt7) hdisj (fun _ _ => rfl) $$ HS
  have hname7 : imgLE (imgM Mt7) (G'.pn + 8 * f.vars.length) 8 = p.toNat := by
    rw [← imgW_toNat, ← ldv_ld_img, hout.name, h69]
  have hnames : ∀ k, k < f.vars.length → ∀ o, o < 8 →
      imgM Mt7 (G'.pn + 8 * k + o) = img (G.pn + 8 * k + o) := fun k hk o ho => by
    rw [hout.frame _ (by unfold InExt; omega) (by unfold InExt; omega) (by unfold InExt; omega)]
    exact hR.oldNames k hk o ho
  have hvals : ∀ k, k < f.vars.length → ∀ o, o < 24 →
      imgM Mt7 (G'.pv + 24 * k + o) = img (G.pv + 24 * k + o) := fun k hk o ho => by
    rw [hout.frame _ (by unfold InExt; omega) (by unfold InExt; omega) (by unfold InExt; omega)]
    exact hR.oldVals k hk o ho
  have hslot5 := hR.slot
  have hvp5 : ∀ o, o < 24 → imgM Mt5 (C.vp.toNat + o) = C.so (C.vp.toNat + o) :=
    fun o ho => hslot5 _ (by omega) (by omega)
  have w : ∀ o, o + 8 ≤ 24 → ldv .ld Mt7 (G'.pv + 24 * f.vars.length + o) = ldv .ld Mt5 (C.vp.toNat + o) →
      imgW (imgM Mt7) (G'.pv + 24 * f.vars.length + o) = imgW C.so (C.vp.toNat + o) := fun o ho h => by
    rw [← ldv_ld_img, h, ldv_ld_img]
    exact imgW_agree fun k hk => by
      have := hvp5 (o + k) (by omega)
      rwa [show C.vp.toNat + (o + k) = C.vp.toNat + o + k by omega] at this
  have hnewv : valImg (GF := GF) N (imgM Mt7) (G'.pv + 24 * f.vars.length) C.v =
      valImg N C.so C.vp.toNat C.v := by
    unfold valImg
    rw [show G'.pv + 24 * f.vars.length = G'.pv + 24 * f.vars.length + 0 from rfl,
      w 0 (by omega) (by rw [Nat.add_zero, Nat.add_zero]; exact hout.w0), w 8 (by omega) hout.w1,
      w 16 (by omega) hout.w2, Nat.add_zero]
  ihave #Hb' := bindings_move N (img' := imgM Mt7) (pn' := G'.pn) (pv' := G'.pv) hnames hvals $$ Hb
  ihave #Hb'' := bindings_snoc N (imgM Mt7) G'.pn G'.pv f.vars C.x C.v $$ [Hb' Hnew Hv]
  · rw [hname7, hnewv]; iframe Hb' Hnew Hv
  have hdef : defineFrame f C.x C.v = { f with vars := f.vars ++ [(C.x, C.v)] } := by
    unfold defineFrame; simp only [hmiss, Bool.false_eq_true, ite_false]
  ihave Hst := Hclose $$ %(st.define fa C.x C.v) %(defineFrame f C.x C.v) %G'.blocks
    %⟨rfl, define_frames_toList hf C.x C.v, hinv.define st fa C.x C.v⟩ [HF]
  · unfold frameOwn frameBody
    iexists G'
    isplitr
    · ipureintro; rfl
    rw [hR.e]
    iframe HGe
    iexists (imgM Mt7)
    rw [hdef]
    dsimp only
    rw [hR.par, List.length_append, List.length_singleton]
    iframe HF Hb'' Hp
    ipureintro; exact hlay'
  -- the return
  have hs7 : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat → imgM Mt7 a = imgM Mt5 a := fun a h1 h2 => by
    have hn := hR.sepStk (G'.pn + 8 * f.vars.length) (by
      unfold frameS; right; refine ⟨by omega, .inl ?_⟩; rw [hna]; unfold InExt; simp only; omega)
    have hv := hR.sepStk (G'.pv + 24 * f.vars.length) (by
      unfold frameS; right; refine ⟨by omega, .inr ?_⟩; rw [hva]; unfold InExt; simp only; omega)
    have he := hR.sepStk G'.e (by unfold frameS InExt; left; omega)
    have hn' := hR.sepStk (G'.pn + 8 * f.vars.length + 7) (by
      unfold frameS; right; refine ⟨by omega, .inl ?_⟩; rw [hna]; unfold InExt; simp only; omega)
    have hv' := hR.sepStk (G'.pv + 24 * f.vars.length + 23) (by
      unfold frameS; right; refine ⟨by omega, .inr ?_⟩; rw [hva]; unfold InExt; simp only; omega)
    have he' := hR.sepStk (G'.e + 3) (by unfold frameS InExt; left; omega)
    exact hout.frame a (by unfold InExt; omega) (by unfold InExt; omega) (by unfold InExt; omega)
  have hstk7 : DefStack C.s.toNat C.r (pairVal C.saved) R7 Mt7 :=
    hR.stack.congr (by
      rw [hk7 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), e6 2 (by omega)]) (fun a h1 h2 => hs7 a h1 h2) hs64
  have hslot7 : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt7 a = C.so a := fun a h1 h2 => by
    have hn := hR.sepOut (G'.pn + 8 * f.vars.length) (by
      unfold frameS; right; refine ⟨by omega, .inl ?_⟩; rw [hna]; unfold InExt; simp only; omega)
    have hv := hR.sepOut (G'.pv + 24 * f.vars.length) (by
      unfold frameS; right; refine ⟨by omega, .inr ?_⟩; rw [hva]; unfold InExt; simp only; omega)
    have he := hR.sepOut G'.e (by unfold frameS InExt; left; omega)
    have hn' := hR.sepOut (G'.pn + 8 * f.vars.length + 7) (by
      unfold frameS; right; refine ⟨by omega, .inl ?_⟩; rw [hna]; unfold InExt; simp only; omega)
    have hv' := hR.sepOut (G'.pv + 24 * f.vars.length + 23) (by
      unfold frameS; right; refine ⟨by omega, .inr ?_⟩; rw [hva]; unfold InExt; simp only; omega)
    have he' := hR.sepOut (G'.e + 3) (by unfold frameS InExt; left; omega)
    rw [hout.frame a (by unfold InExt; omega) (by unfold InExt; omega) (by unfold InExt; omega)]
    exact hslot5 a h1 h2
  rw [def_sp hC h32]
  iapply def_ret Wp hl N hC hstk7 hslot7
  iframe Ht Hgp Hv Hpc HR HB Hscr HK
  unfold heapStore
  iexists ((p.toNat, C.x.length + 1) :: H), (B₁ ++ G'.blocks ++ B₂)
  iframe Hh Hst
  ipureintro
  exact fun b hb => List.mem_cons_of_mem _ (hBH b hb)

end Sinks

end VsaIris.Interp
