import VsaIris.Interp.EnvCalls
import VsaIris.Interp.EnvNewSpans
import VsaIris.Stack
import VsaIris.Interp.Bridge

/-!
# `env_new`, proved over `heapStore` (INTERP_DESIGN.md §9 H1)

`envNew_spec : textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ⊢ envNewSpec Wp N`,
for every `MachWP` and both allocator regimes. It generalises the pilot
(`VsaIris/Vsa/EnvNewPilot.lean`: raw `isHeap`, a 32-byte block handed back) to
the interpreter's store: the fresh block becomes frame `st.frames.size` of
`storeRepr` (`storeRepr_allocFrame`), charged `envBytes` in the counted regime,
and malloc's NULL (uncounted only) takes the out-of-memory arm (`oomAt`).

Three spans (`EnvNewSpans.lean`) around one `jal malloc` (`wp_call_malloc`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section Main

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- The empty frame `env_new` leaves at `p` under `par`: struct only. -/
def newGeom (p par : Nat) : FrameGeom :=
  ⟨p, 0, 0, 0, par, (p, 32), (0, 0), (0, 0)⟩

/-- A zero word's two halves are zero. -/
theorem imgLE_halves_zero {img : Nat → BitVec 8} {a : Nat} (h : imgLE img a 8 = 0) :
    imgLE img a 4 = 0 ∧ imgLE img (a + 4) 4 = 0 := by
  have := imgLE_split img a 4 4
  rw [h] at this
  have h1 : 0 < 256 ^ 4 := by decide
  constructor
  · omega
  · rcases Nat.eq_zero_or_pos (imgLE img (a + 4) 4) with h0 | h0
    · exact h0
    · have := Nat.mul_le_mul_left (256 ^ 4) h0; omega

/-- The empty frame's layout from the initialized block. -/
theorem newGeom_layout {img : Nat → BitVec 8} {p par : Nat}
    (hp0 : p ≠ 0) (hpw : 0x80000000 ≤ p ∧ p + 32 ≤ 0x100000000 ∧ htifLo + 16 ≤ p ∧ p % 16 = 0)
    (h0 : imgLE img p 8 = 0) (h8 : imgLE img (p + 8) 8 = 0) (h16 : imgLE img (p + 16) 8 = 0)
    (h24 : imgLE img (p + 24) 8 = par) : FrameLayout img (newGeom p par) 0 where
  e_ne := hp0
  sblk := ⟨Nat.le_refl _, Nat.le_refl _⟩
  count := (imgLE_halves_zero h0).1
  cap := (imgLE_halves_zero h0).2
  names := h8
  vals := h16
  parent := h24
  count_le := Nat.le_refl _
  empty := fun _ => ⟨rfl, rfl⟩
  arrays := fun h => by simp [newGeom] at h
  disjoint := by simp [FrameGeom.blocks, newGeom]
  win := by
    intro b hb
    simp [FrameGeom.blocks, newGeom] at hb
    subst hb
    exact ⟨hpw.1, hpw.2.1, hpw.2.2.1, hpw.2.2.2⟩
  e_align := by unfold newGeom; have := hpw.2.2.2; simp only []; omega
  cap_canon := rfl

/-- **`env_new`** (`env.c:12`), for every `MachWP`, both regimes. -/
theorem envNew_spec (Wp : MachWP (GF := GF) (vsaModel live)) (hl : ∀ p ∈ envText, live p.1)
    (A : AllocSpecs live) (N : NativeAddrs) :
    textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ⊢ envNewSpec Wp N := by
  iintro ⟨#Ht, #Hat, #Hgp⟩
  unfold envNewSpec
  imodintro
  iintro %ρ %st %po %par %s %saved %hsv
  unfold fnSpecAbort
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hr, hsp⟩, Ha0, Hsp, -, Hcl, Hsv, Hstk, #Hpar, Hhs⟩ HK
  unfold heapStore
  icases Hhs with ⟨%H, %B, Hh, Hst, %hBH⟩
  ihave ⟨Hst, %hinv⟩ := keep_pure (storeRepr_pure N st B) $$ Hst
  have hslo : htifLo + 16 + 16 ≤ s.toNat := by
    have := hsp.lo; unfold htifLo envNewNeed allocHeadroom at this; unfold htifLo; omega
  have hs528 : 528 ≤ s.toNat := by have := hsp.lo; unfold htifLo envNewNeed allocHeadroom at this; omega
  -- the stack: malloc's scratch and env_new's 16-byte frame
  ihave ⟨Hscr, Hfr⟩ := stackScratch_frame (s := s) (f := 16#64) (n := envNewNeed)
    (by unfold envNewNeed allocHeadroom; omega) (by unfold envNewNeed allocHeadroom; decide) $$ Hstk
  have hsf : (s - 16#64).toNat = s.toNat - 16 := toNat_sub_frame (by simp; omega)
  rw [show envNewNeed - (16#64 : BitVec 64).toNat = allocHeadroom from rfl, hsf]
  ihave ⟨%fs, Hfr⟩ := blockOwn_img _ _ $$ Hfr
  ihave Hfr := ownSet_iff (T := fun a => s.toNat - 16 ≤ a ∧ a < s.toNat) _
    (fun a => by unfold InExt; simp; omega) $$ Hfr
  ihave ⟨%Mt0, -, Hfr⟩ := ownSet_tracked _ _ $$ Hfr
  -- the register file
  have hperm : (([(VsaIris.ra, r), (10, par), (VsaIris.sp, s)] ++ saved).map Prod.fst ++
      retClob).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hsv]; decide
  ihave ⟨%R0, %hR0, HR⟩ := regsOf_entry gprs _ retClob hperm gprs_nodup $$ [Hra Ha0 Hsp Hsv Hcl]
  · iframe Hcl
    unfold savedOwn
    iapply (sepL_append _ _ _).2
    isplitr [Hsv]
    · simp only [sepL_cons, sepL_nil]
      isplitl [Hra]
      · iexact Hra
      iframe Ha0
      isplitl [Hsp]
      · iexact Hsp
      iempintro
    · iexact Hsv
  have hR : ∀ k v, (k, v) ∈ [(VsaIris.ra, r), (10, par), (VsaIris.sp, s)] ++ saved → R0 k = v :=
    fun k v h => hR0 (k, v) h
  -- the prologue
  unfold envNewPC
  iapply wp_span Wp (new_pro hl (s := s.toNat) (R := R0) (Mt := Mt0)
    hslo hsp.hi hsp.align
    (by
      have h := hR VsaIris.sp s (List.mem_append_left _ (by simp))
      exact congrArg BitVec.toNat h))
  iframe Ht Hgp Hpc HR Hfr
  iintro %pc1 %R1 %Mt1 %⟨rfl, hstk1, h8, h10, hk1⟩ Hpc HR Hfr
  -- facts for the rest of the run
  have hR2 : R1 2 = s - 16#64 := by
    apply BitVec.eq_of_toNat_eq; rw [hstk1.sp, hsf]
  have hparR : R1 8 = par := h8.trans (hR 10 par (List.mem_append_left _ (by simp)))
  ihave ⟨⟨Hst, -⟩, %hparent⟩ := keep_pure (show storeRepr (GF := GF) N st B ∗ parentAt po par.toNat ⊢
      ⌜∀ pa, po = some pa → pa < st.frames.size⌝ from by
    cases po with
    | none => iintro _; ipureintro; intro pa h; cases h
    | some pa =>
      unfold parentAt
      iintro ⟨Hs, -, #Hpa⟩
      ihave %h := storeRepr_frameAt N $$ [Hs Hpa]
      · iframe Hs Hpa
      ipureintro; intro pa' hpa'; cases hpa'; exact h) $$ [Hst Hpar]
  · iframe Hst Hpar
  -- `jal malloc`
  rw [← hR2, show envBytes = 32 from rfl]
  iapply wp_call_malloc A Wp (i := 0x80002a10) (R := R1)
    (show JalExec (vsaModel live) 0x80002a10 _ mallocEntryBV from
      jalx_80002a10 live fun p hp => hl _ (env_code_80002a10 p hp))
    (by decide) ρ H 32 (by rw [h10]; exact ⟨by decide, by decide⟩)
    ⟨by rw [hstk1.sp]; have := hsp.lo; unfold htifLo envNewNeed allocHeadroom at this;
        unfold Vsa.Sim.tohostAddr allocHeadroom; omega,
     by rw [hstk1.sp]; have := hsp.hi; omega,
     by rw [hstk1.sp]; have := hsp.align; omega⟩
  isplitl []
  · iapply instrAt_of_text env_code_80002a10 $$ Ht
  iframe Hat Hgp HR Hscr
  isplitl [Hpc]
  · iexact Hpc
  isplitl [Hh]
  · iexact Hh
  iintro %R2 %p %⟨h10', h1', hk2⟩ Hpc HR Hscr Hres
  unfold mallocRes
  icases Hres with (⟨%⟨hp0, hρ⟩, Hh⟩ | ⟨%⟨hfresh, hal⟩, Hh, Hblk⟩)
  · -- NULL: the out-of-memory arm
    subst hρ
    rw [show BitVec.ofNat 64 (0x80002a10 + 4) = 0x80002a14#64 from rfl]
    iapply wp_span Wp (new_null hl (S := fun a => s.toNat - 16 ≤ a ∧ a < s.toNat) (Mt := Mt1)
      (h10'.trans hp0))
    iframe Ht Hgp Hpc HR Hfr
    iintro %pc3 %R3 %Mt3 %⟨rfl, rfl, rfl⟩ Hpc HR Hfr
    ihave Kab := and_elim_r $$ HK
    iapply Kab
    isplitl []
    · ipureintro; rfl
    unfold oomAt
    iframe Hpc
    have hperm : ([(VsaIris.sp, s - 16#64)].map Prod.fst ++
        (VsaIris.ra :: 10 :: retClob ++ newSaved)).Perm gprs := by
      simp only [List.map_cons, List.map_nil]; decide
    ihave ⟨Hsp, Hcl⟩ := regsOf_exit gprs _ _ hperm _ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      show _ = _
      exact (hk2 2 (by decide)).trans hR2) $$ HR
    unfold savedOwn
    simp only [sepL_cons, sepL_nil]
    icases Hsp with ⟨Hsp, -⟩
    isplitl [Hsp]
    · iapply regPt_congr (x := VsaIris.sp) (y := VsaIris.sp) rfl hR2.symm $$ Hsp
    iframe Hcl
    isplitl [Hscr Hfr]
    · iapply stackScratch_unframe (s := s) (f := 16#64) (n := envNewNeed)
        (by unfold envNewNeed allocHeadroom; omega) (by unfold envNewNeed allocHeadroom; decide)
      rw [show envNewNeed - (16#64 : BitVec 64).toNat = allocHeadroom from rfl, hsf, ← hR2]
      iframe Hscr
      ihave Hfr := ownSet_iff (T := InExt (s.toNat - 16, 16)) _
        (fun a => by unfold InExt; omega) $$ Hfr
      rw [show (16#64 : BitVec 64).toNat = 16 from rfl]
      unfold blockOwn
      iapply ownSet_forget $$ Hfr
    unfold heapStore
    iexists H, B
    iframe Hh Hst
    ipureintro; exact hBH
  · -- a fresh block: initialize the `Env`, return it
    have h32 : (R1 10).toNat = 32 := by rw [h10]; rfl
    rw [h32]
    rw [h32] at hfresh
    have hp0' : p ≠ 0#64 := fun h => hfresh.nonzero (by rw [h]; rfl)
    obtain ⟨-, hplo, hphi, -⟩ := hfresh.destruct
    have hpw : 0x80000000 ≤ p.toNat ∧ p.toNat + 32 ≤ 0x100000000 ∧ htifLo + 16 ≤ p.toNat ∧
        p.toNat % 16 = 0 := by
      have hlo' : Vsa.Sim.DlHeap.heapStart ≤ p.toNat := hplo
      have hhi' : p.toNat + 32 ≤ Vsa.Sim.DlHeap.heapEnd := hphi
      unfold Vsa.Sim.DlHeap.heapStart at hlo'; unfold Vsa.Sim.DlHeap.heapEnd at hhi'; unfold htifLo
      omega
    -- the block beside the frame bytes, at one tracking memory
    unfold blockOwn
    ihave ⟨%fb, Hblk⟩ := ownSet_fn _ $$ Hblk
    ihave ⟨⟨Hfr, Hblk⟩, %hdb⟩ := keep_pure (ownSet_disj _ _ (imgM Mt1) fb) $$ [Hfr Hblk]
    · iframe Hfr Hblk
    have hsep : p.toNat + 32 ≤ s.toNat - 16 ∨ s.toNat ≤ p.toNat := by
      have := interval_apart (a := p.toNat) (n := 32) (b := s.toNat - 16) (m := 16)
        (by omega) (by omega) fun c h1 h2 => by
          have := hdb c ⟨h1, by omega⟩; unfold InExt at this; omega
      omega
    ihave HS := ownSet_glue _ _ (imgM Mt1) fb hdb $$ [Hfr Hblk]
    · iframe Hfr Hblk
    ihave HS := ownSet_iff (T := fun a => (s.toNat - 16 ≤ a ∧ a < s.toNat) ∨
      (p.toNat ≤ a ∧ a < p.toNat + 32)) _ (fun a => by unfold InExt; exact Iff.rfl) $$ HS
    ihave ⟨%Mt2, %hag, HS⟩ := ownSet_tracked _ _ $$ HS
    have hstk2 : NewStack s.toNat r (R0 8) R2 Mt2 :=
      ⟨by rw [hk2 2 (by decide)]; exact hstk1.sp,
       (ldv_congr .ld fun j hj => by
          simp only [widthOfM] at hj
          rw [hag _ (.inl ⟨by omega, by omega⟩)]; simp [glue, show s.toNat - 16 ≤ s.toNat - 8 + j by omega,
            show s.toNat - 8 + j < s.toNat by omega]).trans
         (hstk1.ra.trans (hR VsaIris.ra r (List.mem_append_left _ (by simp)) ▸ rfl)),
       (ldv_congr .ld fun j hj => by
          simp only [widthOfM] at hj
          rw [hag _ (.inl ⟨by omega, by omega⟩)]; simp [glue, show s.toNat - 16 ≤ s.toNat - 16 + j by omega,
            show s.toNat - 16 + j < s.toNat by omega]).trans hstk1.s0⟩
    rw [show BitVec.ofNat 64 (0x80002a10 + 4) = 0x80002a14#64 from rfl]
    iapply wp_span Wp (new_ok hl (s := s.toNat) (pn := p.toNat) (R := R2) (Mt := Mt2) hslo hsp.hi hr
      hstk2 (by rw [h10']; exact hp0') (by rw [h10']) hpw hsep)
    iframe Ht Hgp Hpc HR HS
    iintro %pc4 %R4 %Mt4 %⟨hpc4, h10'', h1'', h8'', h2'', hk4, hw0, hw8, hw16, hw24⟩ Hpc HR HS
    rw [hpc4]
    -- the frame's bytes: the initialized block
    ihave ⟨Hfr, Hblk⟩ := ownSet_unglue (fun a => s.toNat - 16 ≤ a ∧ a < s.toNat)
      (fun a => p.toNat ≤ a ∧ a < p.toNat + 32) _ (fun a h1 h2 => by omega) $$ HS
    have hpar8 : R2 8 = par := (hk2 8 (by decide)).trans hparR
    have hlay : FrameLayout (imgM Mt4) (newGeom p.toNat par.toNat) 0 := by
      refine newGeom_layout (by intro h; exact hp0' (BitVec.eq_of_toNat_eq (by simpa using h))) hpw
        ?_ ?_ ?_ ?_
      · rw [← imgW_toNat, ← ldv_ld_img, hw0]; rfl
      · rw [← imgW_toNat, ← ldv_ld_img, hw8]; rfl
      · rw [← imgW_toNat, ← ldv_ld_img, hw16]; rfl
      · rw [← imgW_toNat, ← ldv_ld_img, hw24, hpar8]
    have hst' : (st.allocFrame po).1.frames.toList = st.frames.toList ++ [⟨po, []⟩] := by
      simp [Store.allocFrame]
    have hinv' : Vsa.Sim.StoreInvariant (st.allocFrame po).1 :=
      hinv.allocFrame st po hparent
    iapply Wp.fupd
    imod storeRepr_allocFrame N (s := st) (s' := (st.allocFrame po).1) (B := B)
      (f := ⟨po, []⟩) (Gm := newGeom p.toNat par.toNat) hst' rfl hinv' $$ [Hst Hblk]
      with ⟨Hst, #He⟩
    · iframe Hst
      unfold frameBody
      iexists (imgM Mt4)
      isplitr
      · ipureintro; exact hlay
      isplitl [Hblk]
      · iapply ownSet_iff _ (fun a => by
          simp [BlocksCover, FrameGeom.blocks, newGeom, InExt]) $$ Hblk
      isplitl []
      · unfold bindings; simp only [List.zipIdx_nil, sepL_nil]; iempintro
      · dsimp only [newGeom]; iexact Hpar
    imodintro
    -- the return
    ihave Kok := and_elim_l $$ HK
    have hperm' : (([(VsaIris.ra, r), (10, p), (VsaIris.sp, s)] ++ saved).map Prod.fst ++
        retClob).Perm gprs := by
      simp only [List.map_append, List.map_cons, List.map_nil, hsv]; decide
    have hfix : ∀ q ∈ [(VsaIris.ra, r), (10, p), (VsaIris.sp, s)] ++ saved, R4 q.1 = q.2 := by
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact h1''
        · exact h10''.trans h10'
        · show R4 2 = s; rw [h2'']; exact BitVec.eq_of_toNat_eq (by simp)
      · have hk : q.1 ∈ newSaved := by rw [← hsv]; exact List.mem_map_of_mem hq
        have hq' := hR q.1 q.2 (List.mem_append_right _ hq)
        by_cases h8q : q.1 = 8
        · rw [h8q] at hq' ⊢
          rw [h8'']; exact hq'
        · have hq1 : q.1 ≠ 1 := by simp [newSaved] at hk; omega
          have hq2 : q.1 ≠ 2 := by simp [newSaved] at hk; omega
          have hq10 : q.1 ≠ 10 := by simp [newSaved] at hk; omega
          have hkc : q.1 ∉ VsaIris.ra :: 10 :: vsaClob := by
            simp [newSaved, vsaClob, VsaIris.ra] at hk ⊢; omega
          rw [hk4 _ hq1 hq2 h8q, hk2 _ hkc, hk1 _ hq2 h8q hq10]
          exact hq'
    ihave ⟨Hfx, Hcl⟩ := regsOf_exit gprs _ retClob hperm' R4 hfix $$ HR
    unfold savedOwn
    ihave ⟨H3, Hsv⟩ := (sepL_append _ _ _).1 $$ Hfx
    simp only [sepL_cons, sepL_nil]
    icases H3 with ⟨Hra, Ha0, Hsp, -⟩
    iapply Kok $$ Hpc Hra
    iexists p
    iframe Ha0 Hcl Hsv
    isplitl [Hsp]
    · iexact Hsp
    isplitl [Hscr Hfr]
    · iapply stackScratch_unframe (s := s) (f := 16#64) (n := envNewNeed)
        (by unfold envNewNeed allocHeadroom; omega) (by unfold envNewNeed allocHeadroom; decide)
      rw [show envNewNeed - (16#64 : BitVec 64).toNat = allocHeadroom from rfl, hsf, ← hR2,
        show (16#64 : BitVec 64).toNat = 16 from rfl]
      iframe Hscr
      ihave Hfr := ownSet_iff (T := InExt (s.toNat - 16, 16)) _
        (fun a => by unfold InExt; omega) $$ Hfr
      unfold blockOwn
      iapply ownSet_forget $$ Hfr
    isplitl [Hh Hst]
    · iexists (p.toNat, 32) :: H, B ++ (newGeom p.toNat par.toNat).blocks
      iframe Hh Hst
      ipureintro
      intro b hb
      simp only [List.mem_append, FrameGeom.blocks, newGeom] at hb
      rcases hb with hb | hb
      · exact List.mem_cons_of_mem _ (hBH b hb)
      · simp at hb; subst hb; exact List.mem_cons_self
    · dsimp only [newGeom] at *; iexact He

end Main

end VsaIris.Interp

#print axioms VsaIris.Interp.envNew_spec
