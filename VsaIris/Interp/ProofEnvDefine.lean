import VsaIris.Interp.EnvDefineGrow

/-!
# `env_define`, proved (INTERP_DESIGN.md §9 H1)

`envDefine_spec : textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗
strlenSpec Wp ∗ memcpySpec Wp ⊢ envDefineSpec Wp N`, for every `MachWP`, in both
regimes, given H4's allocator (`AllocHoles`) and `realloc(NULL, n)`
(`ReallocNullHoles`).

The entry opens frame `fa` (`storeRepr_openAt`), runs the prologue and the
count test, then: an empty frame grows (`def_empty`, `def_grow`); otherwise the
name loop (`scan_frame` at `defLoop`, invariant `DefFrame`) finds the name
(`def_hit`: `Store.define`'s replacement) or misses it, and the capacity test
(`def_cap`) grows a full frame (`def_grow`) or appends at once
(`def_append`). The counted regime's charge `defineCost` splits as the name
copy plus `growthCost` (`defineCost_miss`, `growthCost_eq`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

section Unfold

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

theorem heapStore_parts (N : NativeAddrs) (ρ : Regime) (st : Store) :
    heapStore (GF := GF) N ρ st ⊢ ∃ H B, heapRes vsaLayoutP vsaRoomB ρ H ∗ storeRepr N st B ∗
      ⌜∀ b ∈ B, b ∈ H⌝ := by
  iintro H; unfold heapStore; iexact H

theorem valAt_parts (N : NativeAddrs) (a : Nat) (v : Value) :
    valAt (GF := GF) N a v ⊢ ∃ img, ownImg (InExt (a, 24)) img ∗ valImg N img a v := by
  iintro H; unfold valAt; iexact H

end Unfold

section Main

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- **`env_define`** (`env.c:22`), for every `MachWP`, both regimes. -/
theorem envDefine_spec (Wp : MachWP (GF := GF) (vsaModel live)) (hl : ∀ p ∈ envText, live p.1)
    (AH : AllocHoles) (NH : ReallocNullHoles) (hlive : AllocLive live) (N : NativeAddrs) :
    textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ strlenSpec Wp ∗
      memcpySpec Wp ⊢ envDefineSpec Wp N := by
  iintro ⟨#Ht, #Hat, #Hgp, #Hcmp, #Hsl, #Hmc⟩
  unfold envDefineSpec
  imodintro
  iintro %ρ %st %fa %x %v %e %pn %pv %s %saved %hsv
  unfold fnSpecAbort
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hr, hsp, hslot⟩, Ha0, Ha1, Ha2, Hsp, -, Hcl, Hsv, Hstk, #Hfa, #Hx, Hval,
    Hhs⟩ HK
  -- the heap and the store; the frame opened
  ihave ⟨%H, %B, Hh, Hst, %hBH⟩ := heapStore_parts N _ st $$ Hhs
  ihave ⟨Hst, %hBd⟩ := keep_pure (storeRepr_blocks_disjoint N) $$ Hst
  ihave ⟨%f, %Gm, %img, %B₁, %B₂, %⟨hf, hGe, hlay, hinv, hB⟩, Hown, #Hb, #Hp, #HGe, Hclose⟩ :=
    storeRepr_openAt N $$ [Hst Hfa]
  · iframe Hst Hfa
  subst hB
  -- the value slot, apart from the stack
  ihave ⟨%fo, Hout, #Hv⟩ := valAt_parts N _ v $$ Hval
  ihave ⟨⟨Hout, Hstk⟩, %hdo⟩ := keep_pure (ownSet_off _ _ fo) $$ [Hout Hstk]
  · iframe Hout; unfold stackScratch blockOwn; iexact Hstk
  have hs576 : envDefineNeed ≤ s.toNat := by have := hsp.lo; unfold htifLo at this; omega
  have hsep : pv.toNat + 24 ≤ s.toNat - envDefineNeed ∨ s.toNat ≤ pv.toNat := by
    have := interval_apart (a := pv.toNat) (n := 24) (b := s.toNat - envDefineNeed)
      (m := envDefineNeed) (by omega) (by unfold envDefineNeed; omega) fun c h1 h2 => by
        have := hdo c
        unfold InExt at this; omega
    omega
  let C : DefCall := ⟨s, r, pn, pv, x, v, saved, fo⟩
  have hC : C.OK := ⟨hsp, hslot, hr, hsv, hsep⟩
  have hs64 : 64 ≤ s.toNat := by have := hsp.lo; unfold envDefineNeed htifLo at this; omega
  -- the frame's bytes: the stack frame, the value slot and the frame's blocks
  ihave ⟨Hscr, Hfr⟩ := def_stack_split hC $$ [Hstk]
  · unfold stackScratch blockOwn; iexact Hstk
  simp only [C]
  ihave ⟨%fs, Hfr⟩ := blockOwn_img _ _ $$ Hfr
  have hsep64 : pv.toNat + 24 ≤ s.toNat - 64 ∨ s.toNat ≤ pv.toNat := hC.sepStk
  ihave HBa := ownSet_glue (InExt (s.toNat - 64, 64)) (InExt (pv.toNat, 24)) fs fo
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$ [Hfr Hout]
  · iframe Hfr Hout
  ihave HBa := ownSet_iff (T := baseS s.toNat pv.toNat) _ (fun a => by
    unfold baseS InExt; omega) $$ HBa
  ihave ⟨%Mt0, %hag0, HBa⟩ := ownSet_tracked _ _ $$ HBa
  ihave ⟨%Mt1, %⟨hbase1, himg1, hdisj⟩, HS⟩ := get_join _ _ Gm Mt0 img $$ [HBa Hown]
  · iframe HBa Hown
  have hslot1 : ∀ a, pv.toNat ≤ a → a < pv.toNat + 24 → imgM Mt1 a = fo a := fun a h1 h2 => by
    rw [hbase1 a (.inr ⟨h1, h2⟩), hag0 a (by unfold baseS; omega)]
    have : ¬ InExt (s.toNat - 64, 64) a := by unfold InExt; omega
    simp [glue, this]
  have hlay1 : FrameLayout (imgM Mt1) Gm f.vars.length := hlay.congr himg1
  have hsepS : ∀ a, frameS Gm a → a < s.toNat - 64 ∨ s.toNat ≤ a := fun a ha => by
    have := hdisj a ha; unfold baseS at this; omega
  have hsepO : ∀ a, frameS Gm a → a < pv.toNat ∨ pv.toNat + 24 ≤ a := fun a ha => by
    have := hdisj a ha; unfold baseS at this; omega
  -- the register file
  have hperm : (([(VsaIris.ra, r), (10, e), (11, pn), (12, pv), (VsaIris.sp, s)] ++ saved).map
      Prod.fst ++ argClob).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hsv]; decide
  ihave ⟨%R0, %hR0, HR⟩ := regsOf_entry gprs _ argClob hperm gprs_nodup
    $$ [Hra Ha0 Ha1 Ha2 Hsp Hsv Hcl]
  · iframe Hcl
    unfold savedOwn
    iapply (sepL_append _ _ _).2
    isplitr [Hsv]
    · simp only [sepL_cons, sepL_nil]
      isplitl [Hra]
      · iexact Hra
      iframe Ha0 Ha1 Ha2
      isplitl [Hsp]
      · iexact Hsp
      iempintro
    · iexact Hsv
  have hR : ∀ k v, (k, v) ∈ [(VsaIris.ra, r), (10, e), (11, pn), (12, pv), (VsaIris.sp, s)] ++
      saved → R0 k = v := fun k v h => hR0 (k, v) h
  have hsvR : ∀ k ∈ defineSaved, R0 k = pairVal saved k := fun k hk => by
    rw [← hsv] at hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    rw [hR0 p (List.mem_append_right _ hp), pairVal_of_mem saved (by rw [hsv]; decide) p hp]
  have he0 : (R0 10).toNat = Gm.e := by rw [hR 10 e (by simp), hGe]
  -- the prologue
  unfold envDefinePC
  iapply wp_span Wp (def_pro hl (s := s.toNat) (out := pv.toNat) (n := f.vars.length) (G := Gm)
    (R := R0) (Mt := Mt1) hC.s64 hsp.hi hsp.align
    (by rw [show (2 : Nat) = VsaIris.sp from rfl, hR VsaIris.sp s (by simp)])
    (hR VsaIris.ra r (by simp)) hsvR hlay1 he0 hsepS)
  iframe Ht Hgp Hpc HR HS
  iintro %pc1 %R1 %Mt2 %⟨rfl, hstk, h10, h20, h18, h21, h19, hfr2⟩ Hpc HR HS
  have hag2 : ∀ a, frameS Gm a → imgM Mt2 a = img a := fun a ha =>
    (hfr2 a (hsepS a ha)).trans (himg1 a ha)
  have hlay2 : FrameLayout (imgM Mt2) Gm f.vars.length := hlay.congr hag2
  have hslot2 : ∀ a, pv.toNat ≤ a → a < pv.toNat + 24 → imgM Mt2 a = fo a := fun a h1 h2 =>
    (hfr2 a (by omega)).trans (hslot1 a h1 h2)
  have he1 : (R1 10).toNat = Gm.e := by rw [h10]; exact he0
  have he20 : (R1 20).toNat = Gm.e := by rw [h20]; exact he0
  have hname1 : R1 18 = pn := by rw [h18, hR 11 pn (by simp)]
  have hvp1 : R1 21 = pv := by rw [h21, hR 12 pv (by simp)]
  -- the count test
  iapply wp_span Wp (def_head hl (s := s.toNat) (out := pv.toNat) hlay2 he1 h19)
  iframe Ht Hgp Hpc HR HS
  iintro %pc2 %R2 %Mt3 %⟨rfl, hcase⟩ Hpc HR HS
  have hBH' : ∀ b ∈ B₁ ++ Gm.blocks ++ B₂, b ∈ H := hBH
  rcases hcase with ⟨hn0, rfl, rfl⟩ | ⟨hpos, rfl, hhd⟩
  · -- an empty frame: the first growth
    have hnil : f.vars = [] := List.eq_nil_of_length_eq_zero hn0
    have hmiss : ¬ f.vars.any (·.1 == x) := by simp [hnil]
    have hlay0 : FrameLayout (imgM Mt3) Gm 0 := hn0 ▸ hlay2
    iapply wp_span Wp (def_empty hl (s := s.toNat) (out := pv.toNat) hlay0 he1
      (by rw [h19, hn0]))
    iframe Ht Hgp Hpc HR HS
    iintro %pc3 %R3 %Mt4 %⟨rfl, rfl, hg⟩ Hpc HR HS
    have hGR : GrowReady C Gm f.vars.length img R3 _ :=
      { stack := hstk.congr (hg.keep 2 (by decide) (by decide) (by decide)) (fun _ _ _ => rfl) hs64
        name := (hg.keep 18 (by decide) (by decide) (by decide)).trans hname1
        vp := (hg.keep 21 (by decide) (by decide) (by decide)).trans hvp1
        env := by rw [hg.keep 20 (by decide) (by decide) (by decide)]; exact he20
        lay := hlay2
        full := by rw [hlay2.cap_canon, hn0]; rfl
        img := hag2
        sepOut := hsepO
        sepStk := hsepS
        slot := hslot2
        cap := by rw [hg.cap, hn0]; rfl
        names := by rw [hg.names, hn0]; rfl
        arr := hg.arr }
    rw [defineCost_miss hf hmiss, show growthCost f.vars.length =
      arrayReallocCost (nextCap f.vars.length) by rw [hn0]; rfl]
    iapply def_grow Wp hl AH NH hlive N hC hGR hf hinv hmiss hdisj hBH' hBd
    iframe Ht Hat Hgp Hsl Hmc Hx Hv Hpc HR HS Hscr Hh Hb Hp HGe Hclose
    unfold defK; iexact HK
  · -- the name loop
    have hF : DefFrame C Gm f.vars.length img R2 Mt3 :=
      { stack := hstk.congr (hhd.keep 2 (by decide) (by decide) (by decide)) (fun _ _ _ => rfl) hs64
        name := (hhd.keep 18 (by decide) (by decide) (by decide)).trans hname1
        vp := (hhd.keep 21 (by decide) (by decide) (by decide)).trans hvp1
        env := by rw [hhd.keep 20 (by decide) (by decide) (by decide)]; exact he20
        cnt := (hhd.keep 19 (by decide) (by decide) (by decide)).trans h19
        arr := hhd.arr
        lay := hlay2
        img := hag2
        sepOut := hsepO
        sepStk := hsepS
        slot := hslot2 }
    obtain ⟨-, -, hn2, -, -, hnw, -⟩ := hlay2.slot hpos
    iapply scan_frame Wp (defLoop live hl) N (defFrame_scanInv hl C hs64) f.vars.length 0 R2 Mt3
      (by omega) hpos (by simp) hhd.idx
      (by rw [hhd.cur, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hnw.hi; omega)]; simp)
      hF.cnt hF
    rw [show (defLoop live hl).scan = 0x80002ab0#64 from rfl]
    iframe Ht Hgp Hcmp Hx Hb Hpc HR HS
    isplit
    · -- `x` unbound in the frame: grow or append
      iintro %R3 %Mt4 %⟨hF3, hmissF⟩ Hpc HR HS
      rw [show (defLoop live hl).tail = 0x80002b14#64 from rfl]
      have hmiss : ¬ f.vars.any (·.1 == x) := by
        intro h
        obtain ⟨p, hp, hpx⟩ := List.any_eq_true.1 h
        exact hmissF p hp (by simpa using hpx)
      rw [defineCost_miss hf hmiss]
      iapply wp_span Wp (def_cap hl (s := s.toNat) (out := pv.toNat) hF3.lay hF3.env hF3.cnt
        hF3.arr)
      iframe Ht Hgp Hpc HR HS
      iintro %pc4 %R4 %Mt5 %⟨rfl, hcase⟩ Hpc HR HS
      rcases growthCost_eq f.vars.length with ⟨hc1, -, hgc⟩ | ⟨hc1, -, hgc⟩
      · rcases hcase with ⟨hcn, rfl, hg⟩ | ⟨hcn, -, -⟩
        · -- a full frame: grow
          have hnc : nextCap f.vars.length = 2 * Gm.cap := by
            unfold nextCap; rw [if_neg (by omega), hcn]
          have hGR : GrowReady C Gm f.vars.length img R4 _ :=
            { stack := hF3.stack.congr (hg.keep 2 (by decide) (by decide) (by decide))
                (fun _ _ _ => rfl) hs64
              name := (hg.keep 18 (by decide) (by decide) (by decide)).trans hF3.name
              vp := (hg.keep 21 (by decide) (by decide) (by decide)).trans hF3.vp
              env := by rw [hg.keep 20 (by decide) (by decide) (by decide)]; exact hF3.env
              lay := hF3.lay
              full := hcn
              img := hF3.img
              sepOut := hF3.sepOut
              sepStk := hF3.sepStk
              slot := hF3.slot
              cap := by rw [hg.cap, hnc]
              names := by rw [hg.names, hnc]
              arr := hg.arr }
          rw [hgc]
          iapply def_grow Wp hl AH NH hlive N hC hGR hf hinv hmiss hdisj hBH' hBd
          iframe Ht Hat Hgp Hsl Hmc Hx Hv Hpc HR HS Hscr Hh Hb Hp HGe Hclose
          unfold defK; iexact HK
        · exact absurd (hF3.lay.cap_canon.trans hc1) hcn
      · rcases hcase with ⟨hcn, -, -⟩ | ⟨hcn, rfl, hk4⟩
        · exact absurd (hcn ▸ hF3.lay.cap_canon) (by omega)
        · -- room left: append
          have hAR : AppReady C Gm Gm f.vars.length img R4 _ :=
            { stack := hF3.stack.congr (hk4 2 (by decide)) (fun _ _ _ => rfl) hs64
              name := (hk4 18 (by decide)).trans hF3.name
              vp := (hk4 21 (by decide)).trans hF3.vp
              env := by rw [hk4 20 (by decide)]; exact hF3.env
              lay := hF3.lay.appLayout hcn
              e := rfl
              par := rfl
              oldNames := fun k hk o ho => hF3.img _ (frameS_name hF3.lay hk ho)
              oldVals := fun k hk o ho => hF3.img _ (frameS_val hF3.lay hk ho)
              sepOut := hF3.sepOut
              sepStk := hF3.sepStk
              slot := hF3.slot }
          rw [hgc, Nat.add_zero]
          iapply def_append Wp hl (allocSpecs AH live hlive) N hC hAR hf hinv hmiss hdisj hBH'
          iframe Ht Hat Hgp Hsl Hmc Hx Hv Hpc HR HS Hscr Hh Hb Hp HGe Hclose
          unfold defK; iexact HK
    · -- `x` bound: replace its value
      iintro %j %v0 %R3 %Mt4 %⟨hj, -, hF3, h8⟩ Hpc HR HS
      rw [show (defLoop live hl).hit = 0x80002ac0#64 from rfl]
      have hany : f.vars.any (·.1 == x) := by
        rw [List.any_eq_true]
        exact ⟨(x, v0), List.mem_of_getElem? hj, by simp⟩
      rw [defineCost_hit hf hany, Regime.plus_zero]
      iapply def_hit Wp hl N hC hF3 h8 hj hf hinv hdisj hBH'
      iframe Ht Hgp Hv Hpc HR HS Hscr Hh Hb Hp HGe Hclose
      unfold defK; iexact HK

end Main

end VsaIris.Interp

#print axioms VsaIris.Interp.envDefine_spec
