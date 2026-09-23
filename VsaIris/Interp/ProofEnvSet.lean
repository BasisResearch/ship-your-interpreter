import VsaIris.Interp.EnvScan
import VsaIris.Interp.EnvSetHit

/-!
# `env_set`, proved (INTERP_DESIGN.md §9 H1)

`envSet_spec : textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ envSetSpec Wp N`,
for every `MachWP`.

`env_set` is the scan code (`EnvScan.lean`) at `setSite` — its spans are the
generated `EnvSetSpans.lean` — with the hit arm `set_hit` (write the caller's
value into `vals[i]`, return 1, `EnvSetHit.lean`). The machine's store is
`Store.set?`'s: the chain's path keeps the assignment (`ChainFrom.setAt`),
the root misses (`setAt_root`), and at the first match the spec's map-update
is the one-slot write (`FirstMatch.single_update`, names unique).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- `env_set`'s address of the scan code. -/
def setSite (live : Nat → Prop) (hl : ∀ p ∈ envText, live p.1) : ScanSite live where
  entry := 0x80002cdc#64
  head := 0x80002d0c#64
  scan := 0x80002d2c#64
  jal := 0x80002d34
  jcode := [0xef#8, 0x40#8, 0xc0#8, 0x16#8]
  hit := 0x80002d3c#64
  tail := 0x80002d90#64
  epi := 0x80002d6c#64
  jexec := jalx_80002d34 live fun p hp => hl _ (env_code_80002d34 p hp)
  jtext := env_code_80002d34
  jal4 := by decide
  sEntry := set_entry hl
  sHead := set_head hl
  sLoad := set_load hl
  sCmp := set_cmp hl
  sParent := set_parent hl
  sEpi := set_epi hl

/-! ## The assignment the machine performs -/

/-- `Store.set` needs no more gas than the frame address plus one. -/
theorem set_stable {st : Store} (hp : StoreParents st) (x : String) (v : Value) :
    ∀ a, a < st.frames.size → ∀ g, a < g → st.set g a x v = st.set (a + 1) a x v := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hf : st.frames[a]? = some st.frames[a] := Array.getElem?_eq_getElem ha
    simp only [Store.set, hf]
    dsimp only [Bind.bind, Option.bind]
    split
    · rfl
    · cases hpar : st.frames[a].parent with
      | none => rfl
      | some p =>
        have hpa : p < a := hp a ha p hpar
        dsimp only
        have hag : a ≤ g' := by omega
        rw [ih p hpa (Nat.lt_trans hpa ha) g' (Nat.lt_of_lt_of_le hpa hag),
          ih p hpa (Nat.lt_trans hpa ha) a hpa]

/-- The assignment's result from frame `a`. -/
def setAt (st : Store) (a : Addr) (x : String) (v : Value) : Option Store :=
  st.set (a + 1) a x v

theorem set?_eq_setAt {st : Store} (hp : StoreParents st) {a : Addr} (ha : a < st.frames.size)
    (x : String) (v : Value) : st.set? a x v = setAt st a x v :=
  set_stable hp x v a ha _ ha

theorem setAt_root {st : Store} {a : Addr} {f : Frame} {x : String} {v : Value}
    (hf : st.frames[a]? = some f) (h : FrameMiss f.vars x) (hp : f.parent = none) :
    setAt st a x v = none := by
  unfold setAt
  simp [Store.set, hf, h.any_eq_false, hp]

theorem setAt_parent {st : Store} (hps : StoreParents st) {a p : Addr} {f : Frame} {x : String}
    {v : Value} (hf : st.frames[a]? = some f) (h : FrameMiss f.vars x) (hp : f.parent = some p) :
    setAt st a x v = setAt st p x v := by
  have ha : a < st.frames.size := by
    rcases Nat.lt_or_ge a st.frames.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hf
  have hfa : st.frames[a] = f := by simpa [Array.getElem?_eq_getElem ha] using hf
  have hpa : p < a := hps a ha p (by rw [hfa]; exact hp)
  unfold setAt
  simp only [Store.set, hf, Option.bind_eq_bind, Option.bind_some, h.any_eq_false, hp]
  exact set_stable hps x v p (Nat.lt_trans hpa ha) a hpa

theorem setAt_hit {st : Store} {a : Addr} {f : Frame} {x : String} {v v₀ : Value}
    (hf : st.frames[a]? = some f) (h : FirstMatch f.vars x v₀) :
    setAt st a x v = some { st with frames := st.frames.modify a fun f =>
      { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } } := by
  unfold setAt
  simp [Store.set, hf, h.any_eq_true]

/-- Along the path, the assignment does not change. -/
theorem ChainFrom.setAt {st : Store} (hps : StoreParents st) {x : String} {v : Value}
    {fa a : Addr} (h : ChainFrom st x fa a) : Interp.setAt st fa x v = Interp.setAt st a x v := by
  induction h with
  | refl => rfl
  | step _ hf hm hp ih => exact ih.trans (setAt_parent hps hf hm hp)

/-- Under unique names, the spec's map-update is the one-slot write. -/
theorem map_replace_eq_set {vars : List (String × Value)} {x : String} {v v₀ : Value} {j : Nat}
    (hj : vars[j]? = some (x, v₀)) (hu : FrameNamesUnique vars) :
    vars.map (fun p => if p.1 == x then (x, v) else p) = vars.set j (x, v) := by
  have hlt : j < vars.length := by
    rcases Nat.lt_or_ge j vars.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hj
  have hvj : vars[j] = (x, v₀) := by simpa [List.getElem?_eq_getElem hlt] using hj
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_set]
  by_cases hk : j = k
  · subst hk; simp [hvj]
  · rw [if_neg hk]
    have hk' : k < vars.length := by simpa using h2
    have hne : vars[k].1 ≠ x := fun h => by
      have := (List.Nodup.getElem_inj hu (i := k) (j := j) (hi := by simpa using hk')
        (hj := by simpa using hlt)).mp (by simp [h, hvj])
      exact hk this.symm
    simp [hne]

/-! ## The frame after the write -/

section Frame

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- A value's meaning reads only its 24 bytes. -/
theorem valImg_agree (N : NativeAddrs) {img img' : Nat → BitVec 8} {a : Nat} (v : Value)
    (h : ∀ o, o < 24 → img' (a + o) = img (a + o)) :
    valImg (GF := GF) N img' a v = valImg N img a v := by
  have w : ∀ o, o + 8 ≤ 24 → imgW img' (a + o) = imgW img (a + o) := fun o ho =>
    imgW_agree fun k hk => by
      have := h (o + k) (by omega)
      rwa [show a + (o + k) = a + o + k by omega] at this
  unfold valImg
  rw [show a = a + 0 from rfl, w 0 (by omega), w 8 (by omega), w 16 (by omega)]

/-- **The bindings after writing value `j`**: the names are unchanged, the
other values unchanged, value `j` the new one. -/
theorem bindings_set (N : NativeAddrs) {img img' : Nat → BitVec 8} {pn pv : Nat}
    {vars : List (String × Value)} {j : Nat} {x : String} {v : Value}
    (hj : j < vars.length) (hx : vars[j].1 = x)
    (hn : ∀ k, k < vars.length → ∀ o, o < 8 → img' (pn + 8 * k + o) = img (pn + 8 * k + o))
    (hv : ∀ k, k < vars.length → k ≠ j → ∀ o, o < 24 →
      img' (pv + 24 * k + o) = img (pv + 24 * k + o)) :
    bindings (GF := GF) N img pn pv vars ∗ valImg N img' (pv + 24 * j) v ⊢
      bindings N img' pn pv (vars.set j (x, v)) := by
  iintro ⟨#Hb, #Hv⟩
  unfold bindings
  iapply sepL_of_all
  imodintro
  iintro %q %hq
  obtain ⟨p, k⟩ := q
  rw [List.mem_zipIdx_iff_getElem?] at hq
  have hk : k < vars.length := by
    have := List.getElem?_eq_some_iff.1 hq; simpa using this.1
  ihave ⟨#Hname, #Hval⟩ := sepL_zipIdx_get _ vars hk $$ Hb
  have hname : imgLE img' (pn + 8 * k) 8 = imgLE img (pn + 8 * k) 8 :=
    imgLE_congr fun o ho => hn k hk o ho
  by_cases hkj : k = j
  · subst hkj
    have hp : p = (x, v) := by simp [List.getElem?_set] at hq; exact hq.2.symm
    subst hp
    dsimp only
    rw [hname, ← hx]
    iframe Hname Hv
  · have hp : p = vars[k] := by
      rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_eq_getElem hk] at hq
      exact (Option.some.inj hq).symm
    subst hp
    dsimp only
    rw [hname, valImg_agree N _ (hv k hk hkj)]
    iframe Hname Hval

omit I in
/-- The frame layout reads only the `Env` struct's bytes. -/
theorem FrameLayout.congr_struct {img img' : Nat → BitVec 8} {Gm : FrameGeom} {n : Nat}
    (h : FrameLayout img Gm n) (hag : ∀ a, Gm.e ≤ a → a < Gm.e + 32 → img' a = img a) :
    FrameLayout img' Gm n := by
  have e : ∀ o w, o + w ≤ 32 → imgLE img' (Gm.e + o) w = imgLE img (Gm.e + o) w := fun o w how =>
    imgLE_congr fun k hk => hag _ (by omega) (by omega)
  exact { h with
    count := by have := e 0 4 (by omega); simp at this; rw [this]; exact h.count
    cap := by rw [e 4 4 (by omega)]; exact h.cap
    names := by rw [e 8 8 (by omega)]; exact h.names
    vals := by rw [e 16 8 (by omega)]; exact h.vals
    parent := by rw [e 24 8 (by omega)]; exact h.parent }

end Frame

/-! ## `env_set` -/

/-- The store after assigning at frame `a`. -/
def setStore (st : Store) (a : Addr) (x : String) (v : Value) : Store :=
  { st with frames := st.frames.modify a fun f =>
      { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } }

theorem setStore_frames_toList {st : Store} {a : Addr} {f : Frame} (hf : st.frames[a]? = some f)
    (x : String) (v : Value) :
    (setStore st a x v).frames.toList = st.frames.toList.set a
      { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } := by
  unfold setStore
  rw [Array.toList_modify, List.modify_eq_set]
  have hf' : st.frames.toList[a]? = some f := by rw [Array.getElem?_toList]; exact hf
  rw [hf']
  rfl

section Main

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- **`env_set`** (`env.c:56`), for every `MachWP`. -/
theorem envSet_spec (Wp : MachWP (GF := GF) (vsaModel live)) (hl : ∀ p ∈ envText, live p.1)
    (N : NativeAddrs) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ envSetSpec Wp N := by
  iintro ⟨#Ht, #Hgp, #Hcmp⟩
  unfold envSetSpec
  imodintro
  iintro %st %B %fa %x %v %e %pn %pv %s %saved %hsv
  unfold fnSpecW
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hr, hsp, hslot⟩, Ha0, Ha1, Ha2, Hsp, Hcl, Hsv, Hstk, #Hfa, #Hx, Hval, Hst⟩ Hk
  ihave ⟨Hst, %⟨-, hfalt, hinv⟩⟩ := storeRepr_frameInfo N $$ [Hst Hfa]
  · iframe Hst Hfa
  have hs64 : 64 ≤ s.toNat := by have := hsp.lo; unfold htifLo envGetNeed at this; omega
  have hset : ∀ a, ChainFrom st x fa a → st.set? fa x v = setAt st a x v := fun a h =>
    (set?_eq_setAt hinv.parents hfalt x v).trans (h.setAt hinv.parents)
  unfold valAt
  icases Hval with ⟨%fo, Hout, #Hv⟩
  ihave ⟨⟨Hout, Hstk⟩, %hdo⟩ := keep_pure (ownSet_off _ _ fo) $$ [Hout Hstk]
  · iframe Hout; unfold stackScratch blockOwn; iexact Hstk
  have hsep : pv.toNat + 24 ≤ s.toNat - 64 ∨ s.toNat ≤ pv.toNat := by
    have := interval_apart (a := pv.toNat) (n := 24) (b := s.toNat - envGetNeed)
      (m := envGetNeed) (by omega) (by unfold envGetNeed; omega) fun c h1 h2 => by
        have := hdo c
        unfold InExt at this; omega
    unfold envGetNeed at this; omega
  unfold envSetPC
  iapply scan_entry Wp (setSite live hl) N (fo := fo) hsv hr hsp hslot
  rw [show (setSite live hl).entry = 0x80002cdc#64 from rfl]
  iframe Ht Hgp Hcmp Hpc Hra Ha0 Ha1 Ha2 Hsp Hcl Hsv Hfa Hx Hout Hst
  isplitl [Hstk]
  · unfold stackScratch blockOwn; iexact Hstk
  isplit
  · -- `x` unbound on the chain: return 0, the store unchanged
    unfold scanMissK
    iintro %R' %Mt' %fa'' %f'' %⟨hret, hpath, hf, hmiss, hroot, hslotm⟩ Hpc HR HB Hst
    have hnone : st.set? fa x v = none := (hset fa'' hpath).trans (setAt_root hf hmiss hroot)
    dsimp only at hslotm
    ihave ⟨Hra, Ha0, Hsp, Hsv, Hcl⟩ := scan_exit_regs hsv hret $$ HR
    ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt') hs64 hsep $$ HB
    iapply Hk $$ Hpc Hra
    iexists 0#64
    iframe Ha0 Hsp Hcl Hsv
    isplitl [Hstk]
    · unfold stackScratch envGetNeed; iexact Hstk
    isplitl [Hout]
    · iexists (imgM Mt')
      iframe Hout
      rw [valImg_agree N v fun o ho => hslotm _ (by omega) (by omega)]
      iexact Hv
    unfold setOut
    rw [hnone]
    dsimp only
    iframe Hst
    ipureintro; rfl
  · -- the first match in frame `fa'`: write the value, return 1
    unfold scanHitK
    iintro %fa' %f %Gm %img %j %v0 %R %Mt %B₁ %B₂
      %⟨hpath, hf, hj, hne, hF, h8, hB, hinv', hlay, hdisj⟩ Hpc HR HS #Hb #Hp #HGe Hclose
    have hlt : j < f.vars.length := by
      rcases Nat.lt_or_ge j f.vars.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hj
    have hvj : f.vars[j] = (x, v0) := by simpa [List.getElem?_eq_getElem hlt] using hj
    have hfm : FirstMatch f.vars x v0 := firstMatch_of_index hj hne
    have hsome : st.set? fa x v = some (setStore st fa' x v) :=
      (hset fa' hpath).trans (setAt_hit hf hfm)
    have hfalt' : fa' < st.frames.size := by
      rcases Nat.lt_or_ge fa' st.frames.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at hf
    have hfa' : st.frames[fa'] = f := by simpa [Array.getElem?_eq_getElem hfalt'] using hf
    have hmap : f.vars.map (fun p => if p.1 == x then (x, v) else p) = f.vars.set j (x, v) :=
      map_replace_eq_set hj (by have := hinv'.unique fa' hfalt'; rwa [hfa'] at this)
    obtain ⟨hcap, hn1, hn2, hv1, hv2, hnw, hvw⟩ := hF.lay.slot hlt
    have hstkv : Gm.pv + 24 * j + 24 ≤ s.toNat - 64 ∨ s.toNat ≤ Gm.pv + 24 * j := by
      have := interval_apart (a := Gm.pv + 24 * j) (n := 24) (b := s.toNat - 64) (m := 64)
        (by omega) (by omega) fun c h1 h2 => by
          rcases Nat.lt_or_ge c (Gm.pv + 24 * j) with h | h
          · exact .inl h
          · rcases Nat.lt_or_ge c (Gm.pv + 24 * j + 24) with h' | h'
            · have := hF.sepStk c (by
                unfold frameS InExt; exact .inr ⟨hcap, .inr ⟨by omega, by omega⟩⟩)
              dsimp only at this; omega
            · exact .inr h'
      omega
    have hwo : 0x80000000 ≤ pv.toNat ∧ pv.toNat + 24 ≤ 0x100000000 ∧
        htifLo + 16 ≤ pv.toNat ∧ pv.toNat % 8 = 0 :=
      ⟨hslot.lo, hslot.hi, hslot.htif, hslot.align⟩
    have h21 : (R 21).toNat = pv.toNat := by rw [hF.out]
    rw [show (setSite live hl).hit = 0x80002d3c#64 from rfl]
    iapply wp_span Wp (set_hit hl (G := Gm) hsp.lo hsp.hi hr hF.stack hF.lay hlt h8 hF.env h21
      hwo hstkv)
    iframe Ht Hgp Hpc HR HS
    iintro %pc4 %R4 %Mt4 %⟨rfl, hret, hco⟩ Hpc HR HS
    -- the frame's bytes after the write
    have hwin : ∀ a, (a < Gm.pv + 24 * j ∨ Gm.pv + 24 * j + 24 ≤ a) → imgM Mt4 a = imgM Mt a :=
      hco.frame
    ihave ⟨HB, HF⟩ := get_split (img := imgM Mt4) hdisj (fun _ _ => rfl) $$ HS
    have hbl : Gm.blocks = [Gm.sblk, Gm.nblk, Gm.vblk] := by simp [FrameGeom.blocks, hcap]
    have hdis := hlay.disjoint
    rw [hbl] at hdis
    have hSV : ExtDisj Gm.sblk Gm.vblk := (List.pairwise_cons.1 hdis).1 _ (by simp)
    have hNV : ExtDisj Gm.nblk Gm.vblk :=
      (List.pairwise_cons.1 (List.pairwise_cons.1 hdis).2).1 _ (by simp)
    have hsb := hlay.sblk
    -- off the written window: the struct, the names, the other values
    have hoff : ∀ a, (InExt Gm.sblk a ∨ InExt Gm.nblk a) →
        (a < Gm.pv + 24 * j ∨ Gm.pv + 24 * j + 24 ≤ a) := fun a ha => by
      have hnotv : ¬ InExt Gm.vblk a := by
        rcases ha with ha | ha
        · exact hSV a ha
        · exact hNV a ha
      unfold InExt at hnotv
      omega
    have hstruct : ∀ a, Gm.e ≤ a → a < Gm.e + 32 → imgM Mt4 a = imgM Mt a := fun a h1 h2 =>
      hwin a (hoff a (.inl ⟨by omega, by omega⟩))
    have hnames : ∀ k, k < f.vars.length → ∀ o, o < 8 →
        imgM Mt4 (Gm.pn + 8 * k + o) = img (Gm.pn + 8 * k + o) := fun k hk o ho => by
      obtain ⟨-, hn1', hn2', -, -, -, -⟩ := hF.lay.slot hk
      rw [hwin _ (hoff _ (.inr ⟨by omega, by omega⟩))]
      exact hF.img _ (frameS_name hF.lay hk ho)
    have hvals : ∀ k, k < f.vars.length → k ≠ j → ∀ o, o < 24 →
        imgM Mt4 (Gm.pv + 24 * k + o) = img (Gm.pv + 24 * k + o) := fun k hk hkj o ho => by
      rw [hwin _ (by
        rcases Nat.lt_or_gt_of_ne hkj with h | h
        · left; omega
        · right; omega)]
      exact hF.img _ (frameS_val hF.lay hk ho)
    -- the value slot is off the written window
    have hww : Gm.pv + 24 * j + 24 ≤ pv.toNat ∨ pv.toNat + 24 ≤ Gm.pv + 24 * j := by
      have := interval_apart (a := pv.toNat) (n := 24) (b := Gm.pv + 24 * j) (m := 24)
        (by omega) (by omega) fun c h1 h2 => by
          have := hF.sepOut c (by
            unfold frameS InExt
            exact .inr ⟨hcap, .inr ⟨hv1 ▸ Nat.le_trans (Nat.le_add_right _ _) h1,
              Nat.lt_of_lt_of_le h2 hv2⟩⟩)
          exact this
      omega
    have hslotF : ∀ a, pv.toNat ≤ a → a < pv.toNat + 24 → imgM Mt a = fo a := hF.slot
    have hslotw : ∀ o, o < 24 → imgM Mt4 (pv.toNat + o) = fo (pv.toNat + o) := fun o ho =>
      (hwin _ (by omega)).trans (hslotF _ (by omega) (by omega))
    -- the written value's meaning
    have w : ∀ o, o + 8 ≤ 24 → ldv .ld Mt4 (Gm.pv + 24 * j + o) = ldv .ld Mt (pv.toNat + o) →
        imgW (imgM Mt4) (Gm.pv + 24 * j + o) = imgW fo (pv.toNat + o) := fun o ho h => by
      rw [← ldv_ld_img, h, ldv_ld_img]
      exact imgW_agree fun k hk => by
        exact hslotF (pv.toNat + o + k) (by omega) (by omega)
    have hnewv : valImg (GF := GF) N (imgM Mt4) (Gm.pv + 24 * j) v = valImg N fo pv.toNat v := by
      unfold valImg
      rw [show Gm.pv + 24 * j = Gm.pv + 24 * j + 0 from rfl, w 0 (by omega) hco.w0,
        w 8 (by omega) hco.w1, w 16 (by omega) hco.w2, Nat.add_zero]
    -- the frame after the write, and the store
    ihave #Hb' := bindings_set N (img := img) (img' := imgM Mt4) hlt (by rw [hvj]) hnames hvals
      $$ [Hb]
    · iframe Hb; rw [hnewv]; iexact Hv
    have hlay' : FrameLayout (imgM Mt4) Gm (f.vars.set j (x, v)).length := by
      rw [List.length_set]; exact hF.lay.congr_struct hstruct
    ihave Hst := Hclose $$ %(setStore st fa' x v) %{ f with vars := f.vars.set j (x, v) }
      %Gm.blocks %⟨rfl, by rw [setStore_frames_toList hf, hmap], hinv.set? hsome⟩ [HF]
    · unfold frameOwn frameBody
      iexists Gm
      iframe HGe
      isplitr
      · ipureintro; rfl
      iexists (imgM Mt4)
      iframe HF Hb' Hp
      ipureintro; exact hlay'
    rw [← hB]
    -- the return
    ihave ⟨Hra, Ha0, Hsp, Hsv, Hcl⟩ := scan_exit_regs hsv hret $$ HR
    ihave ⟨Hstk, Hout⟩ := scan_exit_bytes (Mt := Mt4) hs64 hsep $$ HB
    iapply Hk $$ Hpc Hra
    iexists 1#64
    iframe Ha0 Hsp Hcl Hsv
    isplitl [Hstk]
    · unfold stackScratch envGetNeed; iexact Hstk
    isplitl [Hout]
    · iexists (imgM Mt4)
      iframe Hout
      rw [valImg_agree N v hslotw]
      iexact Hv
    unfold setOut
    rw [hsome]
    dsimp only
    iframe Hst
    ipureintro; rfl

end Main

end VsaIris.Interp

#print axioms VsaIris.Interp.envSet_spec
