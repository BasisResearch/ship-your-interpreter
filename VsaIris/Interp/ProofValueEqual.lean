import VsaIris.Interp.HelperRun
import VsaIris.Interp.SpecValue

/-!
# `value_equal` (lane H2)

The kinds differ: `0`. Same kind: the jump table at `0x80019ef8` selects the
arm; `null` is `1`, `bool`/`int`/closure/native compare a payload word (a
closure by the store's address map, a native by its entry address), and a
string calls `strcmp` below a 16-byte frame.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- Two closures at one machine address are one closure: the store's
address map is injective (`StoreMaps.clos_inj`). The store is kept. -/
theorem storeRepr_clos_inj (N : NativeAddrs) {st : Store} {B : List (Nat × Nat)} {a b p : Nat} :
    storeRepr (GF := GF) N st B ∗ closAt a p ∗ closAt b p ⊢ storeRepr N st B ∗ ⌜a = b⌝ := by
  unfold storeRepr closAt
  iintro ⟨⟨%mf, %mc, %Bs, Hf, Hc, %hpure, Hfr, Hcl⟩, #Ha, #Hb⟩
  ihave %ha := ghost_map_lookup $$ Hc Ha
  ihave %hb := ghost_map_lookup $$ Hc Hb
  isplitl
  · iexists mf, mc, Bs
    iframe Hf Hc Hfr Hcl
    ipureintro; exact hpure
  · ipureintro; exact hpure.1.clos_inj a b p ha hb

/-- One instance of `strcmp`'s spec. -/
theorem strcmpSpecV_at {M : MachineModel} {Wp : MachWP (GF := GF) M} (p q : BitVec 64) (x y : String) :
    strcmpSpecV M Wp ⊢ helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(strAt p.toNat x ∗ strAt q.toNat y) (fun rv' => iprop(⌜rv' 10 = 0#64 ↔ x = y⌝)) := by
  unfold strcmpSpecV
  iintro #H
  iapply H

/-- The closure case of `value_equal`: the payload words are equal exactly
when the closures are. -/
def VeqClo : Value → Value → BitVec 64 → BitVec 64 → Prop
  | .closure ca, .closure cb, wa, wb => (wa = wb ↔ ca = cb)
  | _, _, _, _ => True

theorem veq_clo_facts (N : NativeAddrs) {st : Store} {B : List (Nat × Nat)}
    (fa fb : Nat → BitVec 8) (pa pb : Nat) (a b : Value) :
    storeRepr (GF := GF) N st B ∗ valImg N fa pa a ∗ valImg N fb pb b ⊢
      storeRepr N st B ∗ ⌜VeqClo a b (imgW fa (pa + 8)) (imgW fb (pb + 8))⌝ := by
  by_cases hcl : ∃ ca cb, a = .closure ca ∧ b = .closure cb
  case neg =>
    have hv : VeqClo a b (imgW fa (pa + 8)) (imgW fb (pb + 8)) := by
      cases a <;> cases b <;> simp_all [VeqClo]
    iintro ⟨H, -, -⟩
    iframe H
    ipureintro; exact hv
  obtain ⟨ca, cb, rfl, rfl⟩ := hcl
  unfold valImg valOf VeqClo
  iintro ⟨H, ⟨-, #Ha⟩, ⟨-, #Hb⟩⟩
  generalize imgW fa (pa + 8) = wa
  generalize imgW fb (pb + 8) = wb
  by_cases hw : wa = wb
  · subst hw
    ihave ⟨H, %h⟩ := storeRepr_clos_inj N (a := ca) (b := cb) (p := wa.toNat) $$ [H Ha Hb]
    · iframe H Ha Hb
    iframe H
    ipureintro; exact ⟨fun _ => h, fun _ => rfl⟩
  · iframe H
    by_cases hc : ca = cb
    · subst hc
      ihave %h := closAt_agree ca wa.toNat wb.toNat $$ [Ha Hb]
      · iframe Ha Hb
      ipureintro; exact absurd (BitVec.eq_of_toNat_eq h) hw
    · ipureintro; exact ⟨fun h => absurd h hw, fun h => absurd h hc⟩

/-- `sub; seqz`: `1` exactly when the two words are equal (`sltiu … 1` with
the immediate normalized). -/
theorem seqz_sub (x y : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (x - y) 1#64)) : BitVec 64) =
      if x = y then 1#64 else 0#64 := by
  have h := seqz_val (x - y)
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 by decide] at h
  rw [h]
  by_cases hxy : x = y
  · subst hxy; simp
  · have : (x - y == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h0; exact hxy (by rw [BitVec.sub_eq_iff_eq_add] at h0; simpa using h0)
    rw [this]; simp [hxy]

/-- The owned bytes of a `value_equal` run: the two slots and the frame. -/
abbrev veqS (pa pb s : BitVec 64) (x : Nat) : Prop :=
  (InExt (pa.toNat, 24) x ∨ InExt (pb.toNat, 24) x) ∨ InExt (s.toNat - 16, 16) x

/-- `ix_run`'s byte-set side conditions over `veqS`. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, veqS, VsaIris.InExt] at *; sx_addr))

/-- **`value_equal`'s return**, shared by its arms: at the return address,
the slots' bytes as they were, `a0` the result. -/
theorem veq_close (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {pa pb s r : BitVec 64} {a b : Value} {st : Store} {B : List (Nat × Nat)}
    {rv R : Nat → BitVec 64} {M Ma Mb : Mem}
    (h1 : R 1 = r) (h10 : R 10 = if Value.equal a b then 1#64 else 0#64)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → R x = rv x)
    (hA : ∀ x, InExt (pa.toNat, 24) x → imgM M x = imgM Ma x)
    (hB : ∀ x, InExt (pb.toNat, 24) x → imgM M x = imgM Mb x)
    (hdab : ∀ x, InExt (pa.toNat, 24) x → ¬ InExt (pb.toNat, 24) x)
    (hdk : ∀ x, (InExt (pa.toNat, 24) x ∨ InExt (pb.toNat, 24) x) → ¬ InExt (s.toNat - 16, 16) x)
    (hsg : StackGeom s 16) :
    ms r R (veqS pa pb s) M ∗ valImg (GF := GF) N (imgM Ma) pa.toNat a ∗
      valImg N (imgM Mb) pb.toNat b ∗ storeRepr N st B ∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
        (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
          (valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ storeRepr N st B ∗ stackAt s 16 ∗
            ⌜rv' 10 = if Value.equal a b then 1#64 else 0#64⌝)) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨⟨Hpc, Hra, Hregs, HS⟩, #Hwa, #Hwb, Hst, Hk⟩
  ihave ⟨HS, Hk16⟩ := ownSet_split_tracked _ _ M hdk $$ HS
  ihave ⟨HA, HB⟩ := ownSet_split_tracked _ _ M hdab $$ HS
  rw [h1]
  iapply Hk $$ Hpc Hra
  iexists R
  iframe Hregs Hst
  isplitr
  · ipureintro; exact hkeep
  isplitl [HA]
  · iapply valAt_of_img
    iframe Hwa
    iapply ownSet_congr (fun x hx => by rw [hA x hx]) $$ HA
  isplitl [HB]
  · iapply valAt_of_img
    iframe Hwb
    iapply ownSet_congr (fun x hx => by rw [hB x hx]) $$ HB
  isplitl [Hk16]
  · unfold stackAt stackScratch blockOwn
    isplitl
    · iapply ownSet_forget $$ Hk16
    · ipureintro; exact hsg
  · ipureintro; exact h10

/-- The frame of `value_equal`'s run: the values' meanings, the store, the
`strcmp` spec and the return continuation. -/
def Fveq (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (pa pb s r : BitVec 64) (a b : Value) (st : Store) (B : List (Nat × Nat)) (rv : Nat → BitVec 64)
    (Ma Mb : Mem) : IProp GF :=
  iprop(valImg N (imgM Ma) pa.toNat a ∗ valImg N (imgM Mb) pb.toNat b ∗
    storeRepr N st B ∗ strcmpSpecV (vsaModel live) Wp ∗ codeRes ∗
    (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
      (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = rv x⌝ ∗
        (valAt N pa.toNat a ∗ valAt N pb.toNat b ∗ storeRepr N st B ∗ stackAt s 16 ∗
          ⌜rv' 10 = if Value.equal a b then 1#64 else 0#64⌝)) -∗ Wp.W Φ))

/-- **Closing a `value_equal` run** at the return address. -/
theorem veq_swp_close (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {pa pb s r : BitVec 64} {a b : Value} {st : Store} {B : List (Nat × Nat)}
    {rv R : Nat → BitVec 64} {M Ma Mb : Mem}
    (hA : ∀ x, InExt (pa.toNat, 24) x → imgM M x = imgM Ma x)
    (hB : ∀ x, InExt (pb.toNat, 24) x → imgM M x = imgM Mb x)
    (hdab : ∀ x, InExt (pa.toNat, 24) x → ¬ InExt (pb.toNat, 24) x)
    (hdk : ∀ x, (InExt (pa.toNat, 24) x ∨ InExt (pb.toNat, 24) x) → ¬ InExt (s.toNat - 16, 16) x)
    (hsg : StackGeom s 16)
    (h1 : R 1 = r) (h10 : R 10 = if Value.equal a b then 1#64 else 0#64)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → R x = rv x) :
    IW live ∅ [] (veqS pa pb s) (RunK Wp Φ (Fveq Wp Φ N pa pb s r a b st B rv Ma Mb) (veqS pa pb s))
      r R M := by
  apply swp_closeF
  refine .trans ?_ (veq_close Wp (N := N) (st := st) (B := B) h1 h10 hkeep hA hB hdab hdk hsg)
  unfold Fveq
  iintro ⟨⟨#Hwa, #Hwb, Hst, #Hcmp, #Hcode, Hk⟩, Hms⟩
  iframe Hms Hwa Hwb Hst Hk

/-- The pure context of a `value_equal` run (named, CLAUDE.md law 6). -/
structure VeqCtx (live : Nat → Prop) (pa pb s r : BitVec 64) (rv : Nat → BitVec 64) (M Ma Mb : Mem) :
    Prop where
  hlive : ∀ p ∈ interpText, live p.1
  hal : r.toNat % 4 = 0
  h10 : rv 10 = pa
  h11 : rv 11 = pb
  h2 : rv 2 = s
  hga : SlotGeom pa
  hgb : SlotGeom pb
  hsg : StackGeom s 16
  hMa : ∀ x, InExt (pa.toNat, 24) x → imgM M x = imgM Ma x
  hMb : ∀ x, InExt (pb.toNat, 24) x → imgM M x = imgM Mb x
  hdab : ∀ x, InExt (pa.toNat, 24) x → ¬ InExt (pb.toNat, 24) x
  hdk : ∀ x, (InExt (pa.toNat, 24) x ∨ InExt (pb.toNat, 24) x) → ¬ InExt (s.toNat - 16, 16) x

namespace VeqCtx

variable {pa pb s r : BitVec 64} {rv : Nat → BitVec 64} {M Ma Mb : Mem}

theorem kindA (c : VeqCtx live pa pb s r rv M Ma Mb) {N : NativeAddrs} {a : Value}
    (hp : ValPure N a (imgW (imgM Ma) pa.toNat) (imgW (imgM Ma) (pa.toNat + 8))
      (imgW (imgM Ma) (pa.toNat + 16))) :
    ldv .lw M pa.toNat = BitVec.ofNat 64 (kindTag a) := by
  have := c.hga.hi
  refine ldv_lw_kind (by rw [imgW_agree (fun i hi => c.hMa _ (by simp [InExt]; omega))]; exact hp.kind)
    (by cases a <;> simp [kindTag])

theorem kindB (c : VeqCtx live pa pb s r rv M Ma Mb) {N : NativeAddrs} {b : Value}
    (hp : ValPure N b (imgW (imgM Mb) pb.toNat) (imgW (imgM Mb) (pb.toNat + 8))
      (imgW (imgM Mb) (pb.toNat + 16))) :
    ldv .lw M pb.toNat = BitVec.ofNat 64 (kindTag b) := by
  have := c.hgb.hi
  refine ldv_lw_kind (by rw [imgW_agree (fun i hi => c.hMb _ (by simp [InExt]; omega))]; exact hp.kind)
    (by cases b <;> simp [kindTag])

/-- A payload word of the first value, read through the run's memory. -/
theorem wordA (c : VeqCtx live pa pb s r rv M Ma Mb) (o : Nat) (ho : o ≤ 16) :
    imgW (imgM M) (pa + BitVec.ofNat 64 o).toNat = imgW (imgM Ma) (pa.toNat + o) := by
  have := c.hga.hi
  rw [show (pa + BitVec.ofNat 64 o).toNat = pa.toNat + o by
    rw [BitVec.toNat_add]; simp; omega]
  exact imgW_agree (fun i hi => c.hMa _ (by simp [InExt]; omega))

theorem wordB (c : VeqCtx live pa pb s r rv M Ma Mb) (o : Nat) (ho : o ≤ 16) :
    imgW (imgM M) (pb + BitVec.ofNat 64 o).toNat = imgW (imgM Mb) (pb.toNat + o) := by
  have := c.hgb.hi
  rw [show (pb + BitVec.ofNat 64 o).toNat = pb.toNat + o by
    rw [BitVec.toNat_add]; simp; omega]
  exact imgW_agree (fun i hi => c.hMb _ (by simp [InExt]; omega))

end VeqCtx

/-- The goal of a `value_equal` run. -/
abbrev VeqGoal (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (N : NativeAddrs)
    (pa pb s r : BitVec 64) (a b : Value) (st : Store) (B : List (Nat × Nat)) (rv : Nat → BitVec 64)
    (M Ma Mb : Mem) : Prop :=
  IW live ∅ [] (veqS pa pb s) (RunK Wp Φ (Fveq Wp Φ N pa pb s r a b st B rv Ma Mb) (veqS pa pb s))
    valueEqualPC (upd rv 1 r) M

section Arms

variable (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} {N : NativeAddrs}
  {pa pb s r : BitVec 64} {st : Store} {B : List (Nat × Nat)} {rv : Nat → BitVec 64} {M Ma Mb : Mem}

/-- The kinds differ: `0`. -/
theorem veq_ne (c : VeqCtx live pa pb s r rv M Ma Mb) {a b : Value}
    (hpa : ValPure N a (imgW (imgM Ma) pa.toNat) (imgW (imgM Ma) (pa.toNat + 8))
      (imgW (imgM Ma) (pa.toNat + 16)))
    (hpb : ValPure N b (imgW (imgM Mb) pb.toNat) (imgW (imgM Mb) (pb.toNat + 8))
      (imgW (imgM Mb) (pb.toNat + 16)))
    (hk : kindTag a ≠ kindTag b) : VeqGoal Wp Φ N pa pb s r a b st B rv M Ma Mb := by
  have hka := c.kindA hpa; have hkb := c.kindB hpb
  have h10 := c.h10; have h11 := c.h11; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  have hne : BitVec.ofNat 64 (kindTag b) ≠ BitVec.ofNat 64 (kindTag a) := by
    cases a <;> cases b <;> simp_all [kindTag]
  unfold VeqGoal valueEqualPC
  ix_run1 c.hlive using [h10, h11, hka, hkb]
  · intro _
    ix_run1 c.hlive
    exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
      (by ix_reg; rw [equal_false_of_kind_ne _ _ hk]; rfl) (by helper_keep)
  · intro hc; exfalso; apply hc; ix_reg; exact hne

/-- `null`: `1`. -/
theorem veq_null (c : VeqCtx live pa pb s r rv M Ma Mb)
    (hpa : ValPure N .null (imgW (imgM Ma) pa.toNat) (imgW (imgM Ma) (pa.toNat + 8))
      (imgW (imgM Ma) (pa.toNat + 16)))
    (hpb : ValPure N .null (imgW (imgM Mb) pb.toNat) (imgW (imgM Mb) (pb.toNat + 8))
      (imgW (imgM Mb) (pb.toNat + 16))) : VeqGoal Wp Φ N pa pb s r .null .null st B rv M Ma Mb := by
  have hka := c.kindA hpa; have hkb := c.kindB hpb
  simp only [kindTag] at hka hkb
  have h10 := c.h10; have h11 := c.h11; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  unfold VeqGoal valueEqualPC
  ix_run1 c.hlive using [h10, h11, hka, hkb]
  exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg) (by ix_reg; rfl) (by helper_keep)

/-- `bool`: the payloads' low words. -/
theorem veq_bool (c : VeqCtx live pa pb s r rv M Ma Mb) {b1 b2 : Bool}
    (hpa : ValPure N (.bool b1) (imgW (imgM Ma) pa.toNat) (imgW (imgM Ma) (pa.toNat + 8))
      (imgW (imgM Ma) (pa.toNat + 16)))
    (hpb : ValPure N (.bool b2) (imgW (imgM Mb) pb.toNat) (imgW (imgM Mb) (pb.toNat + 8))
      (imgW (imgM Mb) (pb.toNat + 16))) :
    VeqGoal Wp Φ N pa pb s r (.bool b1) (.bool b2) st B rv M Ma Mb := by
  have hka := c.kindA hpa; have hkb := c.kindB hpb
  simp only [kindTag] at hka hkb
  have hla := ldv_lw_kind (Mt := M) (a := (pa + 8#64).toNat) (k := cond b1 1 0)
    (by rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c.wordA 8 (by omega)]; exact hpa.2)
    (by cases b1 <;> decide)
  have hlb := ldv_lw_kind (Mt := M) (a := (pb + 8#64).toNat) (k := cond b2 1 0)
    (by rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c.wordB 8 (by omega)]; exact hpb.2)
    (by cases b2 <;> decide)
  have h10 := c.h10; have h11 := c.h11; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  unfold VeqGoal valueEqualPC
  ix_run1 c.hlive using [h10, h11, hka, hkb, hla, hlb]
  exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
    (by ix_reg; rw [seqz_sub]; cases b1 <;> cases b2 <;> decide) (by helper_keep)

/-- The word compare's result. -/
theorem veq_res {a b : Value} {wa wb : BitVec 64} (heq : wa = wb ↔ Value.equal a b = true) :
    (if wa = wb then 1#64 else 0#64) = if Value.equal a b then 1#64 else 0#64 := by
  by_cases h : wa = wb
  · simp only [h, heq.1 h, ite_true]
  · have h' : ¬ Value.equal a b = true := fun h' => h (heq.2 h')
    simp [h, h']

/-- A payload word compare at `0x80002894` (`int`, closure: kinds `2`, `4`). -/
theorem veq_word8 (c : VeqCtx live pa pb s r rv M Ma Mb) {a b : Value}
    (hka : ldv .lw M pa.toNat = BitVec.ofNat 64 (kindTag a))
    (hkb : ldv .lw M pb.toNat = BitVec.ofNat 64 (kindTag a))
    (harm : kindTag a = 2 ∨ kindTag a = 4)
    (heq : (imgW (imgM Ma) (pa.toNat + 8) = imgW (imgM Mb) (pb.toNat + 8)) ↔ Value.equal a b = true) :
    VeqGoal Wp Φ N pa pb s r a b st B rv M Ma Mb := by
  have hla := (ldv_ld_imgW M (pa + BitVec.ofNat 64 8).toNat).trans (c.wordA 8 (by omega))
  have hlb := (ldv_ld_imgW M (pb + BitVec.ofNat 64 8).toNat).trans (c.wordB 8 (by omega))
  have h10 := c.h10; have h11 := c.h11; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  have hres := veq_res heq
  generalize imgW (imgM Ma) (pa.toNat + 8) = wa at hla hres
  generalize imgW (imgM Mb) (pb.toNat + 8) = wb at hlb hres
  unfold VeqGoal valueEqualPC
  rcases harm with ht | ht <;> rw [ht] at hka hkb
  · ix_run1 c.hlive using [h10, h11, hka, hkb, hla, hlb]
    exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
      (by ix_reg; rw [seqz_sub, hres]) (by helper_keep)
  · ix_run1 c.hlive using [h10, h11, hka, hkb, hla, hlb]
    exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
      (by ix_reg; rw [seqz_sub, hres]) (by helper_keep)

/-- The native compare at `0x800028e8`: word 2, the entry address. -/
theorem veq_word16 (c : VeqCtx live pa pb s r rv M Ma Mb) {a b : Value}
    (hka : ldv .lw M pa.toNat = 5#64) (hkb : ldv .lw M pb.toNat = 5#64)
    (heq : (imgW (imgM Ma) (pa.toNat + 16) = imgW (imgM Mb) (pb.toNat + 16)) ↔
      Value.equal a b = true) :
    VeqGoal Wp Φ N pa pb s r a b st B rv M Ma Mb := by
  have hla := (ldv_ld_imgW M (pa + BitVec.ofNat 64 16).toNat).trans (c.wordA 16 (by omega))
  have hlb := (ldv_ld_imgW M (pb + BitVec.ofNat 64 16).toNat).trans (c.wordB 16 (by omega))
  have h10 := c.h10; have h11 := c.h11; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  have hres := veq_res heq
  generalize imgW (imgM Ma) (pa.toNat + 16) = wa at hla hres
  generalize imgW (imgM Mb) (pb.toNat + 16) = wb at hlb hres
  unfold VeqGoal valueEqualPC
  ix_run1 c.hlive using [h10, h11, hka, hkb, hla, hlb]
  exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
    (by ix_reg; rw [seqz_sub, hres]) (by helper_keep)

/-- The string arm after `strcmp` returns: restore `ra`, `seqz`, return. -/
theorem veq_str_run2 (c : VeqCtx live pa pb s r rv M Ma Mb) {x1 x2 : String} {R' : Nat → BitVec 64}
    (h2 : R' 2 = s + 18446744073709551600#64) (h10 : R' 10 = 0#64 ↔ x1 = x2)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → x ≠ 2 → R' x = rv x) :
    IW live ∅ [] (veqS pa pb s)
      (RunK Wp Φ (Fveq Wp Φ N pa pb s r (.str x1) (.str x2) st B rv Ma Mb) (veqS pa pb s))
      (BitVec.ofNat 64 (0x800028d4 + 4)) (upd R' 1 (BitVec.ofNat 64 (0x800028d4 + 4)))
      (writeLog M [((s + 18446744073709551600#64 + 8#64).toNat, 8, r)]) := by
  have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  have hs1 := c.hsg.le; have hs2 := c.hsg.lo; have hs3 := c.hsg.hi; have hs4 := c.hsg.al
  unfold Vsa.Sim.LayoutInstance.stackSL at hs2 hs3
  simp only at hs2 hs3
  have hsa : (s + 18446744073709551600#64).toNat = s.toNat - 16 := by
    rw [BitVec.toNat_add]; simp; omega
  have hsa8 : (s + 18446744073709551600#64 + 8#64).toNat = s.toNat - 8 := by
    rw [BitVec.toNat_add, hsa]; simp; omega
  have hsp : s + 18446744073709551600#64 + 16#64 = s := by
    rw [BitVec.add_assoc]; simp
  have hsd : ∀ x, (InExt (pa.toNat, 24) x ∨ InExt (pb.toNat, 24) x) →
      imgM (writeLog M [((s + 18446744073709551600#64 + 8#64).toNat, 8, r)]) x = imgM M x := by
    intro x hx
    have := c.hdk x hx
    simp only [InExt] at this hx
    exact imgM_store_miss _ _ (by rw [hsa8]; omega)
  ix_run1 c.hlive using [h2]
  refine veq_swp_close Wp (fun x hx => (hsd x (.inl hx)).trans (c.hMa x hx))
    (fun x hx => (hsd x (.inr hx)).trans (c.hMb x hx)) c.hdab c.hdk c.hsg (by ix_reg) ?_ ?_
  · ix_reg
    have e := seqz_sub (R' 10) 0#64
    rw [BitVec.sub_zero] at e
    rw [e]
    by_cases h : R' 10 = 0#64
    · simp [h, Value.equal, h10.1 h]
    · have : x1 ≠ x2 := fun h' => h (h10.2 h')
      simp [h, Value.equal, this]
  · intro x hx hc
    have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
    by_cases hx2 : x = 2
    · subst hx2; ix_reg; rw [hsp, c.h2]
    · simp only [upd, h1, hx2, ite_false]
      have h10' : x ≠ 10 := fun e => by subst e; exact hc (by decide)
      simp only [h10', ite_false]
      exact hkeep x hx hc hx2

/-- The string arm at `jal strcmp`: the call, then the rest of the run. -/
theorem veq_str_call (c : VeqCtx live pa pb s r rv M Ma Mb) {x1 x2 : String} {R1 : Nat → BitVec 64}
    (h10 : R1 10 = imgW (imgM Ma) (pa.toNat + 8)) (h11 : R1 11 = imgW (imgM Mb) (pb.toNat + 8))
    (h2 : R1 2 = s + 18446744073709551600#64)
    (hkeep : ∀ x ∈ fRegs, x ∉ callerSaved → x ≠ 2 → R1 x = rv x) :
    Fveq Wp Φ N pa pb s r (.str x1) (.str x2) st B rv Ma Mb ∗
      ms 0x800028d4#64 R1 (veqS pa pb s)
        (writeLog M [((s + 18446744073709551600#64 + 8#64).toNat, 8, r)]) ⊢ Wp.W Φ := by
  unfold Fveq
  iintro ⟨⟨#Hwa, #Hwb, Hst, #Hcmp, #Hcode, Hk⟩, Hms⟩
  ihave #Hxa := valImg_str $$ Hwa
  ihave #Hxb := valImg_str $$ Hwb
  ihave #Hsc := strcmpSpecV_at (imgW (imgM Ma) (pa.toNat + 8)) (imgW (imgM Mb) (pb.toNat + 8)) x1 x2
    $$ Hcmp
  iapply ms_callHelper Wp (i := 0x800028d4)
    (jalx_800028d4 live (fun p hp => c.hlive _ (interp_code_800028d4 p hp))) interp_code_800028d4
    (by decide) (clob := callerSaved)
    (pins := fun rv => rv 10 = imgW (imgM Ma) (pa.toNat + 8) ∧ rv 11 = imgW (imgM Mb) (pb.toNat + 8))
    (Pre := iprop(strAt (imgW (imgM Ma) (pa.toNat + 8)).toNat x1 ∗
      strAt (imgW (imgM Mb) (pb.toNat + 8)).toNat x2))
    (Post := fun rv' => iprop(⌜rv' 10 = 0#64 ↔ x1 = x2⌝))
  isplitl []
  · ipureintro; exact ⟨h10, h11⟩
  isplitl []
  · iexact Hsc
  iframe Hcode Hms
  isplitl []
  · iframe Hxa Hxb
  iintro %R' %hk' %hres Hms
  iapply wp_swpF Wp (S := veqS pa pb s)
    (F := Fveq Wp Φ N pa pb s r (.str x1) (.str x2) st B rv Ma Mb)
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    rw [hro]
    unfold Fveq
    iframe Hcode Hwa Hwb Hst Hcmp Hk Hms
  intro F'
  have hk2 : R' 2 = R1 2 := hk' 2 (by decide) (by decide)
  exact veq_str_run2 Wp c (hk2.trans h2) hres
    (fun x hx hc hx2 => (hk' x hx hc).trans (hkeep x hx hc hx2))

/-- The string arm: up to `jal strcmp`, then `veq_str_call`. -/
theorem veq_str (c : VeqCtx live pa pb s r rv M Ma Mb) {x1 x2 : String}
    (hka : ldv .lw M pa.toNat = 3#64) (hkb : ldv .lw M pb.toNat = 3#64) :
    VeqGoal Wp Φ N pa pb s r (.str x1) (.str x2) st B rv M Ma Mb := by
  have hla := (ldv_ld_imgW M (pa + BitVec.ofNat 64 8).toNat).trans (c.wordA 8 (by omega))
  have hlb := (ldv_ld_imgW M (pb + BitVec.ofNat 64 8).toNat).trans (c.wordB 8 (by omega))
  have h10 := c.h10; have h11 := c.h11; have h2 := c.h2; have hal := c.hal
  have ha1 := c.hga.al; have ha2 := c.hga.lo; have ha3 := c.hga.hi
  have hb1 := c.hgb.al; have hb2 := c.hgb.lo; have hb3 := c.hgb.hi
  have hs1 := c.hsg.le; have hs2 := c.hsg.lo; have hs3 := c.hsg.hi; have hs4 := c.hsg.al
  unfold Vsa.Sim.LayoutInstance.stackSL at hs2 hs3
  simp only at hs2 hs3
  unfold VeqGoal valueEqualPC
  ix_run1 c.hlive using [h10, h11, h2, hka, hkb, hla, hlb] at 0x800028d4
  apply swp_closeF
  refine veq_str_call Wp c (by ix_reg) (by ix_reg) (by ix_reg; try exact congrArg (· + _) h2) ?_
  intro x hx hc hx2
  have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hc
  simp only [upd]
  simp_all

end Arms

/-- **The run of `value_equal`**, by the kinds. -/
theorem veq_run (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF} {N : NativeAddrs}
    {pa pb s r : BitVec 64} {a b : Value} {st : Store} {B : List (Nat × Nat)} {rv : Nat → BitVec 64}
    {M Ma Mb : Mem} (c : VeqCtx live pa pb s r rv M Ma Mb)
    (hpa : ValPure N a (imgW (imgM Ma) pa.toNat) (imgW (imgM Ma) (pa.toNat + 8))
      (imgW (imgM Ma) (pa.toNat + 16)))
    (hpb : ValPure N b (imgW (imgM Mb) pb.toNat) (imgW (imgM Mb) (pb.toNat + 8))
      (imgW (imgM Mb) (pb.toNat + 16)))
    (hclo : VeqClo a b (imgW (imgM Ma) (pa.toNat + 8)) (imgW (imgM Mb) (pb.toNat + 8)))
    (hinj : NativeInj N) : VeqGoal Wp Φ N pa pb s r a b st B rv M Ma Mb := by
  by_cases hk : kindTag a = kindTag b
  · have hka := c.kindA hpa; have hkb := c.kindB hpb
    rcases a with _ | b1 | n1 | x1 | c1 | f1 <;> rcases b with _ | b2 | n2 | x2 | c2 | f2 <;>
      simp only [kindTag] at hk <;> (try omega)
    · exact veq_null Wp c hpa hpb
    · exact veq_bool Wp c hpa hpb
    · refine veq_word8 Wp c hka hkb (.inl rfl) ?_
      have e1 := hpa.2; have e2 := hpb.2
      constructor
      · intro h; rw [h] at e1; rw [← e1, ← e2]; simp [Value.equal]
      · intro h
        have : n1 = n2 := by simpa [Value.equal] using h
        subst this
        exact BitVec.eq_of_toInt_eq (by rw [e1, e2])
    · exact veq_str Wp c hka hkb
    · refine veq_word8 Wp c hka hkb (.inr rfl) ?_
      simp only [VeqClo] at hclo
      rw [hclo]; simp [Value.equal]
    · refine veq_word16 Wp c hka hkb ?_
      have e1 := hpa.2; have e2 := hpb.2
      constructor
      · intro h
        have : N.addr f1 = N.addr f2 := by rw [← e1, ← e2, h]
        rw [hinj f1 f2 this]; simp [Value.equal]
      · intro h
        have : f1 = f2 := by simpa [Value.equal] using h
        subst this
        exact BitVec.eq_of_toNat_eq (by rw [e1, e2])
  · exact veq_ne Wp c hpa hpb hk

/-- **`value_equal`**, for either WP. -/
theorem valueEqual_spec (hlive : ∀ p ∈ interpText, live p.1)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : NativeAddrs) (pa pb s : BitVec 64) (a b : Value)
    (st : Store) (B : List (Nat × Nat)) :
    ⊢ valueEqualSpec (vsaModel live) N Wp pa pb s a b st B := by
  unfold valueEqualSpec helperSpec fnSpecW
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %⟨h10, h11, h2⟩, #Hcode, Hva, Hvb, %⟨hga, hgb, hinj⟩,
    Hst, ⟨Hsk, %hsg⟩, #Hcmp⟩ Hk
  ihave ⟨%Ma, HA, #Hwa⟩ := valAt_tracked N _ a $$ Hva
  ihave ⟨%Mb, HB, #Hwb⟩ := valAt_tracked N _ b $$ Hvb
  ihave %hpa := valOf_pure N a _ _ _ $$ Hwa
  ihave %hpb := valOf_pure N b _ _ _ $$ Hwb
  unfold stackScratch blockOwn
  ihave ⟨%fk, Hsk⟩ := ownSet_fn _ $$ Hsk
  ihave ⟨%Mk, Hsk, %hMk⟩ := ownSet_trackedAt _ fk $$ Hsk
  ihave ⟨%M1, H1, %⟨h1a, h1b, hdab⟩⟩ := ownSet_join_tracked _ _ Ma Mb $$ [HA HB]
  · iframe HA HB
  ihave ⟨%M, HS, %⟨hM1, _, hdk⟩⟩ := ownSet_join_tracked _ _ M1 Mk $$ [H1 Hsk]
  · iframe H1 Hsk
  have hMa : ∀ x, InExt (pa.toNat, 24) x → imgM M x = imgM Ma x := fun x hx =>
    (hM1 x (.inl hx)).trans (h1a x hx)
  have hMb : ∀ x, InExt (pb.toNat, 24) x → imgM M x = imgM Mb x := fun x hx =>
    (hM1 x (.inr hx)).trans (h1b x hx)
  ihave ⟨Hst, %hclo⟩ := veq_clo_facts N (imgM Ma) (imgM Mb) pa.toNat pb.toNat a b $$ [Hst Hwa Hwb]
  · iframe Hst Hwa Hwb
  iapply wp_swpF Wp (S := veqS pa pb s) (R := upd rv 1 r) (Mt := M) (pc := valueEqualPC)
    (F := Fveq Wp Φ N pa pb s r a b st B rv Ma Mb)
  rotate_left
  · have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
      unfold codeRes; simp [dataOf]
    rw [hro]
    unfold ms Fveq
    rw [regFile_upd_ra]; simp only [upd_same]
    iframe Hcode Hwa Hwb Hst Hcmp Hk Hpc Hra Hregs HS
  intro F'
  exact veq_run Wp ⟨hlive, hal, h10, h11, h2, hga, hgb, hsg, hMa, hMb, hdab, hdk⟩ hpa hpb hclo hinj

end

end VsaIris.Interp
