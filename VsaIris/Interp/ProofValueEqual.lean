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
    storeRepr N st B ∗ strcmpSpecV (vsaModel live) Wp ∗
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
  iintro ⟨⟨#Hwa, #Hwb, Hst, #Hcmp, Hk⟩, Hms⟩
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
  ix_run c.hlive using [h10, h11, hka, hkb]
  · intro _
    ix_run c.hlive
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
  ix_run c.hlive using [h10, h11, hka, hkb]
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
  ix_run c.hlive using [h10, h11, hka, hkb, hla, hlb]
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
  · ix_run c.hlive using [h10, h11, hka, hkb, hla, hlb]
    exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
      (by ix_reg; rw [seqz_sub, hres]) (by helper_keep)
  · ix_run c.hlive using [h10, h11, hka, hkb, hla, hlb]
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
  ix_run c.hlive using [h10, h11, hka, hkb, hla, hlb]
  exact veq_swp_close Wp c.hMa c.hMb c.hdab c.hdk c.hsg (by ix_reg)
    (by ix_reg; rw [seqz_sub, hres]) (by helper_keep)

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
    · sorry
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
