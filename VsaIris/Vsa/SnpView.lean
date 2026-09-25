import VsaIris.Vsa.SnpSnprintf
import VsaIris.Vsa.StdioRead
import VsaIris.Vsa.BinImg
import VsaIris.Interp.Arm

/-!
# A `snprintf` run's read-only cells and boundary facts (lane N2)

`NW live Dt DA` reads the family's code (`snpText`, live) and a persistent
data view: `Dt` on the addresses `DA`. A hole's data view is a byte function
`f` on `DA` (`viewMem f DA`) whose bytes the caller holds read-only
(`sepL_view`): `.rodata` and `_impure_ptr` (`snpImg`: the format, `"."`,
the conversion table `TabAt`), and the `%s` argument's string.

newlib's data enters the run at a `StdioOK` image; the locale words
`_svfprintf_r` reads come from it as load values (`LocaleMt`, `localeMt_of`).
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib

/-! ## The code, from the binary's image -/

/-- Every byte of `snpText` is the fixed binary's `.text` byte. -/
theorem snpText_img :
    snpText.all (fun p => decide (textDom p.1) && textByte p.1 == p.2) = true := by
  decide +kernel

theorem snpText_img_mem : ∀ p ∈ snpText, textDom p.1 ∧ textByte p.1 = p.2 := by
  intro p hp
  have h := List.all_eq_true.1 snpText_img p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem snpText_live {live : Nat → Prop} (h : CodeLive live) : ∀ p ∈ snpText, live p.1 :=
  fun p hp => h _ (snpText_img_mem p hp).1

/-! ## Data views -/

/-- The data view holding `f` on `DA`. -/
def viewMem (f : Nat → BitVec 8) (DA : List Nat) : Mem := fillMem f DA

theorem imgM_viewMem {f : Nat → BitVec 8} {DA : List Nat} {a : Nat} (h : a ∈ DA) :
    imgM (viewMem f DA) a = f a := by
  unfold imgM viewMem
  rw [fillMem_get f h]
  rfl

/-- `.rodata` with `_impure_ptr`: the bytes every `snprintf` view reads
besides its `%s` strings. -/
def snpImg (a : Nat) : BitVec 8 := if impureW a then impureByte a else rodataByte a

/-- `_svfprintf_r`'s conversion table is the image's `.rodata`. -/
theorem rodata_tab : ∀ j, j < 364 → rodataByte (0x8001a0fc + j) = snpROImg (0x8001a0fc + j) := by
  decide +kernel

/-- The addresses every view holds: `"."`, the conversion table,
`_impure_ptr`. -/
def baseDA : List Nat := accAddrs 0x80019770 2 ++ accAddrs 0x8001a0fc 364 ++ accAddrs 0x8001b970 8

/-- A view holding `snpImg` on `baseDA` has `"."`, the table and `_impure_ptr`. -/
structure BaseView (Dt : Mem) (DA : List Nat) : Prop where
  dot : DotAt Dt DA
  tab : TabAt Dt DA
  imp : InDA DA 0x8001b970 0x8001b978

theorem baseView_of {f : Nat → BitVec 8} {DA : List Nat} (hsub : ∀ a ∈ baseDA, a ∈ DA)
    (hf : ∀ a ∈ baseDA, f a = snpImg a) : BaseView (viewMem f DA) DA := by
  have hm : ∀ lo w a, a ∈ accAddrs lo w → (lo = 0x80019770 ∧ w = 2 ∨ lo = 0x8001a0fc ∧ w = 364 ∨
      lo = 0x8001b970 ∧ w = 8) → a ∈ baseDA := fun lo w a ha hw => by
    unfold baseDA
    simp only [List.mem_append]
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (.inl ha)
    · exact .inl (.inr ha)
    · exact .inr ha
  have hv : ∀ a, a ∈ baseDA → imgM (viewMem f DA) a = snpImg a := fun a ha => by
    rw [imgM_viewMem (hsub a ha), hf a ha]
  refine ⟨⟨fun b h1 h2 => hsub b (hm _ 2 b (mem_accAddrs_iff.2 ⟨h1, h2⟩) (.inl ⟨rfl, rfl⟩)), ?_, ?_⟩,
    ⟨fun b h1 h2 => hsub b (hm _ 364 b (mem_accAddrs_iff.2 ⟨h1, h2⟩) (.inr (.inl ⟨rfl, rfl⟩))), ?_⟩,
    fun b h1 h2 => hsub b (hm _ 8 b (mem_accAddrs_iff.2 ⟨h1, h2⟩) (.inr (.inr ⟨rfl, rfl⟩)))⟩
  · rw [hv _ (hm _ 2 _ (mem_accAddrs_iff.2 ⟨by decide, by decide⟩) (.inl ⟨rfl, rfl⟩))]; decide
  · rw [hv _ (hm _ 2 _ (mem_accAddrs_iff.2 ⟨by decide, by decide⟩) (.inl ⟨rfl, rfl⟩))]; decide
  · intro a h1 h2
    rw [hv _ (hm _ 364 _ (mem_accAddrs_iff.2 ⟨h1, h2⟩) (.inr (.inl ⟨rfl, rfl⟩)))]
    unfold snpImg
    rw [if_neg (show ¬ impureW a by unfold impureW; omega)]
    have := rodata_tab (a - 0x8001a0fc) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **A data view from read-only bytes**: every listed address's byte of `f`
is read-only under `P`. -/
theorem sepL_view (P : IProp GF) [Persistent P] (f : Nat → BitVec 8) (DA : List Nat) :
    ∀ l : List Nat, (∀ a ∈ l, a ∈ DA) → (∀ a ∈ l, P ⊢ a ↦ₘ□ f a) →
      P ⊢ sepL (l.map fun a => (a, imgM (viewMem f DA) a)) (fun p => p.1 ↦ₘ□ p.2)
  | [], _, _ => by iintro _; simp only [List.map_nil, sepL_nil]; iempintro
  | a :: l, hs, hb => by
    simp only [List.map_cons, sepL_cons]
    iintro #H
    isplitl []
    · rw [imgM_viewMem (hs a List.mem_cons_self)]
      iapply hb a List.mem_cons_self $$ H
    · iapply sepL_view P f DA l (fun b h => hs b (List.mem_cons_of_mem _ h))
        (fun b h => hb b (List.mem_cons_of_mem _ h)) $$ H

/-- One image byte, read-only. -/
theorem snpBin_byte {a : Nat} {b : BitVec 8}
    (h : (textDom a ∧ textByte a = b) ∨ (rodataDom a ∧ rodataByte a = b)) :
    binImg (GF := GF) ⊢ a ↦ₘ□ b := by
  unfold binImg roImg
  iintro ⟨#Ht, #Hr⟩
  rcases h with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · iapply Ht $$ %a %hd
  · iapply Hr $$ %a %hd

/-- `.text` bytes of a list, read-only. -/
theorem snpBin_text : ∀ l : List (Nat × BitVec 8), (∀ p ∈ l, textDom p.1 ∧ textByte p.1 = p.2) →
    binImg (GF := GF) ⊢ sepL l (fun p => p.1 ↦ₘ□ p.2)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | q :: l, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl
    · iapply snpBin_byte (.inl (h q List.mem_cons_self)) $$ H
    · iapply snpBin_text l (fun p hp => h p (List.mem_cons_of_mem _ hp)) $$ H

/-- One byte of `snpImg`, read-only from the image and `_impure_ptr`. -/
theorem snpImg_byte {a : Nat} (h : impureW a ∨ rodataDom a) :
    iprop(binImg ∗ impureRO) ⊢@{IProp GF} a ↦ₘ□ snpImg a := by
  iintro ⟨#Hb, #Hi⟩
  unfold snpImg
  by_cases hi : impureW a
  · simp only [hi, ↓reduceIte]; iapply impureRO_byte hi $$ Hi
  · simp only [hi, ↓reduceIte]
    iapply snpBin_byte (.inr ⟨h.resolve_left hi, rfl⟩) $$ Hb

/-- **The run's read-only cells**: `gp`, the code, and a data view. -/
theorem roOwn_snp (P : IProp GF) [Persistent P] (f : Nat → BitVec 8) (DA : List Nat)
    (hv : P ⊢ sepL (dataOf (viewMem f DA) DA) (fun p => p.1 ↦ₘ□ p.2)) :
    iprop(gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ P) ⊢@{IProp GF}
      roOwn roR (snpText ++ dataOf (viewMem f DA) DA) := by
  unfold roOwn
  iintro ⟨#Hgp, #Himg, #HP⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply snpBin_text snpText snpText_img_mem $$ Himg
  · iapply hv $$ HP

end Own

/-! ## The locale at the boundary -/

/-- The locale words `_svfprintf_r` reads, as load values. -/
structure LocaleMt (Mt : Mem) : Prop where
  mbtowc : ldv .ld Mt 0x8001b880 = 0x80012268#64
  mbMax : ldv .lbu Mt 0x8001b8f8 = 1#64
  decPoint : ldv .ld Mt 0x8001b898 = 0x80019770#64

theorem locale_imgLE {img : Nat → BitVec 8} {Mt : Mem}
    (hM : ∀ a, stdioExcl a → imgM Mt a = img a) {a n v : Nat}
    (hr : readLE (fillMem img dataList) a n = some v)
    (hin : ∀ i, i < n → stdioExcl (a + i)) : imgLE (imgM Mt) a n = v := by
  have h := readLE_memImg hr
  rw [← h]
  refine imgLE_congr fun i hi => ?_
  rw [hM _ (hin i hi)]
  unfold memImg
  rw [fillMem_get img (mem_dataList (hin i hi).1)]
  rfl

/-- **The C locale at the boundary, as loads.** -/
theorem localeMt_of {img : Nat → BitVec 8} (h : StdioOK img) {Mt : Mem}
    (hM : ∀ a, stdioExcl a → imgM Mt a = img a) : LocaleMt Mt := by
  obtain ⟨_, _, _, hL⟩ := h.facts
  have F : ∀ a n, 0x8001b53c ≤ a → a + n ≤ 0x8001b960 → ∀ i, i < n → stdioExcl (a + i) := by
    intro a n h1 h2 i hi; unfold stdioExcl stdioFoot InRange impureW; omega
  refine ⟨ldvf_ld_imgLE (locale_imgLE hM hL.mbtowc (F _ _ (by decide) (by decide))), ?_,
    ldvf_ld_imgLE (locale_imgLE hM hL.decPoint (F _ _ (by decide) (by decide)))⟩
  have h1 := locale_imgLE hM hL.mbMax (F _ _ (by decide) (by decide))
  simp only [imgLE, Nat.mul_zero, Nat.add_zero, localeMbMaxAddr] at h1
  show BitVec.zeroExtend 64 (imgM Mt 0x8001b8f8) = 1#64
  rw [show imgM Mt 0x8001b8f8 = 1#8 from BitVec.eq_of_toNat_eq (by simpa using h1)]
  rfl

/-- The locale words survive a run that keeps newlib's data. -/
theorem LocaleMt.transport {Mt Mt' : Mem} (h : LocaleMt Mt)
    (hf : ∀ a, 0x8001b880 ≤ a → a < 0x8001b900 → imgM Mt' a = imgM Mt a) : LocaleMt Mt' where
  mbtowc := (ldv_agree .ld fun i hi => hf _ (by omega) (by simp only [widthOfM] at hi; omega)).trans h.mbtowc
  mbMax := (ldv_agree .lbu fun i hi => hf _ (by omega) (by simp only [widthOfM] at hi; omega)).trans h.mbMax
  decPoint := (ldv_agree .ld fun i hi => hf _ (by omega) (by simp only [widthOfM] at hi; omega)).trans h.decPoint

/-! ## Rendered integers are C strings -/

theorem natDigits_digit : ∀ (fuel n : Nat), ∀ c ∈ Vsa.While.natDigits fuel n,
    48 ≤ c.toNat ∧ c.toNat ≤ 57
  | 0, _ => by simp [Vsa.While.natDigits]
  | fuel + 1, n => by
    have hd : ∀ k, k < 10 → 48 ≤ (Nat.digitChar k).toNat ∧ (Nat.digitChar k).toNat ≤ 57 := by decide
    unfold Vsa.While.natDigits
    split
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc; exact hd n (by omega)
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact natDigits_digit fuel (n / 10) c hc
      · simp only [List.mem_singleton] at hc
        subst hc; exact hd _ (Nat.mod_lt _ (by decide))

/-- Every character of a rendered integer is `'-'` or a digit. -/
theorem intToString_ascii (v : BitVec 64) :
    ∀ c ∈ (Vsa.While.intToString v.toInt).toList, 0 < c.toNat ∧ c.toNat < 128 := by
  intro c hc
  rw [Vsa.Sim.intToString_of_bv v] at hc
  have hn : ∀ m, c ∈ (Vsa.While.natToString m).toList → 0 < c.toNat ∧ c.toNat < 128 := fun m hm => by
    rw [Vsa.Sim.natToString_toList_39] at hm
    have := natDigits_digit _ _ c hm
    omega
  split at hc
  · rw [String.toList_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have : c = '-' := by simpa using hc
      subst this; decide
    · exact hn _ hc
  · exact hn _ hc

/-- A C string in an image from its rendered bytes and a NUL. -/
theorem cstrImg_of_bytes {img : Nat → BitVec 8} {p : Nat} {x : String}
    (hA : ∀ c ∈ x.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hb : ∀ i, i < (strBytes x).length → img (p + i) = (strBytes x).getD i 0)
    (hz : img (p + (strBytes x).length) = 0) : CStrImg img p x := by
  have hl : (strBytes x).length = x.toList.length := by simp [strBytes]
  refine ⟨fun i h => ⟨?_, hA _ (List.getElem_mem h)⟩, by rw [← hl]; exact hz⟩
  rw [hb i (by omega)]
  simp [strBytes, List.getD_eq_getElem?_getD, h]

end VsaIris.Sym
