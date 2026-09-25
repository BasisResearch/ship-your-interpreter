import VsaIris.Vsa.SnpHoles
import VsaIris.Vsa.SnpFmt

/-!
# `snprintf` on any `%s`/`%d` format (lane N2)

`snprintf_gen` is H5's `newlib.snprintf` statement proved for a stack and a
destination above newlib's data and readable bytes in RAM off the HTIF words
(`ReadGeom`), with a 4-aligned return address. The run reads the format and
every `%s` argument (`readL`) through its data view: the read-only ones from
`roImg Sro rd`, the owned ones promoted (`snpSpec_of_runO`). RAM bounds each
string below `2^27` bytes, so the rendering stays below `2^31`
(`fmtRen_length_le`), which `_svfprintf_r`'s 32-bit count needs.
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open VsaIris.Inst

/-! ## Readable bytes -/

/-- Readable bytes lie in RAM with a string routine's 8-byte read window off
the HTIF words. -/
def ReadGeom (R : Nat → Prop) : Prop :=
  ∀ a, R a → 0x80000000 ≤ a ∧ a + 8 ≤ 0x88000000 ∧ (a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a)

/-- A run of readable bytes has a string routine's window. -/
theorem readGeom_win {R : Nat → Prop} (hg : ReadGeom R) {p len : Nat}
    (h : ∀ i, i ≤ len → R (p + i)) :
    0x80000000 ≤ p ∧ p + len + 8 ≤ 0x88000000 ∧ (p + len + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ p) := by
  obtain ⟨h0, -, h0h⟩ := hg p (by simpa using h 0 (Nat.zero_le _))
  obtain ⟨-, hl, -⟩ := hg (p + len) (h len (Nat.le_refl _))
  refine ⟨h0, hl, ?_⟩
  rcases h0h with h0h | h0h
  · if hc : p + len + 8 ≤ 0x8001ad00 then exact .inl hc
    else
      obtain ⟨-, -, hb⟩ := hg (p + (0x8001acf9 - p)) (h _ (by omega))
      omega
  · exact .inr h0h

/-- The `%s` argument `i`'s string, when there is one. -/
noncomputable def strT (R : Nat → Prop) (rd : Nat → BitVec 8) (args : List (BitVec 64)) (i : Nat) :
    List (BitVec 8) :=
  open Classical in
  if h : ∃ t, CStrCov R rd (args.getD i 0).toNat t then Classical.choose h else []

theorem strT_spec {R : Nat → Prop} {rd : Nat → BitVec 8} {args : List (BitVec 64)} {i : Nat}
    (h : ∃ t, CStrCov R rd (args.getD i 0).toNat t) : CStrCov R rd (args.getD i 0).toNat (strT R rd args i) := by
  unfold strT
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The bytes a format's run reads besides `baseDA`: the format with its NUL,
each `%s` argument's string with its NUL. -/
noncomputable def readL (R : Nat → Prop) (rd : Nat → BitVec 8) (fmt : Nat) (bytes : List (BitVec 8))
    (convs : List Conv) (args : List (BitVec 64)) : List Nat :=
  accAddrs fmt (bytes.length + 1) ++ (List.range convs.length).flatMap fun i =>
    if convs[i]? = some .str then accAddrs (args.getD i 0).toNat ((strT R rd args i).length + 1) else []

theorem mem_readL {R : Nat → Prop} {rd : Nat → BitVec 8} {fmt : Nat} {bytes : List (BitVec 8)}
    {convs : List Conv} {args : List (BitVec 64)} {a : Nat} :
    a ∈ readL R rd fmt bytes convs args ↔ (fmt ≤ a ∧ a < fmt + bytes.length + 1) ∨
      ∃ i, i < convs.length ∧ convs[i]? = some .str ∧ (args.getD i 0).toNat ≤ a ∧
        a < (args.getD i 0).toNat + (strT R rd args i).length + 1 := by
  unfold readL
  simp only [List.mem_append, mem_accAddrs_iff, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (h | ⟨i, hi, hm⟩)
    · exact .inl ⟨h.1, by omega⟩
    · split at hm
      · rw [mem_accAddrs_iff] at hm; exact .inr ⟨i, hi, by assumption, hm.1, by omega⟩
      · simp at hm
  · rintro (h | ⟨i, hi, hc, h1, h2⟩)
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr ⟨i, hi, by rw [if_pos hc, mem_accAddrs_iff]; omega⟩

/-- Every byte the run reads is readable. -/
theorem readL_R {R : Nat → Prop} {rd : Nat → BitVec 8} {fmt : BitVec 64} {args : List (BitVec 64)}
    {bytes : List (BitVec 8)} {convs : List Conv} (FA : FmtArgsAt R rd fmt args bytes convs) {a : Nat}
    (ha : a ∈ readL R rd fmt.toNat bytes convs args) : R a := by
  rcases mem_readL.1 ha with ⟨h1, h2⟩ | ⟨i, hi, hc, h1, h2⟩
  · obtain ⟨j, rfl⟩ : ∃ j, a = fmt.toNat + j := ⟨a - fmt.toNat, by omega⟩
    rcases Nat.lt_or_ge j bytes.length with hj | hj
    · exact (FA.fmt_str.bytes j hj).1
    · rw [show j = bytes.length by omega]; exact FA.fmt_str.nul.1
  · have hs := strT_spec (R := R) (rd := rd) (i := i) (by
      have hc' : convs[i] = .str := by simpa [List.getElem?_eq_getElem hi] using hc
      obtain ⟨t, ht⟩ := FA.strs i hi hc'
      exact ⟨t, by rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (Nat.lt_of_lt_of_le hi FA.arity)]⟩)
    obtain ⟨j, rfl⟩ : ∃ j, a = (args.getD i 0).toNat + j := ⟨a - (args.getD i 0).toNat, by omega⟩
    rcases Nat.lt_or_ge j (strT R rd args i).length with hj | hj
    · exact (hs.bytes j hj).1
    · rw [show j = (strT R rd args i).length by omega]; exact hs.nul.1

/-! ## The view -/

/-- The view's image: the readable bytes on the read list, `.rodata` and
`_impure_ptr` elsewhere. -/
noncomputable def genImg (L : List Nat) (rd : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if a ∈ L then rd a else snpImg a

open Classical in
/-- The read-only part of the view: the base and the read list, less the owned
read bytes. -/
noncomputable def genRO (L : List Nat) (Sown : Nat → Prop) : List Nat :=
  (baseDA ++ L).filter fun a => ¬ (a ∈ L ∧ Sown a)

open Classical in
/-- The owned read bytes. -/
noncomputable def genOwn (L : List Nat) (Sown : Nat → Prop) : List Nat := L.filter fun a => Sown a

theorem mem_genRO {L : List Nat} {Sown : Nat → Prop} {a : Nat} :
    a ∈ genRO L Sown ↔ (a ∈ baseDA ∨ a ∈ L) ∧ ¬ (a ∈ L ∧ Sown a) := by
  classical
  unfold genRO
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]

theorem mem_genOwn {L : List Nat} {Sown : Nat → Prop} {a : Nat} :
    a ∈ genOwn L Sown ↔ a ∈ L ∧ Sown a := by
  classical
  unfold genOwn
  simp [List.mem_filter]

theorem mem_genDA {L : List Nat} {Sown : Nat → Prop} {a : Nat} :
    a ∈ genRO L Sown ++ genOwn L Sown ↔ a ∈ baseDA ∨ a ∈ L := by
  rw [List.mem_append, mem_genRO, mem_genOwn]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    · exact .inr h
  · intro h
    by_cases h' : a ∈ L ∧ Sown a
    · exact .inr h'
    · exact .inl ⟨h, h'⟩

theorem genView_read {L : List Nat} {Sown : Nat → Prop} {rd : Nat → BitVec 8} {a : Nat} (h : a ∈ L) :
    imgM (viewMem (genImg L rd) (genRO L Sown ++ genOwn L Sown)) a = rd a := by
  rw [imgM_viewMem (mem_genDA.2 (.inr h))]
  unfold genImg
  rw [if_pos h]


theorem base_byte {a : Nat} (h : a ∈ baseDA) : impureW a ∨ rodataDom a := by
  simp only [baseDA, List.mem_append, mem_accAddrs_iff] at h
  unfold impureW rodataDom
  omega

theorem genImg_base {L : List Nat} {rd : Nat → BitVec 8} (hag : ∀ a ∈ baseDA, a ∈ L → rd a = snpImg a)
    {a : Nat} (h : a ∈ baseDA) : genImg L rd a = snpImg a := by
  unfold genImg
  by_cases hL : a ∈ L
  · rw [if_pos hL]; exact hag a h hL
  · rw [if_neg hL]

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A list of read-only bytes of a byte function. -/
theorem sepL_map_ro (P : IProp GF) [Persistent P] (f : Nat → BitVec 8) :
    ∀ l : List Nat, (∀ a ∈ l, P ⊢ a ↦ₘ□ f a) → P ⊢ sepL (l.map fun a => (a, f a)) (fun p => p.1 ↦ₘ□ p.2)
  | [], _ => by iintro _; simp only [List.map_nil, sepL_nil]; iempintro
  | a :: l, hb => by
    simp only [List.map_cons, sepL_cons]
    iintro #H
    isplitl []
    · iapply hb a List.mem_cons_self $$ H
    · iapply sepL_map_ro P f l (fun b h => hb b (List.mem_cons_of_mem _ h)) $$ H

/-- Read-only bytes agree with the image where the base holds them. -/
theorem base_agree (Sro : Nat → Prop) (rd : Nat → BitVec 8) :
    iprop(roImg Sro rd ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      ⌜∀ a, a ∈ baseDA → Sro a → rd a = snpImg a⌝ := by
  iintro ⟨#Hr, #Hb, #Hi⟩
  iintro %a %h1 %h2
  unfold roImg
  ihave #Ha := Hr $$ %a %h2
  ihave #Hs := snpImg_byte (base_byte h1) $$ [Hb Hi]
  · iframe Hb Hi
  ihave %e := snpRO_agree a (rd a) (snpImg a) $$ [Ha Hs]
  · iframe Ha Hs
  ipureintro; exact e

/-- One read-only byte of the view. -/
theorem genView_byte (L : List Nat) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8)
    (hL : ∀ a ∈ L, Sro a ∨ Sown a) {a : Nat} (ha : a ∈ genRO L Sown) :
    iprop(roImg Sro rd ∗ binImg ∗ impureRO) ⊢@{IProp GF} a ↦ₘ□ genImg L rd a := by
  obtain ⟨hm, hno⟩ := mem_genRO.1 ha
  unfold genImg
  by_cases hl : a ∈ L
  · rw [if_pos hl]
    have hs : Sro a := (hL a hl).resolve_right fun h => hno ⟨hl, h⟩
    iintro ⟨#Hr, -, -⟩
    unfold roImg
    iapply Hr $$ %a %hs
  · rw [if_neg hl]
    iintro ⟨-, #Hb, #Hi⟩
    iapply snpImg_byte (base_byte (hm.resolve_right hl)) $$ [Hb Hi]
    iframe Hb Hi

/-- **The readable input as the run's view**: the read-only part of the read
list and the base as persistent bytes, the owned read bytes apart, and a wand
giving the input back. -/
theorem genData (L : List Nat) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8)
    (hL : ∀ a ∈ L, Sro a ∨ Sown a) :
    iprop(readable Sro Sown rd ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      ∃ _ : Unit, sepL (dataOf (viewMem (genImg L rd) (genRO L Sown ++ genOwn L Sown)) (genRO L Sown))
          (fun p => p.1 ↦ₘ□ p.2) ∗
        ownSet (fun a => Sown a ∧ a ∈ L) (fun a => a ↦ₘ genImg L rd a) ∗
        ⌜(∀ a ∈ baseDA, a ∈ L → rd a = snpImg a) ∧ ∀ a, (Sown a ∧ a ∈ L) ↔ a ∈ genOwn L Sown⌝ ∗
        (ownSet (fun a => Sown a ∧ a ∈ L) (fun a => a ↦ₘ genImg L rd a) -∗ readable Sro Sown rd) := by
  classical
  unfold readable
  iintro ⟨⟨#Hro, Hown⟩, #Hb, #Hi⟩
  ihave ⟨⟨Hown, -⟩, %hbo⟩ := keep_pure (ownSet_ro_off Sown rd (baseDA.map fun a => (a, snpImg a)))
    $$ [Hown]
  · iframe Hown
    iapply sepL_map_ro (iprop(binImg ∗ impureRO)) snpImg baseDA
      (fun a ha => snpImg_byte (base_byte ha)) $$ [Hb Hi]
    iframe Hb Hi
  ihave %hag := base_agree Sro rd $$ [Hro Hb Hi]
  · iframe Hro Hb Hi
  have hag' : ∀ a ∈ baseDA, a ∈ L → rd a = snpImg a := fun a ha hl => by
    rcases hL a hl with h | h
    · exact hag a ha h
    · exact absurd h (hbo (a, snpImg a) (List.mem_map_of_mem (f := fun a => (a, snpImg a)) ha))
  ihave ⟨H1, H2⟩ := ownSet_split Sown (fun a => a ∈ L) _ $$ Hown
  iexists ()
  isplitl []
  · iapply sepL_view (iprop(roImg Sro rd ∗ binImg ∗ impureRO)) (genImg L rd) _ _
      (fun a h => List.mem_append_left _ h) (fun a ha => genView_byte L Sro Sown rd hL ha)
    iframe Hro Hb Hi
  isplitl [H1]
  · iapply ownSet_congr (fun a (ha : Sown a ∧ a ∈ L) => by simp only [genImg, if_pos ha.2]) $$ H1
  isplitr
  · ipureintro
    exact ⟨hag', fun a => by rw [mem_genOwn]; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩⟩
  iintro H1
  isplitl []
  · iexact Hro
  ihave H1 := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ rd a))
    (fun a (ha : Sown a ∧ a ∈ L) => by simp only [genImg, if_pos ha.2]) $$ H1
  ihave H := ownSet_join _ _ _ (fun a (h1 : Sown a ∧ a ∈ L) (h2 : Sown a ∧ ¬ a ∈ L) => h2.2 h1.2) $$ [H1 H2]
  · iframe H1 H2
  iapply ownSet_iff _ (fun a => ⟨fun h => h.elim (·.1) (·.1),
    fun h => if hl : a ∈ L then .inl ⟨h, hl⟩ else .inr ⟨h, hl⟩⟩) $$ H

end Own


/-- A `%s` argument's string, as the run's view reads it. -/
theorem genDStr {R : Nat → Prop} {rd : Nat → BitVec 8} {fmt : BitVec 64} {args : List (BitVec 64)}
    {bytes : List (BitVec 8)} {convs : List Conv} {Sown : Nat → Prop} (FA : FmtArgsAt R rd fmt args bytes convs)
    (hg : ReadGeom R) {i : Nat} (hi : i < convs.length) (hia : i < args.length) (hc : convs[i] = .str) :
    DStr (viewMem (genImg (readL R rd fmt.toNat bytes convs args) rd)
        (genRO (readL R rd fmt.toNat bytes convs args) Sown ++ genOwn (readL R rd fmt.toNat bytes convs args) Sown))
      (genRO (readL R rd fmt.toNat bytes convs args) Sown ++ genOwn (readL R rd fmt.toNat bytes convs args) Sown)
      (args[i]).toNat (strT R rd args i).length ∧ (strT R rd args i).length < 2 ^ 27 := by
  have hgd : args.getD i 0 = args[i] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia]; rfl
  have hs := strT_spec (R := R) (rd := rd) (i := i) (by
    obtain ⟨t, ht⟩ := FA.strs i hi hc
    exact ⟨t, by rwa [hgd]⟩)
  rw [hgd] at hs
  have hin : ∀ j, j ≤ (strT R rd args i).length →
      (args[i]).toNat + j ∈ readL R rd fmt.toNat bytes convs args := fun j hj =>
    mem_readL.2 (.inr ⟨i, hi, by simp [List.getElem?_eq_getElem hi, hc], by rw [hgd]; omega,
      by rw [hgd]; omega⟩)
  have hR : ∀ j, j ≤ (strT R rd args i).length → R ((args[i]).toNat + j) := fun j hj => by
    rcases Nat.lt_or_ge j (strT R rd args i).length with h | h
    · exact (hs.bytes j h).1
    · rw [show j = (strT R rd args i).length by omega]; exact hs.nul.1
  obtain ⟨hlo, hhi, hht⟩ := readGeom_win hg hR
  refine ⟨⟨fun b h1 h2 => mem_genDA.2 (.inr (by
      have := hin (b - (args[i]).toNat) (by omega); rwa [Nat.add_sub_cancel' h1] at this)),
    fun j hj => by rw [genView_read (hin j (by omega)), (hs.bytes j hj).2.1]; exact (hs.bytes j hj).2.2,
    by rw [genView_read (hin _ (Nat.le_refl _))]; exact hs.nul.2, hlo, by omega, by omega⟩, by omega⟩

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`newlib.snprintf`**: `snprintf(dst, n, fmt, args…)` with a `%s`/`%d`
format writes a NUL-terminated string into `dst[0, n)`, keeps the readable
bytes and newlib's data, for a 4-aligned return address, a stack and a
destination above newlib's data, and readable bytes in RAM off the HTIF words. -/
theorem snprintf_gen (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s dst n fmt : BitVec 64) (args : List (BitVec 64)) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (hcl : CodeLive live) (hargs5 : args.length ≤ 5)
    (hn0 : 0 < n.toNat) (hn : n.toNat < 2 ^ 31) (hfa : FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt args)
    (hsp : SpIn s snprintfNeed) (hbss : 0x8001c168 ≤ s.toNat - snprintfNeed)
    (hd1 : 0x8001c168 ≤ dst.toNat) (hd2 : dst.toNat + n.toNat ≤ 0x100000000)
    (hrg : ReadGeom (fun a => Sro a ∨ Sown a)) :
    ⊢ fnSpecW Wp snprintfEntry
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ argsAt ([dst, n, fmt] ++ args) ∗ blockOwn dst.toNat n.toNat ∗
        readable Sro Sown rd ∗ stdioOwn ∗ callFrame s snprintfNeed Newlib.calleeSaved cs))
      (fun _ => iprop(clobbered argRegs ∗ cstrBuf dst.toNat n.toNat ∗ readable Sro Sown rd ∗
        stdioOwn ∗ callFrame s snprintfNeed Newlib.calleeSaved cs)) := by
  obtain ⟨bytes, convs, FA⟩ := hfa
  have hs1 := hsp.hi
  have hs2 := hsp.align
  unfold snprintfNeed at hbss
  let L := readL (fun a => Sro a ∨ Sown a) rd fmt.toNat bytes convs args
  have hLR : ∀ a ∈ L, Sro a ∨ Sown a := fun a ha => readL_R FA ha
  refine snpSpec_of_runO (X := Unit) (f := fun _ => genImg L rd) (DAro := fun _ => genRO L Sown)
    (DAown := fun _ => genOwn L Sown) (O := fun _ a => Sown a ∧ a ∈ L)
    (Pf := fun _ => ∀ a ∈ baseDA, a ∈ L → rd a = snpImg a)
    (Post := fun img => ∃ k, k < n.toNat ∧ img (dst.toNat + k) = 0) (s := s) (dst := dst.toNat)
    (n := n.toNat) (args := [dst, n, fmt] ++ args) (Rr := readable Sro Sown rd) Wp
    (fun g g' hgg ⟨k, hk, hz⟩ => ⟨k, hk, by rw [← hgg _ (by unfold InExt; simp only; omega)]; exact hz⟩)
    (by simp; omega) (by omega) (fun r => .rfl) (fun r => ?_)
    ((genData L Sro Sown rd hLR).trans (by iintro ⟨%u, H⟩; iexists u; iexact H)) ?_
  · unfold cstrBuf
    iintro ⟨Ha, ⟨%img, Hd, %hp⟩, HR, Hs, Hc⟩
    iframe Ha HR Hs Hc
    iexists img
    iframe Hd
    ipureintro; exact hp
  intro _ Q R Mt hag hal h2 hargs hL hoff D hk
  let Dt := viewMem (genImg L rd) (genRO L Sown ++ genOwn L Sown)
  let DA := genRO L Sown ++ genOwn L Sown
  have SG : SnpGeom s.toNat dst.toNat n.toNat :=
    ⟨by omega, hs1, hs2, hn0, hn, hd1, hd2, D.sep (by omega) hn0⟩
  have BV : BaseView Dt DA :=
    baseView_of (fun a h => mem_genDA.2 (.inl h)) (fun a h => genImg_base hag h)
  have hDA : ∀ a ∈ DA, (0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000) ∧
      (a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a) := fun a ha => by
    rcases mem_genDA.1 ha with h | h
    · simp only [baseDA, List.mem_append, mem_accAddrs_iff] at h; omega
    · obtain ⟨h1, h2, h3⟩ := hrg a (hLR a h); omega
  have DO := dataOff_of (s := s.toNat) (dst := dst.toNat) (n := n.toNat)
    (fun a ha => (hDA a ha).1) (fun a ha => (hDA a ha).2) hoff BV.tab
  have e2 : R 2 = BitVec.ofNat 64 s.toNat := by rw [h2]; simp
  have e10 : R 10 = BitVec.ofNat 64 dst.toNat := by
    have := hargs 0 (by simp); simp only [List.cons_append, List.getElem_cons_zero] at this
    rw [this]; simp
  have e11 : R 11 = BitVec.ofNat 64 n.toNat := by
    have := hargs 1 (by simp); simp only [List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at this
    rw [this]; simp
  have e12 : R 12 = fmt := by
    have := hargs 2 (by simp); simpa using this
  have e13 : ∀ i (h : i < args.length), R (13 + i) = args[i] := fun i h => by
    have := hargs (3 + i) (by simp; omega)
    rw [show 10 + (3 + i) = 13 + i by omega] at this
    rw [this]; simp only [List.cons_append, List.nil_append]
    simp only [show 3 + i = i + 1 + 1 + 1 by omega, List.getElem_cons_succ]
  -- the format in the view
  have hfin : ∀ j, j ≤ bytes.length → fmt.toNat + j ∈ L := fun j hj =>
    mem_readL.2 (.inl ⟨by omega, by omega⟩)
  have hfR : ∀ j, j ≤ bytes.length → (Sro (fmt.toNat + j) ∨ Sown (fmt.toNat + j)) := fun j hj =>
    hLR _ (hfin j hj)
  obtain ⟨hflo, hfhi, hfht⟩ := readGeom_win hrg hfR
  have F : FmtAt Dt DA fmt.toNat bytes :=
    ⟨fun i h => by
      rw [genView_read (hfin i (by omega))]
      exact ⟨(FA.fmt_str.bytes i h).2.1, (FA.fmt_str.bytes i h).2.2⟩,
     by rw [genView_read (hfin _ (Nat.le_refl _))]; exact FA.fmt_str.nul.2,
     ⟨fun b h1 h2 => mem_genDA.2 (.inr (by
        have := hfin (b - fmt.toNat) (by omega); rwa [Nat.add_sub_cancel' h1] at this)),
      hflo, by omega, by omega⟩⟩
  have HS : StrArgs Dt DA convs args := fun i h h' hc =>
    ⟨_, (genDStr (Sown := Sown) FA hrg h h' hc).1⟩
  have hB : ∀ i (h : i < convs.length) (h' : i < args.length), convs[i] = .str →
      (cstrOf (imgM Dt) (args[i]).toNat (2 ^ 32)).length ≤ 2 ^ 27 := fun i h h' hc => by
    obtain ⟨hd, hl⟩ := genDStr (Sown := Sown) FA hrg h h' hc
    rw [cstrOf_eq _ _ _ _ hd.nz hd.nul (by have := hd.hi; omega)]
    simp; omega
  have hlenT := fmtRen_length_le (imgM Dt) (2 ^ 27) (by decide) bytes.length bytes convs args
    (Nat.le_refl _) FA.parse FA.arity hB
  have hcl5 : convs.length ≤ 5 := Nat.le_trans FA.arity hargs5
  refine snprintf_nw (snpText_live hcl) R Mt SG e2 e10 e11 hal hL.decPoint BV.dot BV.imp
    (fmtRen (imgM Dt) bytes args) (by omega) (fun R0 Mt0 SA => ?_) (fun R' Mt' hr1 hr2 hsv O => ?_)
  · have hp : (R0 12).toNat = fmt.toNat := by rw [SA.r12, e12]
    have hap : (R0 13).toNat = s.toNat - 40 := by rw [SA.r13]; exact toNat_ofNat_lt (by omega)
    rw [hp, hap]
    have hL0 : LocaleMt Mt0 := hL.transport fun a h1 h2 => SA.frame a (.inl (by omega))
    refine loop_fmt (snpText_live hcl) R0 Mt0 SG DO hL0.mbtowc hL0.mbMax (by rw [SA.r1]; decide) _ _
      bytes convs args F FA.parse FA.arity (fun i h => by
        rw [SA.args i (by omega), e13 i h]) (by omega) (by omega) HS (by omega)
  · refine hk R' Mt' ⟨hr1, hr2, fun z hz => hsv z ?_, O.frame⟩
      ⟨min (fmtRen (imgM Dt) bytes args).length (n.toNat - 1), by omega, O.nul⟩
    simp only [Newlib.calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
    omega

end Spec

end VsaIris.Sym
