import VsaIris.Vsa.SnpIris

/-!
# The `snprintf` holes (lane N2)

`out.snprintfInt`: `snprintf(buf, 64, "%lld", i)` (`snprintfInt_out`), from
`snprintf_nw` with the format's loop `loop_lld`, through `snpSpec_of_run`.
The data view is `.rodata` (the format, `"."`, the conversion table) and
`_impure_ptr`.
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open VsaIris.Inst Vsa.While

/-! ## Geometry from ownership -/

/-- The stack and the destination are apart: both are owned. -/
theorem SnpDisj.sep {s dst n : Nat} (D : SnpDisj s dst n) (hs : 1024 ≤ s) (hn : 0 < n) :
    dst + n ≤ s - 1024 ∨ s ≤ dst := by
  if h : dst + n ≤ s - 1024 ∨ s ≤ dst then exact h
  else exact (D.stack_dst (max dst (s - 1024)) (by unfold InExt; simp only; omega)
    (by unfold InExt; simp only; omega)).elim

/-- A data view off the owned bytes, in RAM off the HTIF words, holding the
conversion table. -/
theorem dataOff_of {Dt : Mem} {DA : List Nat} {s dst n : Nat}
    (hram : ∀ a ∈ DA, 0x80000000 ≤ a ∧ a + 8 ≤ 0x100000000)
    (hhtif : ∀ a ∈ DA, a + 8 ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ a)
    (hoff : ∀ a ∈ DA, ¬ snpS s dst n a) (tab : TabAt Dt DA) : DataOff Dt DA s dst n where
  ram := hram
  htif := hhtif
  stack a ha := by
    have h : ¬ (s - 1024 ≤ a ∧ a < s) := fun h => hoff a ha (.inr (.inl h))
    omega
  dst a ha := by
    have h : ¬ (dst ≤ a ∧ a < dst + n) := fun h => hoff a ha (.inr (.inr h))
    omega
  tab := tab

/-! ## `out.snprintfInt` -/

/-- `"%lld"` besides the base view. -/
def intDA : List Nat := accAddrs 0x800192c0 5 ++ baseDA

theorem mem_intDA {a : Nat} (h : a ∈ intDA) :
    (0x800192c0 ≤ a ∧ a < 0x800192c5) ∨ (0x80019770 ≤ a ∧ a < 0x80019772) ∨
      (0x8001a0fc ≤ a ∧ a < 0x8001a268) ∨ (0x8001b970 ≤ a ∧ a < 0x8001b978) := by
  simp only [intDA, baseDA, List.mem_append, mem_accAddrs_iff] at h
  omega

theorem intView_byte {a : Nat} (h : a ∈ intDA) : impureW a ∨ rodataDom a := by
  have := mem_intDA h
  unfold impureW rodataDom
  omega

theorem intView_fmt {j : Nat} (hj : j < 5) :
    imgM (viewMem snpImg intDA) (0x800192c0 + j) = rodataByte (0x800192c0 + j) := by
  rw [imgM_viewMem (show 0x800192c0 + j ∈ intDA from
    List.mem_append_left _ (mem_accAddrs_iff.2 ⟨by omega, by omega⟩))]
  unfold snpImg
  rw [if_neg (show ¬ impureW (0x800192c0 + j) by unfold impureW; omega)]

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`out.snprintfInt`**: `snprintf(buf, 64, "%lld", i)` leaves `intToString i`
and a NUL in `buf` (at most 20 characters, never cut), for a stack and a
buffer above newlib's data. -/
theorem snprintfInt_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf i : BitVec 64) (cs : Nat → BitVec 64) (hcl : CodeLive live)
    (hsp : SpIn s snprintfNeed) (hbss : 0x8001c168 ≤ s.toNat - snprintfNeed)
    (hb1 : 0x8001c168 ≤ buf.toNat) (hb2 : buf.toNat + 64 ≤ 0x100000000) :
    ⊢ snprintfIntSpec live Wp s buf i cs := by
  have hs1 := hsp.hi
  have hs2 := hsp.align
  unfold snprintfNeed at hbss
  unfold snprintfIntSpec
  refine snpSpec_of_run (X := Unit) (f := fun _ => snpImg) (DA := fun _ => intDA)
    (Pf := fun _ => True) (Rr := iprop(emp)) (s := s) (dst := buf.toNat) (n := 64)
    (args := [buf, 64#64, 0x800192c0#64, i])
    (Post := fun img => CStrImg img buf.toNat (intToString i.toInt)) Wp (by simp) (by omega)
    (fun r => ?_) (fun r => .rfl) ?_ ?_
  · iintro ⟨%h, Ha, Hb, Hs, Hc⟩
    iframe Ha Hb Hs Hc
    ipureintro; exact h
  · iintro ⟨-, #H⟩
    iexists ()
    isplitl
    · iapply sepL_view (iprop(binImg ∗ impureRO)) snpImg intDA intDA (fun a h => h)
        (fun a ha => snpImg_byte (intView_byte ha)) $$ H
    · ipureintro; trivial
  intro _ Q R Mt _ hal h2 hargs hL hoff D hk
  have SG : SnpGeom s.toNat buf.toNat 64 :=
    ⟨by omega, hs1, hs2, by decide, by decide, hb1, hb2, D.sep (by omega) (by decide)⟩
  have BV : BaseView (viewMem snpImg intDA) intDA :=
    baseView_of (fun a h => List.mem_append_right _ h) (fun _ _ => rfl)
  have DO : DataOff (viewMem snpImg intDA) intDA s.toNat buf.toNat 64 :=
    dataOff_of (fun a ha => by have := mem_intDA ha; omega)
      (fun a ha => by have := mem_intDA ha; omega) hoff BV.tab
  have e2 : R 2 = BitVec.ofNat 64 s.toNat := by rw [h2]; simp
  have e10 : R 10 = BitVec.ofNat 64 buf.toNat := by
    have := hargs 0 (by simp); simp only [List.getElem_cons_zero] at this; rw [this]; simp
  have e11 : R 11 = BitVec.ofNat 64 64 := hargs 1 (by simp)
  have e12 : R 12 = 0x800192c0#64 := hargs 2 (by simp)
  have e13 : R 13 = i := hargs 3 (by simp)
  have hlen := intToString_length_le i
  refine snprintf_nw (snpText_live hcl) R Mt SG e2 e10 e11 hal hL.decPoint BV.dot BV.imp
    (strBytes (intToString i.toInt)) (by omega) (fun R0 Mt0 SA => ?_) (fun R' Mt' hr1 hr2 hsv O => ?_)
  · have hp : (R0 12).toNat = 0x800192c0 := by rw [SA.r12, e12]; rfl
    have hap : (R0 13).toNat = s.toNat - 40 := by rw [SA.r13]; exact toNat_ofNat_lt (by omega)
    rw [hp, hap]
    have hL0 : LocaleMt Mt0 := hL.transport fun a h1 h2 => SA.frame a (.inl (by omega))
    have hv : ldv .ld Mt0 (BitVec.ofNat 64 (s.toNat - 40)).toNat = i := by
      have := SA.args 0 (by decide)
      simpa [e13] using this
    refine loop_lld (snpText_live hcl) R0 Mt0 SG DO hL0.mbtowc hL0.mbMax
      (by rw [SA.r1]; decide) _ _
      ⟨fun b h1 h2 => List.mem_append_left _ (mem_accAddrs_iff.2 ⟨h1, by omega⟩), by decide,
        by decide, .inl (by decide)⟩
      ((intView_fmt (j := 0) (by decide)).trans (by decide))
      ((intView_fmt (j := 1) (by decide)).trans (by decide))
      ((intView_fmt (j := 2) (by decide)).trans (by decide))
      ((intView_fmt (j := 3) (by decide)).trans (by decide))
      ((intView_fmt (j := 4) (by decide)).trans (by decide))
      i hv (by omega) (by omega)
  · have hm : min (strBytes (intToString i.toInt)).length (64 - 1) =
        (strBytes (intToString i.toInt)).length := Nat.min_eq_left (by omega)
    refine hk R' Mt' ⟨hr1, hr2, fun z hz => hsv z ?_, O.frame⟩ ?_
    · simp only [Newlib.calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
      omega
    · refine cstrImg_of_bytes (intToString_ascii i) (fun j hj => O.bytes j (by rw [hm]; exact hj)) ?_
      have := O.nul
      rwa [hm] at this

end Spec

/-! ## `out.snprintfFn` -/

theorem strBytes_append (x y : String) : strBytes (x ++ y) = strBytes x ++ strBytes y := by
  simp [strBytes, String.toList_append]

/-- A C string in an image from a rendering's bytes cut at `k`, and a NUL. -/
theorem cstrImg_cut {img : Nat → BitVec 8} {p k : Nat} {y : String}
    (hA : ∀ c ∈ y.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hb : ∀ i, i < min (strBytes y).length k → img (p + i) = (strBytes y).getD i 0)
    (hz : img (p + min (strBytes y).length k) = 0) : CStrImg img p (String.ofList (y.toList.take k)) := by
  have hl : (strBytes y).length = y.toList.length := by simp [strBytes]
  unfold CStrImg
  simp only [String.toList_ofList]
  have hlt : (y.toList.take k).length = min (strBytes y).length k := by simp [hl, Nat.min_comm]
  refine ⟨fun i h => ⟨?_, hA _ (List.mem_of_mem_take (List.getElem_mem h))⟩, by rw [hlt]; exact hz⟩
  rw [hb i (by omega)]
  simp only [List.length_take] at h
  simp [strBytes, List.getD_eq_getElem?_getD, List.getElem_take, show i < y.toList.length by omega]

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Two read-only bytes at one address agree. -/
theorem snpRO_agree (a : Nat) (b b' : BitVec 8) :
    (a ↦ₘ□ b) ∗ (a ↦ₘ□ b') ⊢@{IProp GF} ⌜b = b'⌝ := by
  unfold memPointsTo; exact ghost_map_elem_agree _ _ _ _ _ _

end Own

/-- `"<fn %s>"` besides the base view. -/
def fnFixDA : List Nat := accAddrs 0x800192c8 8 ++ baseDA

theorem mem_fnFixDA {a : Nat} (h : a ∈ fnFixDA) :
    (0x800192c8 ≤ a ∧ a < 0x800192d0) ∨ (0x80019770 ≤ a ∧ a < 0x80019772) ∨
      (0x8001a0fc ≤ a ∧ a < 0x8001a268) ∨ (0x8001b970 ≤ a ∧ a < 0x8001b978) := by
  simp only [fnFixDA, baseDA, List.mem_append, mem_accAddrs_iff] at h
  omega

theorem fnFix_byte {a : Nat} (h : a ∈ fnFixDA) : impureW a ∨ rodataDom a := by
  have := mem_fnFixDA h
  unfold impureW rodataDom
  omega

/-- The `"<fn %s>"` view: the name's bytes, then the fixed bytes. -/
def fnDA (p len : Nat) : List Nat := fnFixDA ++ accAddrs p (len + 1)

instance (e : Nat × Nat) (a : Nat) : Decidable (InExt e a) := by unfold InExt; infer_instance

def fnImg (p len : Nat) (nimg : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if InExt (p, len + 1) a then nimg a else snpImg a

/-- The name's C string, agreeing with the fixed bytes where they overlap. -/
structure FnName (p : Nat) (x : String) (nimg : Nat → BitVec 8) : Prop where
  cstr : CStrImg nimg p x
  win : StrWin p x.toList.length
  agree : ∀ a, InExt (p, x.toList.length + 1) a → a ∈ fnFixDA → nimg a = snpImg a

theorem FnName.fix {p : Nat} {x : String} {nimg : Nat → BitVec 8} (N : FnName p x nimg) {a : Nat}
    (h : a ∈ fnFixDA) : fnImg p x.toList.length nimg a = snpImg a := by
  unfold fnImg
  by_cases hi : InExt (p, x.toList.length + 1) a
  · simp only [hi, ↓reduceIte]; exact N.agree a hi h
  · simp only [hi, ↓reduceIte]

theorem FnName.view_fix {p : Nat} {x : String} {nimg : Nat → BitVec 8} (N : FnName p x nimg)
    {a : Nat} (h : a ∈ fnFixDA) :
    imgM (viewMem (fnImg p x.toList.length nimg) (fnDA p x.toList.length)) a = snpImg a := by
  rw [imgM_viewMem (show a ∈ fnDA p x.toList.length from List.mem_append_left _ h), N.fix h]

theorem FnName.view_name {p : Nat} {x : String} {nimg : Nat → BitVec 8} (N : FnName p x nimg)
    {i : Nat} (hi : i ≤ x.toList.length) :
    imgM (viewMem (fnImg p x.toList.length nimg) (fnDA p x.toList.length)) (p + i) = nimg (p + i) := by
  rw [imgM_viewMem (show p + i ∈ fnDA p x.toList.length from
    List.mem_append_right _ (mem_accAddrs_iff.2 ⟨by omega, by omega⟩))]
  unfold fnImg
  rw [if_pos (show InExt (p, x.toList.length + 1) (p + i) by unfold InExt; simp only; omega)]

theorem fnFix_fmt {j : Nat} (hj : j < 8) : 0x800192c8 + j ∈ fnFixDA :=
  List.mem_append_left _ (mem_accAddrs_iff.2 ⟨by omega, by omega⟩)

theorem snpImg_fmt {j : Nat} (hj : j < 8) : snpImg (0x800192c8 + j) = rodataByte (0x800192c8 + j) := by
  unfold snpImg
  rw [if_neg (show ¬ impureW (0x800192c8 + j) by unfold impureW; omega)]

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The name's bytes agree with the image's where they overlap. -/
theorem fnName_agree (p l : Nat) (nimg : Nat → BitVec 8) :
    iprop(roImg (InExt (p, l)) nimg ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      ⌜∀ a, InExt (p, l) a → a ∈ fnFixDA → nimg a = snpImg a⌝ := by
  iintro ⟨#Hn, #Hb, #Hi⟩
  iintro %a %h1 %h2
  unfold roImg
  ihave #Ha := Hn $$ %a %h1
  ihave #Hs := snpImg_byte (fnFix_byte h2) $$ [Hb Hi]
  · iframe Hb Hi
  ihave %e := snpRO_agree a (nimg a) (snpImg a) $$ [Ha Hs]
  · iframe Ha Hs
  ipureintro; exact e

/-- One byte of the `"<fn %s>"` view, read-only. -/
theorem fnView_byte (p len : Nat) (nimg : Nat → BitVec 8) {a : Nat} (ha : a ∈ fnDA p len) :
    iprop(roImg (InExt (p, len + 1)) nimg ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      a ↦ₘ□ fnImg p len nimg a := by
  unfold fnImg
  by_cases hi : InExt (p, len + 1) a
  · simp only [hi, ↓reduceIte]
    iintro ⟨#H, -, -⟩
    unfold roImg
    iapply H $$ %a %hi
  · simp only [hi, ↓reduceIte]
    have hf : a ∈ fnFixDA := by
      rcases List.mem_append.mp ha with h | h
      · exact h
      · exact absurd (by rw [mem_accAddrs_iff] at h; unfold InExt; simp only; omega) hi
    iintro ⟨-, #Hb, #Hi⟩
    iapply snpImg_byte (fnFix_byte hf) $$ [Hb Hi]
    iframe Hb Hi

/-- **`out.snprintfFn`**: `snprintf(buf, 64, "<fn %s>", name)` leaves
`fnRender x` (`"<fn " ++ x ++ ">"` cut to 63 characters) and a NUL in `buf`,
for a stack and a buffer above newlib's data. -/
theorem snprintfFn_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s buf name : BitVec 64) (x : String) (cs : Nat → BitVec 64) (hcl : CodeLive live)
    (hsp : SpIn s snprintfNeed) (hbss : 0x8001c168 ≤ s.toNat - snprintfNeed)
    (hb1 : 0x8001c168 ≤ buf.toNat) (hb2 : buf.toNat + 64 ≤ 0x100000000) :
    ⊢ snprintfFnSpec live Wp s buf name x cs := by
  have hs1 := hsp.hi
  have hs2 := hsp.align
  unfold snprintfNeed at hbss
  unfold snprintfFnSpec
  refine snpSpec_of_run (X := Nat → BitVec 8) (f := fnImg name.toNat x.toList.length)
    (DA := fun _ => fnDA name.toNat x.toList.length) (Pf := FnName name.toNat x)
    (Rr := strAt name.toNat x) (s := s) (dst := buf.toNat) (n := 64)
    (args := [buf, 64#64, 0x800192c8#64, name])
    (Post := fun img => CStrImg img buf.toNat (fnRender x)) Wp (by simp) (by omega)
    (fun r => .rfl) (fun r => .rfl) ?_ ?_
  · iintro ⟨Hs, #Hb, #Hi⟩
    unfold strAt
    icases Hs with ⟨%nimg, %⟨hC, hW⟩, #Hn⟩
    ihave %hag := fnName_agree name.toNat (x.toList.length + 1) nimg $$ [Hn Hb Hi]
    · iframe Hn Hb Hi
    iexists nimg
    isplitl
    · iapply sepL_view (iprop(roImg (InExt (name.toNat, x.toList.length + 1)) nimg ∗ binImg ∗
          impureRO)) (fnImg name.toNat x.toList.length nimg) _ _ (fun a h => h)
          (fun a ha => fnView_byte _ _ nimg ha)
      iframe Hn Hb Hi
    · ipureintro; exact ⟨hC, hW, hag⟩
  intro nimg Q R Mt N hal h2 hargs hL hoff D hk
  have hw := N.win
  have hc := N.cstr
  have hwlo := hw.lo; have hwhi := hw.hi; have hwh := hw.htif
  simp only [htifLo] at hwh
  have SG : SnpGeom s.toNat buf.toNat 64 :=
    ⟨by omega, hs1, hs2, by decide, by decide, hb1, hb2, D.sep (by omega) (by decide)⟩
  have BV : BaseView (viewMem (fnImg name.toNat x.toList.length nimg) (fnDA name.toNat x.toList.length))
      (fnDA name.toNat x.toList.length) :=
    baseView_of (fun a h => List.mem_append_left _ (List.mem_append_right _ h))
      (fun a h => N.fix (List.mem_append_right _ h))
  have hDA : ∀ a ∈ fnDA name.toNat x.toList.length, (0x80000000 ≤ a ∧ a < 0x8001acf0) ∨
      (0x8001b970 ≤ a ∧ a < 0x8001b978) ∨ (name.toNat ≤ a ∧ a ≤ name.toNat + x.toList.length) :=
    fun a ha => by
      rcases List.mem_append.mp ha with h | h
      · have := mem_fnFixDA h; omega
      · rw [mem_accAddrs_iff] at h; omega
  have DO := dataOff_of (s := s.toNat) (dst := buf.toNat) (n := 64)
    (fun a ha => by have := hDA a ha; omega)
    (fun a ha => by have := hDA a ha; omega) hoff BV.tab
  have e2 : R 2 = BitVec.ofNat 64 s.toNat := by rw [h2]; simp
  have e10 : R 10 = BitVec.ofNat 64 buf.toNat := by
    have := hargs 0 (by simp); simp only [List.getElem_cons_zero] at this; rw [this]; simp
  have e11 : R 11 = BitVec.ofNat 64 64 := hargs 1 (by simp)
  have e12 : R 12 = 0x800192c8#64 := hargs 2 (by simp)
  have e13 : R 13 = name := hargs 3 (by simp)
  let Dt := viewMem (fnImg name.toNat x.toList.length nimg) (fnDA name.toNat x.toList.length)
  have hfx : ∀ j, j < 8 → imgM Dt (0x800192c8 + j) = rodataByte (0x800192c8 + j) := fun j hj =>
    (N.view_fix (fnFix_fmt hj)).trans (snpImg_fmt hj)
  have hnm : ∀ i, i < x.toList.length → imgM Dt (name.toNat + i) = BitVec.ofNat 8 (x.toList[i]!).toNat :=
    fun i hi => by
      rw [N.view_name (by omega), (hc.1 i hi).1]
      simp [hi]
  have hA : ∀ c ∈ x.toList, 0 < c.toNat ∧ c.toNat < 128 := fun c hc' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    exact (hc.1 i hi).2
  have hpb : pieceBytes (imgM Dt) name.toNat x.toList.length = strBytes x := by
    apply List.ext_getElem (by simp [strBytes])
    intro i h1 h2
    simp only [pieceBytes, List.getElem_map, List.getElem_range]
    rw [hnm i (by simpa using h1)]
    simp [strBytes, List.getElem!_eq_getElem?_getD, show i < x.toList.length by simpa using h1]
  have hp4 : pieceBytes (imgM Dt) 0x800192c8 4 = strBytes "<fn " := by
    simp only [pieceBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.map_append]
    rw [hfx 0 (by decide), hfx 1 (by decide), hfx 2 (by decide), hfx 3 (by decide)]
    decide
  have hp1 : pieceBytes (imgM Dt) (0x800192c8 + 6) 1 = strBytes ">" := by
    simp only [pieceBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil]
    rw [show 0x800192c8 + 6 + 0 = 0x800192c8 + 6 from rfl, hfx 6 (by decide)]
    decide
  have htot : pieceBytes (imgM Dt) 0x800192c8 4 ++ pieceBytes (imgM Dt) name.toNat x.toList.length ++
      pieceBytes (imgM Dt) (0x800192c8 + 6) 1 = strBytes ("<fn " ++ x ++ ">") := by
    rw [hp4, hpb, hp1, strBytes_append, strBytes_append]
  refine snprintf_nw (snpText_live hcl) R Mt SG e2 e10 e11 hal hL.decPoint BV.dot BV.imp
    (strBytes ("<fn " ++ x ++ ">")) (by simp [strBytes]; omega) (fun R0 Mt0 SA => ?_)
    (fun R' Mt' hr1 hr2 hsv O => ?_)
  · have hp : (R0 12).toNat = 0x800192c8 := by rw [SA.r12, e12]; rfl
    have hap : (R0 13).toNat = s.toNat - 40 := by rw [SA.r13]; exact toNat_ofNat_lt (by omega)
    rw [hp, hap, ← htot]
    have hL0 : LocaleMt Mt0 := hL.transport fun a h1 h2 => SA.frame a (.inl (by omega))
    have hv : ldv .ld Mt0 (BitVec.ofNat 64 (s.toNat - 40)).toNat = BitVec.ofNat 64 name.toNat := by
      have := SA.args 0 (by decide)
      simpa [e13] using this
    refine loop_fn (snpText_live hcl) R0 Mt0 SG DO hL0.mbtowc hL0.mbMax
      (by rw [SA.r1]; decide) _ _
      ⟨fun b h1 h2 => List.mem_append_left _ (fnFix_fmt (j := b - 0x800192c8) (by omega) |> fun h => by
          rwa [Nat.add_sub_cancel' h1] at h), by decide, by decide, .inl (by decide)⟩
      (fun i hi => by
        rw [hfx i (by omega)]
        revert i; decide)
      ((hfx 4 (by decide)).trans (by decide)) ((hfx 5 (by decide)).trans (by decide))
      (by rw [hfx 6 (by decide)]; decide) ((hfx 7 (by decide)).trans (by decide))
      name.toNat x.toList.length hv (by omega) (by omega)
      ⟨fun b h1 h2 => List.mem_append_right _ (mem_accAddrs_iff.2 ⟨h1, h2⟩),
        fun i hi => by
          rw [hnm i hi]
          have := (hc.1 i hi).2
          simp only [ne_eq, BitVec.ofNat_eq_ofNat]
          intro h
          have := congrArg BitVec.toNat h
          simp [List.getElem!_eq_getElem?_getD, hi] at this
          omega,
        by rw [N.view_name (Nat.le_refl _)]; exact hc.2, hwlo, by omega, by omega⟩
      (by omega)
  · refine hk R' Mt' ⟨hr1, hr2, fun z hz => hsv z ?_, O.frame⟩ ?_
    · simp only [Newlib.calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hz
      omega
    · have hA' : ∀ c ∈ ("<fn " ++ x ++ ">").toList, 0 < c.toNat ∧ c.toNat < 128 := by
        intro c hc'
        simp only [String.toList_append, List.mem_append] at hc'
        rcases hc' with (hc' | hc') | hc'
        · revert c; decide
        · exact hA c hc'
        · revert c; decide
      exact cstrImg_cut hA' O.bytes O.nul

end Spec

end VsaIris.Sym
