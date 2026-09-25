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

end VsaIris.Sym
