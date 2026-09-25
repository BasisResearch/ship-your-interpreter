import VsaIris.Vsa.Stdout.OutSpec
import VsaIris.Vsa.Stdout.Fwrite

/-!
# `out.fwrite` (lane N1)

`fwrite(buf, 1, n, stdout)` of a C string's `n` bytes as an Iris
specification (`NewlibOut.outSpec`), from its symbolic run (`fwrite_run`)
through `outSpec_of_run`. The run's data view is `_impure_ptr` followed by
the string's bytes (`strDt`), both persistent (`impureRO`, `strAt`); where
they overlap they agree (`roImg_agree`).
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open VsaIris.Inst

theorem putcs_chars : ∀ (l : List Char), (∀ c ∈ l, c.toNat < 256) →
    putcs (l.map fun c => BitVec.ofNat 8 c.toNat) = String.ofList l
  | [], _ => by simp
  | c :: l, h => by
    rw [List.map_cons, putcs_cons, putcs_chars l (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    have hc := h c List.mem_cons_self
    simp only [VsaIris.Inst.putcStr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Char.ofNat_toNat]
    apply String.toList_injective
    simp [String.toList_append]
    rw [show toString c = String.singleton c from rfl, String.toList_singleton]; rfl

/-- A string's characters as bytes. -/
def strBytes (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat

theorem strBytes_length (s : String) : (strBytes s).length = s.toList.length := by
  simp [strBytes]

theorem putcs_strBytes (s : String) (h : ∀ c ∈ s.toList, c.toNat < 256) : putcs (strBytes s) = s := by
  rw [strBytes, putcs_chars _ h, String.ofList_toList]

/-- The data view's image: `_impure_ptr`'s bytes, else the string's. -/
def strG (img : Nat → BitVec 8) (a : Nat) : BitVec 8 := if impureW a then impureByte a else img a

/-- The data view's addresses: `_impure_ptr`, then the string's `n` bytes at `p`. -/
def strDA (p n : Nat) : List Nat := accAddrs 0x8001b970 8 ++ List.range' p n

/-- The data view of a stdout run over a string. -/
def strDt (img : Nat → BitVec 8) (p n : Nat) : Mem := fillMem (strG img) (strDA p n)

theorem imgM_strDt {img : Nat → BitVec 8} {p n a : Nat} (h : a ∈ strDA p n) :
    imgM (strDt img p n) a = strG img a := by
  unfold imgM strDt; rw [fillMem_get _ h]; rfl

theorem ldv_strDt (img : Nat → BitVec 8) (p n : Nat) :
    ldv .ld (strDt img p n) 0x8001b970 = 0x8001b538#64 := by
  have e : ∀ j, j < 8 → imgM (strDt img p n) (0x8001b970 + j) = impureByte (0x8001b970 + j) :=
    fun j hj => by
      rw [imgM_strDt (List.mem_append_left _ (mem_accAddrs hj))]
      unfold strG; rw [if_pos (show impureW _ by unfold impureW; omega)]
  have h : imgLE (imgM (strDt img p n)) 0x8001b970 8 = 0x8001b538 := by
    rw [imgLE_congr (img' := impureByte) e]; decide
  exact ldvf_ld_imgLE h

theorem mem_strDA_str {p n i : Nat} (h : i < n) : p + i ∈ strDA p n :=
  List.mem_append_right _ (List.mem_range'.mpr ⟨i, h, by simp⟩)

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `_impure_ptr` and a string, persistently, as one image. -/
theorem roImg_strG (p n : Nat) (img : Nat → BitVec 8) :
    iprop(impureRO ∗ roImg (InExt (p, n + 1)) img) ⊢@{IProp GF}
      roImg (fun a => impureW a ∨ InExt (p, n + 1) a) (strG img) := by
  unfold impureRO roImg
  iintro ⟨#H1, #H2⟩
  imodintro
  iintro %k %hk
  by_cases hi : impureW k
  · unfold strG; rw [if_pos hi]; iapply H1 $$ %k %hi
  · unfold strG; rw [if_neg hi]; iapply H2 $$ %k %(hk.resolve_left hi)

/-- **The read-only cells of a stdout run over a string.** -/
theorem roOwn_str (p n : Nat) (img : Nat → BitVec 8) :
    iprop(gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO ∗ roImg (InExt (p, n + 1)) img) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf (strDt img p n) (strDA p n)) := by
  unfold roOwn
  iintro ⟨#Hgp, #Himg, #Hr, #Hs⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply binImg_sepL stdioText (fun p hp => .inl (stdioText_img_mem p hp)) $$ Himg
  unfold dataOf
  rw [sepL_map]
  ihave #H := roImg_strG p n img $$ [Hr Hs]
  · iframe Hr Hs
  ihave #H := roImg_restrict (T := fun a => a ∈ strDA p n) (g := imgM (strDt img p n))
    (fun a ha => by
      unfold strDA at ha
      rcases List.mem_append.mp ha with ha | ha
      · rw [mem_accAddrs_iff] at ha; left; unfold impureW; omega
      · rw [List.mem_range'] at ha; right; unfold InExt; obtain ⟨i, hi, rfl⟩ := ha; simp; omega)
    (fun k hk => (imgM_strDt hk).symm) $$ H
  iapply roImg_list _ (imgM (strDt img p n)) _ (fun a ha => ha) $$ H

end Own

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`fwrite(buf, 1, n, stdout)`** of a C string's `n` bytes prints them
(`OutHoles.fwrite`, with the stack above `.bss`). -/
theorem fwrite_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (buf s : BitVec 64) (cs : Nat → BitVec 64) (frag o : String) (hcl : CodeLive live)
    (hsp : SpIn s fwriteNeed) (hbss : 0x8001c168 ≤ s.toNat - fwriteNeed) :
    ⊢ outSpec live Wp fwriteEntry [buf, 1#64, BitVec.ofNat 64 frag.toList.length, stdoutFile]
        (strAt buf.toNat frag) s fwriteNeed cs o frag := by
  have hlo := hsp.lo
  have hhi := hsp.hi
  unfold tohostAddr fwriteNeed at hlo
  unfold fwriteNeed at hbss
  refine outSpec_of_run (X := Nat → BitVec 8)
    (Pf := fun img => CStrImg img buf.toNat frag ∧ StrWin buf.toNat frag.toList.length ∧
      ∀ a, InExt (buf.toNat, frag.toList.length + 1) a → impureW a → impureByte a = img a)
    (Dt := fun img => strDt img buf.toNat frag.toList.length)
    (DA := fun _ => strDA buf.toNat frag.toList.length)
    Wp (by simp) (by unfold fwriteNeed; omega) hbss ?_
    (fun img R Mt r img0 hal h1 h2 hargs hcs hok himp hMt hPf hoff => ?_)
  · unfold strAt
    iintro ⟨⟨%img, %⟨hc, hw⟩, #Hs⟩, #Hgp, #Himg, #Hr⟩
    ihave #Ha := (show impureRO ⊢@{IProp GF} roImg (fun a => InExt (buf.toNat, frag.toList.length + 1) a ∧
        impureW a) impureByte from by
      unfold impureRO; exact roImg_restrict (fun _ h => h.2) (fun _ _ => rfl)) $$ Hr
    ihave #Hb := roImg_restrict (T := fun a => InExt (buf.toNat, frag.toList.length + 1) a ∧ impureW a)
      (g := img) (fun _ h => h.1) (fun _ _ => rfl) $$ Hs
    ihave %hag := roImg_agree (f := impureByte) (g := img) $$ [Ha Hb]
    · iframe Ha Hb
    iexists img
    isplitl
    · iapply roOwn_str $$ [Hgp Himg Hr Hs]
      iframe Hgp Himg Hr Hs
    · ipureintro; exact ⟨hc, hw, fun a h1 h2 => hag a ⟨h1, h2⟩⟩
  · obtain ⟨hc, hw, hag⟩ := hPf
    have hw1 := hw.lo
    have hw2 := hw.hi
    have hw3 := hw.htif
    have hn : (strBytes frag).length = frag.toList.length := strBytes_length frag
    -- the string avoids newlib's first owned byte, so it is shorter than the writer's cap
    have hoffA : ∀ i, i < frag.toList.length → ¬ outS s fwriteNeed (buf.toNat + i) := fun i hi =>
      hoff (buf.toNat + i, _) (List.mem_map.mpr ⟨_, mem_strDA_str hi, rfl⟩)
    have hn1 : (strBytes frag).length ≤ 0x7ffffc00 := by
      rw [hn]
      refine Nat.le_of_not_lt fun hc' => ?_
      have hb : buf.toNat ≤ 0x8001b520 := by omega
      have h0 := hoffA (0x8001b520 - buf.toNat) (by omega)
      apply h0
      unfold outS stdioFoot Stdio.InRange impureW
      left; constructor <;> omega
    have hs5 : 0x8001c168 ≤ s.toNat - 512 := Nat.le_trans hbss (Nat.sub_le_sub_left (by decide) _)
    have hcm := consoleMt_of hok fun a ha hi => hMt a ⟨ha, hi⟩
    refine fwrite_run (stdioText_live hcl) (bs := strBytes frag) (buf := buf.toNat)
      (by unfold fwriteNeed; omega) hhi hbss hsp.align hal hn1 h1
      (by rw [hargs 0 (by simp)]; simp) (hargs 1 (by simp))
      (by rw [hargs 2 (by simp), hn]; rfl) (hargs 3 (by simp)) h2 hcm
      (ldv_strDt img _ _) hw1 (by rw [hn]; omega) (by rw [hn]; unfold htifLo at hw3; unfold tohostAddr; omega)
      (fun i hi => hoffA i (by rw [hn] at hi; exact hi)) (fun i hi => ⟨mem_strDA_str (by rw [hn] at hi; exact hi), ?_⟩)
      (fun R' M' hR hK hF => swpo_done fun rv mv hm => ?_)
    · rw [hn] at hi
      rw [imgM_strDt (mem_strDA_str hi)]
      have hx := (hc.1 i hi).1
      unfold strG
      split
      · rename_i hi'
        rw [hag _ ⟨by simp, by omega⟩ hi', hx]; simp [strBytes]
      · rw [hx]; simp [strBytes]
    · refine outEnd_of (k := 512) hok himp hMt hR h1 h2 hcs hs5
        (hK.mono fun a ha => by simp only [outKeep] at ha; simp only [dataKeep]; omega)
        ?_ ?_ hF hm ?_
      · rw [ldv_keep8 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.p
      · rw [ldv_keep4 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.w
      · rw [putcs_strBytes frag (fun c hcm' => by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcm'
          have := (hc.1 i hi).2.2; omega)]

end Spec

end VsaIris.Sym
