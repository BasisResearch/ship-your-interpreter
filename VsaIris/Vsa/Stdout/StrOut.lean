import VsaIris.Vsa.Stdout.OutSpec
import VsaIris.Vsa.Stdout.Fwrite
import VsaIris.Vsa.Stdout.Fputs
import VsaIris.Vsa.BvLits

/-!
# `out.fwrite` and `out.fputs` (lane N1)

`fwrite(buf, 1, n, stdout)` of a C string's `n` bytes and `fputs(str,
stdout)` as Iris specifications (`NewlibOut.outSpec`), from their symbolic
runs (`fwrite_run`, `fputs_run`) through `outSpec_of_run`. The run's data
view is `_impure_ptr` followed by the string's first `m` bytes (`strDt`; `m =
n` for `fwrite`, `n + 1` with the NUL for `fputs`, whose `strlen` reads it),
both persistent (`impureRO`, `strAt`); where they overlap they agree
(`roImg_agree`), recorded in `StrView` by `strView_open`.
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
theorem roOwn_str (p n m : Nat) (hm : m ≤ n + 1) (img : Nat → BitVec 8) :
    iprop(gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO ∗ roImg (InExt (p, n + 1)) img) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf (strDt img p m) (strDA p m)) := by
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
  ihave #H := roImg_restrict (T := fun a => a ∈ strDA p m) (g := imgM (strDt img p m))
    (fun a ha => by
      unfold strDA at ha
      rcases List.mem_append.mp ha with ha | ha
      · rw [mem_accAddrs_iff] at ha; left; unfold impureW; omega
      · rw [List.mem_range'] at ha; right; unfold InExt; obtain ⟨i, hi, rfl⟩ := ha; simp; omega)
    (fun k hk => (imgM_strDt hk).symm) $$ H
  iapply roImg_list _ (imgM (strDt img p m)) _ (fun a ha => ha) $$ H

/-- What a stdout run knows of a string argument's image: the C string, its
window, and agreement with `_impure_ptr` where they overlap. -/
structure StrView (img : Nat → BitVec 8) (p : Nat) (x : String) : Prop where
  cstr : CStrImg img p x
  win : StrWin p x.toList.length
  imp : ∀ a, InExt (p, x.toList.length + 1) a → impureW a → impureByte a = img a

/-- **Opening a string argument** as a stdout run's data view over its first
`m ≤ n + 1` bytes. -/
theorem strView_open (p m : Nat) (x : String) (hm : m ≤ x.toList.length + 1) :
    iprop(strAt p x ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      ∃ img, roOwn roR (stdioText ++ dataOf (strDt img p m) (strDA p m)) ∗ ⌜StrView img p x⌝ := by
  unfold strAt
  iintro ⟨⟨%img, %⟨hc, hw⟩, #Hs⟩, #Hgp, #Himg, #Hr⟩
  ihave #Ha := (show impureRO ⊢@{IProp GF} roImg (fun a => InExt (p, x.toList.length + 1) a ∧
      impureW a) impureByte from by
    unfold impureRO; exact roImg_restrict (fun _ h => h.2) (fun _ _ => rfl)) $$ Hr
  ihave #Hb := roImg_restrict (T := fun a => InExt (p, x.toList.length + 1) a ∧ impureW a)
    (g := img) (fun _ h => h.1) (fun _ _ => rfl) $$ Hs
  ihave %hag := roImg_agree (f := impureByte) (g := img) $$ [Ha Hb]
  · iframe Ha Hb
  iexists img
  isplitl
  · iapply roOwn_str p x.toList.length m hm $$ [Hgp Himg Hr Hs]
    iframe Hgp Himg Hr Hs
  · ipureintro; exact ⟨hc, hw, fun a h1 h2 => hag a ⟨h1, h2⟩⟩

end Own

/-- The view's image on the string is the string's image. -/
theorem StrView.dt {img : Nat → BitVec 8} {p m : Nat} {x : String} (h : StrView img p x)
    {i : Nat} (hi : i < m) (hm : m ≤ x.toList.length + 1) :
    imgM (strDt img p m) (p + i) = img (p + i) := by
  rw [imgM_strDt (mem_strDA_str hi)]
  unfold strG
  split
  · rename_i hi'; exact h.imp _ ⟨by simp, by omega⟩ hi'
  · rfl

/-- The string's bytes, as the view holds them. -/
theorem StrView.bytes {img : Nat → BitVec 8} {p m : Nat} {x : String} (h : StrView img p x)
    {i : Nat} (hi : i < x.toList.length) (hm : x.toList.length ≤ m) (hm' : m ≤ x.toList.length + 1) :
    imgM (strDt img p m) (p + i) = (strBytes x)[i]'(by rw [strBytes_length]; exact hi) := by
  rw [h.dt (by omega) hm', (h.cstr.1 i hi).1]; simp [strBytes]

/-- The string avoids newlib's first owned byte, so it is shorter than
`__sfvwrite_r`'s chunk cap. -/
theorem StrView.short {img : Nat → BitVec 8} {p m : Nat} {x : String} (h : StrView img p x)
    {s : BitVec 64} {need : Nat} (hm : x.toList.length ≤ m)
    (hoff : ∀ q ∈ dataOf (strDt img p m) (strDA p m), ¬ outS s need q.1) :
    x.toList.length ≤ 0x7ffffc00 := by
  have hw1 := h.win.lo
  have hw2 := h.win.hi
  refine Nat.le_of_not_lt fun hc' => ?_
  have hb : p ≤ 0x8001b520 := by omega
  apply hoff (p + (0x8001b520 - p), _) (List.mem_map.mpr ⟨_, mem_strDA_str (by omega), rfl⟩)
  unfold outS stdioFoot Stdio.InRange impureW
  left; constructor <;> omega

/-- The string's characters print as the string. -/
theorem StrView.putcs {img : Nat → BitVec 8} {p : Nat} {x : String} (h : StrView img p x) :
    putcs (strBytes x) = x :=
  putcs_strBytes x fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have := (h.cstr.1 i hi).2.2; omega

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
  refine outSpec_of_run (X := Nat → BitVec 8) (Pf := fun img => StrView img buf.toNat frag)
    (Dt := fun img => strDt img buf.toNat frag.toList.length)
    (DA := fun _ => strDA buf.toNat frag.toList.length)
    Wp (by simp) (by unfold fwriteNeed; omega) hbss (strView_open _ _ _ (by omega))
    (fun img R Mt r img0 hal h1 h2 hargs hcs hok himp hMt hv hoff => ?_)
  have hw1 := hv.win.lo
  have hw2 := hv.win.hi
  have hw3 := hv.win.htif
  have hn : (strBytes frag).length = frag.toList.length := strBytes_length frag
  have hoffA : ∀ i, i < frag.toList.length → ¬ outS s fwriteNeed (buf.toNat + i) := fun i hi =>
    hoff (buf.toNat + i, _) (List.mem_map.mpr ⟨_, mem_strDA_str hi, rfl⟩)
  have hs5 : 0x8001c168 ≤ s.toNat - 512 := Nat.le_trans hbss (Nat.sub_le_sub_left (by decide) _)
  have hcm := consoleMt_of hok fun a ha hi => hMt a ⟨ha, hi⟩
  refine fwrite_run (stdioText_live hcl) (bs := strBytes frag) (buf := buf.toNat)
    (by unfold fwriteNeed; omega) hhi hbss hsp.align hal (by rw [hn]; exact hv.short (Nat.le_refl _) hoff) h1
    (by rw [hargs 0 (by simp)]; simp) (hargs 1 (by simp))
    (by rw [hargs 2 (by simp), hn]; rfl) (hargs 3 (by simp)) h2 hcm
    (ldv_strDt img _ _) hw1 (by rw [hn]; omega) (by rw [hn]; unfold htifLo at hw3; unfold tohostAddr; omega)
    (fun i hi => hoffA i (by rw [hn] at hi; exact hi))
    (fun i hi => ⟨mem_strDA_str (by rw [hn] at hi; exact hi),
      hv.bytes (by rw [hn] at hi; exact hi) (Nat.le_refl _) (by omega)⟩)
    (fun R' M' hR hK hF => swpo_done fun rv mv hm => ?_)
  refine outEnd_of (k := 512) hok himp hMt hR h1 h2 hcs hs5
    (hK.mono fun a ha => by simp only [outKeep] at ha; simp only [dataKeep]; omega)
    ?_ ?_ hF hm (by rw [hv.putcs])
  · rw [ldv_keep8 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.p
  · rw [ldv_keep4 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.w

/-- **`fputs(str, stdout)`** prints the string (`OutHoles.fputs`, with the
stack above `.bss`). -/
theorem fputs_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (str s : BitVec 64) (cs : Nat → BitVec 64) (frag o : String) (hcl : CodeLive live)
    (hsp : SpIn s outNeed) (hbss : 0x8001c168 ≤ s.toNat - outNeed) :
    ⊢ outSpec live Wp fputsEntry [str, stdoutFile] (strAt str.toNat frag) s outNeed cs o frag := by
  have hlo := hsp.lo
  have hhi := hsp.hi
  unfold tohostAddr outNeed at hlo
  unfold outNeed at hbss
  refine outSpec_of_run (X := Nat → BitVec 8) (Pf := fun img => StrView img str.toNat frag)
    (Dt := fun img => strDt img str.toNat (frag.toList.length + 1))
    (DA := fun _ => strDA str.toNat (frag.toList.length + 1))
    Wp (by simp) (by unfold outNeed; omega) hbss (strView_open _ _ _ (Nat.le_refl _))
    (fun img R Mt r img0 hal h1 h2 hargs hcs hok himp hMt hv hoff => ?_)
  have hw1 := hv.win.lo
  have hw2 := hv.win.hi
  have hw3 := hv.win.htif
  have hn : (strBytes frag).length = frag.toList.length := strBytes_length frag
  have hoffA : ∀ i, i < frag.toList.length → ¬ outS s outNeed (str.toNat + i) := fun i hi =>
    hoff (str.toNat + i, _) (List.mem_map.mpr ⟨_, mem_strDA_str (by omega), rfl⟩)
  have hs5 : 0x8001c168 ≤ s.toNat - 512 := Nat.le_trans hbss (Nat.sub_le_sub_left (by decide) _)
  have hcm := consoleMt_of hok fun a ha hi => hMt a ⟨ha, hi⟩
  have c : StrLeaf.LCtx live str 0x800063dc#64 (strBytes frag).length img := by
    rw [hn]; exact ⟨StrLeaf.regions_of_win hv.win, StrLeaf.strBytes_of_img hv.cstr, by decide, StrLeaf.strCode_live hcl⟩
  refine fputs_run (stdioText_live hcl) (bs := strBytes frag) (bv := img) (P := str)
    (by unfold outNeed; omega) hhi hbss hsp.align hal (by rw [hn]; exact hv.short (by omega) hoff) h1
    (by rw [hargs 0 (by simp)]; rfl) (hargs 1 (by simp)) h2 hcm (ldv_strDt img _ _) c
    (fun q hq => ?_) hw1 (by rw [hn]; omega)
    (by rw [hn]; unfold htifLo at hw3; unfold tohostAddr; omega)
    (fun i hi => hoffA i (by rw [hn] at hi; exact hi))
    (fun i hi => ⟨mem_strDA_str (by rw [hn] at hi; omega),
      hv.bytes (by rw [hn] at hi; exact hi) (by omega) (Nat.le_refl _)⟩)
    (fun R' M' hR hK hF => swpo_done fun rv mv hm => ?_)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    rw [hn] at hk
    have hk' : k < frag.toList.length + 1 := List.mem_range.mp hk
    exact List.mem_map.mpr ⟨_, mem_strDA_str hk', by rw [hv.dt hk' (Nat.le_refl _)]⟩
  refine outEnd_of (k := 512) hok himp hMt hR h1 h2 hcs hs5
    (hK.mono fun a ha => by simp only [outKeep] at ha; simp only [dataKeep]; omega)
    ?_ ?_ hF hm (by rw [hv.putcs])
  · rw [ldv_keep8 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.p
  · rw [ldv_keep4 hK (fun i hi => by simp only [dataKeep]; omega)]; exact hcm.w

end Spec

end VsaIris.Sym
