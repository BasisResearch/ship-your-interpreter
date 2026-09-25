import VsaIris.Vsa.Stderr.FwriteRun
import VsaIris.Vsa.Stdout.OutSpec
import VsaIris.Interp.StrIris

/-!
# `newlib.fwrite`, proved (lane N3)

`fwrite_proved`: `Newlib.fwriteSpec` for every Iris instance and both WPs,
from `fwriteErr_run` (the whole call as one printing symbolic run) and N1's
`wp_lroW`:

* the run owns `outS s 768` (newlib's exclusive data, `errno`, the call
  frame's stack) at one tracking memory agreeing with the `StdioOK` image
  (`outS_own`), so `ConsoleMt`/`ErrMt` hold of it;
* its code is `stdioText` (all `.text`, `stdioText_code`, from `binImg`); its
  data view holds `_impure_ptr` (`impureRO`) and the bytes written out
  (`readable`'s read-only part), one image `fwImg` (`fwView`);
* at the return, `FwritePost` makes the data `StdioErrOK` (`fwQ_of`), and
  `RetOK` gives back `sp`, `ra` and the saved registers (`ret_regs`).
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-! ## Code and data view -/

theorem stdioText_all :
    stdioText.all (fun p => decide (textDom p.1) && textByte p.1 == p.2) = true := by
  decide +kernel

/-- `stdioText` is a slice of the image's `.text`. -/
theorem stdioText_code : ∀ p ∈ stdioText, textDom p.1 ∧ textByte p.1 = p.2 := by
  intro p hp
  have h := List.all_eq_true.1 stdioText_all p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem stdioText_live {live : Nat → Prop} (hcl : CodeLive live) : ∀ p ∈ stdioText, live p.1 :=
  fun p hp => hcl _ (stdioText_code p hp).1

/-- The data view's image: `_impure_ptr`, and the read-only bytes `rd`. -/
def fwImg (rd : Nat → BitVec 8) (a : Nat) : BitVec 8 := if impureW a then impureByte a else rd a

/-- The data view's addresses: `_impure_ptr`, the `n` bytes at `p`. -/
abbrev fwDA (p n : Nat) : List Nat := accAddrs 0x8001b970 8 ++ accAddrs p n

/-- The data view. -/
def fwDt (rd : Nat → BitVec 8) (p n : Nat) : Mem := fillMem (fwImg rd) (fwDA p n)

theorem imgM_fwDt {rd : Nat → BitVec 8} {p n a : Nat} (h : a ∈ fwDA p n) :
    imgM (fwDt rd p n) a = fwImg rd a := by
  unfold imgM fwDt; rw [fillMem_get _ h]; rfl

theorem ldv_fwDt (rd : Nat → BitVec 8) (p n : Nat) : ldv .ld (fwDt rd p n) 0x8001b970 = 0x8001b538#64 := by
  have e : ∀ j, j < 8 → imgM (fwDt rd p n) (0x8001b970 + j) = impureByte (0x8001b970 + j) := fun j hj => by
    rw [imgM_fwDt (List.mem_append_left _ (mem_accAddrs hj))]
    unfold fwImg; rw [if_pos (by unfold impureW; omega)]
  have h : imgLE (imgM (fwDt rd p n)) 0x8001b970 8 = 0x8001b538 := by
    rw [imgLE_congr (img' := impureByte) e]; decide
  exact ldvf_ld_imgLE h

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `_impure_ptr` and the read-only bytes, as one read-only image. -/
theorem roImg_fw (Sro : Nat → Prop) (rd : Nat → BitVec 8) :
    impureRO (GF := GF) ∗ roImg Sro rd ⊢ roImg (fun a => impureW a ∨ Sro a) (fwImg rd) := by
  unfold impureRO roImg
  iintro ⟨#Hi, #Hr⟩
  imodintro
  iintro %k %hk
  by_cases hi : impureW k
  · unfold fwImg; rw [if_pos hi]; iapply Hi $$ %k %hi
  · unfold fwImg; rw [if_neg hi]; iapply Hr $$ %k %(hk.resolve_left hi)

/-- **The run's read-only cells**: `gp`, the code, the data view. -/
theorem fwView (Sro : Nat → Prop) (rd : Nat → BitVec 8) (p n : Nat) (hro : ∀ i, i < n → Sro (p + i)) :
    iprop(gp ↦ᵣ□ gpV ∗ binImg ∗ impureRO ∗ roImg Sro rd) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf (fwDt rd p n) (fwDA p n)) := by
  unfold roOwn Newlib.gpV
  iintro ⟨#Hgp, #Hb, #Hi, #Hr⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply binImg_sepL stdioText (fun q hq => .inl (stdioText_code q hq)) $$ Hb
  ihave #H := roImg_fw Sro rd $$ [Hi Hr]
  · iframe Hi Hr
  iapply StrLeaf.roImg_list (fun a => impureW a ∨ Sro a) (fwImg rd) _ ?_ $$ H
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  refine ⟨?_, (imgM_fwDt ha).symm⟩
  rcases List.mem_append.mp ha with h | h
  · exact .inl (by have := of_mem_accAddrs h; unfold impureW; omega)
  · have := of_mem_accAddrs h
    have e := hro (a - p) (by omega)
    rw [show p + (a - p) = a by omega] at e
    exact .inr e

/-! ## The footprint -/

/-- **A stderr call's footprint**: the stack below `s`, newlib's exclusive
data and `errno`, at one tracking memory agreeing with the data's image. -/
theorem outS_own (s : BitVec 64) (need : Nat) (img : Nat → BitVec 8) (hns : need ≤ s.toNat) :
    iprop(stackScratch s need ∗ ownSet stdioExcl (fun a => a ↦ₘ img a) ∗ errnoOwn) ⊢@{IProp GF}
      ∃ M : Mem, ownSet (outS s need) (fun a => a ↦ₘ imgM M a) ∗
        ⌜∀ a, stdioExcl a → imgM M a = img a⌝ := by
  unfold stackScratch blockOwn errnoOwn
  iintro ⟨Hs, Hd, He⟩
  ihave ⟨%fs, Hs⟩ := ownSet_fn _ $$ Hs
  ihave ⟨%Ms, Hs⟩ := ownSet_mem _ fs $$ Hs
  ihave ⟨%fe, He⟩ := ownSet_fn _ $$ He
  ihave ⟨%Me, He⟩ := ownSet_mem _ fe $$ He
  ihave ⟨%Md, Hd, %hMd⟩ := ownSet_trackedAt _ img $$ Hd
  ihave ⟨%M1, H1, %⟨h1d, _, _⟩⟩ := ownSet_join_tracked stdioExcl errnoFoot Md Me $$ [Hd He]
  · iframe Hd He
  ihave ⟨%M, H, %⟨h2, _, _⟩⟩ := ownSet_join_tracked _ (InExt (s.toNat - need, need)) M1 Ms $$ [H1 Hs]
  · iframe H1 Hs
  iexists M
  isplitl
  · iapply ownSet_iff _ (fun a => ?_) $$ H
    simp only [outS, stdioExcl, errnoFoot, InRange, InExt]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨h.1, by omega⟩)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr ⟨h.1, by omega⟩
  · ipureintro
    exact fun a ha => (h2 a (.inl ha)).trans ((h1d a ha).trans (hMd a ha))

/-- **The footprint taken back apart**, at the final image `mv`. -/
theorem outS_split (s : BitVec 64) (need : Nat) (mv : Nat → BitVec 8)
    (hlo : 0x8001c168 ≤ s.toNat - need) (hns : need ≤ s.toNat) :
    ownSet (GF := GF) (outS s need) (fun a => a ↦ₘ mv a) ⊢
      ownSet stdioExcl (fun a => a ↦ₘ mv a) ∗ errnoOwn ∗ stackScratch s need := by
  unfold stackScratch blockOwn errnoOwn
  iintro H
  ihave ⟨Hd, Hr⟩ := ownSet_split _ stdioExcl _ $$ H
  ihave ⟨He, Hs⟩ := ownSet_split _ errnoFoot _ $$ Hr
  isplitl [Hd]
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ Hd
  isplitl [He]
  · ihave He := ownSet_iff _ (T := errnoFoot) (fun a => ⟨fun h => h.2, fun h => ⟨⟨by
      simp only [outS]; exact .inr (.inl (by simpa [errnoFoot, InRange] using h)), by
      simp only [stdioExcl, stdioFoot, InRange, errnoFoot] at h ⊢; omega⟩, h⟩⟩) $$ He
    iapply ownSet_mono _ _ (fun a => by iintro H; iexists mv a; iexact H) $$ He
  · ihave Hs := ownSet_iff _ (T := InExt (s.toNat - need, need)) (fun a => ⟨fun h => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      simp only [outS, InExt, stdioExcl, stdioFoot, InRange, errnoFoot, impureW] at h1 h2 h3 ⊢
      omega, fun h => by
      simp only [outS, InExt, stdioExcl, stdioFoot, InRange, errnoFoot, impureW] at h ⊢
      omega⟩) $$ Hs
    iapply ownSet_mono _ _ (fun a => by iintro H; iexists mv a; iexact H) $$ Hs

end

/-! ## The end state -/

/-- newlib's data at the end: `_impure_ptr` as at the start, every other byte
the run's. -/
def fwOut (img mv : Nat → BitVec 8) (a : Nat) : BitVec 8 := if impureW a then img a else mv a

/-- What the run ends in. -/
def FwQ (o : String) (bs : List (BitVec 8)) (r s : BitVec 64) (cs : Nat → BitVec 64)
    (img : Nat → BitVec 8) (t : String) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  t = o ++ putcs bs ∧ rv 32 = r ∧ rv 1 = r ∧ rv 2 = s ∧ (∀ x ∈ calleeSaved, rv x = cs x) ∧
    StdioErrOK (fwOut img mv)

theorem calleeSaved_kept : ∀ x ∈ calleeSaved, x ∈ iRegs ∧ x ≠ 32 ∧ x ≠ 10 ∧ x ∉ callClob := by
  decide

theorem stdioFoot_off {a : Nat} (h : stdioFoot a) : a < 0x8001c168 ∧ ¬ errnoFoot a := by
  unfold stdioFoot InRange at h; unfold errnoFoot InRange; omega

/-- **The run's end is `FwQ`.** -/
theorem fwQ_of {o : String} {bs : List (BitVec 8)} {r s n : BitVec 64} {cs : Nat → BitVec 64}
    {img : Nat → BitVec 8} {M Mt' : Mem} {rv R' : Nat → BitVec 64} {rv' : Nat → BitVec 64}
    {mv' : Nat → BitVec 8} (hok : StdioOK img) (hM : ∀ a, stdioExcl a → imgM M a = img a)
    (hs : 0x8001c168 ≤ s.toNat - 768)
    (h1 : rv 1 = r) (h2 : rv 2 = s) (hcs : ∀ x ∈ calleeSaved, rv x = cs x)
    (hr : RetOK rv R' n) (hp : FwritePost M Mt' s)
    (hm : Matches iRegs (outS s 768) r R' Mt' rv' mv') :
    FwQ o bs r s cs img (o ++ putcs bs) rv' mv' := by
  have keep : ∀ x, x ∈ iRegs → x ≠ 32 → x ≠ 10 → x ∉ callClob → rv' x = rv x := fun x h1 h2 h3 h4 =>
    (hm.regs x h1 h2).trans (hr.keep x h1 h2 h3 h4)
  have hin : ∀ a, stdioFoot a → ¬ impureW a → mv' a = imgM Mt' a := fun a h1 h2 =>
    hm.img a (.inl ⟨h1, h2⟩)
  have hcur : ∀ a k, (∀ i, i < k → stdioFoot (a + i) ∧ ¬ impureW (a + i)) →
      imgLE (fwOut img mv') a k = imgLE (imgM Mt') a k := fun a k h =>
    imgLE_congr fun i hi => by unfold fwOut; rw [if_neg (h i hi).2]; exact hin _ (h i hi).1 (h i hi).2
  have F : ∀ a k, 0x8001ba68 ≤ a → a + k ≤ 0x8001c168 → ∀ i, i < k →
      stdioFoot (a + i) ∧ ¬ impureW (a + i) := by
    intro a k h1 h2 i hi; unfold stdioFoot InRange impureW; omega
  refine ⟨rfl, hm.pc, (keep 1 (by decide) (by decide) (by decide) (by decide)).trans h1,
    (keep 2 (by decide) (by decide) (by decide) (by decide)).trans h2, fun x hx => ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := calleeSaved_kept x hx
    exact (keep x a1 a2 a3 a4).trans (hcs x hx)
  refine stdioErrOK_of_write hok (fun a hf hw => ?_) ?_ ?_ ?_ ?_
  · unfold fwOut
    by_cases hi : impureW a
    · rw [if_pos hi]
    · rw [if_neg hi, hin a hf hi]
      obtain ⟨hlt, he⟩ := stdioFoot_off hf
      rw [hp.frame a (by omega) hw he]
      exact hM a ⟨hf, hi⟩
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact hp.cursor
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact hp.flags
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact hp.base
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact hp.lockMode

/-! ## The call -/

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`fwrite(ptr, 1, n, stderr)`, proved**: for `0 < n < 2^30` read-only
bytes in RAM off the tohost cells, the stack (below `s`, above newlib's data),
newlib's data and `errno`. -/
theorem fwrite_proved (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s ptr n : BitVec 64) (cs : Nat → BitVec 64) (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8)
    (o : String) (hcl : CodeLive live) (hsp : SpIn s fwriteNeed)
    (hs4 : 0x80100000 ≤ s.toNat - fwriteNeed)
    (hn0 : 0 < n.toNat) (hn : n.toNat < 2 ^ 30)
    (hro : ∀ i, i < n.toNat → Sro (ptr.toNat + i))
    (hb1 : 0x80000000 ≤ ptr.toNat) (hb2 : ptr.toNat + n.toNat ≤ 0x100000000)
    (hb3 : ptr.toNat + n.toNat ≤ tohostAddr ∨ tohostAddr + 8 ≤ ptr.toNat)
    (hbd : ∀ i, i < n.toNat → (ptr.toNat + i < s.toNat - fwriteNeed ∨ s.toNat ≤ ptr.toNat + i) ∧
      ¬ stdioFoot (ptr.toNat + i) ∧ ¬ errnoFoot (ptr.toNat + i)) :
    ⊢ fwriteSpec live Wp s ptr n cs Sro Sown rd o := by
  have hs3 := hsp.hi
  have hal := hsp.align
  unfold fwriteNeed at hs4 hbd
  unfold fwriteSpec fnSpecW readable callFrame stdioOwn stdioAt fwriteNeed
  iintro !> %r %Φ Hpc Hra ⟨%hra, Ha, ⟨#Hro, Hown⟩, ⟨%img, %⟨hok, himp⟩, Hx, #Hi⟩, He, Hc,
    ⟨Hsp, Hss, Hcs, Ht, #Hgp, #Hb⟩⟩ Hk
  ihave ⟨%rv, Hr, %⟨h32, h1, h2, hargs, hcs⟩⟩ :=
    call_regs fwriteEntry r s [ptr, 1#64, n, stderrFile] cs (by simp) $$ [Hpc Hra Ha Hsp Hcs Ht]
  · iframe Hpc Hra Ha Hsp Hcs Ht
  ihave ⟨%M, HS, %hM⟩ := outS_own s 768 img (by omega) $$ [Hss Hx He]
  · iframe Hss Hx He
  have h10 : rv 10 = ptr := hargs 0 (by simp)
  have h11 : rv 11 = 1#64 := hargs 1 (by simp)
  have h12 : rv 12 = n := hargs 2 (by simp)
  have h13 : rv 13 = 0x8001bbd8#64 := hargs 3 (by simp)
  let bs : List (BitVec 8) := (List.range n.toNat).map fun i => rd (ptr.toNat + i)
  have hbl : bs.length = n.toNat := by simp [bs]
  have hMx : ∀ a, stdioFoot a → ¬ impureW a → imgM M a = img a := fun a h1 h2 => hM a ⟨h1, h2⟩
  have run := fwriteErr_run (live := live) (Dt := fwDt rd ptr.toNat n.toNat)
    (DA := accAddrs ptr.toNat n.toNat) (Q := FwQ o bs r s cs img)
    (hlive := stdioText_live hcl) (t := o) (Mt := M) (R := rv) (s := s) (ra := r) (ptr := ptr) (n := n)
    (hs3 := hs3) (hs4 := hs4) (hal := hal) (hra := hra) (hn := hn)
    (hn0 := eq_false fun h => by subst h; simp at hn0)
    (h1 := h1) (h2 := h2) (h10 := h10) (h11 := h11) (h12 := h12) (h13 := h13)
    (hC := consoleMt_of hok hMx) (hE := errMt_of hok hMx) (hDt := ldv_fwDt rd _ _) (bs := bs)
    (hbn := by rw [hbl]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm)
    (hbl0 := by omega) (hbl := by omega) (hb1 := hb1) (hb2 := by omega) (hb3 := by omega)
    (hbd := fun i hi => by
      have := hbd i (by omega)
      refine ⟨this.1, this.2.1, ?_⟩
      have := this.2.2; unfold errnoFoot InRange at this; omega)
    (hsrc := fun i hi => by
      have hin : ptr.toNat + i ∈ fwDA ptr.toNat n.toNat := List.mem_append_right _ (mem_accAddrs (by omega))
      refine .inr ⟨hin, ?_⟩
      rw [imgM_fwDt hin]
      unfold fwImg
      rw [if_neg fun hi' => (hbd i (by omega)).2.1 (by unfold stdioFoot InRange; unfold impureW at hi'; omega)]
      simp [bs])
    (hk := fun R' Mt' hr hp => swpo_done fun rv' mv' hm =>
      fwQ_of hok hM (by omega) h1 h2 hcs hr hp hm)
  iapply wp_lroW Wp (swpo_run run ⟨by rw [show VsaIris.PC = 32 from rfl, h32]; rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩)
  isplitl []
  · iapply fwView Sro rd ptr.toNat n.toNat hro
    iframe Hgp Hb Hi Hro
  iframe Hr HS Hc
  iintro %t' %rv' %mv' %⟨ht, q32, q1, q2, qcs, qerr⟩ Hr HS Hc
  subst ht
  ihave ⟨Hpc, Hra, Ha, Hsp, Hcs, Ht⟩ := ret_regs r s cs rv' q32 q1 q2 qcs $$ Hr
  ihave ⟨Hx, He, Hss⟩ := outS_split s 768 mv' (by omega) (by omega) $$ HS
  iapply Hk $$ Hpc Hra
  try dsimp only
  iframe Ha Hro Hown He Hsp Hss Hcs Ht Hgp Hb
  isplitl [Hx]
  · iexists fwOut img mv'
    isplitr
    · ipureintro
      exact ⟨qerr, fun a ha => by unfold fwOut; rw [if_pos ha]; exact himp a ha⟩
    iframe Hi
    iapply ownSet_congr (fun a ha => by unfold fwOut; rw [if_neg ha.2]) $$ Hx
  · iexists putcs bs
    iexact Hc

end

end VsaIris.Newlib
