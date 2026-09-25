import VsaIris.Vsa.Stderr.FprintfBody
import VsaIris.Vsa.Stderr.FwriteSpec
import VsaIris.Vsa.Stderr.Promote

/-!
# `newlib.fprintf`, proved (lane N3)

`fprintf_proved`: `Newlib.fprintfSpec` for every Iris instance and both WPs,
from `fprintfErr_run` (the whole call as one printing symbolic run) and N1's
`wp_lroW`, as `fwrite_proved`:

* the run owns `outS s 4096` (`outS_own`);
* its data view (`fpDt`) holds `_impure_ptr` (`impureRO`), the `.rodata` it
  reads (`binImg`: the format `"%s\n"`, the decimal point `"."`, the
  conversion jump table) and the string up to its NUL. The string's bytes are
  owned by the caller (`ownImg`): `LRO.promote` runs with them owned, and
  hands them back unchanged;
* at the return, `FprPost` makes the data `StdioErrOK` (`fpQ_of`).
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim
open VsaIris.Interp.StrLeaf VsaIris.Inst.Strlen

/-! ## Loads as little-endian values -/

theorem imgLE8_of_ld {M : Mem} {a : Nat} {v : BitVec 64} (h : ldv .ld M a = v) :
    imgLE (imgM M) a 8 = v.toNat := by
  have e : ldv .ld M a = BitVec.ofNat 64 (imgLE (imgM M) a 8) := ldv_ld_of_imgLE (v := imgLE (imgM M) a 8) rfl
  have hl : imgLE (imgM M) a 8 < 2 ^ 64 := by
    have := imgLE_lt (imgM M) a 8; simp only [Nat.reducePow] at this ⊢; omega
  rw [← h, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]

theorem imgLE2_of_lhu {M : Mem} {a : Nat} {v : BitVec 64} (h : ldv .lhu M a = v) :
    imgLE (imgM M) a 2 = v.toNat := by
  rw [← h, ldv_lhu_img, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 2; simp at this; omega)).symm

theorem imgLE4_of_lw0 {M : Mem} {a : Nat} (h : ldv .lw M a = 0#64) : imgLE (imgM M) a 4 = 0 := by
  rw [ldv_lw_img] at h
  have hx : BitVec.ofNat 32 (imgLE (imgM M) a 4) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun y => y.getLsbD i) h
    simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      BitVec.getLsbD_signExtend, BitVec.getLsbD_zero] at this ⊢
    simpa [show i < 64 by omega, hi] using this
  have := congrArg BitVec.toNat hx
  have hl := imgLE_lt (imgM M) a 4
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at this hl
  omega

/-! ## The end state -/

/-- What the run ends in: some output after `o`, `pc`/`ra` at the return,
`sp` and the saved registers back, newlib's data `StdioErrOK`. -/
def FpQ (o : String) (r s : BitVec 64) (cs : Nat → BitVec 64) (img : Nat → BitVec 8) (t : String)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  (∃ o', t = o ++ o') ∧ rv 32 = r ∧ rv 1 = r ∧ rv 2 = s ∧ (∀ x ∈ calleeSaved, rv x = cs x) ∧
    StdioErrOK (fwOut img mv)

/-- **The run's end is `FpQ`.** -/
theorem fpQ_of {o o' : String} {r s n : BitVec 64} {cs : Nat → BitVec 64}
    {img : Nat → BitVec 8} {M Mt' : Mem} {rv R' : Nat → BitVec 64} {rv' : Nat → BitVec 64}
    {mv' : Nat → BitVec 8} (hok : StdioOK img) (hM : ∀ a, stdioExcl a → imgM M a = img a)
    (hs : 0x8001c168 ≤ s.toNat - 4096)
    (h1 : rv 1 = r) (h2 : rv 2 = s) (hcs : ∀ x ∈ calleeSaved, rv x = cs x)
    (hr : RetOK rv R' n) (hp : FprPost M Mt' s)
    (hm : Matches iRegs (outS s 4096) r R' Mt' rv' mv') :
    FpQ o r s cs img (o ++ o') rv' mv' := by
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
  refine ⟨⟨o', rfl⟩, hm.pc, (keep 1 (by decide) (by decide) (by decide) (by decide)).trans h1,
    (keep 2 (by decide) (by decide) (by decide) (by decide)).trans h2, fun x hx => ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := calleeSaved_kept x hx
    exact (keep x a1 a2 a3 a4).trans (hcs x hx)
  refine stdioErrOK_of_write hok (fun a hf hw => ?_) ?_ ?_ ?_ ?_
  · unfold fwOut
    by_cases hi : impureW a
    · rw [if_pos hi]
    · rw [if_neg hi, hin a hf hi]
      obtain ⟨hlt, he⟩ := stdioFoot_off hf
      rw [hp.frame a (fun h => by
        unfold FprReg at h
        rcases h with h | h | h
        · omega
        · exact hw h
        · exact he h)]
      exact hM a ⟨hf, hi⟩
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact imgLE8_of_ld hp.err.cursor
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact imgLE2_of_lhu hp.err.flagsU
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact imgLE8_of_ld hp.err.base
  · rw [hcur _ _ (F _ _ (by decide) (by decide))]; exact imgLE4_of_lw0 hp.err.flags2

/-! ## The data view -/

/-- The `.rodata` the run reads: the format `"%s\n"`, the decimal point `"."`,
the conversion jump table. -/
abbrev fpRo : List Nat := accAddrs 0x800195e0 4 ++ accAddrs 0x80019770 2 ++ accAddrs 0x8001a288 364

/-- The data view's addresses: the `.rodata` read, the string and its NUL. -/
abbrev fpDA (p len : Nat) : List Nat := fpRo ++ accAddrs p (len + 1)

/-- The data view's image: `_impure_ptr`, `.rodata`, the string's bytes. -/
def fpImg (bv : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if impureW a then impureByte a else if rodataDom a then rodataByte a else bv a

/-- The data view. -/
def fpDt (bv : Nat → BitVec 8) (p len : Nat) : Mem := fillMem (fpImg bv) (fprDA (fpDA p len))

theorem imgM_fpDt {bv : Nat → BitVec 8} {p len a : Nat} (h : a ∈ fprDA (fpDA p len)) :
    imgM (fpDt bv p len) a = fpImg bv a := by
  unfold imgM fpDt; rw [fillMem_get _ h]; rfl

theorem fpDt_ro {bv : Nat → BitVec 8} {p len a : Nat} (h : a ∈ fpRo) :
    imgM (fpDt bv p len) a = rodataByte a := by
  have h' := h
  simp only [List.mem_append, mem_accAddrs_iff] at h'
  rw [imgM_fpDt (List.mem_append_right _ (List.mem_append_left _ h))]
  unfold fpImg
  rw [if_neg (by unfold impureW; omega), if_pos (by unfold rodataDom; omega)]

theorem fpDt_str {bv : Nat → BitVec 8} {p len i : Nat} (hi : i ≤ len)
    (hd : ¬ impureW (p + i) ∧ ¬ rodataDom (p + i)) : imgM (fpDt bv p len) (p + i) = bv (p + i) := by
  rw [imgM_fpDt (List.mem_append_right _ (List.mem_append_right _ (mem_accAddrs (by omega))))]
  unfold fpImg
  rw [if_neg hd.1, if_neg hd.2]

theorem ldv_fpDt (bv : Nat → BitVec 8) (p len : Nat) :
    ldv .ld (fpDt bv p len) 0x8001b970 = 0x8001b538#64 := by
  have e : ∀ j, j < 8 → imgM (fpDt bv p len) (0x8001b970 + j) = impureByte (0x8001b970 + j) := fun j hj => by
    rw [imgM_fpDt (List.mem_append_left _ (mem_accAddrs hj))]
    unfold fpImg; rw [if_pos (by unfold impureW; omega)]
  have h : imgLE (imgM (fpDt bv p len)) 0x8001b970 8 = 0x8001b538 := by
    rw [imgLE_congr (img' := impureByte) e]; decide
  exact ldvf_ld_imgLE h

theorem lbu_of_img {M : Mem} {a : Nat} {b : BitVec 8} (h : imgM M a = b) :
    ldv .lbu M a = BitVec.zeroExtend 64 b := by
  rw [ldv_lbu_img]
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  simp only [imgLE, Nat.mul_zero, Nat.add_zero, h, BitVec.toNat_ofNat, BitVec.toNat_setWidth]

theorem lbu_fpDt {bv : Nat → BitVec 8} {p len a : Nat} (h : a ∈ fpRo) :
    ldv .lbu (fpDt bv p len) a = BitVec.zeroExtend 64 (rodataByte a) :=
  lbu_of_img (fpDt_ro h)

theorem fpRo_fmt : ∀ i, i < 4 → 0x800195e0 + i ∈ fpRo := fun i hi =>
  List.mem_append_left _ (List.mem_append_left _ (mem_accAddrs hi))

theorem fp_fmt0 (bv : Nat → BitVec 8) (p len : Nat) :
    Fp.FmtAt (fpDt bv p len) (fprDA (fpDA p len)) 0x800195e0 [37#8] where
  lo := by decide
  hi := by decide
  mem i hi := List.mem_append_right _ (List.mem_append_left _ (fpRo_fmt i (by simp at hi; omega)))
  byte i hi := by
    obtain rfl : i = 0 := by simp at hi; omega
    rw [lbu_fpDt (fpRo_fmt 0 (by decide))]; simp only [List.getElem_cons_zero]; decide

theorem fp_fmt2 (bv : Nat → BitVec 8) (p len : Nat) :
    Fp.FmtAt (fpDt bv p len) (fprDA (fpDA p len)) 0x800195e2 [10#8, 0#8] where
  lo := by decide
  hi := by decide
  mem i hi := List.mem_append_right _ (List.mem_append_left _ (by
    rw [show 0x800195e2 + i = 0x800195e0 + (2 + i) by omega]; exact fpRo_fmt (2 + i) (by simp at hi; omega)))
  byte i hi := by
    simp at hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [lbu_fpDt (fpRo_fmt 2 (by decide))]; simp only [List.getElem_cons_zero]; decide
    · rw [lbu_fpDt (fpRo_fmt 3 (by decide))]; simp only [List.getElem_cons_succ, List.getElem_cons_zero]; decide

theorem fp_sfmt (bv : Nat → BitVec 8) (p len : Nat) :
    Fp.SFmt (fpDt bv p len) (fprDA (fpDA p len)) 0x800195e0 where
  fmtDA b h1 h2 := List.mem_append_right _ (List.mem_append_left _ (by
    rw [show b = 0x800195e0 + 1 by omega]; exact fpRo_fmt 1 (by decide)))
  tabDA b h1 h2 := List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
    (mem_accAddrs_iff.2 ⟨h1, by omega⟩)))
  s := by rw [lbu_fpDt (fpRo_fmt 1 (by decide))]; decide
  tabS := by
    have hm : ∀ j, j < 4 → 0x8001a3d4 + j ∈ fpRo := fun j hj =>
      List.mem_append_right _ (mem_accAddrs_iff.2 ⟨by omega, by omega⟩)
    have e : ∀ j, j < 4 → imgM (fpDt bv p len) (0x8001a3d4 + j) = rodataByte (0x8001a3d4 + j) :=
      fun j hj => fpDt_ro (hm j hj)
    have h : imgLE (imgM (fpDt bv p len)) 0x8001a3d4 4 = 0xffff10a4 := by
      rw [imgLE_congr (img' := rodataByte) e]; decide
    rw [ldv_lw_of_imgLE h]; decide

/-! ## Ownership -/

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Read-only bytes and exclusively owned ones do not share an address. -/
theorem roImg_ownImg_disj (S T : Nat → Prop) (img img' : Nat → BitVec 8) :
    roImg (GF := GF) S img ∗ ownImg T img' ⊢ ⌜∀ a, S a → ¬ T a⌝ := by
  refine (forall_intro fun a => ?_).trans pure_forall.2
  by_cases ha : S a
  · exact (roImg_ownImg_off ha).trans (pure_mono fun h _ => h)
  · exact (pure_intro fun h => absurd h ha)

/-- The `.rodata` and `_impure_ptr` the run reads, read-only. -/
theorem roImg_fp : iprop(binImg ∗ impureRO) ⊢@{IProp GF}
    roImg (fun a => impureW a ∨ rodataDom a) (fwImg rodataByte) := by
  iintro ⟨#Hb, #Hi⟩
  ihave #Hr := binImg_rodata $$ Hb
  iapply roImg_fw rodataDom rodataByte
  iframe Hi Hr

/-- **The run's read-only cells**, without the string: `gp`, the code, the
`.rodata` read, `_impure_ptr`. -/
theorem fpView (bv : Nat → BitVec 8) (p len : Nat) :
    iprop(gp ↦ᵣ□ gpV ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf (fpDt bv p len) (fprDA fpRo)) := by
  unfold roOwn Newlib.gpV
  iintro ⟨#Hgp, #Hb, #Hi⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply binImg_sepL stdioText (fun q hq => .inl (stdioText_code q hq)) $$ Hb
  ihave #H := roImg_fp $$ [Hb Hi]
  · iframe Hb Hi
  iapply StrLeaf.roImg_list (fun a => impureW a ∨ rodataDom a) (fwImg rodataByte) _ ?_ $$ H
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  have hS : impureW a ∨ rodataDom a := by
    rcases List.mem_append.mp ha with h | h
    · exact .inl (by have := of_mem_accAddrs h; unfold impureW; omega)
    · simp only [List.mem_append, mem_accAddrs_iff] at h
      exact .inr (by unfold rodataDom; omega)
  refine ⟨hS, ?_⟩
  have hin : a ∈ fprDA (fpDA p len) := by
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_left _ h)
  rw [imgM_fpDt hin]
  unfold fpImg fwImg
  by_cases hi : impureW a
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, if_pos (hS.resolve_left hi)]

end

/-! ## The call -/

/-- The first index where `P` holds. -/
theorem first_of_exists {P : Nat → Prop} : ∀ k, P k → ∃ m, m ≤ k ∧ P m ∧ ∀ j, j < m → ¬ P j
  | 0, h => ⟨0, Nat.le_refl _, h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1, h => by
    classical
    by_cases h' : ∃ j, j ≤ k ∧ P j
    · obtain ⟨j, hj, hp⟩ := h'
      obtain ⟨m, hm, hpm, hmin⟩ := first_of_exists j hp
      exact ⟨m, by omega, hpm, hmin⟩
    · exact ⟨k + 1, Nat.le_refl _, h, fun j hj hp => h' ⟨j, by omega, hp⟩⟩

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **`fprintf(stderr, "%s\n", p)`, proved**: a NUL within the `n < 2^30`
owned bytes at `p`, in RAM off the tohost cells; the stack (below `s`, above
newlib's data), newlib's data and `errno`. -/
theorem fprintf_proved (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (s p : BitVec 64) (n : Nat) (bv : Nat → BitVec 8) (cs : Nat → BitVec 64) (o : String)
    (hcl : CodeLive live) (hz : ∃ k, k < n ∧ bv (p.toNat + k) = 0) (hn : n < 2 ^ 30)
    (hp1 : 0x80000000 ≤ p.toNat) (hp2 : p.toNat + n + 8 ≤ 0x100000000)
    (hp3 : p.toNat + n + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat)
    (hsp : SpIn s fprintfNeed) (hs4 : 0x80100000 ≤ s.toNat - fprintfNeed) :
    ⊢ fprintfSpec live Wp s p n bv cs o := by
  classical
  have hs3 := hsp.hi
  have hal := hsp.align
  unfold fprintfNeed at hs4
  obtain ⟨len, hlen, hnul, hmin⟩ : ∃ len, len < n ∧ bv (p.toNat + len) = 0 ∧
      ∀ k, k < len → bv (p.toNat + k) ≠ 0 := by
    obtain ⟨k, hk, h0⟩ := hz
    obtain ⟨m, hm, hpm, hmin⟩ := first_of_exists (P := fun k => bv (p.toNat + k) = 0) k h0
    exact ⟨m, by omega, hpm, hmin⟩
  unfold fprintfSpec fnSpecW callFrame stdioOwn stdioAt fprintfNeed
  iintro !> %r %Φ Hpc Hra ⟨%hra, Ha, Hs, ⟨%img, %⟨hok, himp⟩, Hx, #Hi⟩, He, Hc,
    ⟨Hsp, Hss, Hcs, Ht, #Hgp, #Hb⟩⟩ Hk
  ihave ⟨%rv, Hr, %⟨h32, h1, h2, hargs, hcs⟩⟩ :=
    call_regs fprintfEntry r s [stderrFile, errLineFmt, p] cs (by simp) $$ [Hpc Hra Ha Hsp Hcs Ht]
  · iframe Hpc Hra Ha Hsp Hcs Ht
  ihave ⟨%M, HS, %hM⟩ := outS_own s 4096 img (by omega) $$ [Hss Hx He]
  · iframe Hss Hx He
  ihave ⟨⟨HS, Hs⟩, %hd1⟩ := keep_pure (ownSet_disj (outS s 4096) (InExt (p.toNat, n)) (imgM M) bv)
    $$ [HS Hs]
  · iframe HS Hs
  ihave #HR := roImg_fp $$ [Hb Hi]
  · iframe Hb Hi
  ihave ⟨⟨_, Hs⟩, %hd2⟩ := keep_pure (roImg_ownImg_disj _ (InExt (p.toNat, n)) _ bv) $$ [HR Hs]
  · iframe HR Hs
  ihave ⟨Hs1, Hs2⟩ := ownSet_split (InExt (p.toNat, n)) (InExt (p.toNat, len + 1)) _ $$ Hs
  ihave Hs1 := ownSet_iff (T := InExt (p.toNat, len + 1)) _ (fun a => by unfold InExt; dsimp only; omega)
    $$ Hs1
  have hin : ∀ i, i ≤ len → InExt (p.toNat, n) (p.toNat + i) := fun i hi => by
    unfold InExt; dsimp only; omega
  have hdisj : ∀ i, i ≤ len → ¬ outS s 4096 (p.toNat + i) ∧ ¬ impureW (p.toNat + i) ∧
      ¬ rodataDom (p.toNat + i) := fun i hi =>
    ⟨fun h => hd1 _ h (hin i hi), fun h => hd2 _ (.inl h) (hin i hi), fun h => hd2 _ (.inr h) (hin i hi)⟩
  let Dt := fpDt bv p.toNat len
  have hDs : ∀ i, i ≤ len → imgM Dt (p.toNat + i) = bv (p.toNat + i) := fun i hi =>
    fpDt_str hi ⟨(hdisj i hi).2.1, (hdisj i hi).2.2⟩
  have hstr : FprStr live Dt (fpDA p.toNat len) s p len := {
    ctx := ⟨⟨hp1, by omega, by omega, hp3.imp (fun h => by omega) id⟩,
      ⟨fun k hk => by rw [hDs k (by omega)]; exact hmin k hk, by rw [hDs len (Nat.le_refl _)]; exact hnul⟩,
      by decide, fun q hq => stdioText_live hcl q (strCode_stdio q hq)⟩
    mem := fun i hi => List.mem_append_right _ (mem_accAddrs (by omega))
    len := by omega
    lo := hp1
    hi := by omega
    tohost := hp3.imp (fun h => by omega) id
    off := fun i hi => by
      have hno := (hdisj i (by omega)).1
      simp only [outS, not_or, not_and] at hno
      refine ⟨?_, fun h => hno.1 h (hdisj i (by omega)).2.1, ?_⟩
      · by_cases hlt : s.toNat ≤ p.toNat + i
        · exact .inr hlt
        · exact .inl (Nat.lt_of_not_le fun h => hno.2.2 h (by omega))
      · by_cases hlt : p.toNat + i < 0x8001ba08
        · exact .inl hlt
        · exact .inr (Nat.le_of_not_lt fun h => hno.2.1 (by omega) h) }
  have h10 : rv 10 = 0x8001bbd8#64 := hargs 0 (by simp)
  have h11 : rv 11 = 0x800195e0#64 := hargs 1 (by simp)
  have h12 : rv 12 = p := hargs 2 (by simp)
  have hMx : ∀ a, stdioFoot a → ¬ impureW a → imgM M a = img a := fun a h1 h2 => hM a ⟨h1, h2⟩
  have hroA : ∀ a, a ∈ fpRo → a ∈ fpDA p.toNat len := fun a h => List.mem_append_left _ h
  have run := fprintfErr_run (live := live) (Dt := Dt) (DA := fpDA p.toNat len)
    (Q := FpQ o r s cs img) (stdioText_live hcl) (t := o) (Mt := M) (R := rv) (n := len) hs3 hs4 hal hra
    h1 h2 h10 h11 h12 (ldv_fpDt _ _ _)
    ⟨hroA _ (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega),
      hroA _ (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega)⟩
    ⟨by rw [fpDt_ro (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega)]; decide,
      by rw [fpDt_ro (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega)]; decide⟩
    (consoleMt_of hok hMx) (errMt_of hok hMx) (localeMt_of hok hMx) hstr
    (fp_fmt0 _ _ _) (fp_sfmt _ _ _) (fp_fmt2 _ _ _)
    (hroA _ (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega))
    (by rw [fpDt_ro (by simp only [fpRo, List.mem_append, mem_accAddrs_iff]; omega)]; decide)
    (fun R' Mf hr hp => swpo_done fun rv' mv' hm => by
      rw [String.append_assoc]; exact fpQ_of hok hM (by omega) h1 h2 hcs hr hp hm)
  let mv : Nat → BitVec 8 := fun a => if InExt (p.toNat, n) a then bv a else imgM M a
  have L := swpo_run run (rv := rv) (mv := mv)
    ⟨by rw [show VsaIris.PC = 32 from rfl, h32]; rfl, fun _ _ _ => rfl, fun a ha => if_neg (hd1 a ha)⟩
  have eL : stdioText ++ dataOf Dt (fprDA (fpDA p.toNat len)) =
      (stdioText ++ dataOf Dt (fprDA fpRo)) ++ dataOf Dt (accAddrs p.toNat (len + 1)) := by
    simp only [fprDA, fpDA, dataOf, List.map_append, List.append_assoc]
  rw [eL] at L
  let t2 := dataOf Dt (accAddrs p.toNat (len + 1))
  have ht2 : ∀ a, (∃ q ∈ t2, q.1 = a) ↔ InExt (p.toNat, len + 1) a := fun a => by
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
      have := of_mem_accAddrs hb; unfold InExt; dsimp only; omega
    · intro h; unfold InExt at h; dsimp only at h
      exact ⟨(a, imgM Dt a), List.mem_map_of_mem (f := fun a => (a, imgM Dt a))
        (mem_accAddrs_iff.2 ⟨h.1, h.2⟩), rfl⟩
  have hstrI : ∀ a, InExt (p.toNat, len + 1) a → imgM Dt a = bv a ∧ InExt (p.toNat, n) a := fun a h => by
    unfold InExt at h; dsimp only at h
    have e := hDs (a - p.toNat) (by omega)
    rw [show p.toNat + (a - p.toNat) = a by omega] at e
    exact ⟨e, by unfold InExt; dsimp only; omega⟩
  have L2 := LRO.promote (t2 := t2)
    (fun q hq h => hd1 _ h (hstrI _ ((ht2 _).1 ⟨q, hq, rfl⟩)).2) L
    (fun q hq => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
      have hI := hstrI b ((ht2 b).1 ⟨_, hq, rfl⟩)
      simp only [mv, if_pos hI.2, hI.1])
  iapply wp_lroW Wp L2
  isplitl []
  · iapply fpView bv p.toNat len
    iframe Hgp Hb Hi
  iframe Hr
  isplitl [HS Hs1]
  · ihave HS := ownSet_congr (Ψ := fun a => a ↦ₘ mv a) (fun a ha => by simp only [mv, if_neg (hd1 a ha)])
      $$ HS
    ihave Hs1 := ownSet_congr (Ψ := fun a => a ↦ₘ mv a) (fun a ha => by
      simp only [mv, if_pos (hstrI a ha).2]) $$ Hs1
    ihave Hs1 := ownSet_iff (T := fun a => ∃ q ∈ t2, q.1 = a) _ (fun a => (ht2 a).symm) $$ Hs1
    iapply ownSet_join _ _ _ (fun a ha hq => hd1 a ha (hstrI a ((ht2 a).1 hq)).2)
    iframe HS Hs1
  iframe Hc
  iintro %t' %rv' %mv' %⟨⟨⟨o', ht⟩, q32, q1, q2, qcs, qerr⟩, hback⟩ Hr HS Hc
  subst ht
  ihave ⟨Hpc, Hra, Ha, Hsp, Hcs, Ht⟩ := ret_regs r s cs rv' q32 q1 q2 qcs $$ Hr
  ihave ⟨HO, HT⟩ := ownSet_split _ (outS s 4096) _ $$ HS
  ihave HO := ownSet_iff (T := outS s 4096) _ (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ HO
  ihave ⟨Hx, He, Hss⟩ := outS_split s 4096 mv' (by omega) (by omega) $$ HO
  ihave HT := ownSet_iff (T := InExt (p.toNat, len + 1)) _ (fun a => ⟨fun h => (ht2 a).1
    (h.1.resolve_left h.2), fun h => ⟨.inr ((ht2 a).2 h), fun h' => hd1 a h' (hstrI a h).2⟩⟩) $$ HT
  ihave HT := ownSet_congr (Ψ := fun a => a ↦ₘ bv a) (fun a ha => by
    have hb := hback (a, imgM Dt a) ((ht2 a).2 ha |>.elim fun q ⟨hq, e⟩ => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq; subst e; exact List.mem_map_of_mem hb)
    simp only at hb
    rw [hb, (hstrI a ha).1]) $$ HT
  ihave Hs := ownSet_join (InExt (p.toNat, len + 1))
    (fun a => InExt (p.toNat, n) a ∧ ¬ InExt (p.toNat, len + 1) a) _ (fun a h1 h2 => h2.2 h1) $$ [HT Hs2]
  · iframe HT Hs2
  ihave Hs := ownSet_iff (T := InExt (p.toNat, n)) _ (fun a => by
    unfold InExt; dsimp only; constructor
    · rintro (h | h)
      · omega
      · exact h.1
    · intro h
      by_cases h' : a < p.toNat + (len + 1)
      · exact .inl ⟨h.1, h'⟩
      · exact .inr ⟨h, fun h'' => h' h''.2⟩) $$ Hs
  iapply Hk $$ Hpc Hra
  try dsimp only
  iframe Ha Hs He Hsp Hss Hcs Ht Hgp Hb
  isplitl [Hx]
  · iexists fwOut img mv'
    isplitr
    · ipureintro
      exact ⟨qerr, fun a ha => by unfold fwOut; rw [if_pos ha]; exact himp a ha⟩
    iframe Hi
    iapply ownSet_congr (fun a ha => by unfold fwOut; rw [if_neg ha.2]) $$ Hx
  · iexists o'
    iexact Hc

end

end VsaIris.Newlib
