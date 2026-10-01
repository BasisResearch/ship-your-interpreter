import VsaIris.Interp.SpecEval
import VsaIris.Interp.Bridge
import VsaIris.Interp.ITac

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

theorem iRegs_eq : iRegs = 32 :: 1 :: fRegs := rfl

theorem exists_mem_img (f : Nat → BitVec 8) : ∀ l : List Nat, ∃ Mt : Mem, ∀ a ∈ l, imgM Mt a = f a
  | [] => ⟨∅, fun _ h => by cases h⟩
  | a :: l => by
    obtain ⟨Mt, h⟩ := exists_mem_img f l
    refine ⟨Mt.insert a (f a), fun b hb => ?_⟩
    unfold imgM
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases e : a = b
    · subst e; simp
    · rw [if_neg (by simpa using e)]
      exact h b ((List.mem_cons.mp hb).resolve_left (Ne.symm e))

theorem imgLE_inj {f g : Nat → BitVec 8} :
    ∀ {n a : Nat}, imgLE f a n = imgLE g a n → ∀ j, j < n → f (a + j) = g (a + j)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, a, h, j, hj => by
    simp only [imgLE] at h
    have hf := (f a).isLt; have hg := (g a).isLt
    have h0 : (f a).toNat = (g a).toNat := by omega
    have h1 : imgLE f (a + 1) n = imgLE g (a + 1) n := by omega
    rcases j with _ | j
    · exact BitVec.eq_of_toNat_eq h0
    · have := imgLE_inj h1 j (by omega)
      rwa [show a + 1 + j = a + (j + 1) by omega] at this

theorem imgLE_imgM_store (Mt : Mem) (a : Nat) (w : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 8, w)])) a 8 = w.toNat :=
  readLE_memImg (read64_store_hit Mt a w)

theorem imgM_store_img {Mt : Mem} {a : Nat} {img : Nat → BitVec 8} {j : Nat} (hj : j < 8) :
    imgM (writeLog Mt [(a, 8, imgW img a)]) (a + j) = img (a + j) := by
  refine imgLE_inj (n := 8) ?_ j hj
  rw [imgLE_imgM_store, imgW_toNat]

abbrev slotWrite (Mt : Mem) (a : Nat) (w0 w1 w2 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog Mt [(a, 8, w0)]) [(a + 8, 8, w1)]) [(a + 16, 8, w2)]

theorem imgM_slotWrite_in {Mt : Mem} {a b : Nat} (img : Nat → BitVec 8) (h : InExt (a, 24) b) :
    imgM (slotWrite Mt a (imgW img a) (imgW img (a + 8)) (imgW img (a + 16))) b = img b := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  by_cases c2 : a + 16 ≤ b
  · have := imgM_store_img (Mt := writeLog (writeLog Mt [(a, 8, imgW img a)])
      [(a + 8, 8, imgW img (a + 8))]) (a := a + 16) (img := img) (j := b - (a + 16)) (by omega)
    rwa [show a + 16 + (b - (a + 16)) = b by omega] at this
  rw [imgM_store_miss _ _ (Or.inl (by omega))]
  by_cases c1 : a + 8 ≤ b
  · have := imgM_store_img (Mt := writeLog Mt [(a, 8, imgW img a)]) (a := a + 8) (img := img)
      (j := b - (a + 8)) (by omega)
    rwa [show a + 8 + (b - (a + 8)) = b by omega] at this
  rw [imgM_store_miss _ _ (Or.inl (by omega))]
  have := imgM_store_img (Mt := Mt) (a := a) (img := img) (j := b - a) (by omega)
  rwa [show a + (b - a) = b by omega] at this

theorem imgM_slotWrite_out {Mt : Mem} {a b : Nat} (w0 w1 w2 : BitVec 64) (h : ¬ InExt (a, 24) b) :
    imgM (slotWrite Mt a w0 w1 w2) b = imgM Mt b := by
  simp only [InExt] at h
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega)]

theorem toNat_append4 (f : Nat → BitVec 8) (a : Nat) :
    (((((f (a + 3)).append (f (a + 2))).append (f (a + 1))).append (f a)) : BitVec (8 * 4)).toNat =
      imgLE f a 4 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt; have h1 := (f (a + 1)).isLt; have h2 := (f (a + 1 + 1)).isLt
  have h3 := (f (a + 1 + 1 + 1)).isLt
  simp only [show a + 1 + 1 = a + 2 by omega, show a + 2 + 1 = a + 3 by omega] at *
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem bytesAt4 (f : Nat → BitVec 8) (a : Nat) :
    bytesAt f a 4 = [f a, f (a + 1), f (a + 2), f (a + 3)] := rfl

theorem bytesAt8 (f : Nat → BitVec 8) (a : Nat) :
    bytesAt f a 8 = [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6),
      f (a + 7)] := rfl

theorem ldvf_lw_imgLE {f : Nat → BitVec 8} {a k : Nat} (h : imgLE f a 4 = k) (hk : k < 2 ^ 31) :
    ldvf .lw f a = BitVec.ofNat 64 k := by
  have hw := toNat_append4 f a
  rw [h] at hw
  simp only [ldvf, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
    BitVec.toNat_signExtend]
  have hmsb : ((((f (a + 3)).append (f (a + 2))).append (f (a + 1))).append (f a) :
      BitVec (8 * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hw, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

theorem ldvf_lwu_imgLE {f : Nat → BitVec 8} {a k : Nat} (h : imgLE f a 4 = k) :
    ldvf .lwu f a = BitVec.ofNat 64 k := by
  have hw := toNat_append4 f a
  rw [h] at hw
  have hk : k < 2 ^ 32 := by have := imgLE_lt f a 4; omega
  simp only [ldvf, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend,
    BitVec.toNat_setWidth]
  rw [hw, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

theorem toNat_append8 (f : Nat → BitVec 8) (a : Nat) :
    (((((((((f (a + 7)).append (f (a + 6))).append (f (a + 5))).append (f (a + 4))).append
      (f (a + 3))).append (f (a + 2))).append (f (a + 1))).append (f a)) : BitVec (8 * 8)).toNat =
      imgLE f a 8 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt; have h1 := (f (a + 1)).isLt; have h2 := (f (a + 2)).isLt
  have h3 := (f (a + 3)).isLt; have h4 := (f (a + 4)).isLt; have h5 := (f (a + 5)).isLt
  have h6 := (f (a + 6)).isLt; have h7 := (f (a + 7)).isLt
  simp only [show a + 1 + 1 = a + 2 by omega, show a + 2 + 1 = a + 3 by omega,
    show a + 3 + 1 = a + 4 by omega, show a + 4 + 1 = a + 5 by omega,
    show a + 5 + 1 = a + 6 by omega, show a + 6 + 1 = a + 7 by omega]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem ldvf_ld_imgLE {f : Nat → BitVec 8} {a k : Nat} (h : imgLE f a 8 = k) :
    ldvf .ld f a = BitVec.ofNat 64 k := by
  have hw := toNat_append8 f a
  rw [h] at hw
  simp only [ldvf, bytesAt8, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  have hk : k < 2 ^ 64 := by have := imgLE_lt f a 8; omega
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, ← hw]
  exact congrArg BitVec.toNat (BitVec.signExtend_eq _)

theorem ldv_lw_read32 {m : Mem} {a k : Nat} (h : read32 m a = some k) (hk : k < 2 ^ 31) :
    ldv .lw m a = BitVec.ofNat 64 k := ldvf_lw_imgLE (readLE_memImg h) hk

theorem ldv_lwu_read32 {m : Mem} {a k : Nat} (h : read32 m a = some k) :
    ldv .lwu m a = BitVec.ofNat 64 k := ldvf_lwu_imgLE (readLE_memImg h)

theorem ldv_ld_read64 {m : Mem} {a k : Nat} (h : read64 m a = some k) :
    ldv .ld m a = BitVec.ofNat 64 k := ldvf_ld_imgLE (readLE_memImg h)

theorem ldv_lw_store8 (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b)
    (hk : v.toNat % 2 ^ 32 < 2 ^ 31) :
    ldv .lw (writeLog Mt [(b, 8, v)]) a = BitVec.ofNat 64 (v.toNat % 2 ^ 32) := by
  subst h
  refine ldvf_lw_imgLE ?_ hk
  have h8 := imgLE_imgM_store Mt a v
  have hs : imgLE (imgM (writeLog Mt [(a, 8, v)])) a 8 =
      imgLE (imgM (writeLog Mt [(a, 8, v)])) a 4 +
        256 ^ 4 * imgLE (imgM (writeLog Mt [(a, 8, v)])) (a + 4) 4 := imgLE_split _ a 4 4
  have := imgLE_lt (imgM (writeLog Mt [(a, 8, v)])) a 4
  have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [e] at hs this
  omega

theorem ldv_lw_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lw (writeLog Mt [(b, w, v)]) a = ldv .lw Mt a :=
  ldv_store_miss .lw Mt v h

attribute [ix_mem2_set] ldv_store_hit ldv_ld_hit_eq ldv_ld_miss ldv_lw_miss ldv_lw_store8

macro_rules
  | `(tactic| ix_mem) => `(tactic| simp_set (disch := sx_addr) ix_mem2_set at *)

section Res

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def ms (pc : BitVec 64) (R : Nat → BitVec 64) (S : Nat → Prop) (Mt : Mem) : IProp GF :=
  iprop(PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet S (fun a => a ↦ₘ imgM Mt a))

theorem ownSet_mem (S : Nat → Prop) (f : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ f a) ⊢ ∃ Mt : Mem, ownSet S (fun a => a ↦ₘ imgM Mt a) := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  obtain ⟨Mt, hMt⟩ := exists_mem_img f l
  iexists Mt, l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  rw [sepL_congr (Ψ := fun a => iprop(a ↦ₘ imgM Mt a)) (fun a ha => by rw [hMt a ha])] at *
  iexact Hl

theorem regFile_upd_ra (R : Nat → BitVec 64) (x : BitVec 64) :
    regFile (GF := GF) (upd R 1 x) = regFile R := by
  unfold regFile
  exact sepL_congr fun r hr => by
    rw [upd_other _ _ (fun e => by subst e; revert hr; decide)]

theorem sepL_iRegs (rv : Nat → BitVec 64) :
    sepL (GF := GF) iRegs (fun r => r ↦ᵣ rv r) ⊣⊢ iprop(PC ↦ᵣ rv 32 ∗ ra ↦ᵣ rv 1 ∗ regFile rv) := by
  rw [iRegs_eq]; simp only [sepL_cons]; exact .rfl

variable {live : Nat → Prop}

abbrev RunK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (F : IProp GF) (S : Nat → Prop) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  F ∗ sepL iRegs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ⊢ Wp.W Φ

theorem wp_swpF (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem}
    (h : let F' := F; SWP live text iRegs S (RunK Wp Φ F' S) pc R Mt) :
    roOwn roR text ∗ F ∗ ms pc R S Mt ⊢ Wp.W Φ := by
  obtain ⟨n, hn⟩ := h
  let rv : Nat → BitVec 64 := fun r => if r = 32 then pc else R r
  have hrun := hn rv (imgM Mt) ⟨by simp [rv, VsaIris.PC],
    fun r _ hne => by simp only [rv, show r ≠ 32 from by simpa [VsaIris.PC] using hne, ite_false],
    fun _ _ => rfl⟩
  unfold ms
  iintro ⟨#Hro, HF, ⟨Hpc, Hra, Hregs, HS⟩⟩
  iapply wp_localRunW Wp n rv (imgM Mt) hrun
  iframe Hro HS
  isplitl [Hpc Hra Hregs]
  · iapply (sepL_iRegs rv).2
    have e1 : rv 32 = pc := by simp [rv]
    have e2 : rv 1 = R 1 := by simp [rv]
    have e3 : regFile (GF := GF) rv = regFile R := by
      unfold regFile
      exact sepL_congr fun x hx => by
        have : x ≠ 32 := fun e => by subst e; revert hx; decide
        simp only [rv, this, ite_false]
    rw [e1, e2, e3]
    iframe Hpc Hra Hregs
  iintro %rv' %mv' %hq Hregs HS
  iapply hq
  iframe HF Hregs HS

theorem swp_closeF (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (h : F ∗ ms pc R S Mt ⊢ Wp.W Φ) :
    SWP live text iRegs S (RunK Wp Φ F S) pc R Mt := by
  refine swp_done fun rv mv hm => ?_
  refine .trans ?_ h
  unfold ms
  iintro ⟨HF, Hregs, HS⟩
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs rv).1 $$ Hregs
  have e1 : rv 32 = pc := hm.pc
  have e3 : ∀ x ∈ fRegs, rv x = R x := fun x hx =>
    hm.regs x (by rw [iRegs_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      (fun e => by subst e; revert hx; decide)
  have e2 : rv 1 = R 1 := hm.regs 1 (by decide) (by decide)
  rw [e1, e2]
  iframe HF Hpc Hra
  isplitl [Hregs]
  · unfold regFile
    rw [sepL_congr (Ψ := fun r => iprop(r ↦ᵣ R r)) (fun x hx => by rw [e3 x hx])] at *
    iexact Hregs
  iapply ownSet_congr (fun a ha => by rw [hm.img a ha]) $$ HS

theorem sepL_elem_persist {α : Type} (Φ : α → IProp GF) [∀ x, Persistent (Φ x)] {x : α} :
    ∀ {l : List α}, x ∈ l → sepL l Φ ⊢ Φ x
  | y :: ys, hx => by
    rw [sepL_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · iintro ⟨H, -⟩; iexact H
    · iintro ⟨-, H⟩; iapply sepL_elem_persist Φ hx $$ H

theorem sepL_bytes_sub {T : List (Nat × BitVec 8)} :
    ∀ {l : List (Nat × DFrac × BitVec 8)}, (∀ q ∈ l, q.2.1 = DFrac.discard ∧ (q.1, q.2.2) ∈ T) →
      sepL (GF := GF) T (fun p => p.1 ↦ₘ□ p.2) ⊢ sepL l (fun q => q.1 ↦ₘ{q.2.1} q.2.2)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | q :: qs, h => by
    rw [sepL_cons]
    obtain ⟨h1, h2⟩ := h q List.mem_cons_self
    iintro #H
    isplitl []
    · rw [h1]; iapply sepL_elem_persist (fun p : Nat × BitVec 8 => iprop(p.1 ↦ₘ□ p.2)) h2 $$ H
    · iapply sepL_bytes_sub (fun q hq => h q (List.mem_cons_of_mem _ hq)) $$ H

theorem instrAt_of_codeRes {i : Nat} {code : List (BitVec 8)}
    (h : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText) : codeRes (GF := GF) ⊢ instrAt i code := by
  unfold codeRes roOwn
  rw [instrAt_eq]
  iintro ⟨-, #H⟩
  iapply sepL_bytes_sub (fun q hq => ⟨?_, h q hq⟩) $$ H
  unfold codeFoot at hq
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
  rfl

theorem swp_closeM (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (h : ∀ Mt', Mt' = Mt → F ∗ ms pc R S Mt' ⊢ Wp.W Φ) :
    SWP live text iRegs S (RunK Wp Φ F S) pc R Mt :=
  swp_closeF Wp (h Mt rfl)

theorem swp_closeRM (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ R' Mt', R' = R → Mt' = Mt → F ∗ ms pc R' S Mt' ⊢ Wp.W Φ) :
    SWP live text iRegs S (RunK Wp Φ F S) pc R Mt :=
  swp_closeF Wp (h R Mt rfl rfl)

end Res

section Ends

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem ms_intro {pc r : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} :
    PC ↦ᵣ pc ∗ ra ↦ᵣ r ∗ regFile R ∗ ownSet S byteAny ⊢@{IProp GF}
      ∃ Mt, ms pc (upd R 1 r) S Mt := by
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨%f, HS⟩ := ownSet_fn S $$ HS
  ihave ⟨%Mt, HS⟩ := ownSet_mem S f $$ HS
  iexists Mt
  unfold ms
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

theorem ms_exit {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} :
    ms pc R S Mt ⊢@{IProp GF} PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet S byteAny := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  iframe Hpc Hra Hregs
  iapply ownSet_forget $$ HS

theorem roOn_view {P : Nat → Prop} {m : Mem} :
    ∀ {DA : List Nat}, (∀ a ∈ DA, P a ∧ (m[a]?).isSome) →
      roOn (GF := GF) P m ⊢ sepL DA (fun a => iprop(a ↦ₘ□ imgM m a))
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | a :: DA, h => by
    rw [sepL_cons]
    obtain ⟨hP, hs⟩ := h a List.mem_cons_self
    have hb : m[a]? = some (imgM m a) := by
      unfold imgM; cases e : m[a]? with
      | none => rw [e] at hs; cases hs
      | some b => rfl
    iintro #H
    isplitl []
    · iapply roOn_byte hP hb $$ H
    · iapply roOn_view (fun b hb => h b (List.mem_cons_of_mem _ hb)) $$ H

theorem roOwn_data {P : Nat → Prop} {m : Mem} {DA : List Nat}
    (h : ∀ a ∈ DA, P a ∧ (m[a]?).isSome) :
    codeRes (GF := GF) ∗ roOn P m ⊢ roOwn roR (interpText ++ dataOf m DA) := by
  unfold codeRes roOwn
  iintro ⟨⟨#Hgp, #Htx⟩, #Hro⟩
  iframe Hgp
  iapply (sepL_append _ _ _).2
  iframe Htx
  unfold dataOf
  rw [sepL_map]
  iapply roOn_view h $$ Hro

end Ends

abbrev binView (a : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) 4 ++ accAddrs (a + 16) 16

structure BinNode (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (tag tok : Nat)
    (aL aR : BitVec 64) : Prop where
  kind : ldv .lw m aX.toNat = BitVec.ofNat 64 tag
  kindu : ldv .lwu m aX.toNat = BitVec.ofNat 64 tag
  op : ldv .lw m (aX + 8#64).toNat = BitVec.ofNat 64 tok
  left : ldv .ld m (aX + 16#64).toNat = aL
  right : ldv .ld m (aX + 24#64).toNat = aR
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 32 ≤ 0x100000000
  off : aX.toNat + 32 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aX.toNat
  view : ∀ a ∈ binView aX.toNat, P a ∧ (m[a]?).isSome

theorem isSome_of_readLE {m : Mem} {n a v : Nat} (h : readLE m a n = some v) {i : Nat}
    (hi : i < n) : (m[a + i]?).isSome := by
  rw [readLE_mapped h i hi]; rfl

theorem binNode_of_repr {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {op : BinOp} {l r : Expr}
    (h : ExprReprWithin m P aX.toNat (.binary op l r)) (hg : ∀ k, P k → ReadOK k) :
    ∃ aL aR : Nat, BinNode m P aX 6 (binOpTok op) (BitVec.ofNat 64 aL) (BitVec.ofNat 64 aR) ∧
      ExprReprWithin m P aL l ∧ ExprReprWithin m P aR r ∧ aL < 2 ^ 64 ∧ aR < 2 ^ 64 := by
  cases h with
  | binary h6 c6 hop cop hl cl hrl hr cr hrr =>
    rename_i aL aR
    have g0 := hg _ (c6 0 (by omega)); have g3 := hg _ (c6 3 (by omega))
    have g8 := hg _ (cop 0 (by omega)); have g16 := hg _ (cl 0 (by omega))
    have g31 := hg _ (cr 7 (by omega))
    have e8 : (aX + 8#64).toNat = aX.toNat + 8 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e16 : (aX + 16#64).toNat = aX.toNat + 16 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e24 : (aX + 24#64).toNat = aX.toNat + 24 := by
      have := g31.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have htok : binOpTok op < 2 ^ 31 := by cases op <;> decide
    refine ⟨aL, aR, ⟨?_, ?_, ?_, ?_, ?_, g0.lo, ?_, ?_, ?_⟩, hrl, hrr, readLE_lt hl, readLE_lt hr⟩
    · exact ldv_lw_read32 h6 (by decide)
    · exact ldv_lwu_read32 h6
    · rw [e8]; exact ldv_lw_read32 hop htok
    · rw [e16]; exact ldv_ld_read64 hl
    · rw [e24]; exact ldv_ld_read64 hr
    · have := g31.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h16 := g16.off
      have h31 := g31.off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [List.mem_append, mem_accAddrs_iff] at ha
      rcases ha with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + j := ⟨a - aX.toNat, by omega⟩
        exact ⟨c6 j (by omega), isSome_of_readLE h6 (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 8 + j := ⟨a - (aX.toNat + 8), by omega⟩
        exact ⟨cop j (by omega), isSome_of_readLE hop (by omega)⟩
      · by_cases hj : a < aX.toNat + 24
        · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 16 + j := ⟨a - (aX.toNat + 16), by omega⟩
          exact ⟨cl j (by omega), isSome_of_readLE hl (by omega)⟩
        · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 24 + j := ⟨a - (aX.toNat + 24), by omega⟩
          exact ⟨cr j (by omega), isSome_of_readLE hr (by omega)⟩

def valTag : Value → Nat
  | .null => 0 | .bool _ => 1 | .int _ => 2 | .str _ => 3 | .closure _ => 4 | .native _ => 5

section AstRes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem astEG_of_view {m : Mem} {P : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) (hg : ∀ k, P k → ReadOK k) :
    roOn (GF := GF) P m ⊢ astEG a e := by
  unfold astEG
  iintro #H
  iexists P, m
  iframe H
  ipureintro; exact ⟨h, hg⟩

def evalArmF [InterpGS GF] (P : Nat → Prop) (m : Mem) (env : Nat) (aE s' : BitVec 64) (n' : Nat)
    (Out Wd K : IProp GF) : IProp GF :=
  iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗ stackScratch s' n' ∗ Out ∗ Wd ∗ K)

theorem valOf_tag [InterpGS GF] (N : NativeAddrs) (v : Value) (w0 w1 w2 : BitVec 64) :
    valOf (GF := GF) N v w0 w1 w2 ⊢ ⌜w0.toNat % 2 ^ 32 = valTag v⌝ := by
  cases v <;> unfold valOf <;> simp only [valTag]
  all_goals first
    | (iintro %h; ipureintro; exact h)
    | (iintro %h; ipureintro; exact h.1)
    | (iintro ⟨%h, -⟩; ipureintro; exact h.1)

end AstRes

macro "ix_reg" : tactic => `(tactic| simp_set ix_reg_set)

theorem keep_reg {ks : List Nat} {R R' : Nat → BitVec 64} (h : KeepRegs ks R R') {x : Nat}
    (hx : x ∈ ks) : R' x = R x := h x hx

theorem ofNat_lo32 {w : BitVec 64} {k : Nat} (h : w.toNat % 2 ^ 32 = k) :
    BitVec.ofNat 64 (w.toNat % 2 ^ 32) = BitVec.ofNat 64 k := by rw [h]

syntax "ix_fwd" (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| ix_fwd) => `(tactic| simp (disch := first | rfl | sx_addr) only [slotWrite, ldv_store_hit,
      ldv_ld_hit_eq, ldv_ld_miss, ldv_lw_miss, ldv_lw_store8])
  | `(tactic| ix_fwd using [$hs,*]) => do
    let lems ← hs.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
    `(tactic| ((try simp (disch := decide) only [$lems,*]); ix_fwd))

theorem toInt_add_wrap (x y : BitVec 64) : (x + y).toInt = wrap64 (x.toInt + y.toInt) := by
  unfold wrap64; rw [BitVec.toInt_add, BitVec.toInt_ofInt]

theorem keep_helper {clob : List Nat} {R R' : Nat → BitVec 64}
    (h : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) {x : Nat} (hx : x ∈ fRegs) (hc : x ∉ clob) :
    R' x = R x := h x hx hc

syntax "ix_keep " "[" term,* "]" : tactic
macro_rules
  | `(tactic| ix_keep [$hs,*]) => do
    let mut t ← `(tactic| (try ix_reg))
    for h in hs.getElems do
      let st ← `(tactic| (try rw [keep_reg $h (by decide)]))
      let sh ← `(tactic| (try rw [keep_helper $h (by decide) (by decide)]))
      t ← `(tactic| ($t; $st; $sh; (try ix_reg)))
    `(tactic| ($t; (try rfl)))

theorem toInt_sub_wrap (x y : BitVec 64) : (x - y).toInt = wrap64 (x.toInt - y.toInt) := by
  unfold wrap64; rw [BitVec.toInt_sub, BitVec.toInt_ofInt]

macro "keep_split" : tactic => `(tactic| (intro x hx; simp only [calleeSaved, List.mem_cons,
  List.not_mem_nil, _root_.or_false] at hx; repeat' (first | subst hx | rcases hx with hx | hx)))

theorem KeepRegs.sub {ks ks' : List Nat} {R R' : Nat → BitVec 64} (h : KeepRegs ks R R')
    (hs : ∀ x ∈ ks', x ∈ ks) : KeepRegs ks' R R' := fun x hx => h x (hs x hx)

abbrev evalSP (s : BitVec 64) : BitVec 64 := s + 18446744073709550528#64

theorem evalSP_eq (s : BitVec 64) : s - 1088#64 = evalSP s := by
  rw [BitVec.sub_eq_add_neg]; rfl

theorem evalSP_restore (s : BitVec 64) : evalSP s + 1088#64 = s := by
  rw [BitVec.add_assoc, show (18446744073709550528#64 + 1088#64 : BitVec 64) = 0#64 by decide,
    BitVec.add_zero]

theorem evalSP_off {s : BitVec 64} (hsf : (evalSP s).toNat = s.toNat - 1088)
    (hs : s.toNat ≤ 0x100000000) (c : Nat) (hc : c < 4096) :
    (evalSP s + BitVec.ofNat 64 c).toNat = s.toNat - 1088 + c := by
  rw [BitVec.toNat_add, hsf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

structure EvalSaved (Mt : Mem) (s ret v8 v9 v18 v19 : BitVec 64) : Prop where
  ra : ldv .ld Mt (s.toNat - 1088 + 1080) = ret
  s0 : ldv .ld Mt (s.toNat - 1088 + 1072) = v8
  s1 : ldv .ld Mt (s.toNat - 1088 + 1064) = v9
  s2 : ldv .ld Mt (s.toNat - 1088 + 1056) = v18
  s3 : ldv .ld Mt (s.toNat - 1088 + 1048) = v19

theorem EvalSaved.store {Mt : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : EvalSaved Mt s ret v8 v9 v18 v19) {a w : Nat} (v : BitVec 64)
    (ha : a + w ≤ s.toNat - 1088 + 1048) :
    EvalSaved (writeLog Mt [(a, w, v)]) s ret v8 v9 v18 v19 :=
  ⟨by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.ra,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s0,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s1,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s2,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s3⟩

theorem EvalSaved.slotWrite {Mt : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : EvalSaved Mt s ret v8 v9 v18 v19) {a : Nat} (w0 w1 w2 : BitVec 64)
    (ha : a + 24 ≤ s.toNat - 1088 + 1048) :
    EvalSaved (slotWrite Mt a w0 w1 w2) s ret v8 v9 v18 v19 :=
  ((h.store w0 (by omega)).store w1 (by omega)).store w2 (by omega)

syntax "ix_saved " term " using " term : tactic
macro_rules
  | `(tactic| ix_saved $h using $hoff) => `(tactic| (
      (try unfold slotWrite);
      repeat refine EvalSaved.store ?_ _ (by first | omega | (rw [($hoff:term)] <;> first | omega | decide));
      exact $h))

structure EvalCallGeom (s : BitVec 64) (np nc o : Nat) : Prop where
  sp : (evalSP s).toNat = s.toNat - 1088
  slot : (evalSP s + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o
  child : StackGeom (evalSP s) nc
  fits : nc ≤ np - 1088
  below : np - 1088 ≤ (evalSP s).toNat
  slotGeom : SlotGeom (evalSP s + BitVec.ofNat 64 o)

theorem evalCallGeom {s : BitVec 64} {np nc : Nat} (hsg : StackGeom s np) (hle : nc + 1088 ≤ np)
    {o : Nat} (ho : o + 24 ≤ 1088) (ho8 : o % 8 = 0) : EvalCallGeom s np nc o := by
  have h1 := hsg.le; have h2 := hsg.lo; have h3 := hsg.hi; have h4 := hsg.al; have h5 := hsg.top
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2 h3
  have hsp : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hsl : (evalSP s + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o := by
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsp, hsl, ⟨by omega, ?_, ?_, ?_, ?_⟩, by omega, by omega, ⟨?_, ?_, ?_⟩⟩
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · omega
  · omega
  · rw [hsl]; omega
  · rw [hsl]; unfold Vsa.Sim.tohostAddr; omega
  · rw [hsl]; omega

section FrameRes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem evalFrame_join {s : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hf : 1088 ≤ n) :
    stackScratch (GF := GF) (evalSP s) (n - 1088) ∗ ownSet (InExt (s.toNat - 1088, 1088)) byteAny ⊢
      stackScratch s n := by
  have e : (s - 1088#64).toNat = s.toNat - 1088 := toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 1088#64) (n := n) hn (by simp only [BitVec.toNat_ofNat]; omega)
  rw [e, show (1088#64).toNat = 1088 from rfl, evalSP_eq] at h
  exact h

end FrameRes

section Calls

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

theorem ownSet_carve_slot {S : Nat → Prop} {Mt : Mem} {a : Nat} (h : ∀ b, InExt (a, 24) b → S b) :
    ownSet (GF := GF) S (fun b => b ↦ₘ imgM Mt b) ⊢
      ownSet (fun b => S b ∧ ¬ InExt (a, 24) b) (fun b => b ↦ₘ imgM Mt b) ∗ slot24 a := by
  iintro H
  ihave ⟨H1, H2⟩ := ownSet_split S (InExt (a, 24)) _ $$ H
  iframe H2
  unfold slot24 blockOwn
  ihave H1 := ownSet_forget _ _ $$ H1
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.2, fun hb => ⟨h b hb, hb⟩⟩) $$ H1

theorem ownSet_join_slot {S : Nat → Prop} {Mt : Mem} {a : Nat} {v : Value}
    (h : ∀ b, InExt (a, 24) b → S b) :
    ownSet (GF := GF) (fun b => S b ∧ ¬ InExt (a, 24) b) (fun b => b ↦ₘ imgM Mt b) ∗ valAt N a v ⊢
      ∃ w0 w1 w2, □ valOf N v w0 w1 w2 ∗
        ownSet S (fun b => b ↦ₘ imgM (slotWrite Mt a w0 w1 w2) b) := by
  unfold valAt
  iintro ⟨H1, %img, H2, #Hv⟩
  iexists imgW img a, imgW img (a + 8), imgW img (a + 16)
  isplitr
  · imodintro; iexact Hv
  ihave H1 := ownSet_congr (Ψ := fun b => iprop(b ↦ₘ imgM (slotWrite Mt a (imgW img a)
      (imgW img (a + 8)) (imgW img (a + 16))) b)) (fun b hb => by rw [imgM_slotWrite_out _ _ _ hb.2]) $$ H1
  ihave H2 := ownSet_congr (Ψ := fun b => iprop(b ↦ₘ imgM (slotWrite Mt a (imgW img a)
      (imgW img (a + 8)) (imgW img (a + 16))) b)) (fun b hb => by rw [imgM_slotWrite_in img hb]) $$ H2
  ihave H := ownSet_join _ _ _ (fun b (hb : S b ∧ ¬ InExt (a, 24) b) h2 => hb.2 h2) $$ [$]
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.elim (·.1) (h b), fun hb => by
    by_cases hs : InExt (a, 24) b
    · exact .inr hs
    · exact .inl ⟨hb, hs⟩⟩) $$ H

theorem ms_callEvalT {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code evalEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (D : EvalECost st d env e st' v n)
    {k : Nat} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {slot aC aE s : BitVec 64}
    {m : Nat}
    (hsg : StackGeom s (evalNeed e d)) (hm : evalNeed e d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom slot) (hbb : e.bodiesBound perCallBudget = true) :
    ⌜EvalRegs R slot (BitVec.ofNat 64 inp) aC aE s ∧ ∀ b, InExt (slot.toNat, 24) b → S b⌝ ∗
      evalSpecT_body (vsaModel live) N L Room inp st d env e st' v n D ∗ codeRes ∗
      □ astEG aC.toNat e ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64), ⌜KeepRegs calleeSaved R R'⌝ -∗
        □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S
          (slotWrite Mt slot.toNat w0 w1 w2) -∗
        stackScratch s m -∗ world N L Room inp (.counted k) st' d -∗
        (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  unfold ms evalSpecT_body
  iintro ⟨%⟨hregs, hslot⟩, Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hw, Hk⟩
  ihave ⟨HS, Hslot⟩ := ownSet_carve_slot hslot $$ HS
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %k %slot %aE %aC %s %R
  iapply wp_callW (twpW (vsaModel live)) hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold evalPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  iintro Hpc Hra Hpost
  unfold evalPost
  icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hval, Hw⟩
  ihave Hst := stackScratch_widen hms hm $$ [$]
  ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hslot $$ [$]
  iapply Hk $$ %R' %w0 %w1 %w2 %hkeep Hv [Hpc Hra Hregs HS] Hst Hw
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

theorem ms_callExecT {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code execEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {st : St} {d env : Nat} {sm : Stmt} {st' : St} {status : Status} {n : Nat}
    (D : ExecSCost st d env sm st' status n)
    {k : Nat} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {aS aE aRet s : BitVec 64} {m : Nat}
    (hsg : StackGeom s (execNeed sm d)) (hm : execNeed sm d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom aRet) (hbb : sm.bodiesBound perCallBudget = true) :
    ⌜ExecRegs R (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗
      execSpecT_body (vsaModel live) N L Room inp st d env sm st' status n D ∗ codeRes ∗
      □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗ slot24 aRet.toNat ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s m -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  unfold ms execSpecT_body
  iintro ⟨%hregs, Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hslot, Hw, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %k %aS %aE %aRet %s %R
  iapply wp_callW (twpW (vsaModel live)) hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold execPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  iintro Hpc Hra Hpost
  unfold execPost
  icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hret, Hw⟩
  ihave Hst := stackScratch_widen hms hm $$ [$]
  iapply Hk $$ %R' %hkeep [Hpc Hra Hregs HS] Hst Hret Hw
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

theorem execSpecsP_at (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) :
    execSpecsP (vsaModel live) N L Room inp Core ⊢
      ▷ execSpecP_body (vsaModel live) N L Room inp Core st d env sm := by
  unfold execSpecsP
  iintro #H
  inext
  iapply H

theorem ms_callExecPM {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code execEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {aS aE aRet s : BitVec 64} {m : Nat}
    {K : IProp GF}
    (hsg : StackGeom s (execNeed sm d)) (hm : execNeed sm d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom aRet) (hbb : sm.bodiesBound perCallBudget = true)
    (hab : K ⊢ iprop(abortAt Core s m ∗ slot24 aRet.toNat ∗ ownSet S (fun a => a ↦ₘ imgM Mt a)) -∗
      (wpW (vsaModel live)).W Φ) :
    ⌜ExecRegs R (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗
      ▷ execSpecP_body (vsaModel live) N L Room inp Core st d env sm ∗ codeRes ∗
      □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗ K ∗
      (∀ (R' : Nat → BitVec 64) (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s m -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ K -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold ms execSpecP_body
  iintro ⟨%hregs, Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hslot, Hw, HK, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %aS %aE %aRet %s %R
  have hab' := hab
  simp only [wpW_W] at hab' ⊢
  iapply wp_callAbort_later hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold execPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  isplit
  · iintro Hpc Hra ⟨%st', %status, %hE, Hpost⟩
    unfold execPost
    icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hret, Hw⟩
    ihave Hst := stackScratch_widen hms hm $$ [$]
    iapply Hk $$ %R' %st' %status %hE %hkeep [Hpc Hra Hregs HS] Hst Hret Hw HK
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro ⟨HA, Hslot⟩
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    ihave Hst := stackScratch_widen hms hm $$ [$]
    ihave HA := abortAt_intro _ _ _ $$ [HC Hst]
    · iframe HC Hst
    ihave HK := hab' $$ HK
    iapply HK
    iframe HA Hslot HS

theorem ms_callExecP {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code execEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {aS aE aRet s : BitVec 64} {m : Nat}
    {Kret : IProp GF}
    (hsg : StackGeom s (execNeed sm d)) (hm : execNeed sm d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom aRet) (hbb : sm.bodiesBound perCallBudget = true) :
    ⌜ExecRegs R (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗
      ▷ execSpecP_body (vsaModel live) N L Room inp Core st d env sm ∗ codeRes ∗
      □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      (Kret ∧ (iprop(abortAt Core s m ∗ slot24 aRet.toNat ∗ ownSet S byteAny) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s m -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗
        (Kret ∧ (iprop(abortAt Core s m ∗ slot24 aRet.toNat ∗ ownSet S byteAny) -∗
          (wpW (vsaModel live)).W Φ)) -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ :=
  ms_callExecPM hexec hcode hal hsg hm hms hslg hbb (by
    iintro HK ⟨HA, Hslot, HS⟩
    ihave HS := ownSet_forget _ _ $$ HS
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe HA Hslot HS)

theorem ms_callHelper (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} :
    ⌜pins R⌝ ∗ helperSpec (vsaModel live) Wp entry clob pins Pre Post ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ Pre ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗ Post R' -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms helperSpec
  iintro ⟨%hpins, Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HPre, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %R
  iapply wp_callW Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs HPre]
  · iframe Hregs HPre Hcode
    ipureintro; exact ⟨hal, hpins⟩
  iintro Hpc Hra Hpost
  icases Hpost with ⟨%R', Hregs, %hkeep, HPost⟩
  iapply Hk $$ %R' %hkeep HPost
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

theorem evalSpecsP_at (Core : IProp GF) (st : St) (d env : Nat) (e : Expr) :
    evalSpecsP (vsaModel live) N L Room inp Core ⊢
      ▷ evalSpecP_body (vsaModel live) N L Room inp Core st d env e := by
  unfold evalSpecsP
  iintro #H
  inext
  iapply H

theorem ownSet_unslot {S : Nat → Prop} {Mt : Mem} {a : Nat} (h : ∀ b, InExt (a, 24) b → S b) :
    ownSet (GF := GF) (fun b => S b ∧ ¬ InExt (a, 24) b) (fun b => b ↦ₘ imgM Mt b) ∗ slot24 a ⊢
      ownSet S byteAny := by
  unfold slot24 blockOwn
  iintro ⟨H1, H2⟩
  ihave H1 := ownSet_forget _ _ $$ H1
  ihave H := ownSet_join _ _ _ (fun b (hb : S b ∧ ¬ InExt (a, 24) b) h2 => hb.2 h2) $$ [$]
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.elim (·.1) (h b), fun hb => by
    by_cases hs : InExt (a, 24) b
    · exact .inr hs
    · exact .inl ⟨hb, hs⟩⟩) $$ H

theorem ms_callEvalP {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code evalEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    {R : Nat → BitVec 64} {Mt : Mem} {slot aC aE s0 sret0 : BitVec 64} {m n0 : Nat}
    {Out Kret : IProp GF} (hOut : Out ⊢ slot24 sret0.toNat)
    (hsg : StackGeom (evalSP s0) (evalNeed e d)) (hm : evalNeed e d ≤ m)
    (hms : m ≤ (evalSP s0).toNat) (hn0 : m + 1088 = n0) (hn0s : n0 ≤ s0.toNat)
    (hslg : SlotGeom slot) (hbb : e.bodiesBound perCallBudget = true) :
    ⌜EvalRegs R slot (BitVec.ofNat 64 inp) aC aE (evalSP s0) ∧
      ∀ b, InExt (slot.toNat, 24) b → InExt (s0.toNat - 1088, 1088) b⌝ ∗
      ▷ evalSpecP_body (vsaModel live) N L Room inp Core st d env e ∗ codeRes ∗
      □ astEG aC.toNat e ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R (InExt (s0.toNat - 1088, 1088)) Mt ∗ stackScratch (evalSP s0) m ∗
      world N L Room inp .uncounted st d ∗ Out ∗
      (Kret ∧ (iprop(abortAt Core s0 n0 ∗ slot24 sret0.toNat) -∗ (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (st' : St) (v : Value),
        ⌜EvalE st d env e st' v⌝ -∗ ⌜KeepRegs calleeSaved R R'⌝ -∗ □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4)))
          (InExt (s0.toNat - 1088, 1088)) (slotWrite Mt slot.toNat w0 w1 w2) -∗
        stackScratch (evalSP s0) m -∗ world N L Room inp .uncounted st' d -∗ Out -∗
        (Kret ∧ (iprop(abortAt Core s0 n0 ∗ slot24 sret0.toNat) -∗ (wpW (vsaModel live)).W Φ)) -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold ms evalSpecP_body
  iintro ⟨%⟨hregs, hslot⟩, Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hw, HOut, HK, Hk⟩
  ihave ⟨HS, Hslot⟩ := ownSet_carve_slot hslot $$ HS
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %slot %aE %aC %(evalSP s0) %R
  simp only [wpW_W]
  iapply wp_callAbort_later hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold evalPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  isplit
  · iintro Hpc Hra ⟨%st', %v, %hE, Hpost⟩
    unfold evalPost
    icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hval, Hw⟩
    ihave Hst := stackScratch_widen hms hm $$ [$]
    ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hslot $$ [$]
    iapply Hk $$ %R' %w0 %w1 %w2 %st' %v %hE %hkeep Hv [Hpc Hra Hregs HS] Hst Hw HOut HK
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro ⟨HA, Hslot⟩
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    ihave Hst := stackScratch_widen hms hm $$ [$]
    ihave HS := ownSet_unslot hslot $$ [$]
    ihave Hst := evalFrame_join (s := s0) (n := n0) hn0s (by omega) $$ [Hst HS]
    · rw [show n0 - 1088 = m by omega]; iframe Hst HS
    ihave HOut := hOut $$ HOut
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe HC Hst HOut

end Calls

end VsaIris.Interp
