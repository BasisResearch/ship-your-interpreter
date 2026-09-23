import VsaIris.Interp.SpecEval
import VsaIris.Interp.Bridge
import VsaIris.Interp.ITac

/-!
# The arm layer: symbolic runs between Iris steps (lane G)

INTERP_DESIGN.md §6. A generated case lemma (`Case/*T.lean`, `Case/*P.lean`)
is a chain of three kinds of step over ONE resource, the machine state of the
arm at a symbolic point (`ms pc R S Mt`: the PC, `ra`, the body's registers at
the valuation `R`, and the owned frame bytes `S` at the tracking memory
`Mt`'s image):

* a **run** (`wp_swpF`): a first-order symbolic run (`SWP`, driven by
  `ix_run`) from `ms pc R S Mt`, in continuation form: its post (`RunK`) is
  the rest of the arm, an Iris entailment from the frame `F` and the end
  state's machine state (`swp_closeF`). The end state is whatever the run
  computed, and nothing about it is written down;
* a **child call** (`ms_callEvalT`): the recursive call into
  `eval_expr` through its spec, the result slot carved out of `S` and joined
  back as three written words (`slotWrite`) whose meaning is `□ valOf`;
* a **helper call** (`ms_callHelper`): a runtime helper through its
  `helperSpec`.

After a call the tracking memory is the old one with the slot's three words
written, so the store forwarding of the symbolic runs (`sx_mem`) reads the
child's result and every frame word the child did not touch.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-! ## Tracking memories and byte images -/

theorem iRegs_eq : iRegs = 32 :: 1 :: fRegs := rfl

/-- A tracking memory holding any byte function on a finite address list. -/
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

/-- Little-endian decoding is injective on the bytes. -/
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

/-- The bytes of a doubleword just stored. -/
theorem imgM_store_img {Mt : Mem} {a : Nat} {img : Nat → BitVec 8} {j : Nat} (hj : j < 8) :
    imgM (writeLog Mt [(a, 8, imgW img a)]) (a + j) = img (a + j) := by
  refine imgLE_inj (n := 8) ?_ j hj
  rw [imgLE_imgM_store, imgW_toNat]

/-- A slot's three words written into a tracking memory. -/
abbrev slotWrite (Mt : Mem) (a : Nat) (w0 w1 w2 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog Mt [(a, 8, w0)]) [(a + 8, 8, w1)]) [(a + 16, 8, w2)]

/-- Writing an image's three words reads back the image on the slot. -/
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

/-- Off the slot, writing its words changes nothing. -/
theorem imgM_slotWrite_out {Mt : Mem} {a b : Nat} (w0 w1 w2 : BitVec 64) (h : ¬ InExt (a, 24) b) :
    imgM (slotWrite Mt a w0 w1 w2) b = imgM Mt b := by
  simp only [InExt] at h
  rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
    imgM_store_miss _ _ (by omega)]

/-! ## Load values through the little-endian image -/

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

/-- A signed word load of a small value. -/
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

/-- An unsigned word load. -/
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

/-- A doubleword load. -/
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

/-- A word load of the low half of a doubleword just stored. -/
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

/-- A word load through a disjoint store. -/
theorem ldv_lw_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lw (writeLog Mt [(b, w, v)]) a = ldv .lw Mt a :=
  ldv_store_miss .lw Mt v h

/-- Store forwarding for doubleword and word loads (`ix_run`'s normalizer). -/
macro_rules
  | `(tactic| ix_mem) => `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8] at *)

section Res

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The machine state of an arm at a symbolic point**: the PC, `ra` (at
`R 1`), the body's registers at `R`, and the owned bytes `S` at the tracking
memory `Mt`'s image. -/
def ms (pc : BitVec 64) (R : Nat → BitVec 64) (S : Nat → Prop) (Mt : Mem) : IProp GF :=
  iprop(PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet S (fun a => a ↦ₘ imgM Mt a))

/-- An owned byte set at any image is a tracking memory's image. -/
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

/-- `ra` is not a body register. -/
theorem regFile_upd_ra (R : Nat → BitVec 64) (x : BitVec 64) :
    regFile (GF := GF) (upd R 1 x) = regFile R := by
  unfold regFile
  exact sepL_congr fun r hr => by
    rw [upd_other _ _ (fun e => by subst e; revert hr; decide)]

/-- Registers at a valuation are the body's registers and the PC/`ra`. -/
theorem sepL_iRegs (rv : Nat → BitVec 64) :
    sepL (GF := GF) iRegs (fun r => r ↦ᵣ rv r) ⊣⊢ iprop(PC ↦ᵣ rv 32 ∗ ra ↦ᵣ rv 1 ∗ regFile rv) := by
  rw [iRegs_eq]; simp only [sepL_cons]; exact .rfl

variable {live : Nat → Prop}

/-- The post of a symbolic run in continuation form: from the end state's
registers and bytes, with the frame `F`, the rest of the arm is proved. -/
abbrev RunK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (F : IProp GF) (S : Nat → Prop) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  F ∗ sepL iRegs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ⊢ Wp.W Φ

/-- **A symbolic run**, for either WP, in continuation form: from the
machine state at `pc`, the run `h` reaches an end state from which the rest
of the arm, with the frame `F`, is proved (`swp_closeF`). The read-only bytes
`text` (code, jump tables, the AST view) are persistent. The frame is
`let`-bound in the premise: the proof introduces it as an opaque local, so the
symbolic run's normalizers (`simp … at *`) never rewrite inside it. -/
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

/-- **The end of a symbolic run**: at the symbolic end state, the rest of the
arm is an Iris entailment over the machine state there. -/
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

/-- An element of a persistent separating list. -/
theorem sepL_elem_persist {α : Type} (Φ : α → IProp GF) [∀ x, Persistent (Φ x)] {x : α} :
    ∀ {l : List α}, x ∈ l → sepL l Φ ⊢ Φ x
  | y :: ys, hx => by
    rw [sepL_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · iintro ⟨H, -⟩; iexact H
    · iintro ⟨-, H⟩; iapply sepL_elem_persist Φ hx $$ H

/-- A persistent byte list covers every sub-footprint of it. -/
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

/-- An instruction's bytes, from the interpreter's code. -/
theorem instrAt_of_codeRes {i : Nat} {code : List (BitVec 8)}
    (h : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText) : codeRes (GF := GF) ⊢ instrAt i code := by
  unfold codeRes roOwn
  rw [instrAt_eq]
  iintro ⟨-, #H⟩
  iapply sepL_bytes_sub (fun q hq => ⟨?_, h q hq⟩) $$ H
  unfold codeFoot at hq
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
  rfl

end Res

/-! ## Entry, exit, the data view -/

section Ends

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Entering an arm**: the PC, `ra`, the body's registers and the owned
frame bytes become the machine state, at some tracking memory. -/
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

/-- **Leaving an arm**: the machine state gives back the PC, `ra`, the
registers and the frame bytes. -/
theorem ms_exit {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} :
    ms pc R S Mt ⊢@{IProp GF} PC ↦ᵣ pc ∗ ra ↦ᵣ R 1 ∗ regFile R ∗ ownSet S byteAny := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  iframe Hpc Hra Hregs
  iapply ownSet_forget $$ HS

/-- The present bytes of a read-only view, one by one. -/
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

/-- **The data view of a run**: the code, `gp`, and the bytes `DA` of a
read-only memory view, persistent. Every byte of `DA` is in the view's set
and present. -/
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

/-! ## AST nodes -/

/-- The bytes of a two-child node a run reads: the tag, the operator word,
the two child pointers (not the line field at `+4`). -/
abbrev binView (a : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) 4 ++ accAddrs (a + 16) 16

/-- What a two-child node (`binary`, `logical`) gives the runs: its word
reads at the node's register value, its view, and its placement. -/
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

/-- A binary node's facts, from its representation over a geometric view. -/
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

section AstRes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A child's persistent AST, from the parent's view. -/
theorem astEG_of_view {m : Mem} {P : Nat → Prop} {a : Nat} {e : Expr}
    (h : ExprReprWithin m P a e) (hg : ∀ k, P k → ReadOK k) :
    roOn (GF := GF) P m ⊢ astEG a e := by
  unfold astEG
  iintro #H
  iexists P, m
  iframe H
  ipureintro; exact ⟨h, hg⟩

/-- **The frame of an `eval_expr` arm** beside its machine state: the code,
the AST view, the frame binding, the stack below the lowered `sp`, the result
slot (`Out`: `slot24` before the result is written, `valAt` after), the world
`Wd` and the return continuation `K`. -/
def evalArmF [InterpGS GF] (P : Nat → Prop) (m : Mem) (env : Nat) (aE s' : BitVec 64) (n' : Nat)
    (Out Wd K : IProp GF) : IProp GF :=
  iprop(codeRes ∗ roOn P m ∗ frameAt env aE.toNat ∗ stackScratch s' n' ∗ Out ∗ Wd ∗ K)

end AstRes

/-- Read a register of a symbolic end state (an `upd` chain at a literal). -/
macro "ix_reg" : tactic => `(tactic| simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])

theorem keep_reg {ks : List Nat} {R R' : Nat → BitVec 64} (h : KeepRegs ks R R') {x : Nat}
    (hx : x ∈ ks) : R' x = R x := h x hx

/-- A word's low half, as a loaded value, when it is a small tag. -/
theorem ofNat_lo32 {w : BitVec 64} {k : Nat} (h : w.toNat % 2 ^ 32 = k) :
    BitVec.ofNat 64 (w.toNat % 2 ^ 32) = BitVec.ofNat 64 k := by rw [h]

/-! ## `eval_expr`'s frame -/

/-- `eval_expr`'s stack pointer after its prologue (`addi sp,sp,-1088`), in the
form the runs compute. -/
abbrev evalSP (s : BitVec 64) : BitVec 64 := s + 18446744073709550528#64

theorem evalSP_eq (s : BitVec 64) : s - 1088#64 = evalSP s := by
  rw [BitVec.sub_eq_add_neg]; rfl

/-- The geometry of a child call from `eval_expr`'s frame: the child runs at
the lowered `sp` with its budget, its result slot at frame offset `o`. -/
structure EvalCallGeom (s : BitVec 64) (np nc o : Nat) : Prop where
  sp : (evalSP s).toNat = s.toNat - 1088
  slot : (evalSP s + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o
  child : StackGeom (evalSP s) nc
  fits : nc ≤ np - 1088
  below : np - 1088 ≤ (evalSP s).toNat
  slotGeom : SlotGeom (evalSP s + BitVec.ofNat 64 o)

theorem evalCallGeom {s : BitVec 64} {np nc : Nat} (hsg : StackGeom s np) (hle : nc + 1088 ≤ np)
    {o : Nat} (ho : o + 24 ≤ 1088) (ho8 : o % 8 = 0) : EvalCallGeom s np nc o := by
  have h1 := hsg.le; have h2 := hsg.lo; have h3 := hsg.hi; have h4 := hsg.al
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2 h3
  have hsp : (evalSP s).toNat = s.toNat - 1088 := by
    rw [← evalSP_eq]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hsl : (evalSP s + BitVec.ofNat 64 o).toNat = s.toNat - 1088 + o := by
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsp, hsl, ⟨by omega, ?_, ?_, ?_⟩, by omega, by omega, ⟨?_, ?_, ?_⟩⟩
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · omega
  · rw [hsl]; omega
  · rw [hsl]; unfold Vsa.Sim.tohostAddr; omega
  · rw [hsl]; omega

/-! ## Calls -/

section Calls

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- Carve a 24-byte slot out of the owned frame bytes. -/
theorem ownSet_carve_slot {S : Nat → Prop} {Mt : Mem} {a : Nat} (h : ∀ b, InExt (a, 24) b → S b) :
    ownSet (GF := GF) S (fun b => b ↦ₘ imgM Mt b) ⊢
      ownSet (fun b => S b ∧ ¬ InExt (a, 24) b) (fun b => b ↦ₘ imgM Mt b) ∗ slot24 a := by
  iintro H
  ihave ⟨H1, H2⟩ := ownSet_split S (InExt (a, 24)) _ $$ H
  iframe H2
  unfold slot24 blockOwn
  ihave H1 := ownSet_forget _ _ $$ H1
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.2, fun hb => ⟨h b hb, hb⟩⟩) $$ H1

/-- Join a slot holding a represented value back into the owned frame bytes:
the tracking memory gets the slot's three words, whose meaning is `valOf`. -/
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
  ihave H := ownSet_join _ _ _ (fun b (hb : S b ∧ ¬ InExt (a, 24) b) h2 => hb.2 h2) $$ [H1 H2]
  · iframe H1 H2
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.elim (·.1) (h b), fun hb => by
    by_cases hs : InExt (a, 24) b
    · exact .inr hs
    · exact .inl ⟨hb, hs⟩⟩) $$ H

/-- **A child call into `eval_expr`, total mode.** At the `jal` at `i`, the
arm hands the child the body's registers (argument pins `EvalRegs`), the
result slot carved out of its frame bytes, the stack below its `sp`, the code,
the AST and frame bindings and the world at `k + n` credits; it gets back the
callee-saved registers, the slot's three words with their meaning, and the
world at `k` credits. -/
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
  ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
  · iframe Hslack Hst
  ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hslot $$ [HS Hval]
  · iframe HS Hval
  iapply Hk $$ %R' %w0 %w1 %w2 %hkeep Hv [Hpc Hra Hregs HS] Hst Hw
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

/-- **A helper call**, for either WP: at the `jal` at `i` into a helper meeting
`helperSpec`, the arm hands over the body's registers (the helper's argument
facts `pins` on them) and `Pre`; it gets back the registers the helper keeps
and `Post`. The frame bytes stay with the arm. -/
theorem ms_callHelper (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
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
    ipureintro; exact hpins
  iintro Hpc Hra Hpost
  icases Hpost with ⟨%R', Hregs, %hkeep, HPost⟩
  iapply Hk $$ %R' %hkeep HPost
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

end Calls

end VsaIris.Interp
