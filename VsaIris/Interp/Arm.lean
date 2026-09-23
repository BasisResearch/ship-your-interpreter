import VsaIris.Interp.SpecEval
import VsaIris.Interp.Bridge
import VsaIris.Interp.IRun

/-!
# The arm layer: symbolic runs between Iris steps (lane G)

INTERP_DESIGN.md §6. A generated case lemma (`Case/*T.lean`, `Case/*P.lean`)
is a chain of three kinds of step over ONE resource, the machine state of the
arm at a symbolic point (`ms pc R S Mt`: the PC, `ra`, the body's registers at
the valuation `R`, and the owned frame bytes `S` at the tracking memory
`Mt`'s image):

* a **run** (`wp_swpW`): a first-order symbolic run (`SWP`, driven by
  `ix_run`) from `ms pc R S Mt` to `ms pcf Rf S Mtf`, whose end state is
  whatever the run computed;
* a **child call** (`ms_callEvalT`, `ms_callEvalP`): the recursive call into
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

/-- **A symbolic run**, for either WP: from the machine state at `pc`, the
run `h` ends at the machine state `pcf`/`Rf`/`Mtf` it computed. The read-only
bytes `text` (code, jump tables, the AST view) are persistent. -/
theorem wp_swpW (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc pcf : BitVec 64}
    {R Rf : Nat → BitVec 64} {Mt Mtf : Mem}
    (h : SWP live text iRegs S (Matches iRegs S pcf Rf Mtf) pc R Mt) :
    roOwn roR text ∗ ms pc R S Mt ∗ (ms pcf Rf S Mtf -∗ Wp.W Φ) ⊢ Wp.W Φ := by
  obtain ⟨n, hn⟩ := h
  let rv : Nat → BitVec 64 := fun r => if r = 32 then pc else R r
  have hrun := hn rv (imgM Mt) ⟨by simp [rv, VsaIris.PC],
    fun r _ hne => by simp only [rv, show r ≠ 32 from by simpa [VsaIris.PC] using hne, if_false],
    fun _ _ => rfl⟩
  unfold ms
  iintro ⟨#Hro, ⟨Hpc, Hra, Hregs, HS⟩, Hk⟩
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
        simp only [rv, this, if_false]
    rw [e1, e2, e3]
    iframe Hpc Hra Hregs
  iintro %rv' %mv' %hm Hregs HS
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs rv').1 $$ Hregs
  have e1 : rv' 32 = pcf := hm.pc
  have e3 : ∀ x ∈ fRegs, rv' x = Rf x := fun x hx =>
    hm.regs x (by rw [iRegs_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      (fun e => by subst e; revert hx; decide)
  have e2 : rv' 1 = Rf 1 := hm.regs 1 (by decide) (by decide)
  iapply Hk
  rw [e1, e2]
  iframe Hpc Hra
  isplitl [Hregs]
  · unfold regFile
    rw [sepL_congr (Ψ := fun r => iprop(r ↦ᵣ Rf r)) (fun x hx => by rw [e3 x hx])] at *
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

/-- A run that ends where it is: the symbolic end state is the current one. -/
theorem swp_matches {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} :
    SWP live text rs S (Matches rs S pc R Mt) pc R Mt :=
  swp_done fun _ _ hm => hm

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
    (hregs : EvalRegs R slot (BitVec.ofNat 64 inp) aC aE s)
    (hslot : ∀ b, InExt (slot.toNat, 24) b → S b)
    (hsg : StackGeom s (evalNeed e d)) (hm : evalNeed e d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom slot) (hbb : e.bodiesBound perCallBudget = true) :
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
  iintro ⟨Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hw, Hk⟩
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
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (hpins : pins R) :
    helperSpec (vsaModel live) Wp entry clob pins Pre Post ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ Pre ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗ Post R' -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms helperSpec
  iintro ⟨Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HPre, Hk⟩
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
