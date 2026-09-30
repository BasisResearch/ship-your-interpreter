import VsaIris.Call

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

open Classical

section OwnSet

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

abbrev byteAny (a : Nat) : IProp GF := iprop(∃ b, a ↦ₘ b)

def ownSet (S : Nat → Prop) (Φ : Nat → IProp GF) : IProp GF :=
  iprop(∃ l : List Nat, ⌜l.Nodup ∧ ∀ a, a ∈ l ↔ S a⌝ ∗ sepL l Φ)

theorem sepL_append {α} (l₁ l₂ : List α) (Φ : α → IProp GF) :
    sepL (l₁ ++ l₂) Φ ⊣⊢ sepL l₁ Φ ∗ sepL l₂ Φ := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, sepL_nil]
    exact emp_sep.symm
  | cons x xs ih =>
    simp only [List.cons_append, sepL_cons]
    exact (sep_congr_right ih).trans sep_assoc.symm

theorem sepL_filter {α} (l : List α) (q : α → Bool) (Φ : α → IProp GF) :
    sepL l Φ ⊣⊢ sepL (l.filter q) Φ ∗ sepL (l.filter (fun a => !q a)) Φ := by
  induction l with
  | nil => simp only [List.filter_nil, sepL_nil]; exact emp_sep.symm
  | cons x xs ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hq : q x
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, sepL_cons]
      refine (sep_congr_right ih).trans ?_
      exact sep_assoc.symm.trans ((sep_congr_left sep_comm).trans sep_assoc)
    · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, sepL_cons]
      exact (sep_congr_right ih).trans sep_assoc.symm

theorem sepL_mono {α} (l : List α) (Φ Ψ : α → IProp GF) (h : ∀ a, Φ a ⊢ Ψ a) :
    sepL l Φ ⊢ sepL l Ψ := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih => exact sep_mono (h x) ih

theorem ownSet_iff {S T : Nat → Prop} (Φ : Nat → IProp GF) (h : ∀ a, S a ↔ T a) :
    ownSet S Φ ⊢ ownSet T Φ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  iexists l
  iframe Hl
  ipureintro
  exact ⟨hnd, fun a => (hmem a).trans (h a)⟩

theorem ownSet_mono {S : Nat → Prop} (Φ Ψ : Nat → IProp GF) (h : ∀ a, Φ a ⊢ Ψ a) :
    ownSet S Φ ⊢ ownSet S Ψ := by
  unfold ownSet
  iintro ⟨%l, %hl, Hl⟩
  iexists l
  isplitr
  · ipureintro; exact hl
  iapply sepL_mono l Φ Ψ h $$ Hl

theorem ownSet_split (S B : Nat → Prop) (Φ : Nat → IProp GF) :
    ownSet S Φ ⊢ ownSet (fun a => S a ∧ B a) Φ ∗ ownSet (fun a => S a ∧ ¬ B a) Φ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  ihave ⟨H1, H2⟩ := (sepL_filter l (fun a => decide (B a)) Φ).1 $$ Hl
  isplitl [H1]
  · iexists (l.filter (fun a => decide (B a)))
    iframe H1
    ipureintro
    refine ⟨hnd.filter _, fun a => ?_⟩
    simp [List.mem_filter, hmem]
  · iexists (l.filter (fun a => !decide (B a)))
    iframe H2
    ipureintro
    refine ⟨hnd.filter _, fun a => ?_⟩
    simp [List.mem_filter, hmem]

theorem ownSet_join (S T : Nat → Prop) (Φ : Nat → IProp GF) (hdisj : ∀ a, S a → ¬ T a) :
    ownSet S Φ ∗ ownSet T Φ ⊢ ownSet (fun a => S a ∨ T a) Φ := by
  unfold ownSet
  iintro ⟨⟨%l₁, %⟨hnd₁, hmem₁⟩, H1⟩, ⟨%l₂, %⟨hnd₂, hmem₂⟩, H2⟩⟩
  iexists (l₁ ++ l₂)
  isplitr
  · ipureintro
    refine ⟨List.nodup_append.2 ⟨hnd₁, hnd₂, fun a ha b hb hab => ?_⟩, fun a => ?_⟩
    · subst hab; exact hdisj a ((hmem₁ a).1 ha) ((hmem₂ a).1 hb)
    · simp [List.mem_append, hmem₁, hmem₂]
  iapply (sepL_append l₁ l₂ Φ).2
  iframe H1 H2

theorem owned_off (a : Nat) (v : BitVec 8) (S : Nat → Prop) :
    (a ↦ₘ v) ⊢@{IProp GF} ownSet S byteAny -∗ ⌜¬ S a⌝ := by
  unfold ownSet
  iintro Ha ⟨%l, %⟨_, hmem⟩, Hl⟩
  suffices h : ∀ l : List Nat, (a ↦ₘ v) ⊢@{IProp GF} sepL l byteAny -∗ ⌜a ∉ l⌝ by
    ihave %hn := h l $$ Ha Hl
    ipureintro
    exact fun hs => hn ((hmem a).2 hs)
  intro l
  induction l with
  | nil => iintro _ _; ipureintro; exact List.not_mem_nil
  | cons x xs ih =>
    rw [sepL_cons]
    iintro Ha ⟨⟨%b, Hx⟩, Hxs⟩
    ihave %hx := mem_ne a x _ v b $$ Ha Hx
    ihave %hxs := ih $$ Ha Hxs
    ipureintro
    simp [List.mem_cons, hx, hxs]

end OwnSet

structure DlLayout where

  global : Nat → Prop

  lo : Nat

  hi : Nat

  global_off_arena : ∀ a, global a → a < lo ∨ hi ≤ a

  Shape : (Nat → BitVec 8) → List (Nat × Nat) → Prop

def InExt (e : Nat × Nat) (a : Nat) : Prop := e.1 ≤ a ∧ a < e.1 + e.2

def heapFoot (L : DlLayout) (H : List (Nat × Nat)) (a : Nat) : Prop :=
  L.global a ∨ (L.lo ≤ a ∧ a < L.hi ∧ ∀ e ∈ H, ¬ InExt e a)

def FreshBlock (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat) : Prop :=
  p ≠ 0 ∧ L.lo ≤ p ∧ p + n ≤ L.hi ∧ ∀ e ∈ H, ∀ a, InExt (p, n) a → ¬ InExt e a

theorem FreshBlock.destruct {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat}
    (h : FreshBlock L H p n) :
    p ≠ 0 ∧ L.lo ≤ p ∧ p + n ≤ L.hi ∧ ∀ e ∈ H, ∀ a, InExt (p, n) a → ¬ InExt e a := h

theorem FreshBlock.nonzero {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat}
    (h : FreshBlock L H p n) : p ≠ 0 := h.destruct.1

theorem FreshBlock.lo {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat}
    (h : FreshBlock L H p n) : L.lo ≤ p := by obtain ⟨_, h, _⟩ := h; exact h

theorem FreshBlock.hi {L : DlLayout} {H : List (Nat × Nat)} {p n : Nat}
    (h : FreshBlock L H p n) : p + n ≤ L.hi := by obtain ⟨_, _, h, _⟩ := h; exact h

section Heap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

def isHeap (L : DlLayout) (H : List (Nat × Nat)) : IProp GF :=
  iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H⌝ ∗
    ownSet (heapFoot L H) (fun a => a ↦ₘ img a))

def blockOwn (p n : Nat) : IProp GF := ownSet (InExt (p, n)) byteAny

theorem ownSet_forget (S : Nat → Prop) (img : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ img a) ⊢ ownSet S byteAny :=
  ownSet_mono _ _ (fun a => by iintro H; iexists img a; iexact H)

theorem heapFoot_carve_gen (L : DlLayout) (H : List (Nat × Nat)) (p n : Nat)
    (hf : FreshBlock L H p n) (Φ : Nat → IProp GF) :
    ownSet (GF := GF) (heapFoot L H) Φ ⊢
      ownSet (heapFoot L ((p, n) :: H)) Φ ∗ ownSet (InExt (p, n)) Φ := by
  obtain ⟨_, hlo, hhi, hdisj⟩ := hf
  iintro Hh
  ihave ⟨Hb, Hr⟩ := ownSet_split (heapFoot L H) (InExt (p, n)) Φ $$ Hh
  isplitl [Hr]
  · iapply ownSet_iff Φ _ $$ Hr
    intro a
    unfold heapFoot InExt
    constructor
    · rintro ⟨hg | ⟨h1, h2, h3⟩, hn⟩
      · exact .inl hg
      · refine .inr ⟨h1, h2, fun e he => ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact hn
        · exact h3 e he
    · rintro (hg | ⟨h1, h2, h3⟩)
      · refine ⟨.inl hg, fun ⟨hp1, hp2⟩ => ?_⟩
        rcases L.global_off_arena a hg with h | h <;> simp at hp1 hp2 <;> omega
      · exact ⟨.inr ⟨h1, h2, fun e he => h3 e (List.mem_cons_of_mem _ he)⟩,
          h3 (p, n) List.mem_cons_self⟩
  · iapply ownSet_iff Φ _ $$ Hb
    intro a
    constructor
    · exact fun h => h.2
    · intro ha
      refine ⟨.inr ⟨?_, ?_, fun e he => hdisj e he a ha⟩, ha⟩
      · unfold InExt at ha; simp at ha; omega
      · unfold InExt at ha; simp at ha; omega

def gp : Nat := 3

def clobbered (rs : List Nat) : IProp GF := sepL rs (fun r => iprop(∃ v, r ↦ᵣ v))

def savedOwn (saved : List (Nat × BitVec 64)) : IProp GF := sepL saved (fun p => p.1 ↦ᵣ p.2)

def textOwn (text : List (Nat × BitVec 8)) : IProp GF := sepL text (fun p => p.1 ↦ₘ□ p.2)

instance (text : List (Nat × BitVec 8)) : Persistent (textOwn (GF := GF) text) := by
  unfold textOwn; infer_instance

def stackScratch (s : BitVec 64) (headroom : Nat) : IProp GF :=
  blockOwn (s.toNat - headroom) headroom

def mallocPost (L : DlLayout) (H : List (Nat × Nat)) (n : Nat) (p : BitVec 64) : IProp GF :=
  iprop((⌜p = 0⌝ ∗ isHeap L H) ∨
    (⌜FreshBlock L H p.toNat n ∧ p.toNat % 16 = 0⌝ ∗
      isHeap L ((p.toNat, n) :: H) ∗ blockOwn p.toNat n))

variable {M : MachineModel} (Wp : MachWP (GF := GF) M)

def mallocSpec (L : DlLayout) (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (n s : BitVec 64) : IProp GF :=
  fnSpecW Wp entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ n ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L H))
    (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ mallocPost L H n.toNat p))

def freeSpec (L : DlLayout) (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) : IProp GF :=
  fnSpecW Wp entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ q ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L ((q.toNat, n) :: H) ∗ blockOwn q.toNat n))
    (fun _ => iprop(sp ↦ᵣ s ∗ (∃ v, a0 ↦ᵣ v) ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeap L H))

end Heap

structure DlMallocImpl (M : MachineModel) (L : DlLayout) (SpOK : BitVec 64 → Prop)
    (mallocEntry freeEntry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop where
  malloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (Wp : MachWP (GF := GF) M) H n s
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ mallocSpec Wp L SpOK mallocEntry gpv clob saved headroom H n s
  free : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] (Wp : MachWP (GF := GF) M) H q n s
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ freeSpec Wp L SpOK freeEntry gpv clob saved headroom H q n s

end VsaIris
