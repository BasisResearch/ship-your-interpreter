import VsaIris.LocalRun

/-!
# `DlMallocImpl` from first-order runs

`DlMallocImpl` is an Iris statement. This module reduces it to two
first-order facts about the machine's steps, `MallocLocalRun` and
`FreeLocalRun`, stated with `LocalRun`: from any state whose owned cells hold
given values, the allocator's code runs, each step touching only

* the registers `PC`, `ra`, `a0`, `sp`, the clobbered list and the
  callee-saved registers it restores, and
* its stack scratch window and `heapFoot L H` (for `free`, also the freed
  block),

and returns with the ABI frame restored and the heap shape advanced.
`dlMallocImpl_of_localRuns` proves `DlMallocImpl` from them. These two facts
are the remaining allocator assumption: the instruction-level proof of
`_malloc_r`/`_free_r`. Unlike `MallocContract`, the footprint is relative to
the live extents, and `VsaHeap.Control.live_relative_frame_admits_both`
checks it against the eb73d8c control heap.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

open Classical

/-! ## Owned byte sets and register lists at a valuation -/

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem sepL_congr {α : Type} {l : List α} {Φ Ψ : α → IProp GF}
    (h : ∀ x ∈ l, Φ x = Ψ x) : sepL l Φ = sepL l Ψ := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sepL_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem sepL_map {α β : Type} (l : List α) (g : α → β) (Φ : β → IProp GF) :
    sepL (l.map g) Φ = sepL l (fun x => Φ (g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, sepL_cons, ih]

/-- Existentially valued cells of a duplicate-free list have one valuation. -/
theorem sepL_exists_fn {α β : Type} [Inhabited β] (P : α → β → IProp GF) :
    ∀ l : List α, l.Nodup →
      sepL l (fun x => iprop(∃ v, P x v)) ⊢ ∃ f : α → β, sepL l (fun x => P x (f x))
  | [], _ => by
    iintro _
    iexists (fun _ => default)
    simp only [sepL_nil]
    iempintro
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    rw [sepL_cons]
    iintro ⟨⟨%v, Hx⟩, Hxs⟩
    ihave ⟨%f, Hxs⟩ := sepL_exists_fn P xs hnd.2 $$ Hxs
    iexists (fun y => if y = x then v else f y)
    have htail : sepL xs (fun y => P y (if y = x then v else f y)) =
        sepL xs (fun y => P y (f y)) :=
      sepL_congr fun y hy => by
        have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp [hne]
    simp only [sepL_cons, ite_true, htail]
    iframe Hx Hxs

theorem ownSet_congr {S : Nat → Prop} {Φ Ψ : Nat → IProp GF} (h : ∀ a, S a → Φ a = Ψ a) :
    ownSet S Φ ⊢ ownSet S Ψ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  iexists l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  rw [sepL_congr (l := l) (Φ := Ψ) (Ψ := Φ) (fun a ha => (h a ((hmem a).1 ha)).symm)]
  iexact Hl

/-- Bytes owned at unknown values have one valuation. -/
theorem ownSet_fn (S : Nat → Prop) :
    ownSet (GF := GF) S byteAny ⊢ ∃ f : Nat → BitVec 8, ownSet S (fun a => a ↦ₘ f a) := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  ihave ⟨%f, Hl⟩ := sepL_exists_fn (fun a b => iprop(a ↦ₘ b)) l hnd $$ Hl
  iexists f
  iexists l
  iframe Hl
  ipureintro; exact ⟨hnd, hmem⟩

theorem sepL_off (T : Nat → Prop) (f : Nat → BitVec 8) :
    ∀ l : List Nat, sepL (GF := GF) l (fun a => a ↦ₘ f a) ∗ ownSet T byteAny ⊢ ⌜∀ x ∈ l, ¬ T x⌝
  | [] => by
    iintro _
    ipureintro
    intro x hx; cases hx
  | x :: xs => by
    rw [sepL_cons]
    have A : iprop((x ↦ₘ f x ∗ sepL xs (fun a => a ↦ₘ f a)) ∗ ownSet T byteAny) ⊢@{IProp GF}
        ⌜¬ T x⌝ := by
      iintro ⟨⟨Hx, _⟩, HT⟩
      iapply owned_off x (f x) T $$ Hx HT
    have B : iprop((x ↦ₘ f x ∗ sepL xs (fun a => a ↦ₘ f a)) ∗ ownSet T byteAny) ⊢@{IProp GF}
        ⌜∀ y ∈ xs, ¬ T y⌝ := by
      iintro ⟨⟨_, Hxs⟩, HT⟩
      iapply sepL_off T f xs
      iframe Hxs HT
    refine (and_intro A B).trans (pure_and.1.trans (pure_mono fun h y hy => ?_))
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact h.2 y hy

/-- Bytes owned at values are off any set owned at unknown values (ghost
exclusivity). -/
theorem ownSet_off (S T : Nat → Prop) (f : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ f a) ∗ ownSet T byteAny ⊢ ⌜∀ a, S a → ¬ T a⌝ := by
  iintro ⟨HS, HT⟩
  rw [show ownSet S (fun a => a ↦ₘ f a) = iprop(∃ l : List Nat,
      ⌜l.Nodup ∧ ∀ a, a ∈ l ↔ S a⌝ ∗ sepL l (fun a => a ↦ₘ f a)) from rfl]
  icases HS with ⟨%l, %⟨_, hmem⟩, Hl⟩
  ihave %h := sepL_off T f l $$ [Hl HT]
  · iframe Hl HT
  ipureintro
  exact fun a ha => h a ((hmem a).2 ha)

/-- Two owned byte sets are disjoint (ghost exclusivity). -/
theorem ownSet_disj (S T : Nat → Prop) (f g : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ f a) ∗ ownSet T (fun a => a ↦ₘ g a) ⊢
      ⌜∀ a, S a → ¬ T a⌝ := by
  iintro ⟨HS, HT⟩
  ihave HT := ownSet_forget T g $$ HT
  iapply ownSet_off S T f
  iframe HS HT

/-- Derive a pure fact from resources and keep them. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep_mp

/-- The value a register takes in a (key, value) list. -/
def pairVal (saved : List (Nat × BitVec 64)) (k : Nat) : BitVec 64 :=
  (saved.lookup k).getD 0

theorem savedOwn_fn : ∀ (saved : List (Nat × BitVec 64)), (saved.map Prod.fst).Nodup →
    savedOwn (GF := GF) saved ⊢ sepL (saved.map Prod.fst) (fun k => k ↦ᵣ pairVal saved k)
  | [], _ => by simp only [savedOwn, List.map_nil, sepL_nil]; exact .rfl
  | (k, v) :: rest, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    unfold savedOwn
    simp only [sepL_cons, List.map_cons]
    have hv : pairVal ((k, v) :: rest) k = v := by simp [pairVal, List.lookup]
    have htail : sepL (GF := GF) (rest.map Prod.fst) (fun k' => k' ↦ᵣ pairVal ((k, v) :: rest) k') =
        sepL (rest.map Prod.fst) (fun k' => k' ↦ᵣ pairVal rest k') :=
      sepL_congr fun k' hk' => by
        have hne : (k' == k) = false := by
          simpa using (fun h : k' = k => hnd.1 (h ▸ hk'))
        simp only [pairVal, List.lookup, hne]
    rw [hv, htail]
    iintro ⟨Hk, Hrest⟩
    iframe Hk
    iapply savedOwn_fn rest hnd.2
    unfold savedOwn
    iexact Hrest

theorem savedOwn_back (saved : List (Nat × BitVec 64)) (f : Nat → BitVec 64)
    (h : ∀ p ∈ saved, f p.1 = p.2) :
    sepL (GF := GF) (saved.map Prod.fst) (fun k => k ↦ᵣ f k) ⊢ savedOwn saved := by
  rw [sepL_map]
  unfold savedOwn
  rw [sepL_congr (l := saved) (Ψ := fun p => p.1 ↦ᵣ p.2) (fun p hp => by rw [h p hp])]

theorem clobbered_fn (clob : List Nat) (hnd : clob.Nodup) :
    clobbered (GF := GF) clob ⊢ ∃ f : Nat → BitVec 64, sepL clob (fun r => r ↦ᵣ f r) := by
  unfold clobbered
  exact sepL_exists_fn (fun r v => iprop(r ↦ᵣ v)) clob hnd

theorem clobbered_of_fn (clob : List Nat) (f : Nat → BitVec 64) :
    sepL (GF := GF) clob (fun r => r ↦ᵣ f r) ⊢ clobbered clob := by
  unfold clobbered
  exact sepL_mono clob _ _ fun r => by iintro H; iexists f r; iexact H

end Own

/-! ## The first-order runs -/

/-- Registers a malloc or free call owns during the run. -/
def allocRegs (clob savedRegs : List Nat) : List Nat := PC :: ra :: a0 :: sp :: (clob ++ savedRegs)

/-- The stack scratch window below `sp`. -/
def stackWin (s : BitVec 64) (headroom : Nat) (a : Nat) : Prop :=
  InExt (s.toNat - headroom, headroom) a

/-- Bytes a malloc call owns: its stack scratch and the heap footprint. -/
def mallocBytes (L : DlLayout) (H : List (Nat × Nat)) (s : BitVec 64) (headroom : Nat)
    (a : Nat) : Prop :=
  stackWin s headroom a ∨ heapFoot L H a

/-- Bytes a free call owns: its stack scratch, the heap footprint, and the
freed block. -/
def freeBytes (L : DlLayout) (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64)
    (headroom : Nat) (a : Nat) : Prop :=
  stackWin s headroom a ∨ (heapFoot L ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)

/-- The ABI frame at the return. -/
structure RetFrame (rv' : Nat → BitVec 64) (r s : BitVec 64) (saved : List (Nat × BitVec 64)) :
    Prop where
  pc : rv' PC = r
  ra : rv' ra = r
  sp : rv' sp = s
  saved : ∀ p ∈ saved, rv' p.1 = p.2

/-- What a malloc run ends in: the frame restored, and null with the heap
unchanged in shape, or a fresh aligned block with the extended live list. -/
structure MallocEnd (L : DlLayout) (H : List (Nat × Nat)) (n r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8) : Prop where
  frame : RetFrame rv' r s saved
  result : (rv' a0 = 0 ∧ L.Shape mv' H) ∨
    (FreshBlock L H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
      L.Shape mv' (((rv' a0).toNat, n.toNat) :: H))

/-- What a free run ends in: the frame restored and the block popped. -/
structure FreeEnd (L : DlLayout) (H : List (Nat × Nat)) (r s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8) : Prop where
  frame : RetFrame rv' r s saved
  shape : L.Shape mv' H

/-- The register values at a call entry. -/
structure EntryRegs (rv : Nat → BitVec 64) (entry r arg s : BitVec 64)
    (saved : List (Nat × BitVec 64)) : Prop where
  pc : rv PC = entry
  ra : rv ra = r
  a0 : rv a0 = arg
  sp : rv sp = s
  saved : ∀ p ∈ saved, rv p.1 = p.2

/-- **`_malloc_r`'s run, first-order.** From any owned entry values with the
heap in shape, the code (`text`, with `gp`) runs to the return, every step
confined to `allocRegs` and `mallocBytes`. -/
def MallocLocalRun (M : MachineModel) (L : DlLayout) (entry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
    saved.map Prod.fst = savedRegs → r.toNat % 4 = 0 → EntryRegs rv entry r n s saved →
    L.Shape mv H → (∀ a, stackWin s headroom a → ¬ heapFoot L H a) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (mallocBytes L H s headroom)
      (MallocEnd L H n r s saved) fuel rv mv

/-- **`_free_r`'s run, first-order.** -/
def FreeLocalRun (M : MachineModel) (L : DlLayout) (entry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s r : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
    saved.map Prod.fst = savedRegs → r.toNat % 4 = 0 → EntryRegs rv entry r q s saved →
    L.Shape mv ((q.toNat, n) :: H) →
    (∀ a, stackWin s headroom a → ¬ (heapFoot L ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (freeBytes L H q n s headroom)
      (FreeEnd L H r s saved) fuel rv mv

/-- The heap shape reads only the footprint (`VsaHeap.BlockHeapAt.transport`
for `vsaLayout`). -/
def ShapeLocal (L : DlLayout) : Prop :=
  ∀ (H : List (Nat × Nat)) (img img' : Nat → BitVec 8),
    (∀ a, heapFoot L H a → img a = img' a) → L.Shape img H → L.Shape img' H

/-! ## Building the specs -/

section Build

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- The register valuation at a call entry. -/
def entryVal (entry r arg s : BitVec 64) (clob : List Nat) (cv : Nat → BitVec 64)
    (saved : List (Nat × BitVec 64)) (k : Nat) : BitVec 64 :=
  if k = PC then entry else if k = ra then r else if k = a0 then arg else if k = sp then s
  else if k ∈ clob then cv k else pairVal saved k

theorem ptsto_eq {x : Nat} {v w : BitVec 64} (h : v = w) : (x ↦ᵣ v) ⊢@{IProp GF} (x ↦ᵣ w) := by
  rw [h]

theorem pairVal_of_mem : ∀ (saved : List (Nat × BitVec 64)), (saved.map Prod.fst).Nodup →
    ∀ p ∈ saved, pairVal saved p.1 = p.2
  | [], _, p, hp => by cases hp
  | (k, v) :: rest, hnd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [pairVal, List.lookup]
    · have hk : k ∉ rest.map Prod.fst := hnd.1
      have hne : (p.1 == k) = false := by
        simpa using (fun h : p.1 = k => hk (h ▸ List.mem_map_of_mem (f := Prod.fst) hp))
      have := pairVal_of_mem rest hnd.2 p hp
      simp only [pairVal, List.lookup, hne] at this ⊢
      exact this

/-- The distinctness facts of the owned register list. -/
structure RegsDistinct (clob savedRegs : List Nat) : Prop where
  clob_nd : clob.Nodup
  saved_nd : savedRegs.Nodup
  clob_fixed : ∀ k ∈ clob, k ≠ PC ∧ k ≠ ra ∧ k ≠ a0 ∧ k ≠ sp
  saved_fixed : ∀ k ∈ savedRegs, k ≠ PC ∧ k ≠ ra ∧ k ≠ a0 ∧ k ≠ sp ∧ k ∉ clob

theorem RegsDistinct.of_nodup {clob savedRegs : List Nat} (h : (allocRegs clob savedRegs).Nodup) :
    RegsDistinct clob savedRegs := by
  unfold allocRegs at h
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at h
  obtain ⟨⟨_, _, _, hpc1, hpc2⟩, ⟨_, _, hra1, hra2⟩, ⟨_, ha01, ha02⟩, ⟨hsp1, hsp2⟩, hcs⟩ := h
  rw [List.nodup_append] at hcs
  obtain ⟨hcn, hsn, hcs⟩ := hcs
  refine ⟨hcn, hsn, fun k hk => ?_, fun k hk => ?_⟩
  · refine ⟨fun h => hpc1 (h ▸ hk), fun h => hra1 (h ▸ hk), fun h => ha01 (h ▸ hk),
      fun h => hsp1 (h ▸ hk)⟩
  · refine ⟨fun h => hpc2 (h ▸ hk), fun h => hra2 (h ▸ hk), fun h => ha02 (h ▸ hk),
      fun h => hsp2 (h ▸ hk), fun hc => hcs k hc k hk rfl⟩

theorem allocRegs_split (clob savedRegs : List Nat) (Φ : Nat → IProp GF) :
    sepL (allocRegs clob savedRegs) Φ ⊢
      Φ PC ∗ Φ ra ∗ Φ a0 ∗ Φ sp ∗ sepL clob Φ ∗ sepL savedRegs Φ := by
  unfold allocRegs
  simp only [sepL_cons]
  iintro ⟨Hpc, Hra, Ha0, Hsp, Hrest⟩
  ihave ⟨Hc, Hs⟩ := (sepL_append clob savedRegs Φ).1 $$ Hrest
  iframe Hpc Hra Ha0 Hsp Hc Hs

theorem entry_regs_own {entry r arg s : BitVec 64} {clob : List Nat} {cv : Nat → BitVec 64}
    {saved : List (Nat × BitVec 64)} (hd : RegsDistinct clob (saved.map Prod.fst)) :
    PC ↦ᵣ entry ∗ ra ↦ᵣ r ∗ a0 ↦ᵣ arg ∗ sp ↦ᵣ s ∗ sepL clob (fun k => k ↦ᵣ cv k) ∗
      sepL (saved.map Prod.fst) (fun k => k ↦ᵣ pairVal saved k) ⊢@{IProp GF}
      sepL (allocRegs clob (saved.map Prod.fst))
        (fun k => k ↦ᵣ entryVal entry r arg s clob cv saved k) := by
  have e1 : entryVal entry r arg s clob cv saved PC = entry := by simp [entryVal]
  have e2 : entryVal entry r arg s clob cv saved ra = r := by simp [entryVal, PC, ra]
  have e3 : entryVal entry r arg s clob cv saved a0 = arg := by simp [entryVal, PC, ra, a0]
  have e4 : entryVal entry r arg s clob cv saved sp = s := by simp [entryVal, PC, ra, a0, sp]
  have hc : sepL (GF := GF) clob (fun k => k ↦ᵣ entryVal entry r arg s clob cv saved k) =
      sepL clob (fun k => k ↦ᵣ cv k) := sepL_congr fun k hk => by
    obtain ⟨h1, h2, h3, h4⟩ := hd.clob_fixed k hk
    simp [entryVal, h1, h2, h3, h4, hk]
  have hs : sepL (GF := GF) (saved.map Prod.fst)
      (fun k => k ↦ᵣ entryVal entry r arg s clob cv saved k) =
      sepL (saved.map Prod.fst) (fun k => k ↦ᵣ pairVal saved k) := sepL_congr fun k hk => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd.saved_fixed k hk
    simp [entryVal, h1, h2, h3, h4, h5]
  unfold allocRegs
  simp only [sepL_cons]
  rw [e1, e2, e3, e4]
  iintro ⟨Hpc, Hra, Ha0, Hsp, Hc, Hs⟩
  iframe Hpc Hra Ha0 Hsp
  iapply (sepL_append clob (saved.map Prod.fst) _).2
  rw [hc, hs]
  iframe Hc Hs

theorem entryRegs_entryVal {entry r arg s : BitVec 64} {clob : List Nat} {cv : Nat → BitVec 64}
    {saved : List (Nat × BitVec 64)} (hd : RegsDistinct clob (saved.map Prod.fst)) :
    EntryRegs (entryVal entry r arg s clob cv saved) entry r arg s saved where
  pc := by simp [entryVal]
  ra := by simp [entryVal, PC, ra]
  a0 := by simp [entryVal, PC, ra, a0]
  sp := by simp [entryVal, PC, ra, a0, sp]
  saved := fun p hp => by
    have hk := List.mem_map_of_mem (f := Prod.fst) hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd.saved_fixed p.1 hk
    simp only [entryVal, h1, h2, h3, h4, h5, ite_false]
    exact pairVal_of_mem saved hd.saved_nd p hp

/-- A combined valuation: `f` on `S`, `g` elsewhere. -/
noncomputable def glue (S : Nat → Prop) (f g : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if S a then f a else g a

/-- Join a stack window and a heap footprint, owned at separate valuations,
into one owned set at the glued valuation. -/
theorem ownSet_glue (S T : Nat → Prop) (f g : Nat → BitVec 8) (hdisj : ∀ a, S a → ¬ T a) :
    ownSet (GF := GF) S (fun a => a ↦ₘ f a) ∗ ownSet T (fun a => a ↦ₘ g a) ⊢
      ownSet (fun a => S a ∨ T a) (fun a => a ↦ₘ glue S f g a) := by
  iintro ⟨HS, HT⟩
  ihave HS := ownSet_congr (Ψ := fun a => a ↦ₘ glue S f g a)
    (fun a ha => by simp [glue, ha]) $$ HS
  ihave HT := ownSet_congr (Ψ := fun a => a ↦ₘ glue S f g a)
    (fun a ha => by
      have hn : ¬ S a := fun h => hdisj a h ha
      simp [glue, hn]) $$ HT
  iapply ownSet_join S T _ hdisj
  iframe HS HT

/-- Split an owned union back into its disjoint parts. -/
theorem ownSet_unglue (S T : Nat → Prop) (Φ : Nat → IProp GF) (hdisj : ∀ a, S a → ¬ T a) :
    ownSet (fun a => S a ∨ T a) Φ ⊢ ownSet S Φ ∗ ownSet T Φ := by
  iintro H
  ihave ⟨HS, HT⟩ := ownSet_split (fun a => S a ∨ T a) S Φ $$ H
  isplitl [HS]
  · iapply ownSet_iff Φ _ $$ HS
    intro a; constructor
    · exact fun h => h.2
    · exact fun h => ⟨.inl h, h⟩
  · iapply ownSet_iff Φ _ $$ HT
    intro a; constructor
    · rintro ⟨h | h, hn⟩
      · exact absurd h hn
      · exact h
    · exact fun h => ⟨.inr h, fun hs => hdisj a hs h⟩

theorem isHeap_unfold (L : DlLayout) (H : List (Nat × Nat)) :
    isHeap (GF := GF) L H ⊢ iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H⌝ ∗
      ownSet (heapFoot L H) (fun a => a ↦ₘ img a)) := .rfl

theorem isHeap_fold (L : DlLayout) (H : List (Nat × Nat)) :
    iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H⌝ ∗
      ownSet (heapFoot L H) (fun a => a ↦ₘ img a)) ⊢@{IProp GF} isHeap L H := .rfl

/-- **One allocator call from its local run.** The generic core of every
allocator spec below: the caller hands over the argument, the frame
registers, the stack scratch and a byte set `F` at an image satisfying `P`;
the callee's local run over `allocRegs` and `stackWin ∪ F` ends with the ABI
frame restored and `E`; `post` turns the final bytes of `F` into the
callee's result resource. -/
theorem allocCall_of_localRun {entry gpv r arg s : BitVec 64} {clob : List Nat}
    {saved : List (Nat × BitVec 64)} {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hd : RegsDistinct clob (saved.map Prod.fst))
    (F : Nat → Prop) (P : (Nat → BitVec 8) → Prop)
    (hlocP : ∀ img img', (∀ a, F a → img a = img' a) → P img → P img')
    (E : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (Post : BitVec 64 → IProp GF)
    (post : ∀ rv' mv', E rv' mv' → ownSet F (fun a => a ↦ₘ mv' a) ⊢ Post (rv' a0))
    (hrun : ∀ rv mv, EntryRegs rv entry r arg s saved → P mv →
      (∀ a, stackWin s headroom a → ¬ F a) →
      ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob (saved.map Prod.fst))
        (fun a => stackWin s headroom a ∨ F a)
        (fun rv' mv' => RetFrame rv' r s saved ∧ E rv' mv') fuel rv mv)
    {Φ : Nat × String → IProp GF} :
    textOwn text ∗ PC ↦ᵣ entry ∗ ra ↦ᵣ r ∗ a0 ↦ᵣ arg ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗
      clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      (∃ img : Nat → BitVec 8, ⌜P img⌝ ∗ ownSet F (fun a => a ↦ₘ img a)) ∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗
        (∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
          stackScratch s headroom ∗ Post p) -∗ mTWP M Φ)
    ⊢ mTWP M Φ := by
  unfold stackScratch blockOwn
  iintro ⟨#Htext, Hpc, Hra, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, ⟨%img, %hP, HF⟩, Hk⟩
  ihave ⟨%cv, Hclob⟩ := clobbered_fn clob hd.clob_nd $$ Hclob
  ihave Hsv := savedOwn_fn saved hd.saved_nd $$ Hsv
  ihave ⟨%fs, Hstk⟩ := ownSet_fn _ $$ Hstk
  ihave Hstk := ownSet_iff (S := InExt (s.toNat - headroom, headroom))
    (T := stackWin s headroom) _ (fun _ => Iff.rfl) $$ Hstk
  ihave ⟨⟨Hstk, HF⟩, %hdisj⟩ := keep_pure (ownSet_disj (stackWin s headroom) F fs img)
    $$ [Hstk HF]
  · iframe Hstk HF
  ihave Hbytes := ownSet_glue _ _ fs img hdisj $$ [Hstk HF]
  · iframe Hstk HF
  ihave Hregs := entry_regs_own (entry := entry) (r := r) (arg := arg) (s := s) (cv := cv) hd
    $$ [Hpc Hra Ha0 Hsp Hclob Hsv]
  · iframe Hpc Hra Ha0 Hsp Hclob Hsv
  have hP' : P (glue (stackWin s headroom) fs img) :=
    hlocP img _ (fun a ha => by
      have hn : ¬ stackWin s headroom a := fun h => hdisj a h ha
      simp [glue, hn]) hP
  obtain ⟨fuel, hlr⟩ := hrun _ _ (entryRegs_entryVal hd) hP' hdisj
  iapply wp_localRun fuel _ _ hlr
  isplitr
  · unfold roOwn
    simp only [sepL_cons, sepL_nil]
    isplitr
    · iframe Hgp
    · unfold textOwn at *; iexact Htext
  iframe Hregs Hbytes
  iintro %rv' %mv' %⟨⟨hpc, hra, hsp, hsaved⟩, hE⟩ Hregs Hbytes
  ihave ⟨Hpc, Hra, Ha0, Hsp, Hclob, Hsv⟩ := allocRegs_split _ _ _ $$ Hregs
  ihave Hpc := ptsto_eq hpc $$ Hpc
  ihave Hra := ptsto_eq hra $$ Hra
  ihave Hsp := ptsto_eq hsp $$ Hsp
  ihave Hclob := clobbered_of_fn clob rv' $$ Hclob
  ihave Hsv := savedOwn_back saved rv' hsaved $$ Hsv
  ihave ⟨Hstk, HF⟩ := ownSet_unglue _ _ _ hdisj $$ Hbytes
  ihave Hstk := ownSet_forget _ mv' $$ Hstk
  ihave Hstk := ownSet_iff (S := stackWin s headroom)
    (T := InExt (s.toNat - headroom, headroom)) _ (fun _ => Iff.rfl) $$ Hstk
  ihave Hpost := post rv' mv' hE $$ HF
  iapply Hk $$ Hpc Hra
  iexists rv' a0
  iframe Ha0 Hsp Hclob Hsv Hstk Hpost

/-- **`mallocSpec` from `_malloc_r`'s local run.** -/
theorem mallocSpec_of_localRun {L : DlLayout} {entry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : MallocLocalRun M L entry gpv clob savedRegs headroom text) (hloc : ShapeLocal L)
    (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (n s : BitVec 64) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = savedRegs) :
    textOwn (GF := GF) text ⊢ mallocSpec M L entry gpv clob saved headroom H n s := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold mallocSpec fnSpec
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hral, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, Hheap⟩ Hk
  ihave Hheap := isHeap_unfold L H $$ Hheap
  iapply allocCall_of_localRun hd (heapFoot L H) (fun img => L.Shape img H) (hloc H)
    (fun rv' mv' => (rv' a0 = 0 ∧ L.Shape mv' H) ∨
      (FreshBlock L H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
        L.Shape mv' (((rv' a0).toNat, n.toNat) :: H)))
    (fun p => mallocPost L H n.toNat p) ?_
    (fun rv mv he hs hdj => (hrun H n s r saved rv mv rfl hral he hs hdj).imp fun _ h =>
      LocalRun.mono (fun _ _ he => ⟨he.frame, he.result⟩) _ _ _ h)
  · intro rv' mv' hE
    unfold mallocPost blockOwn
    rcases hE with ⟨h0, hsh⟩ | ⟨hf, hal, hsh⟩
    · iintro HF
      ileft
      isplitr
      · ipureintro; exact h0
      iapply isHeap_fold
      iexists mv'
      iframe HF
      ipureintro; exact hsh
    · iintro HF
      ihave ⟨HF, Hblk⟩ := heapFoot_carve_gen L H _ _ hf _ $$ HF
      ihave Hblk := ownSet_forget _ mv' $$ Hblk
      iright
      isplitr
      · ipureintro; exact ⟨hf, hal⟩
      iframe Hblk
      iapply isHeap_fold
      iexists mv'
      iframe HF
      ipureintro; exact hsh
  · iframe Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk Hheap
    iintro Hpc Hra HQ
    iapply Hk $$ Hpc Hra HQ

theorem heapFoot_sub_return (L : DlLayout) (H : List (Nat × Nat)) (q n a : Nat)
    (h : heapFoot L H a) : heapFoot L ((q, n) :: H) a ∨ InExt (q, n) a := by
  by_cases hb : InExt (q, n) a
  · exact .inr hb
  · left
    rcases h with hg | ⟨h1, h2, h3⟩
    · exact .inl hg
    · refine .inr ⟨h1, h2, fun e he => ?_⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hb
      · exact h3 e he

/-- **`freeSpec` from `_free_r`'s local run.** -/
theorem freeSpec_of_localRun {L : DlLayout} {entry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : FreeLocalRun M L entry gpv clob savedRegs headroom text) (hloc : ShapeLocal L)
    (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (hsv : saved.map Prod.fst = savedRegs) :
    textOwn (GF := GF) text ⊢ freeSpec M L entry gpv clob saved headroom H q n s := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold freeSpec fnSpec blockOwn
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hral, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, Hheap, Hblk⟩ Hk
  ihave ⟨%img, %hsh, Hheap⟩ := isHeap_unfold L _ $$ Hheap
  ihave ⟨%fb, Hblk⟩ := ownSet_fn _ $$ Hblk
  ihave ⟨⟨Hheap, Hblk⟩, %hHB⟩ := keep_pure
    (ownSet_disj (heapFoot L ((q.toNat, n) :: H)) (InExt (q.toNat, n)) img fb) $$ [Hheap Hblk]
  · iframe Hheap Hblk
  ihave Hhb := ownSet_glue _ _ img fb hHB $$ [Hheap Hblk]
  · iframe Hheap Hblk
  iapply allocCall_of_localRun hd (fun a => heapFoot L ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)
    (fun img => L.Shape img ((q.toNat, n) :: H))
    (fun img img' h hs => hloc _ img img' (fun a ha => h a (.inl ha)) hs)
    (fun _ mv' => L.Shape mv' H) (fun _ => isHeap L H) ?_
    (fun rv mv he hs hdj => (hrun H q n s r saved rv mv rfl hral he hs hdj).imp fun _ h =>
      LocalRun.mono (fun _ _ he => ⟨he.frame, he.shape⟩) _ _ _ h)
  · intro rv' mv' hsh'
    iintro HF
    ihave ⟨HF, -⟩ := ownSet_split _ (heapFoot L H) _ $$ HF
    ihave HF := ownSet_iff (T := heapFoot L H) _
      (fun a => ⟨fun h => h.2, fun h => ⟨heapFoot_sub_return L H _ _ a h, h⟩⟩) $$ HF
    iapply isHeap_fold
    iexists mv'
    iframe HF
    ipureintro; exact hsh'
  · iframe Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk
    isplitl [Hhb]
    · iexists (glue (heapFoot L ((q.toNat, n) :: H)) img fb)
      iframe Hhb
      ipureintro
      exact hloc _ img _ (fun a ha => by simp [glue, ha]) hsh
    iintro Hpc Hra ⟨%p, Ha0, Hsp, Hclob, Hsv, Hstk, Hh⟩
    iapply Hk $$ Hpc Hra
    isplitl [Hsp]
    · iexact Hsp
    isplitl [Ha0]
    · iexists p; iexact Ha0
    iframe Hclob Hsv Hstk Hh

/-- **`DlMallocImpl` from the allocator's two local runs.** The remaining
allocator assumption is exactly `MallocLocalRun` and `FreeLocalRun`: the
instruction-level behaviour of `_malloc_r` and `_free_r`, framed by the live
extents. -/
theorem dlMallocImpl_of_localRuns {M : MachineModel} {L : DlLayout}
    {mallocEntry freeEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (hm : MallocLocalRun M L mallocEntry gpv clob savedRegs headroom text)
    (hf : FreeLocalRun M L freeEntry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hnd : (allocRegs clob savedRegs).Nodup) :
    DlMallocImpl M L mallocEntry freeEntry gpv clob savedRegs headroom text where
  malloc H n s saved hsv := mallocSpec_of_localRun hm hloc hnd H n s saved hsv
  free H q n s saved hsv := freeSpec_of_localRun hf hloc hnd H q n s saved hsv

/-! ## Allocation under capacity

`mallocSpec` allows NULL, but VSA's consumers need success: the interpreter's
allocations are bounded by the program's modeled cost (`InitialAllocatorAt.capacity`,
`AllocationReserve`). `isHeapRoom L Room H k` is the heap with room for `k`
more requests (MachCSL's `kalloc_avail`, kept as a pure predicate on the
allocator's own image), and `mallocRoomSpec` spends one credit for a
guaranteed fresh block. -/

/-- A capacity predicate on the allocator's image and live blocks. -/
abbrev RoomPred := (Nat → BitVec 8) → List (Nat × Nat) → Nat → Prop

/-- The capacity predicate reads only the allocator's footprint. -/
def RoomLocal (L : DlLayout) (Room : RoomPred) : Prop :=
  ∀ (H : List (Nat × Nat)) (img img' : Nat → BitVec 8) (k : Nat),
    (∀ a, heapFoot L H a → img a = img' a) → Room img H k → Room img' H k

/-- What a malloc run under capacity ends in: the frame restored, a fresh
aligned block, and the heap in shape with one credit spent. -/
structure MallocRoomEnd (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat))
    (n r s : BitVec 64) (saved : List (Nat × BitVec 64)) (k : Nat)
    (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8) : Prop where
  frame : RetFrame rv' r s saved
  fresh : FreshBlock L H (rv' a0).toNat n.toNat
  align : (rv' a0).toNat % 16 = 0
  shape : L.Shape mv' (((rv' a0).toNat, n.toNat) :: H)
  room : Room mv' (((rv' a0).toNat, n.toNat) :: H) k

/-- **`_malloc_r`'s run under capacity, first-order.** A request within
`maxReq` from a heap with a credit left returns a fresh block. -/
def MallocRoomRun (M : MachineModel) (L : DlLayout) (Room : RoomPred) (maxReq : Nat)
    (SpOK : BitVec 64 → Prop)
    (entry gpv : BitVec 64) (clob savedRegs : List Nat) (headroom : Nat)
    (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k : Nat),
    saved.map Prod.fst = savedRegs → n.toNat ≤ maxReq → SpOK s → r.toNat % 4 = 0 →
    EntryRegs rv entry r n s saved →
    L.Shape mv H → Room mv H (k + 1) → (∀ a, stackWin s headroom a → ¬ heapFoot L H a) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (mallocBytes L H s headroom)
      (MallocRoomEnd L Room H n r s saved k) fuel rv mv

/-- The heap with room for `k` more requests. -/
def isHeapRoom (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat)) (k : Nat) : IProp GF :=
  iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H ∧ Room img H k⌝ ∗
    ownSet (heapFoot L H) (fun a => a ↦ₘ img a))

theorem isHeapRoom_forget (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat)) (k : Nat) :
    isHeapRoom (GF := GF) L Room H k ⊢ isHeap L H := by
  unfold isHeapRoom isHeap
  iintro ⟨%img, %⟨hs, _⟩, HF⟩
  iexists img
  iframe HF
  ipureintro; exact hs

/-- `mallocSpec` under capacity: one credit buys a fresh block. `SpOK` is the
caller's stack-pointer discipline (RAM, alignment, headroom), a pure fact the
caller supplies. The return address is 4-aligned: `ret` (`jalr x0, 0(ra)`)
clears bit 0, so no allocator returns to an odd `r`. -/
def mallocRoomSpec (M : MachineModel) (L : DlLayout) (Room : RoomPred) (SpOK : BitVec 64 → Prop)
    (entry gpv : BitVec 64)
    (clob : List Nat) (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (n s : BitVec 64) (k : Nat) : IProp GF :=
  fnSpec (M := M) entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ n ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeapRoom L Room H (k + 1)))
    (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗
      (⌜FreshBlock L H p.toNat n.toNat ∧ p.toNat % 16 = 0⌝ ∗
        isHeapRoom L Room ((p.toNat, n.toNat) :: H) k ∗ blockOwn p.toNat n.toNat)))

/-- **`mallocRoomSpec` from the capacity run.** -/
theorem mallocRoomSpec_of_run {L : DlLayout} {Room : RoomPred} {maxReq : Nat}
    {SpOK : BitVec 64 → Prop}
    {entry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (hrun : MallocRoomRun M L Room maxReq SpOK entry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hroom : RoomLocal L Room) (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (n s : BitVec 64) (k : Nat) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = savedRegs) (hn : n.toNat ≤ maxReq) :
    textOwn (GF := GF) text ⊢
      mallocRoomSpec M L Room SpOK entry gpv clob saved headroom H n s k := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold mallocRoomSpec fnSpec isHeapRoom
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hspok, hral⟩, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, Hheap⟩ Hk
  iapply allocCall_of_localRun hd (heapFoot L H) (fun img => L.Shape img H ∧ Room img H (k + 1))
    (fun img img' h hs => ⟨hloc H img img' h hs.1, hroom H img img' _ h hs.2⟩)
    (fun rv' mv' => FreshBlock L H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
      L.Shape mv' (((rv' a0).toNat, n.toNat) :: H) ∧
      Room mv' (((rv' a0).toNat, n.toNat) :: H) k)
    (fun p => iprop(⌜FreshBlock L H p.toNat n.toNat ∧ p.toNat % 16 = 0⌝ ∗
      (∃ img : Nat → BitVec 8, ⌜L.Shape img ((p.toNat, n.toNat) :: H) ∧
        Room img ((p.toNat, n.toNat) :: H) k⌝ ∗
        ownSet (heapFoot L ((p.toNat, n.toNat) :: H)) (fun a => a ↦ₘ img a)) ∗
      blockOwn p.toNat n.toNat)) ?_
    (fun rv mv he hs hdj => (hrun H n s r saved rv mv k rfl hn hspok hral he hs.1 hs.2 hdj).imp fun _ h =>
      LocalRun.mono (fun _ _ he => ⟨he.frame, he.fresh, he.align, he.shape, he.room⟩) _ _ _ h)
  · intro rv' mv' ⟨hf, hal, hsh, hrm⟩
    unfold blockOwn
    iintro HF
    ihave ⟨HF, Hblk⟩ := heapFoot_carve_gen L H _ _ hf _ $$ HF
    ihave Hblk := ownSet_forget _ mv' $$ Hblk
    isplitr
    · ipureintro; exact ⟨hf, hal⟩
    iframe Hblk
    iexists mv'
    iframe HF
    ipureintro; exact ⟨hsh, hrm⟩
  · iframe Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk Hheap
    iintro Hpc Hra HQ
    iapply Hk $$ Hpc Hra HQ

/-- **The allocator under capacity, as a module parameter**: malloc with a
credit left always returns a fresh block. -/
structure DlMallocRoomImpl (M : MachineModel) (L : DlLayout) (Room : RoomPred) (maxReq : Nat)
    (SpOK : BitVec 64 → Prop) (mallocEntry gpv : BitVec 64) (clob savedRegs : List Nat) (headroom : Nat)
    (text : List (Nat × BitVec 8)) : Prop where
  malloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] H n s k
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs → n.toNat ≤ maxReq →
    textOwn (GF := GF) text ⊢ mallocRoomSpec M L Room SpOK mallocEntry gpv clob saved headroom H n s k

theorem dlMallocRoomImpl_of_run {M : MachineModel} {L : DlLayout} {Room : RoomPred}
    {maxReq : Nat} {SpOK : BitVec 64 → Prop} {mallocEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (hrun : MallocRoomRun M L Room maxReq SpOK mallocEntry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hroom : RoomLocal L Room) (hnd : (allocRegs clob savedRegs).Nodup) :
    DlMallocRoomImpl M L Room maxReq SpOK mallocEntry gpv clob savedRegs headroom text where
  malloc H n s k saved hsv hn := mallocRoomSpec_of_run hrun hloc hroom hnd H n s k saved hsv hn


/-! ## Freeing under capacity

`freeRoomSpec` is `freeSpec` for a heap in a restricted shape `FreeOK` (for
the binary: the block is the chunk below the top chunk), returning the heap
with its credits. -/

/-- What a free run under capacity ends in: the frame restored, the block
popped, the heap in shape with its credits. -/
structure FreeRoomEnd (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat))
    (r s : BitVec 64) (saved : List (Nat × BitVec 64)) (k : Nat)
    (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8) : Prop where
  frame : RetFrame rv' r s saved
  shape : L.Shape mv' H
  room : Room mv' H k

/-- **`_free_r`'s run under capacity, first-order.** A block whose heap is in
the shape `FreeOK` is freed, keeping `k` credits. -/
def FreeRoomRun (M : MachineModel) (L : DlLayout) (Room FreeOK : RoomPred)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob savedRegs : List Nat) (headroom : Nat)
    (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s r : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k : Nat),
    saved.map Prod.fst = savedRegs → SpOK s → r.toNat % 4 = 0 → EntryRegs rv entry r q s saved →
    L.Shape mv ((q.toNat, n) :: H) → FreeOK mv ((q.toNat, n) :: H) k →
    (∀ a, stackWin s headroom a → ¬ (heapFoot L ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (freeBytes L H q n s headroom)
      (FreeRoomEnd L Room H r s saved k) fuel rv mv

/-- `freeSpec` under capacity: the block goes back, the credits stay. -/
def freeRoomSpec (M : MachineModel) (L : DlLayout) (Room FreeOK : RoomPred)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat)
    (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) (k : Nat) : IProp GF :=
  fnSpec (M := M) entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ q ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗
      clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      isHeapRoom L FreeOK ((q.toNat, n) :: H) k ∗ blockOwn q.toNat n))
    (fun _ => iprop(sp ↦ᵣ s ∗ (∃ v, a0 ↦ᵣ v) ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeapRoom L Room H k))

/-- **`freeRoomSpec` from the capacity run.** -/
theorem freeRoomSpec_of_run {L : DlLayout} {Room FreeOK : RoomPred} {SpOK : BitVec 64 → Prop}
    {entry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (hrun : FreeRoomRun M L Room FreeOK SpOK entry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hfree : RoomLocal L FreeOK) (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) (k : Nat)
    (saved : List (Nat × BitVec 64)) (hsv : saved.map Prod.fst = savedRegs) :
    textOwn (GF := GF) text ⊢ freeRoomSpec M L Room FreeOK SpOK entry gpv clob saved headroom H q n s k := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold freeRoomSpec fnSpec blockOwn isHeapRoom
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hspok, hral⟩, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, ⟨%img, %⟨hsh, hok⟩, Hheap⟩, Hblk⟩ Hk
  ihave ⟨%fb, Hblk⟩ := ownSet_fn _ $$ Hblk
  ihave ⟨⟨Hheap, Hblk⟩, %hHB⟩ := keep_pure
    (ownSet_disj (heapFoot L ((q.toNat, n) :: H)) (InExt (q.toNat, n)) img fb) $$ [Hheap Hblk]
  · iframe Hheap Hblk
  ihave Hhb := ownSet_glue _ _ img fb hHB $$ [Hheap Hblk]
  · iframe Hheap Hblk
  have hagree : ∀ a, heapFoot L ((q.toNat, n) :: H) a →
      img a = glue (heapFoot L ((q.toNat, n) :: H)) img fb a := fun a ha => by simp [glue, ha]
  iapply allocCall_of_localRun hd (fun a => heapFoot L ((q.toNat, n) :: H) a ∨ InExt (q.toNat, n) a)
    (fun img => L.Shape img ((q.toNat, n) :: H) ∧ FreeOK img ((q.toNat, n) :: H) k)
    (fun img img' h hs => ⟨hloc _ img img' (fun a ha => h a (.inl ha)) hs.1,
      hfree _ img img' k (fun a ha => h a (.inl ha)) hs.2⟩)
    (fun _ mv' => L.Shape mv' H ∧ Room mv' H k)
    (fun _ => iprop(∃ img : Nat → BitVec 8, ⌜L.Shape img H ∧ Room img H k⌝ ∗
      ownSet (heapFoot L H) (fun a => a ↦ₘ img a))) ?_
    (fun rv mv he hs hdj => (hrun H q n s r saved rv mv k rfl hspok hral he hs.1 hs.2 hdj).imp
      fun _ h => LocalRun.mono (fun _ _ he => ⟨he.frame, he.shape, he.room⟩) _ _ _ h)
  · intro rv' mv' ⟨hsh', hrm'⟩
    iintro HF
    ihave ⟨HF, -⟩ := ownSet_split _ (heapFoot L H) _ $$ HF
    ihave HF := ownSet_iff (T := heapFoot L H) _
      (fun a => ⟨fun h => h.2, fun h => ⟨heapFoot_sub_return L H _ _ a h, h⟩⟩) $$ HF
    iexists mv'
    iframe HF
    ipureintro; exact ⟨hsh', hrm'⟩
  · iframe Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk
    isplitl [Hhb]
    · iexists (glue (heapFoot L ((q.toNat, n) :: H)) img fb)
      iframe Hhb
      ipureintro
      exact ⟨hloc _ img _ hagree hsh, hfree _ img _ k hagree hok⟩
    iintro Hpc Hra ⟨%p, Ha0, Hsp, Hclob, Hsv, Hstk, Hh⟩
    iapply Hk $$ Hpc Hra
    isplitl [Hsp]
    · iexact Hsp
    isplitl [Ha0]
    · iexists p; iexact Ha0
    iframe Hclob Hsv Hstk Hh

/-- **Freeing under capacity, as a module parameter.** -/
structure DlFreeRoomImpl (M : MachineModel) (L : DlLayout) (Room FreeOK : RoomPred)
    (SpOK : BitVec 64 → Prop) (freeEntry gpv : BitVec 64) (clob savedRegs : List Nat) (headroom : Nat)
    (text : List (Nat × BitVec 8)) : Prop where
  free : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] H q n s k
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ freeRoomSpec M L Room FreeOK SpOK freeEntry gpv clob saved headroom H q n s k

theorem dlFreeRoomImpl_of_run {M : MachineModel} {L : DlLayout} {Room FreeOK : RoomPred}
    {SpOK : BitVec 64 → Prop} {freeEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (hrun : FreeRoomRun M L Room FreeOK SpOK freeEntry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hfree : RoomLocal L FreeOK) (hnd : (allocRegs clob savedRegs).Nodup) :
    DlFreeRoomImpl M L Room FreeOK SpOK freeEntry gpv clob savedRegs headroom text where
  free H q n s k saved hsv := freeRoomSpec_of_run hrun hloc hfree hnd H q n s k saved hsv

end Build

end VsaIris
