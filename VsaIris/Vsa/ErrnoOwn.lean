import VsaIris.Vsa.HeapRoom
import VsaIris.Interp.Repr

/-!
# Lending `errno` out of the heap resource (lane N1)

Every console write runs `_write_r`, which clears libgloss's `errno`
(`0x8001ba08`, `Stdio.errnoFoot`). That word is an allocator global
(`_sbrk_r` clears it too), owned by the heap resource. The allocator's shape
never reads it (`BlockHeapAt.transport_read`: `vsaRead` excludes it), so the
heap resource lends it at any value and takes it back at any value
(`heapRes_errno`). The stdout calls (`NewlibOut.outSpec`) borrow it this way.
-/

namespace VsaIris.ErrnoOwn

open Iris Iris.BI Iris.Std Iris.ProofMode
open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.VsaHeap VsaIris.Stdio VsaIris.Interp

theorem errno_global {a : Nat} (h : errnoFoot a) : allocGlobal a := by
  unfold errnoFoot Stdio.InRange at h; unfold allocGlobal VsaHeap.InRange; omega

theorem errno_vsaFoot {H : List (Nat × Nat)} {a : Nat} (h : errnoFoot a) : vsaFoot H a :=
  .inl (errno_global h)

/-- A memory with the `errno` bytes of an image. -/
def setErrno (m : Mem) (img : Nat → BitVec 8) : Mem :=
  (((m.insert 0x8001ba08 (img 0x8001ba08)).insert 0x8001ba09 (img 0x8001ba09)).insert
    0x8001ba0a (img 0x8001ba0a)).insert 0x8001ba0b (img 0x8001ba0b)

theorem setErrno_get (m : Mem) (img : Nat → BitVec 8) (a : Nat) :
    (setErrno m img)[a]? = if errnoFoot a then some (img a) else m[a]? := by
  unfold setErrno
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  by_cases h0 : (0x8001ba0b : Nat) = a
  · subst h0; simp [errnoFoot, Stdio.InRange]
  by_cases h1 : (0x8001ba0a : Nat) = a
  · subst h1; simp [errnoFoot, Stdio.InRange]
  by_cases h2 : (0x8001ba09 : Nat) = a
  · subst h2; simp [errnoFoot, Stdio.InRange]
  by_cases h3 : (0x8001ba08 : Nat) = a
  · subst h3; simp [errnoFoot, Stdio.InRange]
  have hne : ¬ errnoFoot a := by unfold errnoFoot Stdio.InRange; omega
  simp only [h0, h1, h2, h3, ite_false, if_neg hne]

/-- **The heap's facts ignore `errno`.** -/
theorem pheap_errno {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : PHeapAt m H top brkv chunks bins) (img : Nat → BitVec 8) :
    PHeapAt (setErrno m img) H top brkv chunks bins := by
  have hag : ∀ a, ¬ errnoFoot a → m[a]? = (setErrno m img)[a]? := fun a ha => by
    rw [setErrno_get, if_neg ha]
  refine ⟨h.heap.transport_read fun a ha => hag a fun he => ?_, h.brk_page, fun bb hbb => ?_⟩
  · unfold vsaRead at ha; unfold errnoFoot Stdio.InRange at he; unfold VsaHeap.InRange at ha; omega
  · refine h.bb_lt bb ?_
    rw [read64_agreeP (P := fun a => ¬ errnoFoot a) (fun a ha => hag a ha) ?_]; exact hbb
    intro k hk; unfold errnoFoot Stdio.InRange binblocksAddr avAddr; omega

theorem imgOn_errno {H : List (Nat × Nat)} {img img' : Nat → BitVec 8} {m : Mem}
    (h : ImgOn (vsaFoot H) img m) (hag : ∀ a, ¬ errnoFoot a → img' a = img a) :
    ImgOn (vsaFoot H) img' (setErrno m img') := by
  intro a ha
  rw [setErrno_get]
  by_cases he : errnoFoot a
  · rw [if_pos he]
  · rw [if_neg he, h a ha, hag a he]

theorem pShape_errno {H : List (Nat × Nat)} {img img' : Nat → BitVec 8} (h : pShape img H)
    (hag : ∀ a, ¬ errnoFoot a → img' a = img a) : pShape img' H := by
  obtain ⟨hst, m, top, brkv, chunks, bins, hm, hp⟩ := h
  exact ⟨hst, _, top, brkv, chunks, bins, imgOn_errno hm hag, pheap_errno hp img'⟩

theorem roomB_errno {H : List (Nat × Nat)} {k : Nat} {img img' : Nat → BitVec 8}
    (h : vsaRoomB img H k) (hag : ∀ a, ¬ errnoFoot a → img' a = img a) : vsaRoomB img' H k := by
  obtain ⟨hst, m, top, brkv, chunks, bins, hm, hp, hk⟩ := h
  exact ⟨hst, _, top, brkv, chunks, bins, imgOn_errno hm hag, pheap_errno hp img', hk⟩

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Splitting the `errno` bytes out of an owned image and joining them back at
new values. -/
theorem ownImg_errno (S : Nat → Prop) (hS : ∀ a, errnoFoot a → S a) (img : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ img a) ⊢ errnoOwn ∗
      (∀ f : Nat → BitVec 8, ownSet errnoFoot (fun a => a ↦ₘ f a) -∗
        ownSet S (fun a => a ↦ₘ (if errnoFoot a then f a else img a))) := by
  classical
  iintro H
  ihave ⟨He, Hr⟩ := ownSet_split S errnoFoot _ $$ H
  isplitl [He]
  · unfold errnoOwn
    ihave He := ownSet_iff _ (T := errnoFoot) (fun a => ⟨fun h => h.2, fun h => ⟨hS a h, h⟩⟩) $$ He
    iapply ownSet_mono _ _ (fun a => by iintro H; iexists img a; iexact H) $$ He
  iintro %f Hf
  ihave Hf := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ (if errnoFoot a then f a else img a)))
    (fun a ha => by simp [ha]) $$ Hf
  ihave Hr := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ (if errnoFoot a then f a else img a)))
    (fun a ha => by simp [ha.2]) $$ Hr
  ihave H := ownSet_join _ _ _ (fun a (h1 : errnoFoot a) (h2 : S a ∧ ¬ errnoFoot a) => h2.2 h1) $$ [Hf Hr]
  · iframe Hf Hr
  iapply ownSet_iff _ _ $$ H
  intro a; constructor
  · rintro (h | ⟨h, _⟩); exact hS a h; exact h
  · intro h; by_cases he : errnoFoot a
    · exact .inl he
    · exact .inr ⟨h, he⟩

/-- **The heap resource lends `errno`**, at any value, and takes it back at
any value. -/
theorem heapRes_errno (ρ : Regime) (H : List (Nat × Nat)) :
    heapRes (GF := GF) vsaLayoutP vsaRoomB ρ H ⊢
      errnoOwn ∗ (errnoOwn -∗ heapRes vsaLayoutP vsaRoomB ρ H) := by
  classical
  cases ρ with
  | counted k =>
    unfold heapRes isHeapRoom
    iintro ⟨%img, %⟨hs, hr⟩, H⟩
    ihave ⟨He, Hk⟩ := ownImg_errno (heapFoot vsaLayoutP H) (fun a h => errno_vsaFoot h) img $$ H
    iframe He
    iintro Hn
    unfold errnoOwn
    ihave ⟨%f, Hn⟩ := ownSet_fn _ $$ Hn
    ihave H := Hk $$ %f Hn
    iexists _
    iframe H
    ipureintro
    have hag : ∀ a, ¬ errnoFoot a → (if errnoFoot a then f a else img a) = img a :=
      fun a ha => by simp [ha]
    exact ⟨pShape_errno hs hag, roomB_errno hr hag⟩
  | uncounted =>
    unfold heapRes isHeap
    iintro ⟨%img, %hs, H⟩
    ihave ⟨He, Hk⟩ := ownImg_errno (heapFoot vsaLayoutP H) (fun a h => errno_vsaFoot h) img $$ H
    iframe He
    iintro Hn
    unfold errnoOwn
    ihave ⟨%f, Hn⟩ := ownSet_fn _ $$ Hn
    ihave H := Hk $$ %f Hn
    iexists _
    iframe H
    ipureintro
    exact pShape_errno hs fun a ha => by simp [ha]

/-- A heap resource that lends `errno` (the premise of the printing call
arms, generic in the layout). -/
def ErrnoLend (L : DlLayout) (Room : RoomPred) : Prop :=
  ∀ ρ H, heapRes (GF := GF) L Room ρ H ⊢ errnoOwn ∗ (errnoOwn -∗ heapRes L Room ρ H)

theorem errnoLend_vsa : ErrnoLend (GF := GF) vsaLayoutP vsaRoomB := heapRes_errno

end Own

end VsaIris.ErrnoOwn
