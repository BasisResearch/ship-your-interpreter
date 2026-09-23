import VsaIris.MallocRun

/-!
# Allocation charged in credits

The counted regime (`heapRes (.counted k)`, INTERP_DESIGN §3) charges
`malloc` the cost model's credits for its request, not one credit per call.
`Vsa/While/Cost.lean` counts rounded requested bytes, and a derivation of
cost `n` starts with `n` more credits than it leaves. So `mallocChgSpec`
spends `c` credits on a request `n` admitted by a charge relation `Chg n c`.
The binary's instance is `vsaChg` (`Vsa/HeapRoom.lean`).

`MallocChgRun` is the first-order run behind it. `mallocChgSpec_of_run`
turns the run into the spec through `allocCall_of_localRun`, as
`mallocRoomSpec_of_run` does for the one-credit form.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

/-- A request (bytes) and the credits it is charged. -/
abbrev ChgRel := Nat → Nat → Prop

/-- **`_malloc_r`'s charged run, first-order.** A request `n` charged `c`
credits, from a heap with `k + c` credits, returns a fresh block and leaves
`k`. -/
def MallocChgRun (M : MachineModel) (L : DlLayout) (Room : RoomPred) (Chg : ChgRel)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob savedRegs : List Nat)
    (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k c : Nat),
    saved.map Prod.fst = savedRegs → Chg n.toNat c → SpOK s → r.toNat % 4 = 0 →
    EntryRegs rv entry r n s saved →
    L.Shape mv H → Room mv H (k + c) → (∀ a, stackWin s headroom a → ¬ heapFoot L H a) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (mallocBytes L H s headroom)
      (MallocRoomEnd L Room H n r s saved k) fuel rv mv

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `malloc` in the counted regime: `c` credits buy a fresh block for a
request they cover. -/
def mallocChgSpec (M : MachineModel) (L : DlLayout) (Room : RoomPred) (Chg : ChgRel)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat) (H : List (Nat × Nat)) (n s : BitVec 64)
    (k c : Nat) : IProp GF :=
  fnSpec (M := M) entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0 ∧ Chg n.toNat c⌝ ∗ a0 ↦ᵣ n ∗ sp ↦ᵣ s ∗
      gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      isHeapRoom L Room H (k + c)))
    (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗
      (⌜FreshBlock L H p.toNat n.toNat ∧ p.toNat % 16 = 0⌝ ∗
        isHeapRoom L Room ((p.toNat, n.toNat) :: H) k ∗ blockOwn p.toNat n.toNat)))

/-- **`mallocChgSpec` from the charged run.** -/
theorem mallocChgSpec_of_run {L : DlLayout} {Room : RoomPred} {Chg : ChgRel}
    {SpOK : BitVec 64 → Prop} {entry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : MallocChgRun M L Room Chg SpOK entry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hroom : RoomLocal L Room) (hnd : (allocRegs clob savedRegs).Nodup)
    (H : List (Nat × Nat)) (n s : BitVec 64) (k c : Nat) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = savedRegs) :
    textOwn (GF := GF) text ⊢ mallocChgSpec M L Room Chg SpOK entry gpv clob saved headroom H n s k c := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold mallocChgSpec fnSpec isHeapRoom
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hspok, hral, hchg⟩, Ha0, Hsp, #Hgp, Hclob, Hsv, Hstk, Hheap⟩ Hk
  iapply allocCall_of_localRun hd (heapFoot L H) (fun img => L.Shape img H ∧ Room img H (k + c))
    (fun img img' h hs => ⟨hloc H img img' h hs.1, hroom H img img' _ h hs.2⟩)
    (fun rv' mv' => FreshBlock L H (rv' a0).toNat n.toNat ∧ (rv' a0).toNat % 16 = 0 ∧
      L.Shape mv' (((rv' a0).toNat, n.toNat) :: H) ∧
      Room mv' (((rv' a0).toNat, n.toNat) :: H) k)
    (fun p => iprop(⌜FreshBlock L H p.toNat n.toNat ∧ p.toNat % 16 = 0⌝ ∗
      (∃ img : Nat → BitVec 8, ⌜L.Shape img ((p.toNat, n.toNat) :: H) ∧
        Room img ((p.toNat, n.toNat) :: H) k⌝ ∗
        ownSet (heapFoot L ((p.toNat, n.toNat) :: H)) (fun a => a ↦ₘ img a)) ∗
      blockOwn p.toNat n.toNat)) ?_
    (fun rv mv he hs hdj => (hrun H n s r saved rv mv k c rfl hchg hspok hral he hs.1 hs.2 hdj).imp
      fun _ h => LocalRun.mono (fun _ _ he => ⟨he.frame, he.fresh, he.align, he.shape, he.room⟩) _ _ _ h)
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

/-- **The counted allocator as a module parameter.** -/
structure DlMallocChgImpl (M : MachineModel) (L : DlLayout) (Room : RoomPred) (Chg : ChgRel)
    (SpOK : BitVec 64 → Prop) (mallocEntry gpv : BitVec 64) (clob savedRegs : List Nat)
    (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop where
  malloc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] H n s k c
    (saved : List (Nat × BitVec 64)), saved.map Prod.fst = savedRegs →
    textOwn (GF := GF) text ⊢ mallocChgSpec M L Room Chg SpOK mallocEntry gpv clob saved headroom H n s k c

theorem dlMallocChgImpl_of_run {M : MachineModel} {L : DlLayout} {Room : RoomPred} {Chg : ChgRel}
    {SpOK : BitVec 64 → Prop} {mallocEntry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : MallocChgRun M L Room Chg SpOK mallocEntry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hroom : RoomLocal L Room) (hnd : (allocRegs clob savedRegs).Nodup) :
    DlMallocChgImpl M L Room Chg SpOK mallocEntry gpv clob savedRegs headroom text where
  malloc H n s k c saved hsv := mallocChgSpec_of_run hrun hloc hroom hnd H n s k c saved hsv

end Spec


/-! ## Reallocation, charged

`realloc(p, nNew)` growing a live block `(p, nOld)` in the counted regime:
`c` credits for `nNew` buy a fresh block holding the old contents, never
NULL. -/

/-- What a charged realloc run ends in. -/
structure ReallocChgEnd (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat)) (p : BitVec 64)
    (nOld nNew : Nat) (old : Nat → BitVec 8) (r s : BitVec 64) (saved : List (Nat × BitVec 64))
    (k : Nat) (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8) : Prop where
  frame : RetFrame rv' r s saved
  fresh : FreshBlock L H (rv' a0).toNat nNew
  align : (rv' a0).toNat % 16 = 0
  shape : L.Shape mv' (((rv' a0).toNat, nNew) :: H)
  room : Room mv' (((rv' a0).toNat, nNew) :: H) k
  copies : Copies old mv' p.toNat (rv' a0).toNat nOld

/-- **`_realloc_r`'s charged grow run, first-order.** -/
def ReallocChgRun (M : MachineModel) (L : DlLayout) (Room : RoomPred) (Chg : ChgRel)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob savedRegs : List Nat)
    (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (p : BitVec 64) (nOld nNew : Nat) (s r : BitVec 64)
    (saved : List (Nat × BitVec 64)) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8)
    (old : Nat → BitVec 8) (k c : Nat),
    saved.map Prod.fst = savedRegs → Chg nNew c → SpOK s → r.toNat % 4 = 0 →
    EntryRegs rv entry r p s saved → rv a1 = BitVec.ofNat 64 nNew → nOld < nNew →
    L.Shape mv ((p.toNat, nOld) :: H) → Room mv ((p.toNat, nOld) :: H) (k + c) →
    Copies old mv p.toNat p.toNat nOld →
    (∀ a, stackWin s headroom a → ¬ (heapFoot L ((p.toNat, nOld) :: H) a ∨ InExt (p.toNat, nOld) a)) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (freeBytes L H p nOld s headroom)
      (ReallocChgEnd L Room H p nOld nNew old r s saved k) fuel rv mv

section Realloc

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `realloc`'s counted result: a fresh block with the old contents. -/
def reallocChgPost (L : DlLayout) (Room : RoomPred) (H : List (Nat × Nat)) (p : BitVec 64)
    (nOld nNew : Nat) (old : Nat → BitVec 8) (k : Nat) (p' : BitVec 64) : IProp GF :=
  iprop(⌜FreshBlock L H p'.toNat nNew ∧ p'.toNat % 16 = 0⌝ ∗
    isHeapRoom L Room ((p'.toNat, nNew) :: H) k ∗
    ∃ v : Nat → BitVec 8, ⌜Copies old v p.toNat p'.toNat nOld⌝ ∗ blockOwnAt p'.toNat nNew v)

/-- **`realloc` in the counted regime.** -/
def reallocChgSpec (M : MachineModel) (L : DlLayout) (Room : RoomPred) (Chg : ChgRel)
    (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64) (clob : List Nat)
    (saved : List (Nat × BitVec 64)) (headroom : Nat) (H : List (Nat × Nat)) (p : BitVec 64)
    (nOld nNew : Nat) (s : BitVec 64) (old : Nat → BitVec 8) (k c : Nat) : IProp GF :=
  fnSpec (M := M) entry
    (fun r => iprop(⌜SpOK s ∧ r.toNat % 4 = 0 ∧ nOld < nNew ∧ Chg nNew c⌝ ∗ a0 ↦ᵣ p ∗
      clobberedArg clob a1 (BitVec.ofNat 64 nNew) ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ savedOwn saved ∗
      stackScratch s headroom ∗ isHeapRoom L Room ((p.toNat, nOld) :: H) (k + c) ∗
      blockOwnAt p.toNat nOld old))
    (fun _ => iprop(∃ p', a0 ↦ᵣ p' ∗ sp ↦ᵣ s ∗ clobbered clob ∗ savedOwn saved ∗
      stackScratch s headroom ∗ reallocChgPost L Room H p nOld nNew old k p'))

/-- **`reallocChgSpec` from the charged run.** -/
theorem reallocChgSpec_of_run {L : DlLayout} {Room : RoomPred} {Chg : ChgRel}
    {SpOK : BitVec 64 → Prop} {entry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hrun : ReallocChgRun M L Room Chg SpOK entry gpv clob savedRegs headroom text)
    (hloc : ShapeLocal L) (hroom : RoomLocal L Room) (hnd : (allocRegs clob savedRegs).Nodup)
    (ha1 : a1 ∈ clob)
    (H : List (Nat × Nat)) (p : BitVec 64) (nOld nNew : Nat) (s : BitVec 64)
    (old : Nat → BitVec 8) (k c : Nat) (saved : List (Nat × BitVec 64))
    (hsv : saved.map Prod.fst = savedRegs) :
    textOwn (GF := GF) text ⊢
      reallocChgSpec M L Room Chg SpOK entry gpv clob saved headroom H p nOld nNew s old k c := by
  subst hsv
  have hd := RegsDistinct.of_nodup hnd
  unfold reallocChgSpec fnSpec blockOwnAt clobberedArg isHeapRoom
  iintro #Htext
  imodintro
  iintro %r %Φ Hpc Hra ⟨%⟨hspok, hral, hlt, hchg⟩, Ha0, Hclob, Hsp, #Hgp, Hsv, Hstk,
    ⟨%img, %⟨hsh, hrm⟩, Hheap⟩, Hblk⟩ Hk
  ihave ⟨⟨Hheap, Hblk⟩, %hHB⟩ := keep_pure
    (ownSet_disj (heapFoot L ((p.toNat, nOld) :: H)) (InExt (p.toNat, nOld)) img old) $$ [Hheap Hblk]
  · iframe Hheap Hblk
  ihave Hhb := ownSet_glue _ _ img old hHB $$ [Hheap Hblk]
  · iframe Hheap Hblk
  have hblk : ∀ a, InExt (p.toNat, nOld) a → ¬ heapFoot L ((p.toNat, nOld) :: H) a :=
    fun a hb hh => hHB a hh hb
  have hagree : ∀ a, heapFoot L ((p.toNat, nOld) :: H) a →
      img a = glue (heapFoot L ((p.toNat, nOld) :: H)) img old a := fun a ha => by simp [glue, ha]
  iapply allocCallArgs_of_localRun hd
    (fun a => heapFoot L ((p.toNat, nOld) :: H) a ∨ InExt (p.toNat, nOld) a)
    (fun img => L.Shape img ((p.toNat, nOld) :: H) ∧ Room img ((p.toNat, nOld) :: H) (k + c) ∧
      Copies old img p.toNat p.toNat nOld)
    (fun img img' h hs => ⟨hloc _ img img' (fun a ha => h a (.inl ha)) hs.1,
      hroom _ img img' _ (fun a ha => h a (.inl ha)) hs.2.1,
      fun j hj => (h _ (.inr ⟨by simp only; omega, by simp only; omega⟩)).symm.trans (hs.2.2 j hj)⟩)
    (fun cv => cv a1 = BitVec.ofNat 64 nNew) (fun f g h hf => (h a1 ha1).symm.trans hf)
    (fun rv' mv' => FreshBlock L H (rv' a0).toNat nNew ∧ (rv' a0).toNat % 16 = 0 ∧
      L.Shape mv' (((rv' a0).toNat, nNew) :: H) ∧ Room mv' (((rv' a0).toNat, nNew) :: H) k ∧
      Copies old mv' p.toNat (rv' a0).toNat nOld)
    (fun p' => reallocChgPost L Room H p nOld nNew old k p') ?_
    (fun rv mv he hargs hs hdj => (hrun H p nOld nNew s r saved rv mv old k c rfl hchg hspok hral
      he hargs hlt hs.1 hs.2.1 hs.2.2 hdj).imp fun _ h =>
        LocalRun.mono (fun _ _ he => ⟨he.frame, he.fresh, he.align, he.shape, he.room, he.copies⟩) _ _ _ h)
  · intro rv' mv' ⟨hf, hal, hsh', hrm', hcp⟩
    unfold reallocChgPost blockOwnAt isHeapRoom
    iintro HF
    ihave ⟨HF, -⟩ := ownSet_split _ (heapFoot L H) _ $$ HF
    ihave HF := ownSet_iff (T := heapFoot L H) _
      (fun a => ⟨fun h => h.2, fun h => ⟨heapFoot_sub_return L H _ _ a h, h⟩⟩) $$ HF
    ihave ⟨HF, Hblk⟩ := heapFoot_carve_gen L H _ _ hf _ $$ HF
    isplitr
    · ipureintro; exact ⟨hf, hal⟩
    isplitl [HF]
    · iexists mv'
      iframe HF
      ipureintro; exact ⟨hsh', hrm'⟩
    · iexists mv'
      iframe Hblk
      ipureintro; exact hcp
  · iframe Htext Hpc Hra Ha0 Hsp Hgp Hsv Hstk
    isplitl [Hclob]
    · iexact Hclob
    isplitl [Hhb]
    · iexists (glue (heapFoot L ((p.toNat, nOld) :: H)) img old)
      iframe Hhb
      ipureintro
      refine ⟨hloc _ img _ hagree hsh, hroom _ img _ _ hagree hrm, fun j hj => ?_⟩
      have hb : InExt (p.toNat, nOld) (p.toNat + j) := ⟨by simp only; omega, by simp only; omega⟩
      simp [glue, hblk _ hb]
    iintro Hpc Hra HQ
    iapply Hk $$ Hpc Hra HQ

end Realloc

/-! ## Regimes

`heapRes` (INTERP_DESIGN §3) is `isHeapRoom` counted and `isHeap` uncounted.
Credits are monotone: a heap with room for `k + j` has room for `k`. The
counted heap forgets to the uncounted one. -/

section Regime

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A capacity predicate that is downward closed in the credits. -/
def RoomMono (Room : RoomPred) : Prop :=
  ∀ img H k j, Room img H (k + j) → Room img H k

theorem isHeapRoom_mono {L : DlLayout} {Room : RoomPred} (hm : RoomMono Room)
    (H : List (Nat × Nat)) (k j : Nat) :
    isHeapRoom (GF := GF) L Room H (k + j) ⊢ isHeapRoom L Room H k := by
  unfold isHeapRoom
  iintro ⟨%img, %⟨hs, hr⟩, HF⟩
  iexists img
  iframe HF
  ipureintro; exact ⟨hs, hm img H k j hr⟩

end Regime

end VsaIris
