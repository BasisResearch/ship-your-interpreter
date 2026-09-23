import VsaIris.Vsa.Malloc
import Vsa.Sim.AllocLedger
import Vsa.Sim.AllocCapacity

/-!
# Feeding a VSA allocator consumer from the Iris spec

`EnvDefineAppendAllocatorPost.prepareCopy` (`Vsa/Sim/EnvDefineNameAllocate.lean`)
calls `malloc` through `mallocReturn_of_parked` and uses these fields of the
`MallocReturnAt` it gets back:

| `MallocReturnAt` field | used for | VSA supplier today |
|---|---|---|
| `block` | the fresh extent (`MallocBlock`) | `MallocContract.spec` |
| `owned0`, `owned` (via `.runtime`) | caller ownership survives, block enters | `transport_off` + `OwnedOff` from `privFoot_disjoint`, `priv_arena`, `arena_stack` |
| `store` (via `.runtime`) | store representation survives | `repr_off`, same |
| `agree` + `ownedOff.shared` | shared bytes unchanged | `mem_frame` off `privFoot` |
| `exit.mem_frame` | the value slot and eval-call support unchanged | `mem_frame` + `priv_arena` + `arena_stack` |
| `ainv`, `budget`, `reserve` | allocator invariant and capacity | `MallocSuccessRun`, `AllocLedger` (`reserve` is unsatisfiable for requests whose usable tail reaches the new top; see `vsa_reserve_fails_after_split`) |

This module derives the first five from the Iris spec with no
`MallocContract`, `AllocLedger`, `privFoot` or ledger arithmetic:

* `wp_call_malloc_owns` (Iris): a caller owning any byte set `C` at an image
  gets it back unchanged, and learns `C` is off the fresh block and off the
  allocator's new footprint, by ghost exclusivity;
* `ownSet_agree_state`: owned bytes pin the actual memory of any later
  configuration (`vsaModel`, with the bytes present);
* `mallocCallerFacts_of_iris` (pure): from agreement on the caller's owned
  bytes (`callerFoot`) and `mallocPost`'s `FreshBlock`, VSA's `MallocBlock`,
  both `HeapOwned`s, `StoreRepr` and shared-byte agreement follow by VSA's own
  `HeapOwned.transport`/`.fresh`/`repr_transport`.

`ainv` is `isHeap` itself. `mallocRoomCallerFacts_of_iris` adds `budget` and
the reserve from `mallocRoomSpec` (success under credits). The reserve is the
corrected `Reserve`: VSA's `AllocationReserve` cannot hold after a request
whose usable tail reaches the new top chunk (`vsa_reserve_fails_after_split`),
so that consumer premise must be weakened in VSA to the corrected clause.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section Client

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- **Calling malloc while owning a byte set.** The set comes back at the
same image, and it is disjoint from the fresh block and from the allocator's
new footprint. This replaces `HeapOwned.ownedOff` (`OwnedOff`) and the
`mem_frame` uses of a `MallocReturnAt` in one step. -/
theorem wp_call_malloc_owns {Φ : Nat × String → IProp GF} {L : DlLayout} {SpOK : BitVec 64 → Prop}
    {mallocEntry freeEntry gpv : BitVec 64} {clob savedRegs : List Nat} {headroom : Nat}
    {text : List (Nat × BitVec 8)}
    (impl : DlMallocImpl M L SpOK mallocEntry freeEntry gpv clob savedRegs headroom text)
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec M i code mallocEntry)
    (H : List (Nat × Nat)) (v n s : BitVec 64) (saved : List (Nat × BitVec 64))
    (hsaved : saved.map Prod.fst = savedRegs) (hsp : SpOK s)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    (C : Nat → Prop) (img : Nat → BitVec 8) :
    instrAt (GF := GF) i code ∗ textOwn text ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ a0 ↦ᵣ n ∗
      sp ↦ᵣ s ∗ gp ↦ᵣ□ gpv ∗ clobbered clob ∗ savedOwn saved ∗ stackScratch s headroom ∗
      isHeap L H ∗ ownSet C (fun a => a ↦ₘ img a) ∗
      (∀ p, PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ a0 ↦ᵣ p -∗
        sp ↦ᵣ s -∗ clobbered clob -∗ savedOwn saved -∗ stackScratch s headroom -∗
        mallocPost L H n.toNat p -∗ ownSet C (fun a => a ↦ₘ img a) -∗
        ⌜p ≠ 0 → ∀ a, C a →
          ¬ InExt (p.toNat, n.toNat) a ∧ ¬ heapFoot L ((p.toNat, n.toNat) :: H) a⌝ -∗
        mTWP M Φ)
    ⊢ mTWP M Φ := by
  iintro ⟨Hi, Htext, Hpc, Hra, Ha0, Hsp, Hgp, Hclob, Hsv, Hstk, Hheap, HC, Hk⟩
  iapply wp_call_malloc impl hexec H v n s saved hsaved hsp hal (ownSet C (fun a => a ↦ₘ img a))
  iframe Hi Htext Hpc Hra Ha0 Hsp Hgp Hclob Hsv Hstk Hheap HC
  unfold mallocPost
  iintro %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk Hpost HC
  icases Hpost with (⟨%hp, Hheap⟩ | ⟨%hf, Hheap, Hblk⟩)
  · iapply Hk $$ %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk [Hheap] HC
    · ileft; iframe Hheap; ipureintro; exact hp
    ipureintro
    intro hne; exact absurd hp hne
  · unfold isHeap blockOwn
    icases Hheap with ⟨%img', %hsh, Hheap⟩
    ihave ⟨⟨HC, Hblk⟩, %hb⟩ := keep_pure (ownSet_off C (InExt (p.toNat, n.toNat)) img)
      $$ [HC Hblk]
    · iframe HC Hblk
    ihave ⟨⟨HC, Hheap⟩, %hh⟩ := keep_pure
      (ownSet_disj C (heapFoot L ((p.toNat, n.toNat) :: H)) img img') $$ [HC Hheap]
    · iframe HC Hheap
    iapply Hk $$ %p Hpc Hra Ha0 Hsp Hclob Hsv Hstk [Hheap Hblk] HC
    · iright
      iframe Hblk
      isplitr
      · ipureintro; exact hf
      iexists img'
      iframe Hheap
      ipureintro; exact hsh
    ipureintro
    intro _ a ha
    exact ⟨hb a ha, hh a ha⟩

/-- Owned bytes pin the machine's memory in any state the interpretation
covers. -/
theorem ownSet_agree_state {σ : M.State} (C : Nat → Prop) (img : Nat → BitVec 8) :
    ownSet (GF := GF) C (fun a => a ↦ₘ img a) ∗ mstateInterp M σ ⊢
      ⌜∀ a, C a → M.mem σ a = img a⌝ := by
  unfold ownSet mstateInterp
  iintro ⟨⟨%l, %⟨_, hmem⟩, Hl⟩, ⟨_, Hm, _⟩⟩
  suffices h : ∀ l : List Nat, sepL l (fun a => a ↦ₘ img a) ∗ memInterp M σ ⊢@{IProp GF}
      ⌜∀ a ∈ l, M.mem σ a = img a⌝ by
    ihave %h' := h l $$ [Hl Hm]
    · iframe Hl Hm
    ipureintro
    exact fun a ha => h' a ((hmem a).2 ha)
  intro l
  induction l with
  | nil => iintro _; ipureintro; intro a ha; cases ha
  | cons x xs ih =>
    rw [sepL_cons]
    have A : iprop((x ↦ₘ img x ∗ sepL xs (fun a => a ↦ₘ img a)) ∗ memInterp M σ) ⊢@{IProp GF}
        ⌜M.mem σ x = img x⌝ := by
      iintro ⟨⟨Hx, _⟩, Hm⟩
      iapply mem_valid $$ Hm Hx
    have B : iprop((x ↦ₘ img x ∗ sepL xs (fun a => a ↦ₘ img a)) ∗ memInterp M σ) ⊢@{IProp GF}
        ⌜∀ a ∈ xs, M.mem σ a = img a⌝ := by
      iintro ⟨⟨_, Hxs⟩, Hm⟩
      iapply ih
      iframe Hxs Hm
    refine (and_intro A B).trans (pure_and.1.trans (pure_mono fun h a ha => ?_))
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact h.2 a ha

end Client

end VsaIris

/-! ## The consumer's allocator premises, from the Iris post -/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim Vsa.Sim.DlHeap Vsa.Sim.RuntimeOwnership

/-- Every VSA ledger extent lies in an Iris live block. -/
def Covered (exts : List Extent) (H : List (Nat × Nat)) : Prop :=
  ∀ e ∈ exts, ∃ b ∈ H, ∀ a, InExt e a → InExt b a

/-- The bytes a VSA caller owns: every allocated extent and every shared byte. -/
def callerFoot (alloc : Allocations) (shared : Nat → Prop) (k : Nat) : Prop :=
  (∃ role p n, Allocated alloc role p n ∧ ExtentByte (p, n) k) ∨ shared k

/-- `mallocPost`'s success arm is VSA's `MallocBlock`, for any ledger whose
extents lie in the live blocks. -/
theorem mallocBlock_of_fresh {H : List (Nat × Nat)} {exts : List Extent} {p n : Nat}
    (hf : FreshBlock vsaLayout H p n) (hal : p % 16 = 0) (hn : 0 < n)
    (harena : HeapArena vsaArena exts) (hcov : Covered exts H) :
    MallocBlock vsaArena exts n p where
  nonzero := hf.nonzero
  align := hal
  arena := ⟨hf.lo, hf.hi⟩
  fresh := by
    intro e he
    obtain ⟨b, hb, hsub⟩ := hcov e he
    have hpos := (harena.1 e he).1
    unfold ExtDisjoint
    refine Classical.byContradiction fun hov => ?_
    have hov' : e.1 < p + n ∧ p < e.1 + e.2 := by simp only at hov; omega
    let a := max p e.1
    have ha1 : InExt (p, n) a := by unfold InExt; simp only [a]; omega
    have ha2 : InExt e a := by unfold InExt; simp only [a]; omega
    exact hf.disjoint b hb a ha1 (hsub a ha2)

/-- What `EnvDefineAppendAllocatorPost.prepareCopy` and `envNewAllocator_run`
take from a malloc return, besides the allocator invariant and capacity. -/
structure MallocCallerFacts (exts : List Extent) (n p : Nat) (m0 m1 : Mem) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (shared readable writes : Nat → Prop)
    (s : Store) : Prop where
  block : MallocBlock vsaArena exts n p
  owned0 : HeapOwned vsaArena exts m1 phiF phiC alloc shared readable writes s
  owned : HeapOwned vsaArena ((p, n) :: exts) m1 phiF phiC alloc shared readable writes s
  store : StoreRepr m1 N vsaArena phiF phiC s
  sharedAgree : AgreeP shared m0 m1

/-- **The consumer's allocator premises from the Iris spec.** Agreement on
the caller's owned bytes (what `wp_call_malloc_owns` and
`ownSet_agree_state` give) and `mallocPost`'s fresh block yield every
`MallocReturnAt` field `prepareCopy` uses, except the invariant and capacity.
No `MallocContract`, `AllocLedger`, `privFoot`, `OwnedOff` or stack-window
arithmetic is involved. -/
theorem mallocCallerFacts_of_iris {H : List (Nat × Nat)} {exts : List Extent} {n p : Nat}
    {m0 m1 : Mem} {N : NativeAddrs} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store}
    (h : HeapOwned vsaArena exts m0 phiF phiC alloc shared readable writes s)
    (hr : StoreRepr m0 N vsaArena phiF phiC s)
    (hag : AgreeP (callerFoot alloc shared) m0 m1)
    (hf : FreshBlock vsaLayout H p n) (hal : p % 16 = 0) (hn : 0 < n)
    (hcov : Covered exts H) :
    MallocCallerFacts exts n p m0 m1 N phiF phiC alloc shared readable writes s := by
  have ha : ∀ role q k, Allocated alloc role q k → ∀ x, ExtentByte (q, k) x →
      callerFoot alloc shared x := fun role q k hq x hx => .inl ⟨role, q, k, hq, hx⟩
  have hs : ∀ x, shared x → callerFoot alloc shared x := fun x hx => .inr hx
  have block := mallocBlock_of_fresh hf hal hn h.ledger.arena hcov
  have owned0 := h.transport hag ha hs
  exact
    { block := block
      owned0 := owned0
      owned := owned0.fresh hn block.arena block.fresh
      store := h.store.repr_transport hr hag ha hs
      sharedAgree := fun x hx => hag x (hs x hx) }

/-- A reserve stated over the live blocks holds over any ledger inside them. -/
theorem reserve_of_covered {m : Mem} {H : List (Nat × Nat)} {exts : List Extent}
    {maxReq k : Nat} (h : Reserve m H maxReq k) (hcov : Covered exts H)
    (hpos : ∀ e ∈ exts, 0 < e.2) : Reserve m exts maxReq k := by
  intro positive
  obtain ⟨top, bytes, r⟩ := h positive
  refine ⟨top, bytes, { r with disjoint := ?_ }⟩
  intro e he
  obtain ⟨b, hb, hsub⟩ := hcov e he
  have hp := hpos e he
  have lo := hsub e.1 (by unfold InExt; omega)
  have hi := hsub (e.1 + e.2 - 1) (by unfold InExt; omega)
  unfold InExt at lo hi
  have := r.disjoint b hb
  omega

/-- The consumer's facts with capacity: the budget and the placement reserve
for the remaining credits. -/
structure MallocRoomCallerFacts (exts : List Extent) (n p : Nat) (m0 m1 : Mem)
    (N : NativeAddrs) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (maxReq credits : Nat) : Prop
    extends MallocCallerFacts exts n p m0 m1 N phiF phiC alloc shared readable writes s where
  budget : ResourceBudget vsaArena maxReq ((p, n) :: exts) credits
  /-- The corrected reserve (`Reserve`); VSA's own `AllocationReserve` is not
  satisfiable here in general (`vsa_reserve_fails_after_split`). -/
  reserve : Reserve m1 ((p, n) :: exts) maxReq credits

/-- **Every `MallocReturnAt` field `prepareCopy` uses, from `mallocRoomSpec`.**
Besides `mallocCallerFacts_of_iris`'s inputs: the entry budget (a ledger
count), the request bound, and the room of the returned heap image, pinned in
the actual memory by the allocator's own bytes (`ownSet_agree_state` applied
to `isHeapRoom`). `ainv` is `isHeapRoom` itself. -/
theorem mallocRoomCallerFacts_of_iris {H : List (Nat × Nat)} {exts : List Extent} {n p : Nat}
    {m0 m1 : Mem} {N : NativeAddrs} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {maxReq credits : Nat}
    {img : Nat → BitVec 8}
    (h : HeapOwned vsaArena exts m0 phiF phiC alloc shared readable writes s)
    (hr : StoreRepr m0 N vsaArena phiF phiC s)
    (hag : AgreeP (callerFoot alloc shared) m0 m1)
    (hf : FreshBlock vsaLayout H p n) (hal : p % 16 = 0) (hn : 0 < n)
    (hcov : Covered exts H)
    (hbud : ResourceBudget vsaArena maxReq exts (credits + 1)) (hreq : n ≤ maxReq)
    (hroom : vsaRoom maxReq img ((p, n) :: H) credits)
    (him : ImgOn (vsaFoot ((p, n) :: H)) img m1) :
    MallocRoomCallerFacts exts n p m0 m1 N phiF phiC alloc shared readable writes s
      maxReq credits := by
  have base := mallocCallerFacts_of_iris h hr hag hf hal hn hcov
  have hcov' : Covered ((p, n) :: exts) ((p, n) :: H) := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, List.mem_cons_self, fun a ha => ha⟩
    · obtain ⟨b, hb, hsub⟩ := hcov e he
      exact ⟨b, List.mem_cons_of_mem _ hb, hsub⟩
  have hpos : ∀ e ∈ (p, n) :: exts, 0 < e.2 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hn
    · exact (h.ledger.arena.1 e he).1
  exact
    { toMallocCallerFacts := base
      budget := ResourceBudget.alloc hbud hreq
      reserve := reserve_of_covered (reserve_of_room hroom him) hcov' hpos }


/-! ## Reallocation -/

def reallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Sim.reallocEntry

/-- The binary's `realloc` meets `reallocSpec`, given its first-order run. -/
theorem vsaDlReallocImpl (live : Nat → Prop) {SpOK : BitVec 64 → Prop} (gpv : BitVec 64)
    (headroom : Nat) (text : List (Nat × BitVec 8))
    (hr : ReallocLocalRun (VsaIris.Inst.vsaModel live) vsaLayout SpOK reallocEntryBV gpv vsaClob vsaSaved
      headroom text) :
    DlReallocImpl (VsaIris.Inst.vsaModel live) vsaLayout SpOK reallocEntryBV gpv vsaClob vsaSaved
      headroom text :=
  dlReallocImpl_of_localRun hr shapeLocal_vsaLayout vsaAllocRegs_nodup (by decide)

/-- `reallocPost`'s success arm gives the fresh-block clauses of VSA's
`ReallocGrowResult`: nonzero, aligned, in the arena, and disjoint from every
live extent but the old one. -/
theorem reallocBlock_of_fresh {H : List (Nat × Nat)} {exts : List Extent} {old : Extent} {p n : Nat}
    (hf : FreshBlock vsaLayout H p n) (hal : p % 16 = 0) (hn : 0 < n)
    (harena : HeapArena vsaArena exts) (hcov : Covered (exts.erase old) H) :
    MallocBlock vsaArena (exts.erase old) n p :=
  mallocBlock_of_fresh hf hal hn
    ⟨fun e he => harena.1 e (List.erase_subset he), harena.2.sublist List.erase_sublist⟩ hcov

/-- The old contents at the new block: VSA's `ReallocCopies`, from the owned
bytes before and after (present, as `ImgOn` gives them). -/
theorem reallocCopies_of_owned {m0 m1 : Mem} {old v : Nat → BitVec 8} {pOld pNew nOld : Nat}
    (h0 : ∀ k, k < nOld → m0[pOld + k]? = some (old (pOld + k)))
    (h1 : ∀ k, k < nOld → m1[pNew + k]? = some (v (pNew + k)))
    (hc : Copies old v pOld pNew nOld) : ReallocCopies m0 m1 pOld pNew nOld :=
  fun k hk => by rw [h1 k hk, h0 k hk, hc k hk]

end VsaIris.VsaHeap
