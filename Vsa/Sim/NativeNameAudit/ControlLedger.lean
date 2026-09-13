import Vsa.Sim.NativeNameAudit.ControlHeapMemory

/-! Concrete allocation ledger and shared strings for the heap control. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.NativeNameAudit.Control

open Vsa.Sim.RuntimeOwnership Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

def alloc : Allocations :=
  let a0 : Allocations := fun _ => none
  let a1 := a0.insert (.frame 0) 0x81000000 32
  let a2 := a1.insert (.names 0) 0x81000040 64
  let a3 := a2.insert (.values 0) 0x81000100 192
  let a4 := a3.insert (.binding 0 0) 0x81000200 6
  let a5 := a4.insert (.binding 0 1) 0x81000210 8
  a5.insert (.binding 0 2) 0x81000220 7

/-- The represented AST: one live immutable extent of the heap. -/
def astExtent : Extent := (0x82000000, 0x100)

def roleExts : List Extent :=
  [(0x81000220, 7), (0x81000210, 8), (0x81000200, 6),
   (0x81000100, 192), (0x81000040, 64), (0x81000000, 32)]

def exts : List Extent := astExtent :: roleExts

def shared (k : Nat) : Prop :=
  (0x81000200 ≤ k ∧ k < 0x81000206) ∨
  (0x81000210 ≤ k ∧ k < 0x81000218) ∨
  (0x81000220 ≤ k ∧ k < 0x81000227) ∨ AstPage k

theorem roleLedger : Ledger heapArena roleExts alloc := by
  have h0 : Ledger heapArena [] (fun _ => none) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [HeapArena]
    · intro r p n hr
      simp [Allocated] at hr
    · intro r s p n q size hr _ _
      simp [Allocated] at hr
  have h1 := h0.insert (role := .frame 0) (p := 0x81000000) (n := 32)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp)
  have h2 := h1.insert (role := .names 0) (p := 0x81000040) (n := 64)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp [ExtDisjoint])
  have h3 := h2.insert (role := .values 0) (p := 0x81000100) (n := 192)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp [ExtDisjoint])
  have h4 := h3.insert (role := .binding 0 0) (p := 0x81000200) (n := 6)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp [ExtDisjoint])
  have h5 := h4.insert (role := .binding 0 1) (p := 0x81000210) (n := 8)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp [ExtDisjoint])
  have h6 := h5.insert (role := .binding 0 2) (p := 0x81000220) (n := 7)
    (by decide) (by simp [Arena.contains, heapArena, DlHeap.heapStart, DlHeap.heapEnd]) (by simp [ExtDisjoint])
  exact h6

theorem ledger : Ledger heapArena exts alloc where
  arena := by
    unfold HeapArena exts roleExts astExtent ExtDisjoint Arena.contains heapArena DlHeap.heapStart DlHeap.heapEnd
    decide
  live := fun role p n hp => List.mem_cons_of_mem _ (roleLedger.live role p n hp)
  separated := roleLedger.separated

private theorem mutable_extent {role : Role} {p n : Nat}
    (hm : role.mutable) (ha : Allocated alloc role p n) :
    (p, n) = (0x81000000, 32) ∨ (p, n) = (0x81000040, 64) ∨
      (p, n) = (0x81000100, 192) := by
  cases role with
  | frame fa =>
    by_cases hf : fa = 0
    · subst fa
      have he : (0x81000000, 32) = (p, n) := by
        simpa [Allocated, alloc, Allocations.insert] using ha
      exact Or.inl he.symm
    · simp [Allocated, alloc, Allocations.insert, hf] at ha
  | names fa =>
    by_cases hf : fa = 0
    · subst fa
      have he : (0x81000040, 64) = (p, n) := by
        simpa [Allocated, alloc, Allocations.insert] using ha
      exact Or.inr (Or.inl he.symm)
    · simp [Allocated, alloc, Allocations.insert, hf] at ha
  | values fa =>
    by_cases hf : fa = 0
    · subst fa
      have he : (0x81000100, 192) = (p, n) := by
        simpa [Allocated, alloc, Allocations.insert] using ha
      exact Or.inr (Or.inr he.symm)
    · simp [Allocated, alloc, Allocations.insert, hf] at ha
  | binding fa i => exact hm.elim
  | closure ca => simp [Allocated, alloc, Allocations.insert] at ha

theorem immutable : Immutable alloc shared InitialReadableByte (InitialWriteByte stackSL) where
  readable := by
    intro k hk
    unfold shared AstPage at hk
    unfold InitialReadableByte
    omega
  outsideWrites := by
    intro k hk hw
    unfold shared AstPage at hk
    change (0x8001ad00 ≤ k ∧ k < 0x8001c168) ∨
      (0x87800000 ≤ k ∧ k < 0x88000000) at hw
    omega
  outsideMutable := by
    intro role p n hm ha k hk hin
    have he := mutable_extent hm ha
    unfold shared AstPage at hk
    rcases he with he | he | he
    all_goals rw [he] at hin
    all_goals simp only [ExtentByte, Nat.reduceAdd] at hin
    all_goals omega

theorem reserved : Reserved heapArena exts shared where
  live := by
    intro k hk _ _
    rcases hk with hk | hk | hk | hk
    · exact ⟨(0x81000200, 6), by simp [exts, roleExts], hk⟩
    · exact ⟨(0x81000210, 8), by simp [exts, roleExts], hk⟩
    · exact ⟨(0x81000220, 7), by simp [exts, roleExts], hk⟩
    · refine ⟨astExtent, by simp [exts], ?_⟩
      unfold AstPage at hk
      change 0x82000000 ≤ k ∧ k < 0x82000000 + 0x100
      omega

theorem printShared : SharedCString heapMem shared 0x81000200 "print" where
  repr := heapStoreFacts.printName
  bytes := by
    intro k hk
    change k ≤ 5 at hk
    exact Or.inl ⟨by omega, by omega⟩

theorem printlnShared : SharedCString heapMem shared 0x81000210 "println" where
  repr := heapStoreFacts.printlnName
  bytes := by
    intro k hk
    change k ≤ 7 at hk
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)

theorem assertShared : SharedCString heapMem shared 0x81000220 "assert" where
  repr := heapStoreFacts.assertName
  bytes := by
    intro k hk
    change k ≤ 6 at hk
    exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

#print axioms ledger
#print axioms immutable
#print axioms reserved
#print axioms printShared
#print axioms printlnShared
#print axioms assertShared

end Vsa.Sim.NativeNameAudit.Control
