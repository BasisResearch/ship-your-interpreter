import Vsa.Sim.NativeNameAudit.ControlPhysical
import Vsa.Sim.MemPresence
import Vsa.Sim.InterpSpillReads

/-!
The admitted control with a consistent dlmalloc heap. Over the repaired control
log it writes empty bin lists and the top pointer (`avLog`), then the moved
value array, the break, the `sbrk` base, and in-use chunk headers from `_end`
to the top chunk (`smallLog`). The value array moves to its own chunk payload
at `0x81000100`; the names array keeps its capacity-8 payload at `0x81000040`.

Bin words are read by induction over `binsLog`; small-log words through a
21-entry lookup; every other byte transports from the old control memory.
-/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance Vsa.Sim.DlHeap

def heapTop : Nat := 0x82000200
def heapBrk : Nat := 0x82001000

/-- Bin `i` linked to itself: an empty bin. -/
def binLog (i : Nat) : List WEntry :=
  [(binAt i + 16, 8, BitVec.ofNat 64 (binAt i)),
   (binAt i + 24, 8, BitVec.ofNat 64 (binAt i))]

/-- Bins `1..k`, in address order. -/
def binsLog : Nat → List WEntry
  | 0 => []
  | k + 1 => binsLog k ++ binLog (k + 1)

/-- All 127 bins; irreducible so elaboration never unfolds the list. -/
@[irreducible] def allBins : List WEntry := binsLog 127

theorem allBins_eq : allBins = binsLog 127 := by unfold allBins; rfl

def topEntry : WEntry := (topAddr, 8, BitVec.ofNat 64 heapTop)
def avLog : List WEntry := topEntry :: allBins

/-- The value array at its chunk payload. -/
def storeLog : List WEntry :=
  [(0x81000010, 8, 0x81000100#64),
   (0x81000100, 4, 5#64), (0x81000108, 8, 0x81000200#64), (0x81000110, 8, 0x80002ed4#64),
   (0x81000118, 4, 5#64), (0x81000120, 8, 0x81000210#64), (0x81000128, 8, 0x80002f7c#64),
   (0x81000130, 4, 5#64), (0x81000138, 8, 0x81000220#64), (0x81000140, 8, 0x80002df4#64)]

/-- `sbrk` base, break, and the size word of every chunk up to the top chunk. -/
def chunkLog : List WEntry :=
  [(0x8001b960, 8, 0x8001c170#64), (0x8001b990, 8, 0x82001000#64),
   (0x8001c178, 8, 0xfe3e81#64), (0x80fffff8, 8, 0x41#64), (0x81000038, 8, 0x51#64),
   (0x81000088, 8, 0x71#64), (0x810000f8, 8, 0xd1#64), (0x810001c8, 8, 0x81#64),
   (0x81000248, 8, 0xfffdb1#64), (0x81fffff8, 8, 0x211#64), (0x82000208, 8, 0xe01#64)]

def smallLog : List WEntry := storeLog ++ chunkLog
def heapLog : List WEntry := avLog ++ smallLog
def fullLog : List WEntry := log ++ heapLog
def avMem : Mem := writeLog mem avLog
def heapMem : Mem := writeLog snapshotMem fullLog
def heapConfig : Config := physicalConfigS0 heapMem

theorem heapMem_eq : heapMem = writeLog avMem smallLog := by
  show writeLog snapshotMem (log ++ (avLog ++ smallLog)) =
    writeLog (writeLog (writeLog snapshotMem log) avLog) smallLog
  rw [writeLog_append, writeLog_append]

theorem smallLookup (a : Nat) : heapMem[a]? = logRead (fun k => avMem[k]?) smallLog a := by
  rw [heapMem_eq]
  exact writeLog_getElem?_logRead_of_initial avMem _ (fun _ => rfl) smallLog a

/-- Words written by the small log. -/
local macro "small_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, smallLookup]; decide +kernel))

/-- Words of the old control memory. -/
local macro "old_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, lookup]; decide))

theorem outL_of_forall {l : List WEntry} {k : Nat}
    (h : ∀ e ∈ l, k < e.1 ∨ e.1 + e.2.1 ≤ k) : OutL l k := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨h e (by simp), ih (fun e' he' => h e' (by simp [he']))⟩

theorem outLRange_of_forall {l : List WEntry} {a n : Nat}
    (h : ∀ e ∈ l, a + n ≤ e.1 ∨ e.1 + e.2.1 ≤ a) : OutLRange l a n := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨h e (by simp), ih (fun e' he' => h e' (by simp [he']))⟩

theorem binsLog_bounds : ∀ k e, e ∈ binsLog k →
    avAddr + 32 ≤ e.1 ∧ e.1 + e.2.1 ≤ avAddr + 16 * k + 32
  | 0, e, he => by simp [binsLog] at he
  | k + 1, e, he => by
    rw [binsLog, List.mem_append] at he
    rcases he with he | he
    · have := binsLog_bounds k e he
      omega
    · simp only [binLog, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> (dsimp only [binAt]; omega)

theorem avLog_bounds : ∀ e ∈ avLog, 0x8001ad20 ≤ e.1 ∧ e.1 + e.2.1 ≤ 0x8001b520 := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · decide
  · rw [allBins_eq] at he
    have := binsLog_bounds 127 e he
    simp only [avAddr] at this
    omega

theorem avMem_eq : avMem = writeLog (writeLog mem [topEntry]) allBins :=
  writeLog_append mem [topEntry] allBins

theorem smallLog_bounds : ∀ e ∈ smallLog, 0x8001b520 ≤ e.1 ∨ e.1 + e.2.1 ≤ 0x8001ad20 := by
  decide

theorem heap_unchanged {k : Nat} (hav : k < 0x8001ad20 ∨ 0x8001b520 ≤ k)
    (hsmall : OutL smallLog k) : heapMem[k]? = mem[k]? := by
  rw [heapMem_eq, writeLog_out _ _ _ hsmall]
  exact writeLog_out _ _ _ (outL_of_forall fun e he => by have := avLog_bounds e he; omega)

/-- Bytes of `__malloc_av_` are the bin layer's. -/
theorem heap_av {k : Nat} (hk : 0x8001ad20 ≤ k ∧ k < 0x8001b520) :
    heapMem[k]? = avMem[k]? := by
  rw [heapMem_eq]
  exact writeLog_out _ _ _ (outL_of_forall fun e he => by have := smallLog_bounds e he; omega)

/-- Runtime data, image, and stack bytes are the old control's. -/
theorem unchanged_low {k : Nat}
    (hk : k < 0x8001ad20 ∨ (0x8001b520 ≤ k ∧ k < 0x8001b960) ∨
      (0x8001b968 ≤ k ∧ k < 0x8001b990) ∨ (0x8001b998 ≤ k ∧ k < 0x8001c178) ∨
      0x87800000 ≤ k) : heapMem[k]? = mem[k]? :=
  heap_unchanged (by omega) (by
    simp only [smallLog, storeLog, chunkLog, List.cons_append, List.nil_append, OutL,
      Nat.reduceAdd, and_true]
    omega)

/-- The store words the heap log leaves alone. -/
theorem unchanged_store {k : Nat}
    (hk : (0x81000000 ≤ k ∧ k < 0x81000010) ∨ (0x81000018 ≤ k ∧ k < 0x81000020) ∨
      (0x81000040 ≤ k ∧ k < 0x81000058)) : heapMem[k]? = mem[k]? :=
  heap_unchanged (by omega) (by
    simp only [smallLog, storeLog, chunkLog, List.cons_append, List.nil_append, OutL,
      Nat.reduceAdd, and_true]
    omega)

theorem unchanged_strings {k : Nat} (hk : 0x81000200 ≤ k ∧ k < 0x81000240) :
    heapMem[k]? = mem[k]? :=
  heap_unchanged (by omega) (by
    simp only [smallLog, storeLog, chunkLog, List.cons_append, List.nil_append, OutL,
      Nat.reduceAdd, and_true]
    omega)

theorem unchanged_ast {k : Nat} (hk : 0x82000000 ≤ k ∧ k < 0x82000200) :
    heapMem[k]? = mem[k]? :=
  heap_unchanged (by omega) (by
    simp only [smallLog, storeLog, chunkLog, List.cons_append, List.nil_append, OutL,
      Nat.reduceAdd, and_true]
    omega)

theorem read64_heap {a v : Nat} (hold : read64 mem a = some v)
    (hr : ∀ j, j < 8 → heapMem[a + j]? = mem[a + j]?) : read64 heapMem a = some v := by
  rw [read64_agreeP (P := fun k => heapMem[k]? = mem[k]?) (fun _ hk => hk) hr]
  exact hold

theorem read32_heap {a v : Nat} (hold : read32 mem a = some v)
    (hr : ∀ j, j < 4 → heapMem[a + j]? = mem[a + j]?) : read32 heapMem a = some v := by
  rw [read32_agreeP (P := fun k => heapMem[k]? = mem[k]?) (fun _ hk => hk) hr]
  exact hold

/-- Every bin word written by `binsLog k` reads back over any base memory. -/
theorem binsLog_read (m : Mem) : ∀ k i, 0 < i → i ≤ k →
    read64 (writeLog m (binsLog k)) (binAt i + 16) = some (BitVec.ofNat 64 (binAt i)).toNat ∧
    read64 (writeLog m (binsLog k)) (binAt i + 24) = some (BitVec.ofNat 64 (binAt i)).toNat
  | 0, _, _, hk => absurd hk (by omega)
  | k + 1, i, h0, hk => by
    by_cases hi : i ≤ k
    · obtain ⟨h1, h2⟩ := binsLog_read m k i h0 hi
      have hag : AgreeP (fun a => OutL (binLog (k + 1)) a)
          (writeLog m (binsLog (k + 1))) (writeLog m (binsLog k)) := by
        intro a ha
        show (writeLog m (binsLog k ++ binLog (k + 1)))[a]? = _
        rw [writeLog_append]
        exact writeLog_out _ _ a ha
      constructor
      · rw [read64_agreeP hag (by
          intro j hj
          simp only [binLog, OutL, binAt, and_true]
          omega)]
        exact h1
      · rw [read64_agreeP hag (by
          intro j hj
          simp only [binLog, OutL, binAt, and_true]
          omega)]
        exact h2
    · have he : i = k + 1 := by omega
      subst he
      constructor
      · exact read64_of_writeLog m (binsLog k)
          [(binAt (k + 1) + 24, 8, BitVec.ofNat 64 (binAt (k + 1)))] _ _
          (by simp only [OutLRange, and_true]; omega)
      · have h := read64_of_writeLog m
          (binsLog k ++ [(binAt (k + 1) + 16, 8, BitVec.ofNat 64 (binAt (k + 1)))]) []
          (binAt (k + 1) + 24) (BitVec.ofNat 64 (binAt (k + 1))) trivial
        simpa only [binsLog, binLog, List.append_assoc, List.cons_append,
          List.nil_append] using h

theorem binAt_lt {i : Nat} (hi : i < 128) : binAt i < 2 ^ 64 := by
  simp only [binAt, avAddr]
  omega

/-- Every bin of the heap snapshot is linked to itself. -/
theorem heapBins (i : Nat) (h0 : 0 < i) (hi : i < 128) :
    read64 heapMem (binAt i + 16) = some (binAt i) ∧
      read64 heapMem (binAt i + 24) = some (binAt i) := by
  have hv : (BitVec.ofNat 64 (binAt i)).toNat = binAt i := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (binAt_lt hi)
  have hav : ∀ o, o = 16 ∨ o = 24 → ∀ j, j < 8 →
      heapMem[binAt i + o + j]? = avMem[binAt i + o + j]? := by
    intro o ho j hj
    apply heap_av
    simp only [binAt, avAddr]
    omega
  obtain ⟨h1, h2⟩ := binsLog_read (writeLog mem [topEntry]) 127 i h0 (by omega)
  rw [← allBins_eq, hv] at h1 h2
  constructor
  · rw [read64_agreeP (P := fun k => heapMem[k]? = avMem[k]?) (fun _ hk => hk)
      (hav 16 (Or.inl rfl)), avMem_eq]
    exact h1
  · rw [read64_agreeP (P := fun k => heapMem[k]? = avMem[k]?) (fun _ hk => hk)
      (hav 24 (Or.inr rfl)), avMem_eq]
    exact h2

theorem heapTopPtr : read64 heapMem topAddr = some heapTop := by
  rw [read64_agreeP (P := fun k => heapMem[k]? = avMem[k]?) (fun _ hk => hk)
    (fun j hj => heap_av (by simp only [topAddr, avAddr]; omega))]
  have hd : OutLRange allBins topAddr 8 := outLRange_of_forall fun e he => by
    rw [allBins_eq] at he
    have := binsLog_bounds 127 e he
    simp only [topAddr, avAddr] at this ⊢
    omega
  rw [show avMem = writeLog mem ([] ++ (topAddr, 8, BitVec.ofNat 64 heapTop) :: allBins)
    from rfl, read64_of_writeLog mem [] allBins topAddr _ hd]
  rfl

/-- The global store at the heap layout. -/
structure HeapStoreFacts (m : Mem) : Prop where
  count : read32 m 0x81000000 = some 3
  capacity : read32 m 0x81000004 = some 8
  names : read64 m 0x81000008 = some 0x81000040
  values : read64 m 0x81000010 = some 0x81000100
  parent : read64 m 0x81000018 = some 0
  names0 : read64 m 0x81000040 = some 0x81000200
  names1 : read64 m 0x81000048 = some 0x81000210
  names2 : read64 m 0x81000050 = some 0x81000220
  tag0 : read32 m 0x81000100 = some 5
  name0 : read64 m 0x81000108 = some 0x81000200
  function0 : read64 m 0x81000110 = some 0x80002ed4
  tag1 : read32 m 0x81000118 = some 5
  name1 : read64 m 0x81000120 = some 0x81000210
  function1 : read64 m 0x81000128 = some 0x80002f7c
  tag2 : read32 m 0x81000130 = some 5
  name2 : read64 m 0x81000138 = some 0x81000220
  function2 : read64 m 0x81000140 = some 0x80002df4
  printName : CString m 0x81000200 "print"
  printlnName : CString m 0x81000210 "println"
  assertName : CString m 0x81000220 "assert"

theorem HeapStoreFacts.frame {m : Mem} (h : HeapStoreFacts m) :
    FrameRepr m Nfixed phif phic 0x81000000 globalFrame := by
  refine ⟨h.count, ⟨8, h.capacity, by decide⟩,
    ⟨0x81000040, 0x81000100, h.names, h.values, ?_⟩, h.parent⟩
  intro i hi
  change i < 3 at hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨⟨0x81000200, h.names0, h.printName⟩,
      h.tag0, ⟨0x81000200, h.name0, h.printName⟩, h.function0⟩
  · exact ⟨⟨0x81000210, h.names1, h.printlnName⟩,
      h.tag1, ⟨0x81000210, h.name1, h.printlnName⟩, h.function1⟩
  · exact ⟨⟨0x81000220, h.names2, h.assertName⟩,
      h.tag2, ⟨0x81000220, h.name2, h.assertName⟩, h.function2⟩

theorem HeapStoreFacts.store {m : Mem} (h : HeapStoreFacts m) :
    StoreRepr m Nfixed arena phif phic initSt.store where
  frames := by
    intro fa hfa
    change fa < 1 at hfa
    have hz : fa = 0 := by omega
    subst fa
    exact h.frame
  closures := by
    intro ca hca
    change ca < 0 at hca
    omega
  φf_inj := by
    intro a b ha hb _
    change a < 1 at ha
    change b < 1 at hb
    omega
  φc_inj := by
    intro a b ha _ _
    change a < 0 at ha
    omega
  frames_arena := by
    intro fa hfa
    change fa < 1 at hfa
    have hz : fa = 0 := by omega
    subst fa
    change (0x81000000 ≤ 0x81000000 ∧ 0x81000000 + 32 ≤ 0x81001000) ∧
      0x81000000 % 8 = 0
    decide
  closures_arena := by
    intro ca hca
    change ca < 0 at hca
    omega

theorem HeapStoreFacts.transport {m m' : Mem} (h : HeapStoreFacts m)
    (ha : AgreeP StorePage m m') : HeapStoreFacts m' := by
  have h32 {a v : Nat} (hv : read32 m a = some v)
      (hlo : 0x81000000 ≤ a) (hhi : a + 4 ≤ 0x81001000) :
      read32 m' a = some v := by
    rw [← read32_agreeP ha (by intro k hk; unfold StorePage; omega)]
    exact hv
  have h64 {a v : Nat} (hv : read64 m a = some v)
      (hlo : 0x81000000 ≤ a) (hhi : a + 8 ≤ 0x81001000) :
      read64 m' a = some v := by
    rw [← read64_agreeP ha (by intro k hk; unfold StorePage; omega)]
    exact hv
  exact
    { count := h32 h.count (by decide) (by decide)
      capacity := h32 h.capacity (by decide) (by decide)
      names := h64 h.names (by decide) (by decide)
      values := h64 h.values (by decide) (by decide)
      parent := h64 h.parent (by decide) (by decide)
      names0 := h64 h.names0 (by decide) (by decide)
      names1 := h64 h.names1 (by decide) (by decide)
      names2 := h64 h.names2 (by decide) (by decide)
      tag0 := h32 h.tag0 (by decide) (by decide)
      name0 := h64 h.name0 (by decide) (by decide)
      function0 := h64 h.function0 (by decide) (by decide)
      tag1 := h32 h.tag1 (by decide) (by decide)
      name1 := h64 h.name1 (by decide) (by decide)
      function1 := h64 h.function1 (by decide) (by decide)
      tag2 := h32 h.tag2 (by decide) (by decide)
      name2 := h64 h.name2 (by decide) (by decide)
      function2 := h64 h.function2 (by decide) (by decide)
      printName := cstring_agreeP ha h.printName (by
        intro k hk
        change k ≤ 5 at hk
        unfold StorePage
        omega)
      printlnName := cstring_agreeP ha h.printlnName (by
        intro k hk
        change k ≤ 7 at hk
        unfold StorePage
        omega)
      assertName := cstring_agreeP ha h.assertName (by
        intro k hk
        change k ≤ 6 at hk
        unfold StorePage
        omega) }

theorem stringAgree : AgreeP (fun k => 0x81000200 ≤ k ∧ k < 0x81000240) mem heapMem :=
  fun _ hk => (unchanged_strings hk).symm

theorem heapStoreFacts : HeapStoreFacts heapMem where
  count := read32_heap reads.count (fun j hj => unchanged_store (by omega))
  capacity := read32_heap reads.capacity (fun j hj => unchanged_store (by omega))
  names := read64_heap reads.names (fun j hj => unchanged_store (by omega))
  values := by small_read
  parent := read64_heap reads.parent (fun j hj => unchanged_store (by omega))
  names0 := read64_heap reads.names0 (fun j hj => unchanged_store (by omega))
  names1 := read64_heap reads.names1 (fun j hj => unchanged_store (by omega))
  names2 := read64_heap reads.names2 (fun j hj => unchanged_store (by omega))
  tag0 := by small_read
  name0 := by small_read
  function0 := by small_read
  tag1 := by small_read
  name1 := by small_read
  function1 := by small_read
  tag2 := by small_read
  name2 := by small_read
  function2 := by small_read
  printName := cstring_agreeP stringAgree view.printName (by
    intro k hk; change k ≤ 5 at hk; omega)
  printlnName := cstring_agreeP stringAgree view.printlnName (by
    intro k hk; change k ≤ 7 at hk; omega)
  assertName := cstring_agreeP stringAgree view.assertName (by
    intro k hk; change k ≤ 6 at hk; omega)

theorem heapMemoryFacts : SnapshotMemoryFacts heapMem where
  mainRa := read64_heap memoryFacts.mainRa (fun j hj => unchanged_low (by omega))
  text := memoryFacts.text.transport (fun _ _ hhi => unchanged_low (Or.inl (by omega)))
  rodata := memoryFacts.rodata.transport (fun _ _ hhi => unchanged_low (Or.inl (by omega)))
  statics := by
    simpa (disch := decide) only [Code.ImageStaticsLoaded, Code.imgLldFmt,
      Code.imgDecPointStr, Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot,
      Code.imgDecPointPtr, Code.imgMbCurMax, Code.imgImpurePtr, unchanged_low]
      using memoryFacts.statics
  console := ConsoleStreamAt.of_agree (by
    intro k hk
    apply unchanged_low
    unfold ConsoleFoot consoleImpurePtrAddr consoleReent consoleStdout consoleBuf at hk
    omega) memoryFacts.console
  exitRuntime := memoryFacts.exitRuntime.transport (by
    intro k hk
    obtain ⟨r, hr, hlo, hhi⟩ := hk
    have hb : ∀ r ∈ exitRuntimeExtraRegions,
        (0x8001b520 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001b960) ∨
        (0x8001b968 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001b990) ∨
        (0x8001b998 ≤ r.1 ∧ r.1 + r.2 ≤ 0x8001c178) := by decide
    exact (unchanged_low (by have := hb r hr; omega)).symm)
  globals := read64_heap memoryFacts.globals (fun j hj => unchanged_low (by
    simp only [interpObject]; omega))
  depth := read32_heap memoryFacts.depth (fun j hj => unchanged_low (by
    simp only [interpObject]; omega))
  stackBytes := by
    intro k hlo hhi
    rw [unchanged_low (Or.inr (Or.inr (Or.inr (Or.inr (by
      change 0x87800000 ≤ k at hlo; omega)))))]
    exact memoryFacts.stackBytes k hlo hhi
  store := heapStoreFacts.store
  storeSurvives := by
    intro m' hag
    exact (heapStoreFacts.transport (fun k hk => hag k (storePage_outside_prefix hk))).store

theorem heapPhysicalFacts : InterpRunPhysicalFacts heapConfig 0x82000000 2 fixedInp
    Nfixed arena phif phic 0 := heapMemoryFacts.physicalFactsS0

theorem astAgree : AgreeP AstPage mem heapMem := by
  intro k hk
  exact (unchanged_ast (by unfold AstPage at hk; omega)).symm

theorem heapAstReads : AstReads heapMem where
  array0 := read64_heap astReads.array0 (fun j hj => unchanged_ast (by omega))
  array1 := read64_heap astReads.array1 (fun j hj => unchanged_ast (by omega))
  stmtTag := read32_heap astReads.stmtTag (fun j hj => unchanged_ast (by omega))
  stmtExpr := read64_heap astReads.stmtExpr (fun j hj => unchanged_ast (by omega))
  callTag := read32_heap astReads.callTag (fun j hj => unchanged_ast (by omega))
  callCallee := read64_heap astReads.callCallee (fun j hj => unchanged_ast (by omega))
  callArgs := read64_heap astReads.callArgs (fun j hj => unchanged_ast (by omega))
  callArgc := read32_heap astReads.callArgc (fun j hj => unchanged_ast (by omega))
  varTag := read32_heap astReads.varTag (fun j hj => unchanged_ast (by omega))
  varName := read64_heap astReads.varName (fun j hj => unchanged_ast (by omega))
  astName := cstring_agreeP astAgree astReads.astName (by
    intro k hk; change k ≤ 7 at hk; unfold AstPage; omega)

theorem heap_program_owned (p : Program) (hp : ProgramRepr heapMem 0x82000000 2 p) :
    ProgramReprWithin heapMem AstPage 0x82000000 2 p := by
  rw [heapAstReads.program_unique hp]
  exact heapAstReads.programWithin

theorem heap_present (k : Nat) (hlo : 0x80000000 ≤ k) (hhi : k < 0x88000000) :
    ∃ b, heapMem[k]? = some b :=
  memExtends_writeLog snapshotMem fullLog k (snapshotByte k) (snapshot_get k _ hlo hhi rfl)

theorem heapValueBytes : ∀ k, 0x81000100 ≤ k → k < 0x810001c0 →
    ∃ b : BitVec 8, heapMem[k]? = some b :=
  fun k hlo hhi => heap_present k (by omega) (by omega)

theorem heapArraysReady : RuntimeOwnership.StoreArraysReady heapMem phif initSt.store where
  namesAligned := by
    intro fa hf pn hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans heapStoreFacts.names)
    subst pn
    decide
  valuesAligned := by
    intro fa hf pv hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans heapStoreFacts.values)
    subst pv
    decide
  valueWords := by
    intro fa hf pv hp i hi
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans heapStoreFacts.values)
    subst pv
    change i < 3 at hi
    exact valueWordsTotal_of_interval heapValueBytes (by omega) (by omega)

/-- Allocator words the heap log leaves at their old values. -/
theorem heapTopPad : read64 heapMem topPadAddr = some 0 :=
  read64_heap (by old_read) (fun j hj => unchanged_low (by simp only [topPadAddr]; omega))

theorem heapMaxSbrked : read64 heapMem maxSbrkedAddr = some 0 :=
  read64_heap (by old_read) (fun j hj => unchanged_low (by simp only [maxSbrkedAddr]; omega))

theorem heapMallinfo : read64 heapMem mallinfoAddr = some 0 :=
  read64_heap (by old_read) (fun j hj => unchanged_low (by simp only [mallinfoAddr]; omega))

theorem heapBinblocks : read64 heapMem binblocksAddr = some 0 :=
  read64_heap (by old_read) (fun j hj => unchanged_low (by
    simp only [binblocksAddr, avAddr]; omega))

/-- The heap arena `_sbrk` grows through: `[_end, __heap_end)`. -/
def heapArena : Arena := ⟨heapStart, heapEnd⟩

theorem HeapStoreFacts.storeAt {m : Mem} (h : HeapStoreFacts m) {A : Arena}
    (hA : A.lo ≤ 0x81000000 ∧ 0x81000000 + 32 ≤ A.hi) :
    StoreRepr m Nfixed A phif phic initSt.store where
  frames := h.store.frames
  closures := h.store.closures
  φf_inj := h.store.φf_inj
  φc_inj := h.store.φc_inj
  frames_arena := by
    intro fa hfa
    change fa < 1 at hfa
    have hz : fa = 0 := by omega
    subst fa
    change (A.lo ≤ 0x81000000 ∧ 0x81000000 + 32 ≤ A.hi) ∧ 0x81000000 % 8 = 0
    exact ⟨hA, by decide⟩
  closures_arena := by
    intro ca hca
    change ca < 0 at hca
    omega

theorem heapArena_protected :
    ∀ a, ProtectedInitialByte a → ¬ (heapArena.lo ≤ a ∧ a < heapArena.hi) := by
  intro a ha hin
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  have hb : ∀ r ∈ exitProtectedRegions, r.1 + r.2 ≤ 0x8001c170 ∨ 0x87800000 ≤ r.1 := by
    decide
  have := hb r hr
  simp only [heapArena, heapStart, heapEnd] at hin
  omega

theorem heapStoreSurvivesAt : ∀ m' : Mem,
    (∀ k, ¬ interpRunWriteFootprint fixedInp k → heapMem[k]? = m'[k]?) →
    StoreRepr m' Nfixed heapArena phif phic initSt.store := by
  intro m' hag
  exact (heapStoreFacts.transport (fun k hk => hag k (storePage_outside_prefix hk))).storeAt
    (by decide)

/-- The physical boundary facts at the pinned heap arena. -/
theorem heapPhysicalFactsAt : InterpRunPhysicalFacts heapConfig 0x82000000 2 fixedInp
    Nfixed heapArena phif phic 0 :=
  { heapPhysicalFacts with
    arena_protected := heapArena_protected
    store := by
      show StoreRepr (physicalConfigS0 heapMem).σ.mem Nfixed heapArena phif phic initSt.store
      rw [physicalConfigS0_mem]
      exact heapStoreFacts.storeAt (by decide)
    store_survives := by
      show ∀ m' : Mem, (∀ k, ¬ interpRunWriteFootprint fixedInp k →
        (physicalConfigS0 heapMem).σ.mem[k]? = m'[k]?) →
        StoreRepr m' Nfixed heapArena phif phic initSt.store
      rw [physicalConfigS0_mem]
      exact heapStoreSurvivesAt
    arena_budget := by decide }

#print axioms heapBins
#print axioms heapTopPtr
#print axioms heapPhysicalFactsAt
#print axioms heapStoreFacts
#print axioms heapMemoryFacts
#print axioms heapPhysicalFacts
#print axioms heap_program_owned
#print axioms heapArraysReady

end Vsa.Sim.NativeNameAudit.Control
