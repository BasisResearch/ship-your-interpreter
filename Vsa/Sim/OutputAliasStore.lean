import Vsa.Sim.LayoutInstance
import Vsa.Sim.ReprSurvival

/-! Concrete initial store for the output-alias boundary witness.
Only finite read and ASCII byte facts are inputs. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.OutputAliasLoaded

def Nfixed : NativeAddrs := ⟨0x80002ed4, 0x80002f7c, 0x80002df4⟩
def arena : Arena := ⟨0x81000000, 0x81001000⟩
def phif (n : Addr) : Nat := 0x81000000 + 32 * n
def phic (n : Addr) : Nat := 0x81000400 + 16 * n
def fixedInp : BitVec 64 := 0x87fffe10#64

def StorePage (a : Nat) : Prop := 0x81000000 ≤ a ∧ a < 0x81001000

/-- Finite byte list followed by one NUL byte. No string representation is
assumed; the constructors below derive it from these reads. -/
def NameBytes (m : Mem) : Nat → List (BitVec 8) → Prop
  | a, [] => m[a]? = some 0#8
  | a, b :: bs => m[a]? = some b ∧ NameBytes m (a + 1) bs

private theorem cstr_of_nameBytes {m : Mem} {a : Nat} {bs : List (BitVec 8)}
    (h : NameBytes m a bs)
    (hascii : ∀ b ∈ bs, b ≠ 0#8 ∧ b.toNat < 128) :
    CStr m a (bs.map (fun b => Char.ofNat b.toNat)) := by
  induction bs generalizing a with
  | nil => exact CStr.nil h
  | cons b bs ih =>
    have hb := hascii b (List.mem_cons_self ..)
    exact CStr.cons h.1 hb.1 hb.2
      (ih h.2 (fun b hb => hascii b (List.mem_cons_of_mem _ hb)))

structure StoreReadFacts (m : Mem) : Prop where
  count : read32 m 0x81000000 = some 3
  capacity : read32 m 0x81000004 = some 8
  names : read64 m 0x81000008 = some 0x81000040
  values : read64 m 0x81000010 = some 0x81000080
  parent : read64 m 0x81000018 = some 0
  names0 : read64 m 0x81000040 = some 0x81000200
  names1 : read64 m 0x81000048 = some 0x81000210
  names2 : read64 m 0x81000050 = some 0x81000220
  tag0 : read32 m 0x81000080 = some 5
  name0 : read64 m 0x81000088 = some 0x81000200
  function0 : read64 m 0x81000090 = some 0x80002ed4
  tag1 : read32 m 0x81000098 = some 5
  name1 : read64 m 0x810000a0 = some 0x81000210
  function1 : read64 m 0x810000a8 = some 0x80002f7c
  tag2 : read32 m 0x810000b0 = some 5
  name2 : read64 m 0x810000b8 = some 0x81000220
  function2 : read64 m 0x810000c0 = some 0x80002df4

structure StoreFacts (m : Mem) : Prop extends StoreReadFacts m where
  printBytes : NameBytes m 0x81000200 [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8]
  printlnBytes : NameBytes m 0x81000210
    [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8]
  assertBytes : NameBytes m 0x81000220 [0x61#8, 0x73#8, 0x73#8, 0x65#8, 0x72#8, 0x74#8]

/-- Derived read view used for CString transport, never a backend premise. -/
structure StoreView (m : Mem) : Prop extends StoreReadFacts m where
  printName : CString m 0x81000200 "print"
  printlnName : CString m 0x81000210 "println"
  assertName : CString m 0x81000220 "assert"

theorem StoreFacts.view {m : Mem} (h : StoreFacts m) : StoreView m where
  toStoreReadFacts := h.toStoreReadFacts
  printName := ⟨_, cstr_of_nameBytes h.printBytes (by decide), by decide⟩
  printlnName := ⟨_, cstr_of_nameBytes h.printlnBytes (by decide), by decide⟩
  assertName := ⟨_, cstr_of_nameBytes h.assertBytes (by decide), by decide⟩

def globalFrame : Vsa.While.Frame :=
  ⟨none, [("print", .native .print), ("println", .native .println),
    ("assert", .native .assert)]⟩

theorem StoreView.frame {m : Mem} (h : StoreView m) :
    FrameRepr m Nfixed phif phic 0x81000000 globalFrame := by
  refine ⟨h.count, ⟨8, h.capacity, by decide⟩,
    ⟨0x81000040, 0x81000080, h.names, h.values, ?_⟩, h.parent⟩
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

theorem StoreView.store {m : Mem} (h : StoreView m) :
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

theorem StoreFacts.store {m : Mem} (h : StoreFacts m) :
    StoreRepr m Nfixed arena phif phic initSt.store := h.view.store

theorem StoreReadFacts.transport {m m' : Mem} (h : StoreReadFacts m)
    (ha : AgreeP StorePage m m') : StoreReadFacts m' := by
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
      function2 := h64 h.function2 (by decide) (by decide) }

theorem StoreView.transport {m m' : Mem} (h : StoreView m)
    (ha : AgreeP StorePage m m') : StoreView m' where
  toStoreReadFacts := h.toStoreReadFacts.transport ha
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
    omega)

theorem storePage_outside_prefix {a : Nat} (ha : StorePage a) :
    ¬ LayoutInstance.interpRunWriteFootprint fixedInp a := by
  unfold StorePage at ha
  change ¬ ((0x87800000 ≤ a ∧ a < 0x88000000) ∨
    (0x87fffe10 + 16 ≤ a ∧ a < 0x87fffe10 + 128))
  omega

/-- The complete universal prefix-survival field. It is reconstructed from
the finite initial reads and actual CString transport, for every agreeing
memory. The AST's separate console-buffer alias plays no role in these reads. -/
theorem StoreFacts.store_survives {m : Mem} (h : StoreFacts m) :
    ∀ m' : Mem,
      (∀ k, ¬ LayoutInstance.interpRunWriteFootprint fixedInp k → m[k]? = m'[k]?) →
      StoreRepr m' Nfixed arena phif phic initSt.store := by
  intro m' hagree
  have hpage : AgreeP StorePage m m' :=
    fun k hk => hagree k (storePage_outside_prefix hk)
  exact (h.view.transport hpage).store

#print axioms StoreFacts.store
#print axioms StoreFacts.store_survives

end Vsa.Sim.OutputAliasLoaded
