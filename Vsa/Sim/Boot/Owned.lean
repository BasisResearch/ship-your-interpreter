import Vsa.Sim.Boot.Heap
import Vsa.Sim.LayoutInstance

/-!
# The initial ownership from a boot trace

At `interp_run`'s entry the store is `interp_init`'s global frame: an `Env`
at `env`, names and values arrays of capacity `cap` at `pn`/`pv`, three heap
copies of the native names (the binding keys) and three native values whose
names are `.rodata` literals. `BootOwn` records those addresses and the live
payload extents holding the represented AST; the allocation ledger inserts
the six runtime roles over the AST extents (`Ledger.insert`, as the control
does), and the shared bytes are the keys, the native names and the AST
extents (`BootOwn.sharedRanges`).

Every side condition is a named, decidable field of `OwnOk` (ranges and
extents) or `FrameOk` (reads through a byte view); the generated witnesses
discharge each with one `decide +kernel`.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Sim.RuntimeOwnership
open Vsa.Sim.LayoutInstance

/-- The global frame and the shared bytes at the entry. -/
structure BootOwn where
  env : Nat
  cap : Nat
  pn : Nat
  pv : Nat
  key0 : Nat
  key1 : Nat
  key2 : Nat
  name0 : Nat
  name1 : Nat
  name2 : Nat
  /-- Live payload extents holding the represented AST and its strings. -/
  ast : List Extent

/-- The heap arena `[_end, __heap_end)`. -/
def bootArena : Arena := ⟨DlHeap.heapStart, DlHeap.heapEnd⟩

namespace BootOwn

variable (B : BootOwn)

/-- The allocations: the frame's record and arrays, then the three key copies. -/
def alloc : Allocations :=
  let a0 : Allocations := fun _ => none
  let a1 := Allocations.insert a0 (.frame 0) B.env 32
  let a2 := Allocations.insert a1 (.names 0) B.pn (8 * B.cap)
  let a3 := Allocations.insert a2 (.values 0) B.pv (24 * B.cap)
  let a4 := Allocations.insert a3 (.binding 0 0) B.key0 6
  let a5 := Allocations.insert a4 (.binding 0 1) B.key1 8
  Allocations.insert a5 (.binding 0 2) B.key2 7

/-- The live extents, in insertion order reversed, over the AST extents. -/
def exts : List Extent :=
  (B.key2, 7) :: (B.key1, 8) :: (B.key0, 6) :: (B.pv, 24 * B.cap) :: (B.pn, 8 * B.cap) ::
    (B.env, 32) :: B.ast

/-- The shared (immutable) byte ranges: keys, native names, AST extents. -/
def sharedRanges : List Extent :=
  (B.key0, 6) :: (B.key1, 8) :: (B.key2, 7) :: (B.name0, 6) :: (B.name1, 8) :: (B.name2, 7) ::
    B.ast

def shared (k : Nat) : Prop := ∃ r ∈ B.sharedRanges, ExtentByte r k

/-- The three mutable extents. -/
def mutableExts : List Extent := [(B.env, 32), (B.pn, 8 * B.cap), (B.pv, 24 * B.cap)]

end BootOwn

instance (a b : Extent) : Decidable (ExtDisjoint a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

namespace BootOwn

/-- The role extents in insertion order. -/
def roleExts (B : BootOwn) : List Extent :=
  [(B.env, 32), (B.pn, 8 * B.cap), (B.pv, 24 * B.cap), (B.key0, 6), (B.key1, 8), (B.key2, 7)]

end BootOwn

/-- Range facts of a boot record, each decided per trace. -/
structure OwnOk (B : BootOwn) : Prop where
  /-- The AST extents are positive and in the arena. -/
  astArena : ∀ e ∈ B.ast, 0 < e.2 ∧ bootArena.lo ≤ e.1 ∧ e.1 + e.2 ≤ bootArena.hi
  astDisjoint : B.ast.Pairwise ExtDisjoint
  /-- The role extents are positive and in the arena. -/
  rolesArena : ∀ e ∈ B.roleExts, 0 < e.2 ∧ bootArena.lo ≤ e.1 ∧ e.1 + e.2 ≤ bootArena.hi
  /-- The `Env` record is 8-aligned. -/
  envAligned : B.env % 8 = 0
  /-- The live extents are pairwise disjoint. -/
  extsDisjoint : B.exts.Pairwise ExtDisjoint
  /-- Shared ranges: RAM below `2^32`, off the ELF's writable data and the stack. -/
  sharedRam : ∀ r ∈ B.sharedRanges,
    0x80000000 ≤ r.1 ∧ r.1 + r.2 ≤ 0x100000000 ∧
      (r.1 + r.2 ≤ 0x8001ad00 ∨ 0x8001c168 ≤ r.1) ∧
      (r.1 + r.2 ≤ 0x87800000 ∨ 0x88000000 ≤ r.1)
  /-- Shared ranges avoid the mutable extents. -/
  sharedImmutable : ∀ r ∈ B.sharedRanges, ∀ e ∈ B.mutableExts, ExtDisjoint r e
  /-- Shared ranges in the arena are live extents; the rest lie outside it. -/
  sharedLive : ∀ r ∈ B.sharedRanges,
    (r.1 + r.2 ≤ bootArena.lo ∨ bootArena.hi ≤ r.1) ∨ r ∈ B.exts

namespace OwnOk

variable {B : BootOwn} (h : OwnOk B)
include h

theorem ledger : Ledger bootArena B.exts B.alloc := by
  have hdis := h.extsDisjoint
  simp only [BootOwn.exts, List.pairwise_cons] at hdis
  obtain ⟨d2, d1, d0, dv, dn, de, -⟩ := hdis
  have hr : ∀ e ∈ B.roleExts, 0 < e.2 ∧ bootArena.contains e.1 e.2 :=
    fun e he => ⟨(h.rolesArena e he).1, (h.rolesArena e he).2.1, (h.rolesArena e he).2.2⟩
  have h0 : Ledger bootArena B.ast (fun _ => none) := by
    refine ⟨⟨fun e he => ?_, h.astDisjoint⟩, ?_, ?_⟩
    · exact ⟨(h.astArena e he).1, (h.astArena e he).2.1, (h.astArena e he).2.2⟩
    · intro r p n hr; simp [Allocated] at hr
    · intro r s p n q size hr; simp [Allocated] at hr
  have h1 := h0.insert (role := .frame 0) (hr (B.env, 32) (by simp [BootOwn.roleExts])).1
    (hr (B.env, 32) (by simp [BootOwn.roleExts])).2 de
  have h2 := h1.insert (role := .names 0) (hr (B.pn, 8 * B.cap) (by simp [BootOwn.roleExts])).1
    (hr (B.pn, 8 * B.cap) (by simp [BootOwn.roleExts])).2 dn
  have h3 := h2.insert (role := .values 0) (hr (B.pv, 24 * B.cap) (by simp [BootOwn.roleExts])).1
    (hr (B.pv, 24 * B.cap) (by simp [BootOwn.roleExts])).2 dv
  have h4 := h3.insert (role := .binding 0 0) (hr (B.key0, 6) (by simp [BootOwn.roleExts])).1
    (hr (B.key0, 6) (by simp [BootOwn.roleExts])).2 d0
  have h5 := h4.insert (role := .binding 0 1) (hr (B.key1, 8) (by simp [BootOwn.roleExts])).1
    (hr (B.key1, 8) (by simp [BootOwn.roleExts])).2 d1
  exact h5.insert (role := .binding 0 2) (hr (B.key2, 7) (by simp [BootOwn.roleExts])).1
    (hr (B.key2, 7) (by simp [BootOwn.roleExts])).2 d2

omit h in
/-- The mutable allocations are the frame's record and arrays. -/
theorem mutable_mem {role : Role} {p n : Nat} (hm : role.mutable)
    (ha : Allocated B.alloc role p n) : (p, n) ∈ B.mutableExts := by
  unfold Allocated BootOwn.alloc Allocations.insert at ha
  simp only [BootOwn.mutableExts, List.mem_cons, List.not_mem_nil, or_false]
  cases role with
  | frame fa => by_cases hf : fa = 0 <;> simp_all
  | names fa => by_cases hf : fa = 0 <;> simp_all
  | values fa => by_cases hf : fa = 0 <;> simp_all
  | binding fa i => exact hm.elim
  | closure ca => simp at ha

theorem immutable :
    Immutable B.alloc B.shared InitialReadableByte (InitialWriteByte stackSL) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro k ⟨r, hr, hk⟩
    have := h.sharedRam r hr
    unfold ExtentByte at hk
    exact ⟨by omega, by omega⟩
  · rintro k ⟨r, hr, hk⟩ hw
    have := h.sharedRam r hr
    unfold ExtentByte at hk
    unfold InitialWriteByte at hw
    have hlo : stackSL.lo = 0x87800000 := rfl
    have hhi : stackSL.hi = 0x88000000 := rfl
    rw [hlo, hhi] at hw
    omega
  · rintro role p n hm ha k ⟨r, hr, hk⟩ hin
    have hd := h.sharedImmutable r hr _ (mutable_mem hm ha)
    unfold ExtentByte at hk hin
    unfold ExtDisjoint at hd
    omega

theorem reserved : Reserved bootArena B.exts B.shared := by
  refine ⟨?_⟩
  rintro k ⟨r, hr, hk⟩ hlo hhi
  rcases h.sharedLive r hr with hout | hin
  · unfold ExtentByte at hk; omega
  · exact ⟨r, hin, hk⟩

end OwnOk

/-! ## The global frame's reads -/

theorem readLEv_lt' {v : Nat → Option (BitVec 8)} :
    ∀ {n a x}, readLEv v a n = some x → x < 256 ^ n := by
  intro n
  induction n with
  | zero => intro a x h; simp [readLEv] at h; subst h; decide
  | succ n ih =>
    intro a x h
    simp only [readLEv] at h
    cases hb : v a with
    | none => rw [hb] at h; cases h
    | some b =>
      cases hr : readLEv v (a + 1) n with
      | none => rw [hb, hr] at h; cases h
      | some r =>
        rw [hb, hr] at h
        have hx : b.toNat + 256 * r = x := by simpa using h
        subst hx
        have := ih hr
        have hb' := b.isLt
        rw [Nat.pow_succ]
        omega

theorem readLEv_lt {v : Nat → Option (BitVec 8)} {a x : Nat} (h : readLEv v a 8 = some x) :
    x < 2 ^ 64 := by
  have := readLEv_lt' h; simpa using this

/-- The global frame's reads through a view, each decided per trace. -/
structure FrameOk (v : Nat → Option (BitVec 8)) (B : BootOwn) : Prop where
  cap : readLEv v (B.env + 4) 4 = some B.cap
  names : readLEv v (B.env + 8) 8 = some B.pn
  values : readLEv v (B.env + 16) 8 = some B.pv
  bound : 3 ≤ B.cap
  aligned : B.pn % 8 = 0 ∧ B.pv % 8 = 0
  key0 : readLEv v (B.pn + 8 * 0) 8 = some B.key0
  key1 : readLEv v (B.pn + 8 * 1) 8 = some B.key1
  key2 : readLEv v (B.pn + 8 * 2) 8 = some B.key2
  keyStr0 : cstrIs v B.key0 "print" = true
  keyStr1 : cstrIs v B.key1 "println" = true
  keyStr2 : cstrIs v B.key2 "assert" = true
  name0 : readLEv v (B.pv + 24 * 0 + 8) 8 = some B.name0
  name1 : readLEv v (B.pv + 24 * 1 + 8) 8 = some B.name1
  name2 : readLEv v (B.pv + 24 * 2 + 8) 8 = some B.name2
  nameStr0 : cstrIs v B.name0 "print" = true
  nameStr1 : cstrIs v B.name1 "println" = true
  nameStr2 : cstrIs v B.name2 "assert" = true
  /-- The three value slots' words are present. -/
  words : ((List.range 3).all fun i => (readLEv v (B.pv + 24 * i) 8).isSome &&
    (readLEv v (B.pv + 24 * i + 8) 8).isSome && (readLEv v (B.pv + 24 * i + 16) 8).isSome) = true

namespace FrameOk

variable {m : Mem} {v : Nat → Option (BitVec 8)} {B : BootOwn} (hv : PartialView m v)
  (h : FrameOk v B) {φf : Addr → Nat} (hφ : φf 0 = B.env)
include hv h hφ

omit h hφ in
theorem sharedString {q len : Nat} {s : String} (hs : s.length = len) (hc : cstrIs v q s = true)
    (hr : (q, len + 1) ∈ B.sharedRanges) : SharedCString m B.shared q s :=
  ⟨cstrIs_sound hv hc, fun k hk => ⟨_, hr, by unfold ExtentByte; omega⟩⟩

theorem frameOwned : FrameOwned m φf B.alloc B.shared 0 initFrame := by
  have hread : ∀ {a n x}, readLEv v a n = some x → Vsa.MemRepr.readLE m a n = some x :=
    fun h' => hv.readLE h'
  refine ⟨?_, ⟨⟨B.cap, B.pn, B.pv⟩, ?_⟩, ?_⟩
  · rw [hφ]; simp [Allocated, BootOwn.alloc, Allocations.insert]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hφ]; exact hread h.cap
    · rw [hφ]; exact hread h.names
    · rw [hφ]; exact hread h.values
    · exact h.bound
    · exact Or.inr ⟨show 0 < B.cap by have := h.bound; omega,
        by simp [Allocated, BootOwn.alloc, Allocations.insert]⟩
    · exact Or.inr ⟨show 0 < B.cap by have := h.bound; omega,
        by simp [Allocated, BootOwn.alloc, Allocations.insert]⟩
    · intro i hi
      change i < 3 at hi
      match i, hi with
      | 0, _ =>
        show ∃ q, read64 m (B.pn + 8 * 0) = some q ∧
          CopiedCString m B.alloc B.shared (.binding 0 0) q "print"
        exact ⟨B.key0, hread h.key0,
          ⟨by simp [Allocated, BootOwn.alloc, Allocations.insert] <;> decide,
            sharedString hv (len := 5) rfl h.keyStr0 (by simp [BootOwn.sharedRanges])⟩⟩
      | 1, _ =>
        show ∃ q, read64 m (B.pn + 8 * 1) = some q ∧
          CopiedCString m B.alloc B.shared (.binding 0 1) q "println"
        exact ⟨B.key1, hread h.key1,
          ⟨by simp [Allocated, BootOwn.alloc, Allocations.insert] <;> decide,
            sharedString hv (len := 7) rfl h.keyStr1 (by simp [BootOwn.sharedRanges])⟩⟩
      | 2, _ =>
        show ∃ q, read64 m (B.pn + 8 * 2) = some q ∧
          CopiedCString m B.alloc B.shared (.binding 0 2) q "assert"
        exact ⟨B.key2, hread h.key2,
          ⟨by simp [Allocated, BootOwn.alloc, Allocations.insert] <;> decide,
            sharedString hv (len := 6) rfl h.keyStr2 (by simp [BootOwn.sharedRanges])⟩⟩
  · intro pv hpv i hi
    rw [hφ] at hpv
    have hpe : pv = B.pv := Option.some.inj (hpv.symm.trans (hread h.values))
    subst hpe
    change i < 3 at hi
    match i, hi with
    | 0, _ =>
      show ∃ q, read64 m (B.pv + 24 * 0 + 8) = some q ∧ SharedCString m B.shared q "print"
      exact ⟨B.name0, hread h.name0,
        sharedString hv (len := 5) rfl h.nameStr0 (by simp [BootOwn.sharedRanges])⟩
    | 1, _ =>
      show ∃ q, read64 m (B.pv + 24 * 1 + 8) = some q ∧ SharedCString m B.shared q "println"
      exact ⟨B.name1, hread h.name1,
        sharedString hv (len := 7) rfl h.nameStr1 (by simp [BootOwn.sharedRanges])⟩
    | 2, _ =>
      show ∃ q, read64 m (B.pv + 24 * 2 + 8) = some q ∧ SharedCString m B.shared q "assert"
      exact ⟨B.name2, hread h.name2,
        sharedString hv (len := 6) rfl h.nameStr2 (by simp [BootOwn.sharedRanges])⟩

theorem storeOwned (φc : Addr → Nat) :
    StoreOwned m φf φc B.alloc B.shared initSt.store where
  frames := by
    intro fa hf
    have : fa = 0 := by change fa < 1 at hf; omega
    subst this
    exact frameOwned hv h hφ
  closures := by intro ca hc; change ca < 0 at hc; omega
  valueClosures := ⟨by
    intro fa hf i hi
    have : fa = 0 := by change fa < 1 at hf; omega
    subst this
    change i < 3 at hi
    match i, hi with
    | 0, _ => trivial
    | 1, _ => trivial
    | 2, _ => trivial⟩
  capturedEnvs := by intro ca hc; change ca < 0 at hc; omega
  closureAsts := by intro ca hc; change ca < 0 at hc; omega

theorem arraysReady : StoreArraysReady m φf initSt.store where
  namesAligned := by
    intro fa hf pn hpn
    have : fa = 0 := by change fa < 1 at hf; omega
    subst this
    rw [hφ] at hpn
    rw [Option.some.inj (hpn.symm.trans (hv.readLE h.names))]
    exact h.aligned.1
  valuesAligned := by
    intro fa hf pv hpv
    have : fa = 0 := by change fa < 1 at hf; omega
    subst this
    rw [hφ] at hpv
    rw [Option.some.inj (hpv.symm.trans (hv.readLE h.values))]
    exact h.aligned.2
  valueWords := by
    intro fa hf pv hpv i hi
    have : fa = 0 := by change fa < 1 at hf; omega
    subst this
    rw [hφ] at hpv
    have hpe : pv = B.pv := Option.some.inj (hpv.symm.trans (hv.readLE h.values))
    subst hpe
    change i < 3 at hi
    have hw := List.all_eq_true.mp h.words i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hw
    obtain ⟨⟨⟨w0, h0⟩, ⟨w1, h1⟩⟩, ⟨w2, h2⟩⟩ := hw
    refine ⟨BitVec.ofNat 64 w0, BitVec.ofNat 64 w1, BitVec.ofNat 64 w2, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLEv_lt h0)]; exact hv.readLE h0
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLEv_lt h1)]; exact hv.readLE h1
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLEv_lt h2)]; exact hv.readLE h2

end FrameOk

/-! ## The initial ownership -/

/-- The frame arrays are the only realloc extents. -/
theorem BootOwn.realloc_mem (B : BootOwn) {e : Extent} (h : ReallocExtent B.alloc e) :
    e ∈ [(B.pn, 8 * B.cap), (B.pv, 24 * B.cap)] := by
  obtain ⟨fa, h | h⟩ := h <;>
  · unfold Allocated BootOwn.alloc Allocations.insert at h
    by_cases hf : fa = 0 <;> simp_all

/-- The ownership data of a boot record. -/
def BootOwn.data (B : BootOwn) : InitialOwnershipData := ⟨B.exts, B.alloc, B.shared⟩

/-- **The initial ownership at a boot trace's entry**, from the decided range
and read facts, the heap check, and the two program-dependent facts: the
represented program's reads lie in the shared bytes, and its terminating
derivations fit the heap. -/
theorem initialOwned_of {m : Mem} {v : Nat → Option (BitVec 8)} {B : BootOwn}
    (hv : PartialView m v) (ho : OwnOk B) (hf : FrameOk v B)
    {φf φc : Addr → Nat} (hφ : φf 0 = B.env) {stmts count top brkv : Nat}
    {chunks : List DlHeap.Chunk} {L : List (List Nat)}
    (hh : heapCheck v B.exts [(B.pn, 8 * B.cap), (B.pv, 24 * B.cap)] top brkv chunks L = true)
    (hprog : ∀ p : Program, ProgramRepr m stmts count p →
      ProgramReprWithin m B.shared stmts count p)
    (hcap : ∀ p : Program, ProgramRepr m stmts count p →
      ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n →
        2 * n + DlHeap.extendSlack ≤ DlHeap.heapEnd - top) :
    InitialOwned m bootArena stackSL φf φc stmts count B.data where
  heapLower := Nat.le_refl _
  heapUpper := Nat.le_refl _
  heap := ⟨ho.ledger, ho.immutable, ho.reserved, hf.storeOwned hv hφ φc⟩
  arrays := hf.arraysReady hv hφ
  program := hprog
  allocator := ⟨top, brkv, chunks, binsOf L,
    heapAt_of_check hv hh (fun e _ hr => B.realloc_mem hr), hcap⟩
  arenaHeap := ⟨rfl, rfl⟩

/-! ## The boundary heap facts -/

/-- The global frame's three blocks, from a boot record and the chunk walk. -/
def BootOwn.frame (B : BootOwn) (sblk nblk vblk : Nat × Nat) : BootFrame :=
  ⟨B.cap, B.pn, B.pv, sblk, nblk, vblk⟩

/-- The decided facts behind `BootHeapFacts` (all but the shared bytes' geometry). -/
structure HeapFactsOk (v : Nat → Option (BitVec 8)) (B : BootOwn) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (sblk nblk vblk : Nat × Nat) : Prop where
  top_room : top + 16 ≤ brkv
  brk_page : brkv % 4096 = 0
  binblocks : ∃ bb, readLEv v DlHeap.binblocksAddr 8 = some bb ∧ bb < 2 ^ 32
  stderr : readLEv v impureStderrAddr 8 = some exitStderr
  record : sblk.1 ≤ B.env ∧ B.env + 32 ≤ sblk.1 + sblk.2
  arrays : nblk.1 = B.pn ∧ 8 * B.cap ≤ nblk.2 ∧ vblk.1 = B.pv ∧ 24 * B.cap ≤ vblk.2
  live : ∀ b ∈ [sblk, nblk, vblk], ∃ c ∈ chunks, c.inuse = true ∧ b = (c.addr + 16, c.size - 8)
  nodup : [sblk, nblk, vblk].Nodup
  unshared : ∀ b ∈ [sblk, nblk, vblk], ∀ r ∈ B.sharedRanges, ExtDisjoint b r
  cap_canon : B.cap = 8

theorem bootHeapFacts_of {m : Mem} {v : Nat → Option (BitVec 8)} {B : BootOwn}
    (hv : PartialView m v) (hf : FrameOk v B) {top brkv : Nat} {chunks : List DlHeap.Chunk}
    {sblk nblk vblk : Nat × Nat} (h : HeapFactsOk v B top brkv chunks sblk nblk vblk)
    (hgeom : SharedGeom B.shared stackSL) :
    BootHeapFacts m B.shared B.env top brkv chunks (B.frame sblk nblk vblk) where
  top_room := h.top_room
  brk_page := h.brk_page
  binblocks := by
    intro bb hbb
    obtain ⟨bb', hr, hlt⟩ := h.binblocks
    rw [Option.some.inj (hbb.symm.trans (hv.readLE hr))]
    exact hlt
  frame := {
    cap := hv.readLE hf.cap
    names := hv.readLE hf.names
    vals := hv.readLE hf.values
    sblk := h.record
    arrays := fun _ => h.arrays
    live := by
      intro b hb
      have hb' : b ∈ [sblk, nblk, vblk] := by
        unfold BootOwn.frame BootFrame.blocks at hb
        simpa [show B.cap ≠ 0 by have := hf.bound; omega] using hb
      exact h.live b hb'
    nodup := by
      unfold BootOwn.frame BootFrame.blocks
      simpa [show B.cap ≠ 0 by have := hf.bound; omega] using h.nodup
    unshared := by
      intro b hb k hlo hhi ⟨r, hr, hk⟩
      have hb' : b ∈ [sblk, nblk, vblk] := by
        unfold BootOwn.frame BootFrame.blocks at hb
        simpa [show B.cap ≠ 0 by have := hf.bound; omega] using hb
      have hd := h.unshared b hb' r hr
      unfold ExtDisjoint at hd
      unfold ExtentByte at hk
      omega
    cap_canon := h.cap_canon }
  stderr := hv.readLE h.stderr
  shared_geom := hgeom

end Vsa.Sim.Boot
