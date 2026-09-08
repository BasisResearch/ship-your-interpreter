import Vsa.Sim.IHClauseGenericAlloc
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.AllocClosure
import Vsa.Sim.EnvDefineClose

/-!
# `AllocOff` — owned bytes off the allocator's footprint, once

Every allocating call site of the interpreter must show the same thing before it
may use the allocator's memory frame: the bytes the caller owns (its store's
live extents) and the bytes it shares (AST nodes, string payloads) are OUTSIDE
the three windows an allocator call may touch — the stack region, the
allocator-private set `MallocContract.privFoot`, and the fresh blocks the call
returns.  Before this module that derivation was written by hand at each site
(`envNewPushedRepr`, the `env_define` append and grow lanes), each time from
`Ledger.live`, `HeapArena`, `privFoot_disjoint`, `Reserved.outsideFresh` and
`Reserved.outsidePrivate`.

`OwnedOff` is that conclusion as a named-field structure and
`HeapOwned.ownedOff` is its ONE proof; `HeapOwned.transport_off` and
`.repr_off` consume it for ownership and representation survival.  The ledger
also moves: `HeapOwned.fresh` enters an unassigned live block, `HeapOwned.free`
releases one, and `HeapOwned.pushClosure` (`PROOF_CLOSURE_PLAN.md`, task 2)
completes the closure build at the post-build memory.

The allocator RUNS and the run-global record that carries them are one level up
(`Vsa/Sim/AllocLedger.lean`), so this module stays below every helper's supply
module and can be consumed by all of them.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership

/-! ## 1. Owned bytes off the allocator's footprint -/

/-- Bytes the allocator's call may not touch: outside the stack region, the
private footprint, and the listed fresh blocks. -/
def AllocOff (SL : StackLayout) (priv : Nat → Prop) (fresh : List Extent) (k : Nat) : Prop :=
  ¬ (SL.lo ≤ k ∧ k < SL.hi) ∧ ¬ priv k ∧ ∀ e ∈ fresh, ¬ ExtentByte e k

/-- Every owned extent and every shared byte is off the allocator's footprint. -/
structure OwnedOff (SL : StackLayout) (priv : Nat → Prop) (fresh : List Extent)
    (alloc : Allocations) (shared : Nat → Prop) : Prop where
  alloc : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k →
    AllocOff SL priv fresh k
  shared : ∀ k, shared k → AllocOff SL priv fresh k

/-- The single-block case, as the three windows spelled out. -/
theorem AllocOff.single {SL : StackLayout} {priv : Nat → Prop} {p n k : Nat}
    (h : AllocOff SL priv [(p, n)] k) :
    ¬ (SL.lo ≤ k ∧ k < SL.hi) ∧ ¬ priv k ∧ ¬ (p ≤ k ∧ k < p + n) :=
  ⟨h.1, h.2.1, h.2.2 (p, n) List.mem_cons_self⟩

/-- One fresh block is a one-element fresh list. -/
theorem freshExtents_single {A : Arena} {exts : List Extent} {p n : Nat}
    (hA : A.contains p n) (hf : ∀ e ∈ exts, ExtDisjoint (p, n) e) :
    FreshExtents A exts [(p, n)] := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hA, hf⟩
  · exact absurd he List.not_mem_nil

theorem AllocOff.mono {SL : StackLayout} {priv : Nat → Prop} {fresh fresh' : List Extent}
    (hsub : ∀ e ∈ fresh', e ∈ fresh) {k : Nat} (h : AllocOff SL priv fresh k) :
    AllocOff SL priv fresh' k :=
  ⟨h.1, h.2.1, fun e he => h.2.2 e (hsub e he)⟩

theorem OwnedOff.mono {SL : StackLayout} {priv : Nat → Prop} {fresh fresh' : List Extent}
    {alloc : Allocations} {shared : Nat → Prop}
    (hsub : ∀ e ∈ fresh', e ∈ fresh) (h : OwnedOff SL priv fresh alloc shared) :
    OwnedOff SL priv fresh' alloc shared :=
  ⟨fun role p n ha k hk => (h.alloc role p n ha k hk).mono hsub,
    fun k hk => (h.shared k hk).mono hsub⟩

namespace RuntimeOwnership

variable {A : Arena} {SL : StackLayout} {exts : List Extent} {m : Mem}
  {phiF phiC : Addr → Nat} {alloc : Allocations}
  {shared readable writes : Nat → Prop} {s : Store}

/-- **ONE proof that owned bytes are off the allocator's footprint**: the stack
region is in the caller's write footprint, live extents are off the private
bytes, and fresh blocks are disjoint from every live extent. -/
theorem HeapOwned.ownedOff (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hwrites : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    {priv : Nat → Prop} (hpriv : ∀ e ∈ exts, ∀ k < e.2, ¬ priv (e.1 + k))
    (priv_arena : ∀ a, priv a → A.lo ≤ a ∧ a < A.hi)
    (arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    {fresh : List Extent} (hfresh : FreshExtents A exts fresh) :
    OwnedOff SL priv fresh alloc shared := by
  constructor
  · intro role q n hq k hk
    have hmem := hown.ledger.live role q n hq
    obtain ⟨_, hqA⟩ := hown.ledger.arena.1 (q, n) hmem
    change A.lo ≤ q ∧ q + n ≤ A.hi at hqA
    change q ≤ k ∧ k < q + n at hk
    refine ⟨?_, ?_, ?_⟩
    · intro hst
      rcases arena_stack with h | h <;> omega
    · intro hp
      have := hpriv (q, n) hmem (k - q) (by change k - q < n; omega)
      change ¬ priv (q + (k - q)) at this
      rw [show q + (k - q) = k by omega] at this
      exact this hp
    · intro e he hek
      have hd := (hfresh e he).2 (q, n) hmem
      change e.1 + e.2 ≤ q ∨ q + n ≤ e.1 at hd
      change e.1 ≤ k ∧ k < e.1 + e.2 at hek
      omega
  · intro k hk
    refine ⟨fun hst => hown.immutable.outsideWrites k hk (hwrites k hst.1 hst.2), ?_, ?_⟩
    · exact hown.reserved.outsidePrivate hown.immutable hpriv
        (fun a hp hna => absurd (priv_arena a hp) hna) k hk
    · intro e he
      exact hown.reserved.outsideFresh (hfresh e he).1 (hfresh e he).2 k hk

/-- Ownership survives the allocator's memory frame. -/
theorem HeapOwned.transport_off {m' : Mem} {priv : Nat → Prop} {fresh : List Extent}
    (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hoff : OwnedOff SL priv fresh alloc shared)
    (hag : AgreeP (AllocOff SL priv fresh) m m') :
    HeapOwned A exts m' phiF phiC alloc shared readable writes s :=
  hown.transport hag hoff.alloc hoff.shared

/-- The represented store survives the allocator's memory frame. -/
theorem HeapOwned.repr_off {m' : Mem} {N : NativeAddrs} {priv : Nat → Prop}
    {fresh : List Extent}
    (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hr : StoreRepr m N A phiF phiC s)
    (hoff : OwnedOff SL priv fresh alloc shared)
    (hag : AgreeP (AllocOff SL priv fresh) m m') :
    StoreRepr m' N A phiF phiC s :=
  hown.store.repr_transport hr hag hoff.alloc hoff.shared

/-- A fresh live block enters the ledger unassigned: no role, no memory change. -/
theorem HeapOwned.fresh (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    {p n : Nat} (hpos : 0 < n) (hA : A.contains p n)
    (hf : ∀ e ∈ exts, ExtDisjoint (p, n) e) :
    HeapOwned A ((p, n) :: exts) m phiF phiC alloc shared readable writes s := by
  refine ⟨⟨⟨?_, List.pairwise_cons.mpr ⟨hf, hown.ledger.arena.2⟩⟩, ?_, hown.ledger.separated⟩,
    hown.immutable, hown.reserved.mono (fun e he => List.mem_cons_of_mem _ he), hown.store⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hpos, hA⟩
    · exact hown.ledger.arena.1 e he
  · intro role q size hq
    exact List.mem_cons_of_mem _ (hown.ledger.live role q size hq)

/-- Distinct live extents of one arena ledger are disjoint. -/
theorem HeapArena.disjoint_of_ne {A : Arena} :
    ∀ {exts : List Extent}, HeapArena A exts →
      ∀ a ∈ exts, ∀ b ∈ exts, a ≠ b → ExtDisjoint a b
  | [], _, a, ha, _, _, _ => nomatch ha
  | x :: xs, h, a, ha, b, hb, hne => by
    have hp := List.pairwise_cons.mp h.2
    have htail : HeapArena A xs := ⟨fun e he => h.1 e (List.mem_cons_of_mem _ he), hp.2⟩
    rcases List.mem_cons.mp ha with ha | ha' <;> rcases List.mem_cons.mp hb with hb | hb'
    · exact absurd (ha.trans hb.symm) hne
    · subst ha; exact hp.1 b hb'
    · subst hb; exact extDisjoint_symm (hp.1 a ha')
    · exact HeapArena.disjoint_of_ne htail a ha' b hb' hne

/-- Positive disjoint extents never repeat. -/
theorem HeapArena.nodup {A : Arena} {exts : List Extent} (h : HeapArena A exts) :
    exts.Nodup := by
  apply List.Pairwise.imp_of_mem (p := h.2)
  intro a b ha _ hd he
  subst b
  have hp := (h.1 a ha).1
  change a.1 + a.2 ≤ a.1 ∨ a.1 + a.2 ≤ a.1 at hd
  omega

/-- A released live block is fresh against the surviving ledger. -/
theorem HeapArena.freshErase {A : Arena} {exts : List Extent} (h : HeapArena A exts)
    {q n : Nat} (hq : (q, n) ∈ exts) : FreshExtents A (exts.erase (q, n)) [(q, n)] := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · refine ⟨(h.1 _ hq).2, ?_⟩
    intro e' he'
    have hne : e' ≠ (q, n) := ((List.Nodup.mem_erase_iff (HeapArena.nodup h)).mp he').1
    exact extDisjoint_symm (HeapArena.disjoint_of_ne h e' (List.mem_of_mem_erase he') _ hq hne)
  · exact absurd he List.not_mem_nil

/-- **Releasing an unassigned live block** keeps every owned and shared byte:
the ledger loses the block, the roles and the store are unchanged. -/
theorem HeapOwned.free (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    {q n : Nat}
    (hun : ∀ role, ¬ Allocated alloc role q n)
    (hsh : ∀ k, shared k → ¬ ExtentByte (q, n) k) :
    HeapOwned A (exts.erase (q, n)) m phiF phiC alloc shared readable writes s := by
  refine ⟨⟨⟨?_, List.Pairwise.erase _ hown.ledger.arena.2⟩, ?_, hown.ledger.separated⟩,
    hown.immutable, ⟨?_⟩, hown.store⟩
  · intro e he
    exact hown.ledger.arena.1 e (List.mem_of_mem_erase he)
  · intro role p size hp
    have hne : (p, size) ≠ (q, n) := by
      intro heq
      have hp' : alloc role = some (q, n) := heq ▸ hp
      exact hun role hp'
    exact (List.mem_erase_of_ne hne).mpr (hown.ledger.live role p size hp)
  · intro k hk hlo hhi
    obtain ⟨e, he, heb⟩ := hown.reserved.live k hk hlo hhi
    have hne : e ≠ (q, n) := by
      intro heq
      subst heq
      exact hsh k hk heb
    exact ⟨e, (List.mem_erase_of_ne hne).mpr he, heb⟩

end RuntimeOwnership

/-- **The entry-side allocator separation facts**, as one named-field record: the
four conclusions every allocating lane derives before its first call — shared
bytes avoid the allocator-private set and the stack region, and every live
extent lies in the arena off the private set.  `OwnedOff` is the same content
indexed by a fresh list; this is its entry-side (`fresh = []`) presentation, in
the shape the landed lanes consume. -/
structure EntryOff (A : Arena) (SL : StackLayout) (exts : List Extent)
    (priv : Nat → Prop) (alloc : Allocations) (shared : Nat → Prop) : Prop where
  shared_priv : ∀ k, shared k → ¬ priv k
  shared_stack : ∀ k, shared k → ¬ (SL.lo ≤ k ∧ k < SL.hi)
  ext_arena : ∀ e ∈ exts, ∀ k, ExtentByte e k → A.lo ≤ k ∧ k < A.hi
  ext_priv : ∀ e ∈ exts, ∀ k, ExtentByte e k → ¬ priv k

namespace RuntimeOwnership

/-- **ONE proof of the entry-side separation facts** from the ownership ledger,
the caller's stack write footprint, and the allocator's footprint discipline. -/
theorem HeapOwned.entryOff {A : Arena} {SL : StackLayout} {exts : List Extent} {m : Mem}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes priv : Nat → Prop} {s : Store}
    (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hwrites : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    (hpriv : ∀ e ∈ exts, ∀ k < e.2, ¬ priv (e.1 + k))
    (priv_arena : ∀ a, priv a → A.lo ≤ a ∧ a < A.hi) :
    EntryOff A SL exts priv alloc shared where
  shared_priv := hown.reserved.outsidePrivate hown.immutable hpriv
    (fun k hk hnot => absurd (priv_arena k hk) hnot)
  shared_stack k hk hin := hown.immutable.outsideWrites k hk (hwrites k hin.1 hin.2)
  ext_arena e he k hk := by
    obtain ⟨_, hlo, hhi⟩ := hown.ledger.arena.1 _ he
    change e.1 ≤ k ∧ k < e.1 + e.2 at hk
    omega
  ext_priv e he k hk hp := by
    change e.1 ≤ k ∧ k < e.1 + e.2 at hk
    have := hpriv e he (k - e.1) (by omega)
    rw [show e.1 + (k - e.1) = k by omega] at this
    exact this hp

end RuntimeOwnership

/-! ## 2. The fresh block of one `malloc` -/

/-- The success clause of `MallocContract.spec`, named. -/
structure MallocBlock (A : Arena) (exts : List Extent) (n p : Nat) : Prop where
  nonzero : p ≠ 0
  align : p % 16 = 0
  arena : A.contains p n
  fresh : ∀ e ∈ exts, ExtDisjoint (p, n) e

theorem MallocBlock.freshExtents {A : Arena} {exts : List Extent} {n p : Nat}
    (h : MallocBlock A exts n p) : FreshExtents A exts [(p, n)] :=
  freshExtents_single h.arena h.fresh

theorem MallocBlock.toNat {A : Arena} {exts : List Extent} {n p : Nat}
    (h : MallocBlock A exts n p) (hA : A.hi ≤ 0x100000000) :
    (BitVec.ofNat 64 p).toNat = p := by
  obtain ⟨_, hphi⟩ := h.arena
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## 3. The closure push (plan task 2) -/

namespace RuntimeOwnership

private theorem valueClosuresBounded_mono {n n' : Nat} (h : n ≤ n') {v : Value}
    (hv : ValueClosuresBounded n v) : ValueClosuresBounded n' v := by
  cases v <;> first | exact Nat.lt_of_lt_of_le hv h | exact trivial

/-- **Ownership after pushing one closure**: the old roles and bytes survive the
build's memory (agreement on `P` covering every owned extent and shared byte),
the fresh record takes the closure role at the new index, and its AST is shared. -/
theorem StoreOwned.pushClosure {m m' : Mem} {phiF phiC phiC' : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {s : Store} {cd : ClosureData} {p q : Nat}
    (h : StoreOwned m phiF phiC alloc shared s)
    (hag : AgreeP P m m')
    (ha : ∀ role p n, Allocated alloc role p n → ∀ k, ExtentByte (p, n) k → P k)
    (hs : ∀ k, shared k → P k)
    (hext : PhiExtends phiC phiC' s.closures.size) (hp : phiC' s.closures.size = p)
    (hread : read64 m' p = some q)
    (hfp : ∀ k, ExprFp m' q (.fn cd.name cd.params cd.body) k → shared k)
    (henv : cd.env < s.frames.size) :
    StoreOwned m' phiF phiC' (alloc.insert (.closure s.closures.size) p 16) shared
      (s.allocClosure cd).1 := by
  have h' := h.transport hag ha hs
  refine ⟨?_, ?_, ⟨?_⟩, ?_, ?_⟩
  · intro fa hf
    have hf' : fa < s.frames.size := hf
    exact (h'.frames fa hf').congrAlloc
      (Allocations.insert_other (by intro h; cases h))
      (Allocations.insert_other (by intro h; cases h))
      (Allocations.insert_other (by intro h; cases h))
      (fun _ => Allocations.insert_other (by intro h; cases h))
  · intro ca hc
    have hc' : ca < (s.closures.push cd).size := hc
    rw [Array.size_push] at hc'
    rcases Nat.lt_or_ge ca s.closures.size with hlt | hge
    · show alloc.insert (.closure s.closures.size) p 16 (.closure ca) = some (phiC' ca, 16)
      rw [Allocations.insert_other (fun h => absurd (Role.closure.inj h) (Nat.ne_of_lt hlt)),
        hext ca hlt]
      exact h'.closures ca hlt
    · have hce : ca = s.closures.size := by omega
      subst hce
      show alloc.insert (.closure s.closures.size) p 16 (.closure s.closures.size) =
        some (phiC' s.closures.size, 16)
      rw [hp]
      exact Allocations.insert_same
  · intro fa hf i hi
    exact valueClosuresBounded_mono
      (by show s.closures.size ≤ (s.closures.push cd).size; rw [Array.size_push]; omega)
      (h.valueClosures.bounded fa hf i hi)
  · intro ca hc
    have hc' : ca < (s.closures.push cd).size := hc
    rw [Array.size_push] at hc'
    rcases Nat.lt_or_ge ca s.closures.size with hlt | hge
    · have heq : (s.allocClosure cd).1.closures[ca]'hc = s.closures[ca] :=
        Array.getElem_push_lt hlt
      show ((s.allocClosure cd).1.closures[ca]'hc).env < s.frames.size
      rw [heq]
      exact h.capturedEnvs ca hlt
    · have hce : ca = s.closures.size := by omega
      subst hce
      have heq : (s.allocClosure cd).1.closures[s.closures.size]'hc = cd :=
        Array.getElem_push_eq
      show ((s.allocClosure cd).1.closures[s.closures.size]'hc).env < s.frames.size
      rw [heq]
      exact henv
  · intro ca hc q' hq' k hk
    have hc' : ca < (s.closures.push cd).size := hc
    rw [Array.size_push] at hc'
    rcases Nat.lt_or_ge ca s.closures.size with hlt | hge
    · have heq : (s.allocClosure cd).1.closures[ca]'hc = s.closures[ca] :=
        Array.getElem_push_lt hlt
      rw [heq] at hk
      rw [hext ca hlt] at hq'
      exact h'.closureAsts ca hlt q' hq' k hk
    · have hce : ca = s.closures.size := by omega
      subst hce
      have heq : (s.allocClosure cd).1.closures[s.closures.size]'hc = cd :=
        Array.getElem_push_eq
      rw [heq] at hk
      rw [hp] at hq'
      have hqq : q' = q := Option.some.inj (hq'.symm.trans hread)
      subst hqq
      exact hfp k hk

/-- **`HeapOwned.pushClosure`** (plan task 2): the whole ownership ledger after the
closure build at the post-build memory. -/
theorem HeapOwned.pushClosure {A : Arena} {SL : StackLayout} {exts : List Extent}
    {m m' : Mem} {phiF phiC phiC' : Addr → Nat} {alloc : Allocations}
    {shared readable writes priv : Nat → Prop} {s : Store} {cd : ClosureData} {p q : Nat}
    (hown : HeapOwned A exts m phiF phiC alloc shared readable writes s)
    (hoff : OwnedOff SL priv [(p, 16)] alloc shared)
    (hag : AgreeP (AllocOff SL priv [(p, 16)]) m m')
    (hA : A.contains p 16) (hf : ∀ e ∈ exts, ExtDisjoint (p, 16) e)
    (hext : PhiExtends phiC phiC' s.closures.size) (hp : phiC' s.closures.size = p)
    (hread : read64 m' p = some q)
    (hfp : ∀ k, ExprFp m' q (.fn cd.name cd.params cd.body) k → shared k)
    (henv : cd.env < s.frames.size) :
    HeapOwned A ((p, 16) :: exts) m' phiF phiC'
      (alloc.insert (.closure s.closures.size) p 16) shared readable writes
      (s.allocClosure cd).1 :=
  ⟨hown.ledger.insert (by decide) hA hf, hown.immutable.insert hown.reserved hA hf,
    hown.reserved.mono (fun _ he => List.mem_cons_of_mem _ he),
    hown.store.pushClosure hag hoff.alloc hoff.shared hext hp hread hfp henv⟩

end RuntimeOwnership

#print axioms RuntimeOwnership.HeapOwned.ownedOff
#print axioms RuntimeOwnership.HeapOwned.transport_off
#print axioms RuntimeOwnership.HeapOwned.repr_off
#print axioms RuntimeOwnership.HeapOwned.fresh
#print axioms RuntimeOwnership.HeapOwned.free
#print axioms RuntimeOwnership.HeapArena.disjoint_of_ne
#print axioms RuntimeOwnership.HeapArena.nodup
#print axioms RuntimeOwnership.HeapArena.freshErase
#print axioms RuntimeOwnership.HeapOwned.entryOff
#print axioms AllocOff.single
#print axioms freshExtents_single
#print axioms MallocBlock.freshExtents
#print axioms RuntimeOwnership.StoreOwned.pushClosure
#print axioms RuntimeOwnership.HeapOwned.pushClosure

end Vsa.Sim
