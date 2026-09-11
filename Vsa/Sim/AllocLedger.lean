import Vsa.Sim.rows.EnvDefineMissLedger
import Vsa.Sim.AllocOff
import Vsa.Sim.AllocRuns
import Vsa.Sim.AllocMallocAdapters

/-!
# `AllocLedger` — ONE run-global allocator ledger and its call adapters

Every allocating call site of the interpreter (`env_new`, the three `env_define`
lanes, the closure build of the `fn` arm, the concatenation scratch buffers,
`strdup`, `stringify`) needs the same external facts about the fixed binary's
allocator: the `malloc`/`free`/`realloc` runs with silence and byte presence, the
`strlen`/`memcpy` runs, where the allocator-private footprint lives, how the
arena sits against the stack and the HTIF window, and that the allocator
invariant reads only `gp` and its private bytes.  Before this module each
per-entry ledger (`EnvNewLedger`, `EnvDefineUpdateLedger`, `EnvDefineMissLedger`)
restated those facts field by field, keyed to that entry's `esp`, `m` and `exts`.

`AllocLedger` is the run-global record: one per run, no entry parameters.  The
per-entry ledgers become projections of it plus the facts that are genuinely
entry-local (`EnvNewLedger.of_alloc`, `EnvDefineUpdateLedger.of_alloc`,
`EnvDefineMissLedger.of_alloc`), so a new allocating site adds no allocator
fields at all.

* `AInvAt` states the allocator invariant at a memory with the pinned `gp` and
  transports it; the per-entry `ainv_stable`/`ainv_private` fields collapse to
  `AllocLedger.ainv_stable` and `.ainvAt_transport`.
* `mallocReturn_of_parked` / `freeReturn_of_parked` are the callee adapters:
  from a parked call carrying the caller's ownership to the named return with
  the ledger advanced, the invariant re-established, the memory frame, the
  footprint (`allocFoot`, the allocating clause family), and the caller's store
  and ownership survived — via `OwnedOff` (`Vsa/Sim/AllocOff.lean`), which is
  proved once.
* `closurePushed_of_mallocReturn` completes the `fn` arm's closure build on the
  same adapter (`PROOF_CLOSURE_PLAN.md`, task 2).

The only genuinely new external clause is `AllocLedger.ainv_perm`: the abstract
live list is a set, needed to release a block that is not at the list's head
(`MallocContract.freeSpec` pops the head).  Relating `MallocContract.privFoot`
to dlmalloc's actual bin-link writes stays the verified-allocator obligation
behind `MallocContract` itself.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership

/-! ## 4. The `malloc` adapter -/

/-- A `malloc` call parked at its entry with the caller's ownership. -/
structure MallocParked (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (credits : Nat) (c : Config) : Prop where
  entry : MallocEntry A SL gpv headroom maxReq M g exts n spv r m0 out c
  code : Code.FixedTextLoaded c.σ.mem
  resources : AllocationResources A maxReq credits n exts c.σ.mem
  owned : HeapOwned A exts m0 phiF phiC alloc shared readable writes s
  store : StoreRepr m0 N A phiF phiC s
  writes_stack : ∀ k, SL.lo ≤ k → k < SL.hi → writes k

/-- **The `malloc` return at its fresh block `p`**: the landed exit, the block, the
invariant at the returned memory, the frame, the footprint, and the caller's
ownership and store survived with the block entered unassigned. -/
structure MallocReturnAt (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (credits p : Nat) (c : Config) : Prop where
  exit : MallocExit A SL gpv headroom maxReq M g exts n spv r m0 out c
  budget : ResourceBudget A maxReq ((p, n) :: exts) credits
  reserve : AllocationReserve A c.σ.mem ((p, n) :: exts) maxReq credits
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  block : MallocBlock A exts n p
  ainv : AInvAt M gpv c.σ.mem ((p, n) :: exts)
  /-- The allocator changes nothing outside its stack window and private bytes. -/
  agree : AgreeP (AllocOff SL M.privFoot []) m0 c.σ.mem
  footprint : MemFootprint (fun k => stackWin SL spv.toNat k ∨ M.privFoot k) m0 c.σ.mem
  /-- The caller's ownership at the returned memory, before the block enters. -/
  owned0 : HeapOwned A exts c.σ.mem phiF phiC alloc shared readable writes s
  owned : HeapOwned A ((p, n) :: exts) c.σ.mem phiF phiC alloc shared readable writes s
  store : StoreRepr c.σ.mem N A phiF phiC s
  ownedOff : OwnedOff SL M.privFoot [(p, n)] alloc shared

/-- The `malloc` return, at some fresh block. -/
def MallocReturn (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (credits : Nat) (c : Config) : Prop :=
  ∃ p, MallocReturnAt A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
    shared readable writes s credits p c

/-- The footprint of one `malloc` is `allocFoot` at its block (the allocating
clause family of `IHClauseGenericAlloc`). -/
theorem MallocReturnAt.allocFoot {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {n : Nat}
    {spv r : BitVec 64} {m0 : Mem} {out : Array String} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {credits p : Nat} {c : Config}
    (X : MallocReturnAt A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
      shared readable writes s credits p c) (sret : Nat) :
    MemFootprint (allocFoot M.privFoot [(p, n)] SL A spv.toNat sret) m0 c.σ.mem :=
  X.footprint.mono (fun k hk => by
    rcases hk with hs | hp
    · exact Or.inl (Or.inl hs)
    · exact Or.inr (Or.inl hp))

/-- **The `malloc` adapter**: any parked bounded request returns its fresh block
with the ledger advanced and the caller's ownership survived. -/
theorem mallocReturn_of_parked {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (credits : Nat)
    (hn : n ≤ maxReq) (hpos : 0 < n) :
    Triple
      (MallocParked A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
        shared readable writes s credits)
      (MallocReturn A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
        shared readable writes s credits) := by
  intro c h
  obtain ⟨c', hs, success⟩ := L.mallocSuccess g exts n credits spv r m0 out c
    (MallocSuccessEntry.of_entry h.entry h.code h.resources)
  obtain ⟨p, result⟩ := success.allocated
  have X := success.returned.toMallocExit (M := M) result
  have ha0 := result.pointer.register
  have hp0 := result.pointer.nonzero
  have hp16 := result.pointer.aligned
  have hpA := result.pointer.arena
  have hpdisj := result.disjoint
  have hainv := result.ainv
  have hsp : spv.toNat ≤ SL.hi := h.entry.stack.2.1
  have hag : AgreeP (AllocOff SL M.privFoot []) m0 c'.σ.mem := by
    intro k hk
    exact (X.mem_frame k hk.2.1 (fun hw => hk.1 ⟨hw.1, by omega⟩)).symm
  have hpriv : ∀ e ∈ exts, ∀ k < e.2, ¬ M.privFoot (e.1 + k) :=
    M.privFoot_disjoint c.σ exts h.entry.ainv
  have hoff : OwnedOff SL M.privFoot [] alloc shared :=
    h.owned.ownedOff h.writes_stack hpriv L.priv_arena L.arena_stack
      (fun e he => absurd he List.not_mem_nil)
  have block : MallocBlock A exts n p := ⟨hp0, hp16, hpA, hpdisj⟩
  refine ⟨c', hs, p, ?_⟩
  exact
    { exit := X
      budget := result.budget, reserve := result.reserve
      a0 := ha0
      block := block
      ainv := L.ainvAt_of_state X.gp hainv
      agree := hag
      footprint := ⟨fun k hk => X.mem_frame k (fun hp => hk (Or.inr hp))
        (fun hw => hk (Or.inl hw))⟩
      owned0 := h.owned.transport_off hoff hag
      owned := (h.owned.transport_off hoff hag).fresh hpos hpA hpdisj
      store := h.owned.repr_off h.store hoff hag
      ownedOff := h.owned.ownedOff h.writes_stack hpriv L.priv_arena L.arena_stack
        block.freshExtents }

/-! ## 5. The `free` adapter -/

/-- A `free` call parked at its entry: the block is live (anywhere in the
list), assigned to no role, and outside every shared byte. -/
structure FreeParked (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 freeEntry)
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q)
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : c.σ.regs.get? Register.x2 = some spv
  stack : StackOK SL spv headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : M.AInv c.σ exts
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = out
  live : (q, n) ∈ exts
  unassigned : ∀ role, ¬ Allocated alloc role q n
  shared_out : ∀ k, shared k → ¬ ExtentByte (q, n) k
  owned : HeapOwned A exts m0 phiF phiC alloc shared readable writes s
  store : StoreRepr m0 N A phiF phiC s
  writes_stack : ∀ k, SL.lo ≤ k → k < SL.hi → writes k

/-- **The `free` return**: the block left the ledger, everything the caller owns
survived. -/
structure FreeReturn (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (c : Config) : Prop where
  exit : FreeExit A SL gpv headroom maxReq M g (exts.erase (q, n)) q n spv r m0 out c
  ainv : AInvAt M gpv c.σ.mem (exts.erase (q, n))
  agree : AgreeP (AllocOff SL M.privFoot [(q, n)]) m0 c.σ.mem
  footprint : MemFootprint
    (fun k => stackWin SL spv.toNat k ∨ M.privFoot k ∨ ExtentByte (q, n) k) m0 c.σ.mem
  owned : HeapOwned A (exts.erase (q, n)) c.σ.mem phiF phiC alloc shared readable writes s
  store : StoreRepr c.σ.mem N A phiF phiC s

/-- **The `free` adapter.** -/
theorem freeReturn_of_parked {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) :
    Triple
      (FreeParked A SL gpv headroom maxReq M g exts q n spv r m0 out N phiF phiC alloc
        shared readable writes s)
      (FreeReturn A SL gpv headroom maxReq M g exts q n spv r m0 out N phiF phiC alloc
        shared readable writes s) := by
  intro c h
  have hrot : M.AInv c.σ ((q, n) :: exts.erase (q, n)) :=
    L.ainv_perm c.σ exts _ (List.perm_cons_erase h.live) h.ainv
  obtain ⟨c', hs, X⟩ := L.free g (exts.erase (q, n)) q n spv r m0 out c
    { good := h.good, tick := h.tick, pc := h.pc, a0 := h.a0, ra := h.ra
      ra_align := h.ra_align, sp := h.sp, stack := h.stack, gp := h.gp, frame := h.frame
      ainv := hrot, mem := h.mem, out := h.out }
  have hsp : spv.toNat ≤ SL.hi := h.stack.2.1
  have hag : AgreeP (AllocOff SL M.privFoot [(q, n)]) m0 c'.σ.mem := by
    intro k hk
    have hq : ¬ (q ≤ k ∧ k < q + n) := hk.2.2 (q, n) (List.mem_cons_self)
    exact (X.mem_frame k hk.2.1 hq (fun hw => hk.1 ⟨hw.1, by omega⟩)).symm
  have hown' := h.owned.free h.unassigned h.shared_out
  have hpriv : ∀ e ∈ exts.erase (q, n), ∀ k < e.2, ¬ M.privFoot (e.1 + k) :=
    fun e he => M.privFoot_disjoint c.σ exts h.ainv e (List.mem_of_mem_erase he)
  have hoff : OwnedOff SL M.privFoot [(q, n)] alloc shared :=
    hown'.ownedOff h.writes_stack hpriv L.priv_arena L.arena_stack
      (HeapArena.freshErase h.owned.ledger.arena h.live)
  refine ⟨c', hs, ?_⟩
  exact
    { exit := X
      ainv := L.ainvAt_of_state X.gp X.ainv
      agree := hag
      footprint := ⟨fun k hk => X.mem_frame k (fun hp => hk (Or.inr (Or.inl hp)))
        (fun hb => hk (Or.inr (Or.inr hb))) (fun hw => hk (Or.inl hw))⟩
      owned := hown'.transport_off hoff hag
      store := hown'.repr_off h.store hoff hag }

/-! ## 6. The closure push from the allocator return -/

/-- The pushed closure store: owned and represented at the post-build memory. -/
structure ClosurePushed (A : Arena) (exts : List Extent) (m : Mem) (N : NativeAddrs)
    (phiF phiC' : Addr → Nat) (alloc' : Allocations) (shared readable writes : Nat → Prop)
    (s : Store) (cd : ClosureData) (p : Nat) : Prop where
  owned : HeapOwned A ((p, 16) :: exts) m phiF phiC' alloc' shared readable writes
    (s.allocClosure cd).1
  store : StoreRepr m N A phiF phiC' (s.allocClosure cd).1

/-- **The closure push from the `malloc` return**: the build writes only the fresh
record (and the stack), stores the closure header, and the `fn` node is shared. -/
theorem closurePushed_of_mallocReturn {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent}
    {spv r : BitVec 64} {m0 : Mem} {out : Array String} {N : NativeAddrs}
    {phiF phiC phiC' : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {credits p : Nat} {c : Config}
    (X : MallocReturnAt A SL gpv headroom maxReq M g exts 16 spv r m0 out N phiF phiC alloc
      shared readable writes s credits p c)
    {m' : Mem} {cd : ClosureData} {q : Nat}
    (hag : AgreeP (AllocOff SL M.privFoot [(p, 16)]) c.σ.mem m')
    (hext : PhiExtends phiC phiC' s.closures.size) (hp : phiC' s.closures.size = p)
    (hrepr : ClosureRepr m' phiF p cd)
    (hread : read64 m' p = some q)
    (hfp : ∀ k, ExprFp m' q (.fn cd.name cd.params cd.body) k → shared k)
    (henv : cd.env < s.frames.size) :
    ClosurePushed A exts m' N phiF phiC' (alloc.insert (.closure s.closures.size) p 16)
      shared readable writes s cd p := by
  have hA := X.block.arena
  have hf := X.block.fresh
  refine ⟨X.owned0.pushClosure X.ownedOff hag hA hf hext hp hread hfp henv, ?_⟩
  have hold : StoreRepr m' N A phiF phiC s := X.owned0.repr_off X.store X.ownedOff hag
  have hold' : StoreRepr m' N A phiF phiC' s :=
    storeRepr_phic_mono X.owned0.store.valueClosures hext hold
  refine storeRepr_pushClosure hold' hp hrepr hA (by have := X.block.align; omega) ?_
  intro ca hca heq
  rw [hext ca hca] at heq
  have hmem := X.owned0.ledger.live _ _ _ (X.owned0.store.closures ca hca)
  have hd := hf _ hmem
  change p + 16 ≤ phiC ca ∨ phiC ca + 16 ≤ p at hd
  omega

/-! ## 9. The landed per-entry ledgers as projections -/

/-- `EnvNewLedger` from the run-global ledger and the entry-local facts. -/
theorem EnvNewLedger.of_alloc
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {esp aEnv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (budget : ResourceBudget A maxReq exts 1)
    (reserve : AllocationReserve A m exts maxReq 1)
    (hgp : g Register.x3 = some gpv) (hs0 : (g Register.x8).isSome = true)
    (hesp : esp.toNat ≤ SL.hi) (hA : AInvAt M gpv m exts)
    (hparents : StoreParents st.store)
    (howned : ∃ (alloc : Allocations) (shared readable writes : Nat → Prop),
      HeapOwned A exts m φf φc alloc shared readable writes st.store ∧
      ∀ k, SL.lo ≤ k → k < SL.hi → writes k) :
    EnvNewLedger g N A SL φf φc st env esp aEnv r m M exts :=
  { gp := hgp, s0_present := hs0
    ainv_entry := hA, stack_hi := hesp
    alloc := L, budget := budget, reserve := reserve, parents := hparents, owned := howned }

/-- `EnvDefineUpdateLedger` from the run-global ledger and the entry-local facts. -/
theorem EnvDefineUpdateLedger.of_alloc
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (hgp : g Register.x3 = some gpv) (present : EnvDefineSavedPresent g)
    (hesp : esp.toNat ≤ SL.hi) (hA : AInvAt M gpv m exts)
    (owned : EnvDefineOwned A SL exts m φf φc st x aName pv v)
    (unique : ∀ (h : env < st.store.frames.size), FrameUnique st.store.frames[env])
    (names : ∀ (h : env < st.store.frames.size) (m' : Mem) (pn : Nat), AgreeBelow SL esp m m' →
      read64 m' (φf env + 8) = some pn → ScanNames m' pn aName x st.store.frames[env])
    (arrays_aligned : ∀ vals, read64 m (φf env + 16) = some vals → vals % 8 = 0)
    (define_survives : ∀ m1 : Mem,
      (∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) → m1[k]? = m[k]?) →
      StoreRepr m1 N A φf φc (st.store.define env x v) →
      ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m1[k]? = m'[k]?) →
        StoreRepr m' N A φf φc (st.store.define env x v)) :
    EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts :=
  { gp := hgp, present := present
    ainv_entry := hA, stack_hi := hesp
    alloc := L
    heap := by
      obtain ⟨_, _, _, _, hheap, _, _, _⟩ := owned
      exact hheap.ledger.arena
    owned := owned, unique := unique, names := names, arrays_aligned := arrays_aligned
    define_survives := define_survives }

/-- `EnvDefineMissLedger` from the run-global ledger and the queried name's facts. -/
theorem EnvDefineMissLedger.of_alloc
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (budget : ResourceBudget A maxReq exts 3)
    (reserve : AllocationReserve A m exts maxReq 3)
    (name_regions : StrRegions aName x.length)
    (name_align : aName.toNat % 8 = 0)
    (name_arena : A.contains aName.toNat (x.length + 1))
    (names_aligned : ∀ names, read64 m (φf env + 8) = some names → names % 8 = 0)
    (copy_fit : 8 * ((x.length + 1) / 8) ≤ 64)
    (copy_req : x.length + 1 ≤ maxReq)
    (grow_req : ∀ cap, read32 m (φf env + 4) = some cap → 48 * cap ≤ maxReq) :
    EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts :=
  { alloc := L, budget := budget, reserve := reserve
    name_regions := name_regions, name_align := name_align, name_arena := name_arena
    names_aligned := names_aligned, copy_fit := copy_fit, copy_req := copy_req
    grow_req := grow_req }

#print axioms AllocLedger.ainv_stable
#print axioms AllocLedger.ainvAt_of_state
#print axioms AllocLedger.ainvAt_transport
#print axioms AllocLedger.ainvAt_transport_offStack
#print axioms AllocLedger.privDisjoint_of_ainvAt
#print axioms mallocReturn_of_parked
#print axioms freeReturn_of_parked
#print axioms MallocReturnAt.allocFoot
#print axioms closurePushed_of_mallocReturn
#print axioms EnvNewLedger.of_alloc
#print axioms EnvDefineUpdateLedger.of_alloc
#print axioms EnvDefineMissLedger.of_alloc

end Vsa.Sim
