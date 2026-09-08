import Vsa.Sim.rows.EnvDefineMissLedger
import Vsa.Sim.AllocOff

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

/-! ## 1. The `free` run, named -/

/-- `MallocContract.freeSpec`'s precondition, named: the block `q` of size `n`
is live and at the head of the abstract list. -/
structure FreeEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
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
  ainv : M.AInv c.σ ((q, n) :: exts)
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = out

/-- `MallocContract.freeSpec`'s postcondition, named, plus the console output
and byte presence clauses the abstract contract omits. -/
structure FreeExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some r
  sp : c.σ.regs.get? Register.x2 = some spv
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : M.AInv c.σ exts
  mem_frame : ∀ a, ¬ M.privFoot a → ¬ (q ≤ a ∧ a < q + n) →
    ¬ (SL.lo ≤ a ∧ a < spv.toNat) → c.σ.mem[a]? = m0[a]?
  out : c.σ.sailOutput = out
  mem_extends : MemExtends m0 c.σ.mem

/-- **The `free` run.**  `MallocContract.freeSpec` (named) with the two clauses it
omits.  Supplier: the verified-allocator proof behind `MallocContract.freeSpec`;
`free` writes no HTIF output and the machine's stores only insert bytes. -/
def FreeRun {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    Triple (FreeEntry A SL gpv headroom maxReq M g exts q n sp r m0 out)
      (FreeExit A SL gpv headroom maxReq M g exts q n sp r m0 out)

/-! ## 2. The run-global ledger -/

/-- **The run-global allocator ledger.**  One record per run: the callee runs
and the footprint discipline every allocating call site consumes.  Each field
names its supplier; none depends on an entry. -/
structure AllocLedger (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq) : Prop where
  /-- `MallocContract.spec` with silence and presence (`MallocRun`). -/
  malloc : MallocRun M
  /-- `MallocContract.freeSpec` with silence and presence (`FreeRun`). -/
  free : FreeRun M
  /-- A `realloc` operation instance over the same allocator state and private
  footprint, with silence and presence (`ReallocRun`). -/
  realloc : ReallocInstance A SL gpv headroom maxReq M.AInv M.privFoot
  /-- `strlen` with the console output retained (`StrlenRun`). -/
  strlen : StrlenRun
  /-- `memcpy` on both landed routes with the console output retained
  (`MemcpyRun`). -/
  memcpy : MemcpyRun
  /-- The allocator-private footprint lies inside the arena (the allocator's
  metadata and reent state are arena-resident; linker script, M6). -/
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  priv_arena : ∀ a, M.privFoot a → A.lo ≤ a ∧ a < A.hi
  /-- The arena is RAM above the HTIF window (linker script, M6). -/
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  arena_htif : tohostAddr + 16 ≤ A.lo
  arena_hi : A.hi ≤ 0x100000000
  /-- The arena and the stack region are disjoint (linker script, M6). -/
  arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo
  /-- The allocator invariant reads only `gp` and the allocator-private bytes
  (the `MallocContract` footprint discipline: `privFoot` is the allocator's
  whole state; live extents are caller data). -/
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  ainv_private : ∀ (exts : List Extent) (σa σb : MState),
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a, M.privFoot a → σa.mem[a]? = σb.mem[a]?) →
    M.AInv σa exts → M.AInv σb exts
  /-- The abstract live list is a set: the invariant is stable under
  reordering (dlmalloc keeps no order on the caller's live blocks; the list is
  the specification's own bookkeeping). -/
  ainv_perm : ∀ (σ : MState) (exts exts' : List Extent),
    exts.Perm exts' → M.AInv σ exts → M.AInv σ exts'
  /-- The allocator's stack headroom fits under the largest interpreter helper
  frame that calls it (`env_define`'s 64 bytes under the 1088-byte budget;
  concrete at M6). -/
  headroom_le : headroom + 64 ≤ 1088
  /-- The largest fixed request (the empty frame's first value array, 192 bytes)
  is within the interpreter's static ceiling (concrete at M6). -/
  init_req : 192 ≤ maxReq

namespace AllocLedger

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq}

theorem arena_ram (L : AllocLedger A SL gpv headroom maxReq M) :
    0x80000000 ≤ A.lo ∧ A.hi ≤ 0x100000000 := by
  have h := L.arena_htif
  have ht : tohostAddr = 0x8001ad00 := rfl
  exact ⟨by omega, L.arena_hi⟩

/-- Private bytes are off any stack window below `hi ≤ SL.hi`. -/
theorem priv_off_stack (L : AllocLedger A SL gpv headroom maxReq M)
    {hi : Nat} (hhi : hi ≤ SL.hi) {a : Nat} (hp : M.privFoot a) :
    ¬ (SL.lo ≤ a ∧ a < hi) := by
  have hA := L.priv_arena a hp
  rcases L.arena_stack with h | h <;> omega

end AllocLedger

/-! ## 3. The allocator invariant at a memory -/

/-- The allocator invariant at memory `m` with the pinned `gp`: exactly the
`ainv_entry` field shape of the per-entry ledgers. -/
def AInvAt {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (gpv : BitVec 64) (m : Mem)
    (exts : List Extent) : Prop :=
  ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts

namespace AllocLedger

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq}

/-- The invariant at a state is the invariant at its memory. -/
theorem ainvAt_of_state (L : AllocLedger A SL gpv headroom maxReq M)
    {σ : MState} {exts : List Extent}
    (hgp : σ.regs.get? Register.x3 = some gpv) (h : M.AInv σ exts) :
    AInvAt M gpv σ.mem exts :=
  fun σ' hgp' hm => L.ainv_private exts σ σ' (hgp.trans hgp'.symm) (fun _ _ => by rw [hm]) h

theorem ainvAt_at_state {σ : MState} {exts : List Extent} {m : Mem}
    (h : AInvAt M gpv m exts) (hgp : σ.regs.get? Register.x3 = some gpv)
    (hm : σ.mem = m) : M.AInv σ exts :=
  h σ hgp hm

/-- The invariant survives any memory change off the private bytes. -/
theorem ainvAt_transport (L : AllocLedger A SL gpv headroom maxReq M)
    {m m' : Mem} {exts : List Extent} (h : AInvAt M gpv m exts)
    (hag : ∀ a, M.privFoot a → m[a]? = m'[a]?) : AInvAt M gpv m' exts := by
  intro σ' hgp' hm'
  have hσ : M.AInv { σ' with mem := m } exts := h _ hgp' rfl
  refine L.ainv_private exts { σ' with mem := m } σ' rfl ?_ hσ
  intro a hp
  show m[a]? = σ'.mem[a]?
  rw [hm']
  exact hag a hp

/-- The invariant survives any memory change inside a stack window. -/
theorem ainvAt_transport_offStack (L : AllocLedger A SL gpv headroom maxReq M)
    {m m' : Mem} {exts : List Extent} {hi : Nat} (hhi : hi ≤ SL.hi)
    (h : AInvAt M gpv m exts)
    (hag : ∀ a, ¬ (SL.lo ≤ a ∧ a < hi) → m[a]? = m'[a]?) : AInvAt M gpv m' exts :=
  L.ainvAt_transport h (fun a hp => hag a (L.priv_off_stack hhi hp))

/-- The per-entry `ainv_stable` field, as ONE theorem of the ledger. -/
theorem ainv_stable (L : AllocLedger A SL gpv headroom maxReq M)
    (esp : BitVec 64) (hesp : esp.toNat ≤ SL.hi) (exts : List Extent) :
    ∀ σa σb : MState,
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts → M.AInv σb exts :=
  fun σa σb hgp hag h =>
    L.ainv_private exts σa σb hgp (fun a hp => hag a (L.priv_off_stack hesp hp)) h

/-- Live extents are off the private bytes, at any memory carrying the invariant. -/
theorem privDisjoint_of_ainvAt {m : Mem} {exts : List Extent}
    (h : AInvAt M gpv m exts) (σ : MState) (hgp : σ.regs.get? Register.x3 = some gpv) :
    ∀ e ∈ exts, ∀ k < e.2, ¬ M.privFoot (e.1 + k) :=
  M.privFoot_disjoint { σ with mem := m } exts (h _ hgp rfl)

end AllocLedger

/-! ## 4. The `malloc` adapter -/

/-- A `malloc` call parked at its entry with the caller's ownership. -/
structure MallocParked (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (N : NativeAddrs)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) (c : Config) : Prop where
  entry : MallocEntry A SL gpv headroom maxReq M g exts n spv r m0 out c
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
    (shared readable writes : Nat → Prop) (s : Store) (p : Nat) (c : Config) : Prop where
  exit : MallocExit A SL gpv headroom maxReq M g exts n spv r m0 out c
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
    (shared readable writes : Nat → Prop) (s : Store) (c : Config) : Prop :=
  ∃ p, MallocReturnAt A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
    shared readable writes s p c

/-- The footprint of one `malloc` is `allocFoot` at its block (the allocating
clause family of `IHClauseGenericAlloc`). -/
theorem MallocReturnAt.allocFoot {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {n : Nat}
    {spv r : BitVec 64} {m0 : Mem} {out : Array String} {N : NativeAddrs}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Store} {p : Nat} {c : Config}
    (X : MallocReturnAt A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
      shared readable writes s p c) (sret : Nat) :
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
    (shared readable writes : Nat → Prop) (s : Store)
    (hn : n ≤ maxReq) (hpos : 0 < n) :
    Triple
      (MallocParked A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
        shared readable writes s)
      (MallocReturn A SL gpv headroom maxReq M g exts n spv r m0 out N phiF phiC alloc
        shared readable writes s) := by
  intro c h
  obtain ⟨c', hs, X⟩ := L.malloc g exts n spv r m0 out hn c h.entry
  obtain ⟨p, ha0, hp0, hp16, hpA, hpdisj, hainv⟩ :=
    M.nonNull_of_bounded c'.σ exts n hn X.result
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
    {shared readable writes : Nat → Prop} {s : Store} {p : Nat} {c : Config}
    (X : MallocReturnAt A SL gpv headroom maxReq M g exts 16 spv r m0 out N phiF phiC alloc
      shared readable writes s p c)
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
    (hgp : g Register.x3 = some gpv) (hs0 : (g Register.x8).isSome = true)
    (hesp : esp.toNat ≤ SL.hi) (hA : AInvAt M gpv m exts)
    (hparents : StoreParents st.store)
    (howned : ∃ (alloc : Allocations) (shared readable writes : Nat → Prop),
      HeapOwned A exts m φf φc alloc shared readable writes st.store ∧
      ∀ k, SL.lo ≤ k → k < SL.hi → writes k) :
    EnvNewLedger g N A SL φf φc st env esp aEnv r m M exts :=
  { gp := hgp, s0_present := hs0
    headroom_le := by have := L.headroom_le; omega
    req := by have := L.init_req; omega
    ainv_entry := hA, ainv_stable := L.ainv_stable esp hesp exts, malloc := L.malloc
    priv_arena := L.priv_arena, arena_htif := L.arena_htif, arena_hi := L.arena_hi
    arena_stack := L.arena_stack, parents := hparents, owned := howned }

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
  { gp := hgp, present := present, headroom_le := L.headroom_le
    ainv_entry := hA, ainv_stable := L.ainv_stable esp hesp exts
    heap := by
      obtain ⟨_, _, _, _, hheap, _, _, _⟩ := owned
      exact hheap.ledger.arena
    arena_ram := L.arena_ram, arena_htif := L.arena_htif
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
    (name_regions : StrRegions aName x.length)
    (name_align : aName.toNat % 8 = 0)
    (name_arena : A.contains aName.toNat (x.length + 1))
    (names_aligned : ∀ names, read64 m (φf env + 8) = some names → names % 8 = 0)
    (copy_fit : 8 * ((x.length + 1) / 8) ≤ 64)
    (copy_req : x.length + 1 ≤ maxReq)
    (grow_req : ∀ cap, read32 m (φf env + 4) = some cap → 48 * cap ≤ maxReq) :
    EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts :=
  { malloc := L.malloc, realloc := L.realloc, strlen := L.strlen, memcpy := L.memcpy
    priv_arena := L.priv_arena, arena_stack := L.arena_stack, ainv_private := L.ainv_private
    name_regions := name_regions, name_align := name_align, name_arena := name_arena
    names_aligned := names_aligned, copy_fit := copy_fit, copy_req := copy_req
    grow_req := grow_req, init_req := L.init_req }

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
