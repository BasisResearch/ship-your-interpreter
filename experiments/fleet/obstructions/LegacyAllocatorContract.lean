import Vsa.Alloc
import Vsa.Sim.RuntimeOwnershipDataTransport
import Vsa.Sim.AllocCapacity

/-!
Historical allocator-contract regression. The legacy record and both obstruction
proofs retain their original fields, quantifiers, and proof bodies. The companion
JSON records source hashes and the namespace qualifications used by this fixture.
-/

namespace Vsa.Alloc.Legacy

open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable

/-- **The allocator contract** — the one named hypothesis of the final
theorem. `A` is the heap arena, `SL` the stack region, `gpv` the global
pointer value (pinned for the whole run; `_malloc_r` addresses its state
gp-relative), `headroom` the stack bytes malloc may use, `maxReq` the
largest request the interpreter ever makes (both concrete at M6). -/
structure MallocContract (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) where
  /-- Abstract allocator invariant: machine state × live allocations. -/
  AInv : MState → List (Nat × Nat) → Prop
  /-- Allocator-private addresses (metadata, reent state). -/
  privFoot : Nat → Prop
  /-- Private footprint is disjoint from every live allocation. -/
  privFoot_disjoint : ∀ σ exts, AInv σ exts →
    ∀ e ∈ exts, ∀ k < e.2, ¬ privFoot (e.1 + k)
  /-- The total-correctness triple for one `malloc(n)` call. -/
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List (Nat × Nat)) (n : Nat) (sp r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    n ≤ maxReq →
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n) ∧
        c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        AInv c.σ exts ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        -- NULL on exhaustion, or a fresh, aligned, in-arena block:
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
           (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
           AInv c.σ ((p, n) :: exts))) ∧
        -- memory outside the allocator-private footprint and the stack
        -- window strictly below the entry sp is untouched:
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          c.σ.mem[a]? = m0[a]?))
  /-- **The total-correctness triple for one `free(q)` call** (entry
  `freeEntry`, the wrapper into `_free_r`).

  `free` is part of the SAME allocator interface as `malloc`: the two are duals
  over the abstract live list `AInv … exts`.  We give `free` a real contract —
  not a frame-only no-op — for two reasons dlmalloc's implementation forces:

  1. **The extent must LEAVE the live list.**  dlmalloc REUSES freed blocks: a
  later `malloc` can hand back exactly the just-freed chunk.  If `free(q)` left
  `(q, n)` in `exts`, then `malloc`'s post (`ExtDisjoint (p, n') e` for every
  `e ∈ exts` — the freshness clause) would forbid ever returning that address
  again, so after enough alloc/free cycles the freshness clause becomes
  uninhabitable (the arena is finite).  The post therefore POPS the extent:
  `AInv c.σ' exts` with `(q, n)` gone.

  2. **The freed chunk's bytes are FORFEIT.**  `free` writes free-list link
  pointers INTO the freed chunk (dlmalloc stores `fd`/`bk` in the payload).  So
  the frame clause may NOT claim `[q, q+n)` is preserved — those bytes belong to
  the allocator again the instant `free` returns.  The untouched region is
  therefore everything OUTSIDE `privFoot ∪ [q, q+n) ∪ the stack window below the
  entry sp`.

  Pre mirrors `spec`'s ABI entry (GoodState, `tick < 2`, PC = `freeEntry`,
  `x10 = q` the block to free, `ra`/`sp`+`StackOK`/`gp` pinned, `AbiPreserved`
  tie to `g`) with `AInv c.σ ((q, n) :: exts)` — `q` must be a currently-live
  extent of size `n`, at the head (the caller knows which block it is freeing).
  Post returns to `ra`, restores the ABI frame, and asserts `AInv c.σ' exts`
  (the tail — extent popped).  Nobody constructs `MallocContract`; this field is
  a named hypothesis of the final theorem, so adding it breaks no proof. -/
  freeSpec : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List (Nat × Nat)) (q : Nat) (n : Nat) (sp r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 freeEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q) ∧
        c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        AInv c.σ ((q, n) :: exts) ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        -- the extent is popped off the live list:
        AInv c.σ exts ∧
        -- memory outside the allocator-private footprint, the freed chunk
        -- `[q, q+n)` (whose bytes free reclaims for its link pointers), and the
        -- stack window strictly below the entry sp is untouched:
        (∀ a, ¬ privFoot a → ¬ (q ≤ a ∧ a < q + n) →
          ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?))
  /-- **The arena never OOMs for a bounded request** — the no-exhaustion
  guarantee.

  `spec`'s post is a disjunction: NULL on exhaustion, or a fresh in-arena block.
  For requests within the interpreter's static ceiling `maxReq`, and while the
  allocator invariant holds, the arena provably has capacity — dlmalloc returns
  a real block, never NULL.  This field COLLAPSES `spec`'s post disjunction to
  its non-null (success) disjunct: given `n ≤ maxReq` and the two branches
  exactly as `spec`'s post produces them, the NULL branch is impossible, so the
  fresh-block branch holds.

  This is what makes the `beqz a0` OOM guard (`strdup`/concat/`env_define`
  tails) UNCONDITIONALLY not-taken: the composition need not carry an OOM error
  path because the arena is sized so bounded requests always succeed.  Nobody
  constructs `MallocContract`; this field is a named hypothesis — like `spec`
  and `freeSpec`, its single inhabitant would be a verified-allocator +
  arena-capacity proof, never an `axiom`.  Adding it breaks no proof (the final
  theorem takes one `MallocContract …` and never inspects it further).  A
  vacuous/wrong hypothesis makes theorems vacuous at worst, not
  `False`-derivable, and `#print axioms` stays clean. -/
  nonNull_of_bounded : ∀ (σ : MState) (exts : List (Nat × Nat)) (n : Nat),
    n ≤ maxReq →
    ((σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv σ exts) ∨
     (∃ p, σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
       p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
       (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
       AInv σ ((p, n) :: exts))) →
    (∃ p, σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
      (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
      AInv σ ((p, n) :: exts))

end Vsa.Alloc.Legacy

namespace Vsa.Sim.Legacy

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open Vsa.Sim.RuntimeOwnership

/-- The allocator invariant at memory `m` with the pinned `gp`: exactly the
`ainv_entry` field shape of the per-entry ledgers. -/
def AInvAt {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : Vsa.Alloc.Legacy.MallocContract A SL gpv headroom maxReq) (gpv : BitVec 64) (m : Mem)
    (exts : List Extent) : Prop :=
  ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts

/-- The physical bytes a request of `n` occupies: an 8-byte chunk header, rounded
up to the allocator's 16-byte alignment. -/
def physSize (n : Nat) : Nat := 16 * ((n + 8 + 15) / 16)

/-- The physical cost of a whole ledger. -/
def physTotal (exts : List Extent) : Nat := (exts.map (fun e => physSize e.2)).sum

/-- **Room for `k` further requests at the ceiling.**  `ResourceBound` asserts the
budget at ONE point; this is the same statement indexed by how many more
allocations it still covers, which is what an induction along an execution
needs.  A source-level accounting supplies `k` — the number of allocations the
program can still make — and the lemmas below carry it. -/
def ResourceBudget (A : Arena) (maxReq : Nat) (exts : List Extent) (k : Nat) : Prop :=
  physTotal exts + k * physSize maxReq ≤ A.hi - A.lo

/-- The runtime and allocator invariant share one live extent list and memory. -/
structure RuntimeAllocatorState {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : Vsa.Alloc.Legacy.MallocContract A SL gpv headroom maxReq)
    (N : NativeAddrs) (phiF phiC : Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (credits : Nat) (s : Store) (m : Mem) : Prop where
  heap : HeapOwned A exts m phiF phiC alloc shared InitialReadableByte (InitialWriteByte SL) s
  repr : StoreRepr m N A phiF phiC s
  arrays : StoreArraysReady m phiF s
  geometry : SharedReadGeom shared SL
  parents : StoreParents s
  ainv : Vsa.Sim.Legacy.AInvAt M gpv m exts
  budget : Vsa.Sim.Legacy.ResourceBudget A maxReq exts credits

end Vsa.Sim.Legacy

namespace Vsa.Sim.Legacy.AllocatorContractObstruction

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The bounded non-null rule excludes an invariant at any memory in a finite RAM arena.
`AInvAt` quantifies over register states independently of a malloc execution,
so it includes a state whose result register is zero. -/
theorem no_initial_invariant
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : Vsa.Alloc.Legacy.MallocContract A SL gpv headroom maxReq)
    (arenaHi : A.hi ≤ 0x100000000) (m : Mem) (exts : List Extent) :
    ¬ Vsa.Sim.Legacy.AInvAt M gpv m exts := by
  intro invariant
  let state : MState :=
    { (default : MState) with
      mem := m
      regs := ((default : MState).regs.insert Register.x10 (0#64)).insert Register.x3 gpv }
  have gp : state.regs.get? Register.x3 = some gpv := by
    exact Std.ExtDHashMap.get?_insert_self
  have zero : state.regs.get? Register.x10 = some (0#64 : BitVec 64) := by
    simp [state, Std.ExtDHashMap.get?_insert]
  obtain ⟨p, result, nonzero, aligned, contains, disjoint, next⟩ :=
    M.nonNull_of_bounded state exts maxReq (Nat.le_refl _) (Or.inl ⟨zero, invariant state gp rfl⟩)
  have small : p < 2 ^ 64 := by
    have := contains.2
    omega
  have value : BitVec.ofNat 64 p = (0#64 : BitVec 64) := Option.some.inj (result.symm.trans zero)
  have number := congrArg BitVec.toNat value
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at number
  exact nonzero number

/-- Every owned allocator entry requires the inconsistent initial invariant.
Changing ownership witnesses or increasing credit cannot supply that premise. -/
theorem no_runtime_state
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : Vsa.Alloc.Legacy.MallocContract A SL gpv headroom maxReq) (arenaHi : A.hi ≤ 0x100000000)
    {N : NativeAddrs} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : RuntimeOwnership.Allocations} {exts : List Extent} {shared : Nat → Prop}
    {credits : Nat} {store : Vsa.While.Store} {m : Mem} :
    ¬ Vsa.Sim.Legacy.RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m :=
  fun state => no_initial_invariant M arenaHi m exts state.ainv

#print axioms no_initial_invariant
#print axioms no_runtime_state

end Vsa.Sim.Legacy.AllocatorContractObstruction
