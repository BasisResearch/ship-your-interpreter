import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.ExitFootprint

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

/-! ## 2. The fresh block of one `malloc` -/

/-- The success clause of `MallocContract.spec`, named. -/
structure MallocBlock (A : Arena) (exts : List Extent) (n p : Nat) : Prop where
  nonzero : p ≠ 0
  align : p % 16 = 0
  arena : A.contains p n
  fresh : ∀ e ∈ exts, ExtDisjoint (p, n) e

theorem MallocBlock.toNat {A : Arena} {exts : List Extent} {n p : Nat}
    (h : MallocBlock A exts n p) (hA : A.hi ≤ 0x100000000) :
    (BitVec.ofNat 64 p).toNat = p := by
  obtain ⟨_, hphi⟩ := h.arena
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## 3. The closure push (plan task 2) -/

end Vsa.Sim
