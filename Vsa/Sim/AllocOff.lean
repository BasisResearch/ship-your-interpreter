import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.ExitFootprint

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership

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

end Vsa.Sim
