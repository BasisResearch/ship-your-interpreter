import Vsa.Triple
import Vsa.RuntimeRepr
import Vsa.Sim.GoodState

namespace Vsa.Alloc

open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable

def mallocEntry : Nat := 0x80004790

def freeEntry : Nat := 0x8000479c

structure StackLayout where
  lo : Nat
  hi : Nat

def StackOK (SL : StackLayout) (sp : BitVec 64) (headroom : Nat) : Prop :=
  SL.lo + headroom ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0

def ExtDisjoint (a b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

def AbiPreserved : Register → Bool
  | .x2 | .x3 | .x4 | .x8 | .x9 => true
  | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 => true
  | _ => false

end Vsa.Alloc
