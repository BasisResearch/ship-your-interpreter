import Vsa.Sim.Code.FixedImage
import Vsa.MemRepr
import Vsa.Alloc

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.Sim.Code

def StaticImageByte (k : Nat) : Prop := 0x80000000 ≤ k ∧ k < 0x8001acf0

structure StaticImageSupport (m : Mem) (SL : StackLayout) (A : Arena) : Prop where
  text : FixedTextLoaded m
  rodata : FixedRodataLoaded m
  stack : SL.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ SL.lo
  arena : A.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ A.lo

end Vsa.Sim
