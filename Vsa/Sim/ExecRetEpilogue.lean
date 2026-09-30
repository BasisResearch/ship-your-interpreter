import Vsa.Sim.ExecBrkCont
import Vsa.Sim.SegEffect
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.Alloc

def execRetEpilogueWord (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a+1]?).getD 0, (m[a+2]?).getD 0,
   (m[a+3]?).getD 0, (m[a+4]?).getD 0, (m[a+5]?).getD 0,
   (m[a+6]?).getD 0, (m[a+7]?).getD 0]

theorem execRetEpilogueWord_value (m : Mem) (a : Nat) (value : BitVec 64)
    (h : read64 m a = some value.toNat) :
    bytesVal .ld (execRetEpilogueWord m a) = value := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, _⟩ :=
    read64_bytes m a value.toNat h
  simpa [execRetEpilogueWord, h0, h1, h2, h3, h4, h5, h6, h7, bytesVal] using
    ld_value_eq_read64 m a value.toNat b0 b1 b2 b3 b4 b5 b6 b7
      h h0 h1 h2 h3 h4 h5 h6 h7

end Vsa.Sim
