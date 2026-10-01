import Vsa.Alloc

open Vsa Vsa.Alloc Vsa.MemRepr

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev ramLo : Nat := 0x80000000

abbrev ramHi : Nat := 0x100000000

theorem tohostAddr_val : tohostAddr = 0x8001ad00 := rfl

abbrev Region : Type := Nat × Nat

def RSub (r s : Region) : Prop := s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2

def ramRegion : Region := (ramLo, ramHi - ramLo)

end Vsa.Sim
