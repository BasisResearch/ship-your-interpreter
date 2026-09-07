import Vsa.Sim.Code.__divdi3
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText___divdi3Chunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __divdi3Chunk0 mem := by
  exact ⟨h 18084 (by decide),
    h 18085 (by decide),
    h 18086 (by decide),
    h 18087 (by decide),
    h 18088 (by decide),
    h 18089 (by decide),
    h 18090 (by decide),
    h 18091 (by decide)⟩

theorem FixedTextLoaded.__divdi3Loaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __divdi3Loaded mem :=
  fixedText___divdi3Chunk0 h

#print axioms FixedTextLoaded.__divdi3Loaded

end Vsa.Sim.Code
