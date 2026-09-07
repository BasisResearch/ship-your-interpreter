import Vsa.Sim.Code.Value_null
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_value_nullChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : value_nullChunk0 mem := by
  exact ⟨h 10220 (by decide),
    h 10221 (by decide),
    h 10222 (by decide),
    h 10223 (by decide),
    h 10224 (by decide),
    h 10225 (by decide),
    h 10226 (by decide),
    h 10227 (by decide),
    h 10228 (by decide),
    h 10229 (by decide),
    h 10230 (by decide),
    h 10231 (by decide)⟩

theorem FixedTextLoaded.Value_nullLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : Value_nullLoaded mem :=
  fixedText_value_nullChunk0 h

#print axioms FixedTextLoaded.Value_nullLoaded

end Vsa.Sim.Code
