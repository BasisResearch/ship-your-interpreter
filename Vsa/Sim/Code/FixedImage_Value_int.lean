import Vsa.Sim.Code.Value_int
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_value_intChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : value_intChunk0 mem := by
  exact ⟨h 10252 (by decide),
    h 10253 (by decide),
    h 10254 (by decide),
    h 10255 (by decide),
    h 10256 (by decide),
    h 10257 (by decide),
    h 10258 (by decide),
    h 10259 (by decide),
    h 10260 (by decide),
    h 10261 (by decide),
    h 10262 (by decide),
    h 10263 (by decide),
    h 10264 (by decide),
    h 10265 (by decide),
    h 10266 (by decide),
    h 10267 (by decide)⟩

theorem FixedTextLoaded.Value_intLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : Value_intLoaded mem :=
  fixedText_value_intChunk0 h

#print axioms FixedTextLoaded.Value_intLoaded

end Vsa.Sim.Code
