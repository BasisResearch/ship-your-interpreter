import Vsa.Sim.Code.Value_str
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_value_strChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : value_strChunk0 mem := by
  exact ⟨h 10268 (by decide),
    h 10269 (by decide),
    h 10270 (by decide),
    h 10271 (by decide),
    h 10272 (by decide),
    h 10273 (by decide),
    h 10274 (by decide),
    h 10275 (by decide),
    h 10276 (by decide),
    h 10277 (by decide),
    h 10278 (by decide),
    h 10279 (by decide),
    h 10280 (by decide),
    h 10281 (by decide),
    h 10282 (by decide),
    h 10283 (by decide)⟩

theorem FixedTextLoaded.Value_strLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : Value_strLoaded mem :=
  fixedText_value_strChunk0 h

#print axioms FixedTextLoaded.Value_strLoaded

end Vsa.Sim.Code
