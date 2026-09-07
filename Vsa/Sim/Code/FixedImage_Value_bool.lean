import Vsa.Sim.Code.Value_bool
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_value_boolChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : value_boolChunk0 mem := by
  exact ⟨h 10232 (by decide),
    h 10233 (by decide),
    h 10234 (by decide),
    h 10235 (by decide),
    h 10236 (by decide),
    h 10237 (by decide),
    h 10238 (by decide),
    h 10239 (by decide),
    h 10240 (by decide),
    h 10241 (by decide),
    h 10242 (by decide),
    h 10243 (by decide),
    h 10244 (by decide),
    h 10245 (by decide),
    h 10246 (by decide),
    h 10247 (by decide),
    h 10248 (by decide),
    h 10249 (by decide),
    h 10250 (by decide),
    h 10251 (by decide)⟩

theorem FixedTextLoaded.Value_boolLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : Value_boolLoaded mem :=
  fixedText_value_boolChunk0 h

#print axioms FixedTextLoaded.Value_boolLoaded

end Vsa.Sim.Code
