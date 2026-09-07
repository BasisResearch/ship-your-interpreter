import Vsa.Sim.Code.Value_truthy
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText_value_truthyChunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : value_truthyChunk0 mem := by
  exact ⟨h 10284 (by decide),
    h 10285 (by decide),
    h 10286 (by decide),
    h 10287 (by decide),
    h 10288 (by decide),
    h 10289 (by decide),
    h 10290 (by decide),
    h 10291 (by decide),
    h 10292 (by decide),
    h 10293 (by decide),
    h 10294 (by decide),
    h 10295 (by decide),
    h 10296 (by decide),
    h 10297 (by decide),
    h 10298 (by decide),
    h 10299 (by decide),
    h 10300 (by decide),
    h 10301 (by decide),
    h 10302 (by decide),
    h 10303 (by decide),
    h 10304 (by decide),
    h 10305 (by decide),
    h 10306 (by decide),
    h 10307 (by decide),
    h 10308 (by decide),
    h 10309 (by decide),
    h 10310 (by decide),
    h 10311 (by decide),
    h 10312 (by decide),
    h 10313 (by decide),
    h 10314 (by decide),
    h 10315 (by decide),
    h 10316 (by decide),
    h 10317 (by decide),
    h 10318 (by decide),
    h 10319 (by decide),
    h 10320 (by decide),
    h 10321 (by decide),
    h 10322 (by decide),
    h 10323 (by decide),
    h 10324 (by decide),
    h 10325 (by decide),
    h 10326 (by decide),
    h 10327 (by decide),
    h 10328 (by decide),
    h 10329 (by decide),
    h 10330 (by decide),
    h 10331 (by decide)⟩

theorem FixedTextLoaded.Value_truthyLoaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : Value_truthyLoaded mem :=
  fixedText_value_truthyChunk0 h

#print axioms FixedTextLoaded.Value_truthyLoaded

end Vsa.Sim.Code
