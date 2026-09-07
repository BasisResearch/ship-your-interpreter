import Vsa.Sim.Code.__umoddi3
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText___umoddi3Chunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __umoddi3Chunk0 mem := by
  exact ⟨h 18164 (by decide),
    h 18165 (by decide),
    h 18166 (by decide),
    h 18167 (by decide),
    h 18168 (by decide),
    h 18169 (by decide),
    h 18170 (by decide),
    h 18171 (by decide),
    h 18172 (by decide),
    h 18173 (by decide),
    h 18174 (by decide),
    h 18175 (by decide),
    h 18176 (by decide),
    h 18177 (by decide),
    h 18178 (by decide),
    h 18179 (by decide),
    h 18180 (by decide),
    h 18181 (by decide),
    h 18182 (by decide),
    h 18183 (by decide),
    h 18184 (by decide),
    h 18185 (by decide),
    h 18186 (by decide),
    h 18187 (by decide),
    h 18188 (by decide),
    h 18189 (by decide),
    h 18190 (by decide),
    h 18191 (by decide),
    h 18192 (by decide),
    h 18193 (by decide),
    h 18194 (by decide),
    h 18195 (by decide),
    h 18196 (by decide),
    h 18197 (by decide),
    h 18198 (by decide),
    h 18199 (by decide),
    h 18200 (by decide),
    h 18201 (by decide),
    h 18202 (by decide),
    h 18203 (by decide),
    h 18204 (by decide),
    h 18205 (by decide),
    h 18206 (by decide),
    h 18207 (by decide),
    h 18208 (by decide),
    h 18209 (by decide),
    h 18210 (by decide),
    h 18211 (by decide),
    h 18212 (by decide),
    h 18213 (by decide),
    h 18214 (by decide),
    h 18215 (by decide)⟩

theorem FixedTextLoaded.__umoddi3Loaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __umoddi3Loaded mem :=
  fixedText___umoddi3Chunk0 h

#print axioms FixedTextLoaded.__umoddi3Loaded

end Vsa.Sim.Code
