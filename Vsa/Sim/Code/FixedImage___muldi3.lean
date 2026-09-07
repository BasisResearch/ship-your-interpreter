import Vsa.Sim.Code.__muldi3
import Vsa.Sim.Code.FixedImage

namespace Vsa.Sim.Code

theorem fixedText___muldi3Chunk0 {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __muldi3Chunk0 mem := by
  exact ⟨h 17984 (by decide),
    h 17985 (by decide),
    h 17986 (by decide),
    h 17987 (by decide),
    h 17988 (by decide),
    h 17989 (by decide),
    h 17990 (by decide),
    h 17991 (by decide),
    h 17992 (by decide),
    h 17993 (by decide),
    h 17994 (by decide),
    h 17995 (by decide),
    h 17996 (by decide),
    h 17997 (by decide),
    h 17998 (by decide),
    h 17999 (by decide),
    h 18000 (by decide),
    h 18001 (by decide),
    h 18002 (by decide),
    h 18003 (by decide),
    h 18004 (by decide),
    h 18005 (by decide),
    h 18006 (by decide),
    h 18007 (by decide),
    h 18008 (by decide),
    h 18009 (by decide),
    h 18010 (by decide),
    h 18011 (by decide),
    h 18012 (by decide),
    h 18013 (by decide),
    h 18014 (by decide),
    h 18015 (by decide),
    h 18016 (by decide),
    h 18017 (by decide),
    h 18018 (by decide),
    h 18019 (by decide)⟩

theorem FixedTextLoaded.__muldi3Loaded {mem : Std.ExtHashMap Nat (BitVec 8)}
    (h : FixedTextLoaded mem) : __muldi3Loaded mem :=
  fixedText___muldi3Chunk0 h

#print axioms FixedTextLoaded.__muldi3Loaded

end Vsa.Sim.Code
