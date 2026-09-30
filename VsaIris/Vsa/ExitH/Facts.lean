import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.StdioErr

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

def exitS (s : BitVec 64) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ (0x8001b970 ≤ a ∧ a < 0x8001b978)) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (s.toNat - 256 ≤ a ∧ a < s.toNat)

namespace XH

scoped macro_rules | `(tactic| nx_addr) => `(tactic| (simp only [exitS, stdioFoot, InRange] at ⊢; (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); first | done | omega))
end XH

structure ExitSp (s : BitVec 64) : Prop where
  lo : 0x8001ad00 + 16 + 256 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s.toNat % 16 = 0
  place : s.toNat ≤ 0x8001b520 ∨ 0x8001c168 + 256 ≤ s.toNat

structure ExitEnd (R : Nat → BitVec 64) (s e : BitVec 64) (R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = s
  s0 : R' 8 = e
  saved : ∀ x ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], R' x = R x

end VsaIris.Sym
