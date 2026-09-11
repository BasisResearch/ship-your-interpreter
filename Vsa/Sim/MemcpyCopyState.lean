import Vsa.Sim.MemcpySpec
import Vsa.Sim.MemPresence
import Vsa.Sim.WriteLogNF

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc

/-- Bounds for the allocated destination and the shared source. -/
structure Regions (dst src : BitVec 64) (n : Nat) : Prop where
  dst_lo : 0x80000000 ≤ dst.toNat
  dst_hi : dst.toNat + n ≤ 0x100000000
  dst_win : tohostAddr + 16 ≤ dst.toNat
  src_lo : 0x80000000 ≤ src.toNat
  src_hi : src.toNat + n ≤ 0x100000000
  src_win : src.toNat + n ≤ tohostAddr ∨ tohostAddr + 8 ≤ src.toNat
  disjoint : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat
  code_disjoint : dst.toNat + n ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ dst.toNat

/-- Extend the copied prefix by the bytes written by an executed block. -/
theorem advance {dst src : BitVec 64} {n i count : Nat} {bs : Nat → BitVec 8}
    {m0 before after : Mem} (h : MemInv dst src n bs i m0 before)
    (separate : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat)
    (bound : i + count ≤ n)
    (written : ∀ k, i ≤ k → k < i + count → after[dst.toNat + k]? = some (bs k))
    (outside : ∀ a, (a < dst.toNat + i ∨ dst.toNat + i + count ≤ a) →
      after[a]? = before[a]?) : MemInv dst src n bs (i + count) m0 after := by
  refine { copied := ?_, outside := ?_, src_intact := ?_ }
  · intro k hk
    by_cases old : k < i
    · rw [outside _ (by omega)]
      exact h.copied k old
    · exact written k (by omega) hk
  · intro a ha
    rw [outside a (by omega)]
    exact h.outside a ha
  · intro k lower upper
    rw [outside _ (by omega)]
    exact h.src_intact k (by omega) upper

/-- One byte store advances the copy invariant. -/
theorem storeByte {dst src : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8}
    {m0 mem : Mem} (h : MemInv dst src n bs i m0 mem)
    (separate : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat)
    (bound : i < n) :
    MemInv dst src n bs (i+1) m0 (mem.insert (dst.toNat + i) (bs i)) := by
  apply advance h separate (by omega)
  · intro k lower upper
    have equal : k = i := by omega
    subst k
    simp
  · intro a ha
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- Caller observations retained by the actual copy execution. -/
structure Retained (P : Config → Prop) (before after : Config) : Prop where
  state : P after
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R
  presence : MemExtends before.σ.mem after.σ.mem

theorem Retained.then {P Q : Config → Prop} {origin before after : Config}
    (first : Retained P origin before) (second : Retained Q before after) :
    Retained Q origin after :=
  { second with output := second.output.trans first.output
                frame := fun R hR => (second.frame R hR).trans (first.frame R hR)
                presence := first.presence.trans second.presence }

/-- Common copy state, with the current copied prefix. -/
structure State (dst src r : BitVec 64) (n i : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : Code.MemcpyLoaded c.σ.mem
  tick : c.tick < 2
  a0 : c.σ.regs.get? Register.x10 = some dst
  ra : c.σ.regs.get? Register.x1 = some r
  regions : Regions dst src n
  bound : i ≤ n
  meminv : MemInv dst src n bs i m0 c.σ.mem

/-- The byte loop head, or its exit after the last byte. -/
structure ByteState (dst src r : BitVec 64) (n i : Nat) (bs : Nat → BitVec 8)
    (m0 : Mem) (c : Config) : Prop extends State dst src r n i bs m0 c where
  pc : c.σ.regs.get? Register.PC = some (if i < n then 0x80006c48#64 else 0x80006c5c#64)
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 i)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)

#print axioms advance
#print axioms storeByte

end Vsa.Sim.MemcpyCopy
