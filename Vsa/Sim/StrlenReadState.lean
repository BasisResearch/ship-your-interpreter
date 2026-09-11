import Vsa.Sim.StrlenSpecU
import Vsa.Sim.SharedReadGeometry
import Vsa.Sim.RuntimeOwnership

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic
open Code (StrlenLoaded)

/-- RAM and HTIF bounds for strlen's total word reads. -/
structure StrlenReadRegions (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

/-- The original strlen geometry supplies its read bounds. -/
theorem StrRegions.readRegions {p : BitVec 64} {len : Nat} (h : StrRegions p len) :
    StrlenReadRegions p len := ⟨h.lo, h.hi, h.nowrap, h.htif⟩

/-- Shared string ownership supplies every read bound, including static strings. -/
theorem SharedReadGeom.strlenRegions {shared : Nat → Prop} {SL : StackLayout}
    {p : BitVec 64} {s : String} {m : Mem} (geometry : SharedReadGeom shared SL)
    (name : RuntimeOwnership.SharedCString m shared p.toNat s) : StrlenReadRegions p s.length := by
  have first := geometry.ram _ (name.bytes 0 (Nat.zero_le _))
  have last := geometry.ram _ (name.bytes s.length (Nat.le_refl _))
  exact { lo := by simpa using first.1, hi := last.2, nowrap := by omega
          htif := shared_string_window (by unfold tohostAddr; omega) geometry.htif name.bytes }

namespace StrlenRun

/-- String facts shared by the read-only scan states. -/
structure StringState (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrlenReadRegions p len
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len

structure Pre (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006cf0#64
  a0 : c.σ.regs.get? Register.x10 = some p
  align : p.toNat % 8 = 0

structure UPre (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006cf0#64
  a0 : c.σ.regs.get? Register.x10 = some p
  align : p.toNat % 8 ≠ 0

structure HSt (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem) (m : Nat)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006d78#64
  a0 : c.σ.regs.get? Register.x10 = some p
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 m)
  mle : m ≤ len

structure HAlign (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem) (off0 : Nat)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006cfc#64
  a0 : c.σ.regs.get? Register.x10 = some p
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 off0)
  off0le : off0 ≤ len
  qalign : (p.toNat + off0) % 8 = 0
  offpos : 0 < off0

structure WStG (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem) (off0 j : Nat)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006d10#64
  a0 : c.σ.regs.get? Register.x10 = some p
  a1 : c.σ.regs.get? Register.x11 = some (BitVec.allOnes 64)
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (off0 + 8*j))
  qalign : (p.toNat + off0) % 8 = 0
  jle : off0 + 8*j ≤ len

structure WTailG (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem) (off0 j : Nat)
    (c : Config) : Prop extends StringState p r len cs m0 c where
  pc : c.σ.regs.get? Register.PC = some 0x80006d2c#64
  a0 : c.σ.regs.get? Register.x10 = some p
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (off0 + 8*(j+1)))
  qalign : (p.toNat + off0) % 8 = 0
  jlo : off0 + 8*j ≤ len
  jhi : len < off0 + 8*(j+1)

theorem head_lbu_bounds (base : BitVec 64) (len m : Nat) (hreg : StrlenReadRegions base len)
    (hm : m ≤ len) :
    (base + BitVec.ofNat 64 m).toNat = base.toNat + m ∧
    0x80000000 ≤ ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000 ∧
    (((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat) := by
  have htn : (base + BitVec.ofNat 64 m).toNat = base.toNat + m :=
    ptrN base m (by have := hreg.nowrap; omega)
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hs0 : ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat = base.toNat + m := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero, htn]
  refine ⟨htn, ?_, ?_, ?_⟩ <;> rw [hs0]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega

def HAtHead (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ m, HSt base r len cs m0 m c

def HAtAlign (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ off0, HAlign base r len cs m0 off0 c

def HLoopI (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  HAtHead base r len cs m0 c ∨ AtRet r len m0 (0x80006d90#64) c ∨ HAtAlign base r len cs m0 c

def HLoopB (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  HAtHead base r len cs m0 c

theorem hloopmu_head (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (c : Config) (hSt : HSt base r len cs m0 m c) :
    HLoopMu base len c = len + 1 - m := by
  simp only [HLoopMu, hSt.pc, hSt.a4, Option.getD_some, if_pos]
  have h4 : (base + BitVec.ofNat 64 m).toNat = base.toNat + m :=
    ptrN base m (by have := hSt.regions.nowrap; have := hSt.mle; omega)
  rw [h4]; omega

theorem hloopmu_align (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config)
    (hAl : HAlign base r len cs m0 off0 c) : HLoopMu base len c = 0 := by
  have hne : ¬ (c.σ.regs.get? Register.PC = some (0x80006d78#64)) := by
    rw [hAl.pc]; intro h; injection h with h; exact absurd h (by decide)
  simp only [HLoopMu, if_neg hne]

def WAtHeadG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  ∃ j, WStG base r len cs m0 off0 j c

def WAtTailG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  ∃ j, WTailG base r len cs m0 off0 j c

def WLoopIG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  WAtHeadG base r len cs m0 off0 c ∨ WAtTailG base r len cs m0 off0 c

def WLoopBG (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 : Nat) (c : Config) : Prop :=
  WAtHeadG base r len cs m0 off0 c

theorem wloopmuG_head (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (off0 j : Nat) (c : Config)
    (hSt : WStG base r len cs m0 off0 j c) : WLoopMuG base len c = len + 1 - (off0 + 8*j) := by
  simp only [WLoopMuG, hSt.pc, hSt.a4, Option.getD_some, if_pos]
  have h4 : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hSt.regions.nowrap; have := hSt.jle; omega)
  rw [h4]; omega

theorem wload_boundsG (base : BitVec 64) (len off0 j : Nat) (hreg : StrlenReadRegions base len)
    (hqal : (base.toNat + off0) % 8 = 0) (hj : off0 + 8*j ≤ len) :
    (base + BitVec.ofNat 64 (off0 + 8*j)).toNat = base.toNat + (off0 + 8*j) ∧
    0x80000000 ≤ ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    (((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat) ∧
    ((base + BitVec.ofNat 64 (off0+8*j)) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (base + BitVec.ofNat 64 (off0+8*j)).toNat = base.toNat + (off0+8*j) :=
    ptrN base (off0+8*j) (by have := hreg.nowrap; omega)
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_⟩
  all_goals rw [sext0_add, htn]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega
  · omega

theorem tail_lbu_boundsG (base : BitVec 64) (len off0 j k : Nat) (hreg : StrlenReadRegions base len)
    (hj : off0 + 8*j ≤ len) (hk : k ≤ 7) :
    0x80000000 ≤ (base.toNat + (off0+8*j) + k) ∧
    (base.toNat + (off0+8*j) + k) + 1 ≤ 0x100000000 ∧
    ((base.toNat + (off0+8*j) + k) + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (base.toNat + (off0+8*j) + k)) := by
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by omega, by omega, ?_⟩
  rcases hh with h | h
  · left; omega
  · right; omega

/-- Physical strlen entry facts derived from owned shared reads. -/
structure Input (p r : BitVec 64) (s : String) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some 0x80006cf0#64
  a0 : c.σ.regs.get? Register.x10 = some p
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrlenReadRegions p s.length
  string : CString m0 p.toNat s
  retAlign : r.toNat % 4 = 0

end StrlenRun

#print axioms SharedReadGeom.strlenRegions
end Vsa.Sim
