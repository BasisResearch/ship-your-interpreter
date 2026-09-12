import EnvGetCompareFrame
import Vsa.Sim.WordLoadData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The semantic scan's actual name slot supplies the reflected load and
the conditional comparison entry. Its saved-register frame reaches the result. -/
theorem scan_compare
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g 0x80002c60#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 c) (hi : i < f.vars.length) :
    ∃ after g' pa, CompareResult g' pa name (f.vars[i]'hi).1 nameStr c after := by
  obtain ⟨q, hq, hqstr⟩ := hSt.names.bindPtr i hi
  let cursor := pn + BitVec.ofNat 64 (8 * i)
  let L := env_getX2c60L cursor name
  let load := mkLine 0x80002c60#64 0x0004b503#32
  have hcur : cursor.toNat = pn.toNat + 8 * i := by
    apply ptrN
    have := hSt.names.slotHi i hi
    omega
  have hqNat : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 m0 _ q hq)]
  have hea : eaddrM load L = cursor := by
    change cursor + sign_extend (m := 64) (0#12) = cursor
    rw [sext_zero, BitVec.add_zero]
  obtain ⟨bs, hword⟩ := wordLoadFacts_of_read64 c.σ.mem L load (BitVec.ofNat 64 q)
    (by rfl)
    (by rw [hea, hcur]; exact hSt.names.slotLo i hi)
    (by rw [hea, hcur]; exact hSt.names.slotHi i hi)
    (by rw [hea, hcur]; exact hSt.names.slotHtif i hi)
    (by rw [hea, hcur, hqNat, hSt.mem]; exact hq)
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [bs] env_getX2c60Seg := by
    chain_facts hSt.loadedG with "Vsa.Sim.Code.env_get_at_"
    exact hword.facts
  have hL : GHolds c.σ L := by
    exact ⟨by simpa [gprGet] using hSt.cursor1,
      by simpa [gprGet] using hSt.name3, trivial⟩
  obtain ⟨called, hCall⟩ := call_framed cursor name [bs] c hSt.good hSt.pc
    hSt.tick hL hfacts hSt.loadedG
  have hmem : called.σ.mem = c.σ.mem := hCall.mem.trans (by rfl)
  have ha0 : called.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q) := by
    change gprGet called.σ 10 = some (BitVec.ofNat 64 q)
    apply gholds_lookup _ hCall.registers
    change some (bytesVal .ld bs) = some (BitVec.ofNat 64 q)
    rw [hword.value]
  have ha1 : called.σ.regs.get? Register.x11 = some name := by
    change gprGet called.σ 11 = some name
    apply gholds_lookup _ hCall.registers
    change some (name + sign_extend (m := 64) (0#12)) = some name
    rw [sext_zero, BitVec.add_zero]
  have hpre : StrcmpEntryCond called.σ.regs.get? (BitVec.ofNat 64 q) name
      0x80002c6c#64 (f.vars[i]'hi).1 nameStr c.σ.mem c.σ.sailOutput called :=
    { good := hCall.good
      loaded := by rw [hmem]; exact hSt.loadedS
      mem := hmem
      out := hCall.output
      pc := hCall.pc
      a0 := ha0
      a1 := ha1
      ra := hCall.ra
      minstret := hCall.minstret
      tick := hCall.tick
      ralign := by decide
      cstra := by rw [hSt.mem, hqNat]; exact hqstr
      cstrb := by rw [hSt.mem]; exact hSt.names.nameCStr
      maskpin := by rw [hSt.mem]; exact hSt.names.maskPinned
      wrega := by
        rw [hSt.mem, hqNat]
        exact fun cs hcs => hSt.names.bindRegW i hi q hq cs hcs
      wregb := by rw [hSt.mem]; exact hSt.names.nameRegW
      frame := fun _ _ => rfl }
  obtain ⟨after, hpost⟩ := hCall.compare hpre
  exact ⟨after, called.σ.regs.get?, BitVec.ofNat 64 q, hpost⟩

#print axioms scan_compare

end Vsa.Sim.EnvGetReflected
