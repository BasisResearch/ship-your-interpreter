import EnvGetScanCompare

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- Saved scan registers that remain fixed when the cursor and index advance. -/
def scanFixedKeep (R : Register) : Bool :=
  Vsa.Alloc.AbiPreserved R && R != Register.x8 && R != Register.x9

/-- Re-seat the scan carrier from reached control and cursor observations.
The caller supplies the new index bound and the ghost for this endpoint. -/
theorem _root_.Vsa.Sim.ScanSt.reseat
    {g g' : (R : Register) → Option (RegisterType R)}
    {pc pc' env name out count pn ra ra' sp : BitVec 64} {i j : Nat}
    {f : Vsa.While.Frame} {nameStr : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {m0 : Mem} {before after : Config}
    (hSt : Vsa.Sim.ScanSt g pc env name out count pn ra sp i
      f nameStr N phiF phiC m0 before)
    (hgood : GoodState after.σ) (htick : after.tick < 2)
    (hmem : after.σ.mem = before.σ.mem)
    (hpc : after.σ.regs.get? Register.PC = some pc')
    (hra : after.σ.regs.get? Register.x1 = some ra')
    (hidx : after.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 j))
    (hcursor : after.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * j)))
    (hj : j ≤ f.vars.length)
    (hframe : ∀ R, scanFixedKeep R = true →
      after.σ.regs.get? R = before.σ.regs.get? R)
    (hghost : ∀ R, Vsa.Alloc.AbiPreserved R = true → after.σ.regs.get? R = g' R) :
    Vsa.Sim.ScanSt g' pc' env name out count pn ra' sp j
      f nameStr N phiF phiC m0 after := by
  exact
    { good := hgood
      loadedG := hmem.symm ▸ hSt.loadedG
      loadedS := hmem.symm ▸ hSt.loadedS
      mem := hmem.trans hSt.mem
      pc := hpc
      env4 := (hframe Register.x20 (by decide)).trans hSt.env4
      name3 := (hframe Register.x19 (by decide)).trans hSt.name3
      out5 := (hframe Register.x21 (by decide)).trans hSt.out5
      count2 := (hframe Register.x18 (by decide)).trans hSt.count2
      cursor1 := hcursor
      idx0 := hidx
      ra := hra
      sp2 := (hframe Register.x2 (by decide)).trans hSt.sp2
      minstret := hgood.minstret
      tick := htick
      frame := hSt.frame
      names := hSt.names
      count_eq := hSt.count_eq
      ile := hj
      ghost := hghost }

/-- Transport scan observations through an unchanged memory and ABI frame.
The reached return address is supplied separately from the saved registers. -/
theorem _root_.Vsa.Sim.ScanSt.transport
    {g : (R : Register) → Option (RegisterType R)}
    {pc pc' env name out count pn ra ra' sp : BitVec 64} {i : Nat}
    {f : Vsa.While.Frame} {nameStr : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {m0 : Mem} {before after : Config}
    (hSt : Vsa.Sim.ScanSt g pc env name out count pn ra sp i
      f nameStr N phiF phiC m0 before)
    (hgood : GoodState after.σ) (htick : after.tick < 2)
    (hmem : after.σ.mem = before.σ.mem)
    (hpc : after.σ.regs.get? Register.PC = some pc')
    (hra : after.σ.regs.get? Register.x1 = some ra')
    (hframe : ∀ R, Vsa.Alloc.AbiPreserved R = true →
      after.σ.regs.get? R = before.σ.regs.get? R) :
    Vsa.Sim.ScanSt g pc' env name out count pn ra' sp i
      f nameStr N phiF phiC m0 after := by
  apply ScanSt.reseat hSt hgood htick hmem hpc hra
    ((hframe Register.x8 (by decide)).trans hSt.idx0)
    ((hframe Register.x9 (by decide)).trans hSt.cursor1) hSt.ile
  · intro R hR
    have hk := hR
    simp only [scanFixedKeep, Bool.and_eq_true] at hk
    exact hframe R hk.1.1
  · exact fun R hR => (hframe R hR).trans (hSt.ghost R hR)

/-- Restore the scan carrier at the actual comparison return. The scan's
saved registers retain their original ghost throughout the call. -/
theorem CompareResult.scan
    {g g' : (R : Register) → Option (RegisterType R)}
    {env name out count pn ra sp pa : BitVec 64} {i : Nat}
    {f : Vsa.While.Frame} {nameStr sa : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {m0 : Mem} {before after : Config}
    (hSt : ScanSt g 0x80002c60#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 before)
    (h : CompareResult g' pa name sa nameStr before after) :
    ScanSt g 0x80002c6c#64 env name out count pn 0x80002c6c#64 sp i
      f nameStr N phiF phiC m0 after :=
  ScanSt.transport hSt h.post.good h.post.tick h.post.mem h.post.pc
    h.post.ra h.abi_frame

/-- Semantic scan data and comparison facts at one reached configuration. -/
structure ScanCompareResult
    (g g' : (R : Register) → Option (RegisterType R))
    (env name out count pn sp pa : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr sa : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (before after : Config)
    extends CompareResult g' pa name sa nameStr before after : Prop where
  scan : ScanSt g 0x80002c6c#64 env name out count pn 0x80002c6c#64 sp i
    f nameStr N phiF phiC m0 after

/-- The actual name-slot load, call, and comparison retain the scan carrier
and the caller's register frame at the same return. -/
theorem scan_compare_state
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g 0x80002c60#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 c) (hi : i < f.vars.length) :
    ∃ after g' pa, ScanCompareResult g g' env name out count pn sp pa i
      f nameStr (f.vars[i]'hi).1 N phiF phiC m0 c after := by
  obtain ⟨after, g', pa, h⟩ := scan_compare g env name out count pn ra sp i
    f nameStr N phiF phiC m0 c hSt hi
  exact ⟨after, g', pa, { toCompareResult := h, scan := CompareResult.scan hSt h }⟩

#print axioms ScanSt.reseat
#print axioms ScanSt.transport
#print axioms CompareResult.scan
#print axioms scan_compare_state

end Vsa.Sim.EnvGetReflected
