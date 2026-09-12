import EnvGetFrameScan
import EnvGetParentBranch
import EnvGetOwnedNames

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Machine observations retained by prologue and parent descent. -/
structure FrameRegisters (env name out ra sp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Vsa.Sim.Code.Env_getLoaded c.σ.mem
  loadedS : Vsa.Sim.Code.StrcmpLoaded c.σ.mem
  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  out5 : c.σ.regs.get? Register.x21 = some out
  ra1 : c.σ.regs.get? Register.x1 = some ra
  sp2 : c.σ.regs.get? Register.x2 = some sp
  tick : c.tick < 2

/-- The actual parent load retains the query, destination, stack, and link. -/
theorem FrameRegisters.after_parent
    {env parent name out ra sp : BitVec 64} {present : Bool} {before after : Config}
    (h : FrameRegisters env name out ra sp before)
    (hp : ParentResult parent present before after) :
    FrameRegisters parent name out ra sp after :=
  { good := hp.good
    loadedG := hp.mem.symm ▸ h.loadedG
    loadedS := hp.mem.symm ▸ h.loadedS
    env4 := hp.env
    name3 := (hp.frame Register.x19 (by decide)).trans h.name3
    out5 := (hp.frame Register.x21 (by decide)).trans h.out5
    ra1 := (hp.frame Register.x1 (by decide)).trans h.ra1
    sp2 := (hp.frame Register.x2 (by decide)).trans h.sp2
    tick := hp.tick }

/-- Forget scan-specific data while retaining the reached machine pins. -/
theorem FrameState.registers
    {env name out pn ra sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {c : Config}
    (h : FrameState env name out pn ra sp f query N phiF phiC c) :
    FrameRegisters env name out ra sp c :=
  { good := h.good
    loadedG := h.loadedG
    loadedS := h.loadedS
    env4 := h.env4
    name3 := h.name3
    out5 := h.out5
    ra1 := h.ra1
    sp2 := h.sp2
    tick := h.tick }

/-- An allocated source frame supplies the complete outer-loop state.
The caller provides ownership and array readiness at the reached memory,
the owned query string, and the fixed comparison mask. -/
theorem owned_frame_state
    {env name out ra sp : BitVec 64} {query : String} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Vsa.While.Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {s : Vsa.While.Store} {fa : Vsa.While.Addr} {c : Config}
    (hregs : FrameRegisters env name out ra sp c)
    (hown : StoreOwned c.σ.mem phiF phiC alloc shared s)
    (hrepr : StoreRepr c.σ.mem N A phiF phiC s)
    (hready : StoreArraysReady c.σ.mem phiF s)
    (hl : Ledger A exts alloc) (hgeom : SharedReadGeom shared SL)
    (hlo : 0x80000000 ≤ A.lo) (hhi : A.hi ≤ 0x100000000)
    (hht : tohostAddr + 8 ≤ A.lo)
    (hquery : SharedCString c.σ.mem shared name.toNat query)
    (hmask : MaskPinned c.σ.mem)
    (hfa : fa < s.frames.size) (henv : env.toNat = phiF fa) :
    ∃ pn, FrameState env name out pn ra sp s.frames[fa] query N phiF phiC c := by
  have hfo := hown.frames fa hfa
  have hfr := hrepr.frames fa hfa
  have hheader := (hrepr.frames_arena fa hfa).1
  obtain ⟨arrays, ha⟩ := hfo.arrays
  have hpn : (BitVec.ofNat 64 arrays.names).toNat = arrays.names := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (read64_lt_eg4 c.σ.mem (phiF fa + 8) arrays.names ha.namesRead)]
  have hnames := hfo.scanNames hl hgeom hlo hhi hht ha.namesRead
    (hready.namesAligned fa hfa arrays.names ha.namesRead) hquery hmask
  refine ⟨BitVec.ofNat 64 arrays.names,
    { good := hregs.good
      loadedG := hregs.loadedG
      loadedS := hregs.loadedS
      env4 := hregs.env4
      name3 := hregs.name3
      out5 := hregs.out5
      ra1 := hregs.ra1
      sp2 := hregs.sp2
      tick := hregs.tick
      frame := by rw [henv]; exact hfr
      names := by rw [hpn]; exact hnames
      signed_count := hfo.length_signed hl hhi
      names_read := by rw [hpn, henv]; exact ha.namesRead
      header_lo := ?_
      header_hi := ?_
      header_htif := ?_ }⟩
  · rw [henv]
    exact Nat.le_trans hlo hheader.1
  · rw [henv]
    exact Nat.le_trans hheader.2 hhi
  · rw [henv]
    exact Nat.le_trans hht hheader.1

#print axioms FrameRegisters.after_parent
#print axioms FrameState.registers
#print axioms owned_frame_state

end Vsa.Sim.EnvGetReflected
