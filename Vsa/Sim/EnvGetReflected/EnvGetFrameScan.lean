import Vsa.Sim.EnvGetReflected.EnvGetCountHead
import Vsa.Sim.EnvGetReflected.EnvGetScanStart

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- Frame data independent of whether a names scan has been initialised. -/
structure FrameState (env name out pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Vsa.Sim.Code.Env_getLoaded c.σ.mem
  loadedS : Vsa.Sim.Code.StrcmpLoaded c.σ.mem
  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  out5 : c.σ.regs.get? Register.x21 = some out
  ra1 : c.σ.regs.get? Register.x1 = some ra
  sp2 : c.σ.regs.get? Register.x2 = some sp
  tick : c.tick < 2
  frame : FrameRepr c.σ.mem N phiF phiC env.toNat f
  names : ScanNames c.σ.mem pn.toNat name query f
  signed_count : f.vars.length < 2^31
  names_read : read64 c.σ.mem (env.toNat + 8) = some pn.toNat
  header_lo : 0x80000000 ≤ env.toNat
  header_hi : env.toNat + 32 ≤ 0x100000000
  header_htif : tohostAddr + 8 ≤ env.toNat

/-- The count projection used by the generated outer-loop test. -/
theorem frame_count_read {m : Mem} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {env : Nat} {f : Vsa.While.Frame}
    (h : FrameRepr m N phiF phiC env f) : read32 m env = some f.vars.length := by
  obtain ⟨hcount, _capacity, _arrays, _parent⟩ := h
  exact hcount

/-- The count load preserves the frame state, including uninitialised scans. -/
theorem FrameState.after_count
    {env name out pn ra sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {before after : Config} {empty : Bool}
    (h : FrameState env name out pn ra sp f query N phiF phiC before)
    (hr : CountResult f.vars.length empty before after) :
    FrameState env name out pn ra sp f query N phiF phiC after :=
  { good := hr.good
    loadedG := hr.mem.symm ▸ h.loadedG
    loadedS := hr.mem.symm ▸ h.loadedS
    env4 := (hr.frame Register.x20 (by decide)).trans h.env4
    name3 := (hr.frame Register.x19 (by decide)).trans h.name3
    out5 := (hr.frame Register.x21 (by decide)).trans h.out5
    ra1 := (hr.frame Register.x1 (by decide)).trans h.ra1
    sp2 := (hr.frame Register.x2 (by decide)).trans h.sp2
    tick := hr.tick
    frame := hr.mem.symm ▸ h.frame
    names := hr.mem.symm ▸ h.names
    signed_count := h.signed_count
    names_read := hr.mem.symm ▸ h.names_read
    header_lo := h.header_lo
    header_hi := h.header_hi
    header_htif := h.header_htif }

/-- The positive count branch supplies the complete scan initialisation entry. -/
theorem FrameState.scan_ready
    {env name out pn ra sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {before after : Config}
    (h : FrameState env name out pn ra sp f query N phiF phiC before)
    (hr : CountResult f.vars.length false before after) :
    ScanStartReady env name out (BitVec.ofNat 64 f.vars.length) pn ra sp
      f query N phiF phiC after := by
  have hs := h.after_count hr
  exact
    { good := hs.good
      loadedG := hs.loadedG
      loadedS := hs.loadedS
      pc := hr.pc
      env4 := hs.env4
      name3 := hs.name3
      out5 := hs.out5
      count2 := hr.count2
      ra1 := hs.ra1
      sp2 := hs.sp2
      tick := hs.tick
      frame := hs.frame
      names := hs.names
      count_eq := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.signed_count; omega)]
      names_read := hs.names_read
      header_lo := by have := hs.header_lo; omega
      header_hi := by have := hs.header_hi; omega
      header_htif := Or.inr (by have := hs.header_htif; omega) }

/-- A completed scan retains the frame data with its actual return address. -/
theorem FrameState.after_scan
    {env name out pn ra sp pc scanRa count : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {before after : Config} {i : Nat}
    {g : (R : Register) → Option (RegisterType R)}
    (h : FrameState env name out pn ra sp f query N phiF phiC before)
    (hs : ScanSt g pc env name out count pn scanRa sp i
      f query N phiF phiC before.σ.mem after) :
    FrameState env name out pn scanRa sp f query N phiF phiC after :=
  { good := hs.good
    loadedG := hs.loadedG
    loadedS := hs.loadedS
    env4 := hs.env4
    name3 := hs.name3
    out5 := hs.out5
    ra1 := hs.ra
    sp2 := hs.sp2
    tick := hs.tick
    frame := hs.mem.symm ▸ hs.frame
    names := hs.mem.symm ▸ hs.names
    signed_count := h.signed_count
    names_read := hs.mem.symm ▸ h.names_read
    header_lo := h.header_lo
    header_hi := h.header_hi
    header_htif := h.header_htif }

theorem kept_count : ∀ R, kept R = true → countKeep R = true :=
  kept_of_members (by decide)

section Outcome

variable (env name out pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)

/-- Both an empty frame and an exhausted scan reach the same parent entry. -/
inductive FrameOutcome (c : Config) : Prop where
  | hit {g : (R : Register) → Option (RegisterType R)} {i : Nat}
      (point : ScanLoopPoint env name out (BitVec.ofNat 64 f.vars.length) pn sp
        f query N phiF phiC m0 g 0x80002c70#64 0x80002c6c#64 i c)
      (index : i < f.vars.length)
      (found : f.vars.find? (·.1 == query) = some (f.vars[i]'index))
  | miss {ra : BitVec 64}
      (state : FrameState env name out pn ra sp f query N phiF phiC c)
      (pc : c.σ.regs.get? Register.PC = some 0x80002cc4#64)
      (mem : c.σ.mem = m0)
      (absent : f.vars.find? (·.1 == query) = none)

/-- A complete frame search with caller registers and output retained. -/
structure FrameScanResult (before after : Config) : Prop where
  steps : Steps before after
  outcome : FrameOutcome env name out pn sp f query N phiF phiC m0 after
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R
  output : after.σ.sailOutput = before.σ.sailOutput

end Outcome

/-- Search one frame from the generated count head, including the empty case. -/
theorem frame_scan
    (env name out pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (c : Config)
    (h : FrameState env name out pn ra sp f query N phiF phiC c)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c40#64) :
    ∃ after, FrameScanResult env name out pn sp f query N phiF phiC c.σ.mem c after := by
  obtain ⟨tested, empty, hc⟩ := count_head env f.vars.length c h.good hpc h.tick
    h.env4 h.loadedG h.header_lo (by have := h.header_hi; omega)
    (Or.inr h.header_htif) (frame_count_read h.frame) h.signed_count
  cases empty with
  | true =>
      have hz : f.vars.length = 0 := hc.empty_iff.mp rfl
      have hnone : f.vars.find? (·.1 == query) = none :=
        lookup_scan_miss f.vars query (fun _ hj => False.elim (by omega))
      exact ⟨tested,
        { steps := hc.steps
          outcome := .miss (h.after_count hc) hc.pc hc.mem hnone
          kept_frame := fun R hR => hc.frame R (kept_count R hR)
          output := hc.output }⟩
  | false =>
      have hn : 0 < f.vars.length := by
        have hne : f.vars.length ≠ 0 := by
          intro hz
          have hbad := hc.empty_iff.mpr hz
          cases hbad
        omega
      obtain ⟨after, hs⟩ := scan_frame env name out (BitVec.ofNat 64 f.vars.length)
        pn ra sp f query N phiF phiC tested (h.scan_ready hc) hn
      have houtcome : FrameOutcome env name out pn sp f query N phiF phiC c.σ.mem after := by
        cases hs.outcome with
        | hit hp hi hf =>
            exact .hit (hc.mem ▸ hp) hi hf
        | miss hp ha =>
            exact .miss ((h.after_count hc).after_scan hp.toScanSt) hp.pc
              (hp.mem.trans hc.mem) ha
      exact ⟨after,
        { steps := hc.steps.trans hs.steps
          outcome := houtcome
          kept_frame := fun R hR => (hs.kept_frame R hR).trans (hc.frame R (kept_count R hR))
          output := hs.output.trans hc.output }⟩

#print axioms frame_count_read
#print axioms FrameState.after_count
#print axioms FrameState.scan_ready
#print axioms FrameState.after_scan
#print axioms kept_count
#print axioms frame_scan

end Vsa.Sim.EnvGetReflected
