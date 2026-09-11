import Vsa.Sim.EnvGetReflected.EnvGetScanOutcome

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The positive-count branch supplies these observations before the names
pointer and zero index are loaded. Ownership supplies the names carrier. -/
structure ScanStartReady (env name out count pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loadedG : Vsa.Sim.Code.Env_getLoaded c.σ.mem
  loadedS : Vsa.Sim.Code.StrcmpLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some 0x80002c48#64
  env4 : c.σ.regs.get? Register.x20 = some env
  name3 : c.σ.regs.get? Register.x19 = some name
  out5 : c.σ.regs.get? Register.x21 = some out
  count2 : c.σ.regs.get? Register.x18 = some count
  ra1 : c.σ.regs.get? Register.x1 = some ra
  sp2 : c.σ.regs.get? Register.x2 = some sp
  tick : c.tick < 2
  frame : FrameRepr c.σ.mem N phiF phiC env.toNat f
  names : ScanNames c.σ.mem pn.toNat name query f
  count_eq : count.toNat = f.vars.length
  names_read : read64 c.σ.mem (env.toNat + 8) = some pn.toNat
  header_lo : 0x80000000 ≤ env.toNat + 8
  header_hi : env.toNat + 16 ≤ 0x100000000
  header_htif : env.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 8

/-- The reflected initialisation reaches the actual loop head with index zero. -/
structure ScanStartResult (env name out count pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (before after : Config) : Prop where
  steps : Steps before after
  scan : ScanSt after.σ.regs.get? 0x80002c60#64 env name out count pn ra sp 0
    f query N phiF phiC before.σ.mem after
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R
  output : after.σ.sailOutput = before.σ.sailOutput

/-- Execute the generated names-pointer load, zero index, and jump to c60. -/
theorem scan_start
    (env name out count pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (c : Config)
    (hready : ScanStartReady env name out count pn ra sp f query N phiF phiC c) :
    ∃ after, ScanStartResult env name out count pn ra sp f query N phiF phiC c after := by
  let L : GRegs := [(20, env)]
  let load := mkLine 0x80002c48#64 0x008a3483#32
  have hea : (eaddrM load L).toNat = env.toNat + 8 := by
    change (env + sign_extend (m := 64) (0x008#12)).toNat = _
    rw [show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
      BitVec.toNat_add]
    change (env.toNat + 8) % 2^64 = env.toNat + 8
    exact Nat.mod_eq_of_lt (by have := hready.header_hi; omega)
  obtain ⟨bs, hword⟩ := wordLoadFacts_of_read64 c.σ.mem L load pn
    (by rfl) (by rw [hea]; exact hready.header_lo)
    (by rw [hea]; exact hready.header_hi)
    (by rw [hea]; exact hready.header_htif)
    (by rw [hea]; exact hready.names_read)
  have hloaded := hready.loadedG
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [bs] env_getX2c48Seg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_get_at_"
    exact hword.facts
  have hL : GHolds c.σ L := ⟨by simpa [gprGet] using hready.env4, trivial⟩
  have hproj : GProjects
      (evalBlocks env_getX2c48Seg (SegEvalState.init L [bs])).regs [(8, 0#64), (9, pn)] := by
    refine ⟨rfl, ?_, trivial⟩
    change some (bytesVal .ld bs) = some pn
    rw [hword.value]
  obtain ⟨vm, hvm⟩ := hready.good.minstret
  obtain ⟨after, h⟩ := segEval_selected_framed env_getX2c48Seg L [bs]
    0x80002c48#64 vm (fun _ => False) scanAdvanceKeep [(8, 0#64), (9, pn)] c
    hready.good hready.pc hvm hL (by show KeysOK [20]; decide) hfacts
    (by show ChainOK 0x80002c48#64 [20] _; decide) hready.tick
    (fun _ _ => rfl) scanAdvanceKeep_noise (by decide) hproj
  have hmem : after.σ.mem = c.σ.mem := h.mem
  have hidx : after.σ.regs.get? Register.x8 = some (0#64) := by
    change gprGet after.σ 8 = _
    exact gholds_lookup [(8, 0#64), (9, pn)] h.selected_regs rfl
  have hcursor : after.σ.regs.get? Register.x9 = some pn := by
    change gprGet after.σ 9 = _
    exact gholds_lookup [(8, 0#64), (9, pn)] h.selected_regs rfl
  refine ⟨after,
    { steps := h.steps
      scan :=
        { good := h.good
          loadedG := hmem.symm ▸ hready.loadedG
          loadedS := hmem.symm ▸ hready.loadedS
          mem := hmem
          pc := h.pc
          env4 := (h.reg_frame Register.x20 (by decide)).trans hready.env4
          name3 := (h.reg_frame Register.x19 (by decide)).trans hready.name3
          out5 := (h.reg_frame Register.x21 (by decide)).trans hready.out5
          count2 := (h.reg_frame Register.x18 (by decide)).trans hready.count2
          cursor1 := by simpa using hcursor
          idx0 := hidx
          ra := (h.reg_frame Register.x1 (by decide)).trans hready.ra1
          sp2 := (h.reg_frame Register.x2 (by decide)).trans hready.sp2
          minstret := h.minstret
          tick := h.tick
          frame := hready.frame
          names := hready.names
          count_eq := hready.count_eq
          ile := Nat.zero_le _
          ghost := fun _ _ => rfl }
      kept_frame := fun R hR => h.reg_frame R
        (by simp [scanAdvanceKeep, kept_fixed R hR])
      output := h.output }⟩

/-- Initialise and scan a nonempty frame, retaining source lookup and the
caller's frame through the same composed execution. -/
theorem scan_frame
    (env name out count pn ra sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (c : Config)
    (hready : ScanStartReady env name out count pn ra sp f query N phiF phiC c)
    (hne : 0 < f.vars.length) :
    ∃ after, ScanOutcomeResult env name out count pn sp f query N phiF phiC
      c.σ.mem c after := by
  obtain ⟨head, hstart⟩ := scan_start env name out count pn ra sp f query N phiF phiC c hready
  obtain ⟨after, hscan⟩ := scan_outcome env name out count pn sp f query N phiF phiC
    c.σ.mem head.σ.regs.get? ra 0 head hstart.scan hne (ScanPrefixClear.empty f query)
  exact ⟨after,
    { steps := hstart.steps.trans hscan.steps
      outcome := hscan.outcome
      kept_frame := fun R hR => (hscan.kept_frame R hR).trans (hstart.kept_frame R hR)
      output := hscan.output.trans hstart.output }⟩

#print axioms scan_start
#print axioms scan_frame

end Vsa.Sim.EnvGetReflected
