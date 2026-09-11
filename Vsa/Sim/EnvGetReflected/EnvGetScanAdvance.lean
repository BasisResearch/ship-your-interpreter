import Vsa.Sim.EnvGetReflected.EnvGetScanDecision

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The back-edge preserves fixed scan registers and the return address. -/
def scanAdvanceKeep (R : Register) : Bool := scanFixedKeep R || R == Register.x1

theorem scanAdvanceKeep_noise : ∀ R ∈ noiseRegs, scanAdvanceKeep R = false := by decide

theorem kept_fixed : ∀ R, kept R = true → scanFixedKeep R = true :=
  kept_of_members (by decide)

def scanAdvanceSeg (exhausted : Bool) : List BBlock :=
  if exhausted then env_getX2c54TSeg else env_getX2c54FSeg

def scanAdvancePC (exhausted : Bool) : BitVec 64 :=
  if exhausted then 0x80002cc4#64 else 0x80002c60#64

/-- The generated back-edge advances both live scan registers at one endpoint. -/
structure ScanAdvanceResult
    (env name out count pn ra sp : BitVec 64) (i : Nat) (exhausted : Bool)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (before after : Config) : Prop where
  steps : Steps before after
  scan : ScanSt after.σ.regs.get? (scanAdvancePC exhausted)
    env name out count pn ra sp (i + 1) f nameStr N phiF phiC m0 after
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R
  exhausted_iff : exhausted = true ↔ i + 1 = f.vars.length

/-- Execute index/cursor advancement and its generated count branch. -/
theorem scan_advance
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g 0x80002c54#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 c) (hi : i < f.vars.length) :
    ∃ after exhausted, ScanAdvanceResult env name out count pn ra sp i exhausted
      f nameStr N phiF phiC m0 c after := by
  have hcount := count.isLt
  rw [hSt.count_eq] at hcount
  have hnext : i + 1 < 2^64 := by omega
  have hslots := hSt.names.slotHi i hi
  have hstride : 8 * (i + 1) < 2^64 := by omega
  have hinc := ofNat_succ_bv i hnext
  have hcur := cursor_succ_bv pn i hstride
  let idx := BitVec.ofNat 64 i
  let cursor := pn + BitVec.ofNat 64 (8 * i)
  let L : GRegs := [(8, idx), (9, cursor), (18, count)]
  let selected : GRegs := [(8, BitVec.ofNat 64 (i + 1)),
    (9, pn + BitVec.ofNat 64 (8 * (i + 1)))]
  let exhausted := BitVec.ofNat 64 (i + 1) == count
  have hL : GHolds c.σ L :=
    ⟨by simpa [gprGet] using hSt.idx0,
     by simpa [gprGet] using hSt.cursor1,
     by simpa [gprGet] using hSt.count2, trivial⟩
  have hloaded := hSt.loadedG
  have hbranch : (idx + 1#64 == count) = exhausted := by rw [hinc]
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [] (scanAdvanceSeg exhausted) := by
    generalize he : exhausted = b
    cases b <;> chain_facts hloaded with "Vsa.Sim.Code.env_get_at_" <;>
      simpa only [show sign_extend (m := 64) (0x001#12) = 1#64 from by decide] using
        hbranch.trans he
  have hmemLog : writeLog c.σ.mem
      (evalBlocks (scanAdvanceSeg exhausted) (SegEvalState.init L [])).log = c.σ.mem := by
    generalize exhausted = b
    cases b <;> rfl
  have hpcEval : evalBlocksPC 0x80002c54#64
      (SegEvalState.init L []) (scanAdvanceSeg exhausted) = scanAdvancePC exhausted := by
    generalize exhausted = b
    cases b <;> rfl
  have hproj : GProjects
      (evalBlocks (scanAdvanceSeg exhausted) (SegEvalState.init L [])).regs selected := by
    generalize exhausted = b
    cases b <;> refine ⟨?_, ?_, trivial⟩
    all_goals first
      | change some (idx + sign_extend (m := 64) (0x001#12)) = _
        rw [show sign_extend (m := 64) (0x001#12) = 1#64 from by decide, hinc]
      | change some (cursor + sign_extend (m := 64) (0x008#12)) = _
        rw [show sign_extend (m := 64) (0x008#12) = 8#64 from by decide, hcur]
  obtain ⟨vm, hvm⟩ := hSt.minstret
  obtain ⟨after, h⟩ := segEval_selected_framed (scanAdvanceSeg exhausted) L []
    0x80002c54#64 vm (fun _ => False) scanAdvanceKeep selected c
    hSt.good hSt.pc hvm hL (by show KeysOK [8, 9, 18]; decide) hfacts
    (by generalize exhausted = b; cases b <;> show ChainOK 0x80002c54#64 [8, 9, 18] _ <;> decide)
    hSt.tick (fun _ _ => by rw [hmemLog]) scanAdvanceKeep_noise
    (by generalize exhausted = b; cases b <;> decide) hproj
  have hidx : after.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (i + 1)) := by
    change gprGet after.σ 8 = _
    exact gholds_lookup selected h.selected_regs rfl
  have hcursor : after.σ.regs.get? Register.x9 =
      some (pn + BitVec.ofNat 64 (8 * (i + 1))) := by
    change gprGet after.σ 9 = _
    exact gholds_lookup selected h.selected_regs rfl
  refine ⟨after, exhausted,
    { steps := h.steps
      scan := ScanSt.reseat hSt h.good h.tick (h.mem.trans hmemLog)
        (hpcEval ▸ h.pc) ((h.reg_frame Register.x1 (by decide)).trans hSt.ra)
        hidx hcursor (by omega)
        (fun R hR => h.reg_frame R (by simp [scanAdvanceKeep, hR]))
        (fun _ _ => rfl)
      output := h.output
      kept_frame := fun R hR => h.reg_frame R (by simp [scanAdvanceKeep, kept_fixed R hR])
      exhausted_iff := ?_ }⟩
  change (BitVec.ofNat 64 (i + 1) == count) = true ↔ _
  rw [beq_iff_eq]
  constructor
  · intro heq
    have heqNat := congrArg BitVec.toNat heq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnext, hSt.count_eq] using heqNat
  · intro heq
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnext, hSt.count_eq] using heq

#print axioms scanAdvanceKeep_noise
#print axioms kept_fixed
#print axioms scan_advance

end Vsa.Sim.EnvGetReflected
