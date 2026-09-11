import Vsa.Sim.EnvGetReflected.EnvGetScanLoop

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

section Outcome

variable (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)

/-- A scan exit exposes the same binding selected by source lookup, or the
absence of a binding before descending to the parent. -/
inductive ScanOutcome (c : Config) : Prop where
  | hit {g : (R : Register) → Option (RegisterType R)} {i : Nat}
      (point : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
        g 0x80002c70#64 0x80002c6c#64 i c)
      (index : i < f.vars.length)
      (found : f.vars.find? (·.1 == query) = some (f.vars[i]'index))
  | miss {g : (R : Register) → Option (RegisterType R)}
      (point : ScanLoopPoint env name out count pn sp f query N phiF phiC m0
        g 0x80002cc4#64 0x80002c6c#64 f.vars.length c)
      (absent : f.vars.find? (·.1 == query) = none)

/-- The source lookup result, machine frame, and output share one exit. -/
structure ScanOutcomeResult (before after : Config) : Prop where
  steps : Steps before after
  outcome : ScanOutcome env name out count pn sp f query N phiF phiC m0 after
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R
  output : after.σ.sailOutput = before.σ.sailOutput

end Outcome

/-- Eliminate the loop head and connect the terminal scan to source lookup. -/
theorem ScanLoopExit.outcome
    {env name out count pn sp : BitVec 64}
    {f : Vsa.While.Frame} {query : String} {N : NativeAddrs}
    {phiF phiC : Vsa.While.Addr → Nat} {m0 : Mem} {before after : Config}
    (h : ScanLoopExit env name out count pn sp f query N phiF phiC m0 before after) :
    ScanOutcome env name out count pn sp f query N phiF phiC m0 after := by
  cases h.position with
  | head hp hi => exact False.elim (h.exited hp.pc)
  | hit hp hi hfound =>
      exact .hit hp hi (lookup_first_match f.vars query _ hi
        (fun j hj => hp.earlier j (Nat.lt_trans hj hi) hj) hfound)
  | miss hp =>
      exact .miss hp (lookup_scan_miss f.vars query (fun j hj => hp.earlier j hj hj))

/-- Run the scan and retain its source lookup result at the actual endpoint. -/
theorem scan_outcome
    (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (query : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (ra : BitVec 64) (i : Nat)
    (c : Config)
    (hscan : ScanSt g 0x80002c60#64 env name out count pn ra sp i f query N phiF phiC m0 c)
    (hi : i < f.vars.length) (hclear : ScanPrefixClear f query i) :
    ∃ after, ScanOutcomeResult env name out count pn sp f query N phiF phiC m0 c after := by
  obtain ⟨after, hsteps, hexit⟩ := scan_loop env name out count pn sp f query N
    phiF phiC m0 g ra i c hscan hi hclear
  exact ⟨after, hsteps, hexit.outcome, hexit.kept_frame, hexit.output⟩

#print axioms ScanLoopExit.outcome
#print axioms scan_outcome

end Vsa.Sim.EnvGetReflected
