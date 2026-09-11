import Vsa.Sim.ValueNullCall
import Vsa.Sim.ClosureBodySites
import Vsa.Sim.rows.CallClosureValueNullCallGen

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Initialize the closure body's return slot through the existing reflected call. -/
theorem closureBodyNull_run (before : Config) (sp : BitVec 64) (N : NativeAddrs)
    (phiC : Addr → Nat)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x80003324#64)
    (spReg : before.σ.regs.get? Register.x2 = some sp)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (code : Code.Eval_exprLoaded before.σ.mem) (loaded : Code.Value_nullLoaded before.σ.mem)
    (region : NullRegion (sp + 144#64)) :
    ∃ after, Steps before after ∧
      ValueNullCallPost callClosureValueNullCallSeg (sp + 144#64) 0x8000332c#64 N phiC before after := by
  have facts : ChainFacts before.σ.mem before.σ.mem (callClosureValueNullCallL sp) []
      callClosureValueNullCallSeg := by
    chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  obtain ⟨called, C⟩ := bridgeOfSegFull callClosureValueNullCallSeg (callClosureValueNullCallL sp) []
    0x80003324#64 0x800027ec#64 0x8000332c#64 before good pc minstret tick
    ⟨spReg, trivial⟩ (by change KeysOK [2]; decide) facts
    (by change ChainOK 0x80003324#64 [2] callClosureValueNullCallSeg; decide)
    (by change KeysOK [10, 2]; decide)
    (by change ∀ n ∈ ([10, 2] : List Nat), n ≠ 1; decide) (by
      intro middle hg ht hp hmi hm _
      have hm' : middle.σ.mem = before.σ.mem := hm.trans (by rfl)
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_80003328_closureBody middle.σ middle.tick middle.steps 0x80003328#64 vm
          hg hp hvm (hm'.symm ▸ code) rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  exact C.valueNull rfl rfl loaded region (by decide) (by decide) N phiC

#print axioms closureBodyNull_run

end Vsa.Sim
