import Vsa.Sim.ClosureReturnJoin
import Vsa.Sim.ClosureReturnSites

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The normal closure return initializes the caller's result through its actual JAL. -/
theorem closureReturnNull_run (before : Config) (sret : BitVec 64) (N : NativeAddrs)
    (phiC : Addr → Nat)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x80003964#64)
    (argument : before.σ.regs.get? Register.x10 = some sret)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (code : Code.Eval_exprLoaded before.σ.mem) (loaded : Code.Value_nullLoaded before.σ.mem)
    (region : NullRegion sret) :
    ∃ after, Steps before after ∧ ValueNullCallPost [] sret 0x80003968#64 N phiC before after := by
  obtain ⟨called, C⟩ := bridgeOfSegFull [] [(10, sret)] []
    0x80003964#64 0x800027ec#64 0x80003968#64 before good pc minstret tick
    ⟨argument, trivial⟩ (by change KeysOK [10]; decide) trivial
    (by change ChainOK 0x80003964#64 [10] []; decide)
    (by change KeysOK [10]; decide)
    (by change ∀ n ∈ ([10] : List Nat), n ≠ 1; decide) (by
      intro middle hg ht hp hmi hm _
      have memory : middle.σ.mem = before.σ.mem := hm
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_80003964_closureReturn middle.σ middle.tick middle.steps 0x80003964#64 vm
          hg hp hvm (memory.symm ▸ code) rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  exact C.valueNull rfl rfl loaded region (by decide) (by decide) N phiC

end Vsa.Sim
