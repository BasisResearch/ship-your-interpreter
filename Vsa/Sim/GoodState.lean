import Vsa.Machine
import Vsa.Sim.InitValues

/-!
# The `GoodState` invariant (Layer 0, item 1)

Pins every piece of control state the Sail model consults on the hot path,
at the values that hold for the bare-metal WHILE binary throughout the run
(`PLAN-InterpSim.md` §Layer 0; values from
`experiments/M1-init-footprint.md` / `Vsa.Sim.InitValues`):

- M-mode, translation decided Bare by privilege, interrupts globally dead
  (`mie = 0` — so `dispatchInterrupt = none` regardless of `mip`, which
  `tick_clock` may set), hart active, HTIF not done, PMP at reset (no
  entry matches; M-mode default-allows), PMA map at reset (RAM
  executable), Zicfilp landing pads not expected.
- Registers the machine itself mutates during a run (`mip`, `mtime`,
  `minstret`, `minstret_increment`, `nextPC`, GPRs, …) are deliberately
  NOT pinned here. Control-plane registers that must merely be *present*
  for `readReg` not to throw, but whose value is irrelevant on the hot
  path, get `∃`-fields. GPR definedness is per-lemma (each instruction
  lemma hypothesizes exactly the registers it touches).

Every field is a `σ.regs.get? R = some v` fact, the only interface the
extensional register map supports (experiment E1g). `GoodState` is
preserved by every hot-path step because none of the pinned registers is
written outside trap/CSR paths; each step-characterization lemma
re-establishes it explicitly.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine (MState)

structure GoodState (σ : MState) : Prop where
  cur_privilege :
    σ.regs.get? Register.cur_privilege = some Privilege.Machine
  misa : σ.regs.get? Register.misa = some initMisa
  mstatus : σ.regs.get? Register.mstatus = some initMstatus
  mie : σ.regs.get? Register.mie = some (0#64)
  mseccfg : σ.regs.get? Register.mseccfg = some (0#64)
  satp : σ.regs.get? Register.satp = some (0#64)
  mtvec : σ.regs.get? Register.mtvec = some (0#64)
  mideleg : σ.regs.get? Register.mideleg = some (0#64)
  medeleg : σ.regs.get? Register.medeleg = some (0#64)
  hart_state : σ.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  htif_done : σ.regs.get? Register.htif_done = some false
  htif_tohost :
    ∃ v, σ.regs.get? Register.htif_tohost = some v
  htif_tohost_base :
    σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base)
  elp : σ.regs.get? Register.elp = some (0#1)
  pmpcfg_n : σ.regs.get? Register.pmpcfg_n = some initPmpcfg
  pmpaddr_n : σ.regs.get? Register.pmpaddr_n = some initPmpaddr
  pma_regions : σ.regs.get? Register.pma_regions = some initPmaRegions
  menvcfg : σ.regs.get? Register.menvcfg = some (0#64)
  mcountinhibit : σ.regs.get? Register.mcountinhibit = some (0#32)
  mcyclecfg : σ.regs.get? Register.mcyclecfg = some (0#64)
  minstretcfg : σ.regs.get? Register.minstretcfg = some (0#64)
  -- present-but-unpinned: written by the machine (tick_clock, postlude)
  -- or read with an irrelevant value on the hot path.
  mip : ∃ v, σ.regs.get? Register.mip = some v
  sig_meip : ∃ v, σ.regs.get? Register.sig_meip = some v
  sig_seip : ∃ v, σ.regs.get? Register.sig_seip = some v
  mtime : ∃ v, σ.regs.get? Register.mtime = some v
  mtimecmp : ∃ v, σ.regs.get? Register.mtimecmp = some v
  minstret : ∃ v, σ.regs.get? Register.minstret = some v
  minstret_increment : ∃ v, σ.regs.get? Register.minstret_increment = some v
  mcycle : ∃ v, σ.regs.get? Register.mcycle = some v
  nextPC : ∃ v, σ.regs.get? Register.nextPC = some v
  PC : ∃ v, σ.regs.get? Register.PC = some v

/-- The PC of a good state (some value exists by `GoodState.PC`; lemmas
pin it with an explicit `σ.regs.get? Register.PC = some pc` hypothesis). -/
abbrev pcOf (σ : MState) (pc : BitVec 64) : Prop :=
  σ.regs.get? Register.PC = some pc

end Vsa.Sim
