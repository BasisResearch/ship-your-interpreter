import Vsa.Sim.InitGoodPmp

/-! # `sail_model_init` seed facts for `init_good` -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Sail.ConcurrencyInterfaceV1.PreSail

namespace Vsa.Sim

/-- The pre-reset `misa` value written by `sail_model_init`. -/
def sailInitMisa : BitVec 64 := 0x8000000000000000#64

/-- Facts written by `sail_model_init` which survive `initializeRegisters` or
are read by the later reset. -/
structure SailInitSeed (σ : SequentialState RegisterType trivialChoiceSource) : Prop where
  misa : σ.regs.get? Register.misa = some sailInitMisa
  mstatus : σ.regs.get? Register.mstatus = some initMstatus
  mseccfg : σ.regs.get? Register.mseccfg = some (0#64)
  menvcfg : σ.regs.get? Register.menvcfg = some (0#64)
  sig_meip : σ.regs.get? Register.sig_meip = some (0#1)
  sig_seip : σ.regs.get? Register.sig_seip = some (0#1)
  pc_reset_address : σ.regs.get? Register.pc_reset_address = some (0#64)
  pma_regions : σ.regs.get? Register.pma_regions = some initPmaRegions

private theorem legalize_senvcfg_zero_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some sailInitMisa) :
    (legalize_senvcfg (Mk_SEnvcfg zeros) zeros).run σ = .ok zeros σ := by
  unfold legalize_senvcfg
  simp_all +decide [currentlyEnabled, legalize_xenvcfg_cbie, hartSupports,
    EStateM.run_bind, EStateM.run_pure, EStateM.run_get,
    PreSail.readReg, sailInitMisa, simp_sail]

private theorem legalize_mseccfg_zero_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some sailInitMisa) :
    (legalize_mseccfg (Mk_Seccfg zeros) zeros).run σ = .ok zeros σ := by
  unfold legalize_mseccfg
  simp_all +decide [currentlyEnabled, hartSupports,
    EStateM.run_bind, EStateM.run_pure, EStateM.run_get,
    PreSail.readReg, sailInitMisa, simp_sail]

private theorem legalize_menvcfg_zero_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some sailInitMisa) :
    (legalize_menvcfg (Mk_MEnvcfg zeros) zeros).run σ = .ok zeros σ := by
  unfold legalize_menvcfg
  simp_all +decide [currentlyEnabled, legalize_xenvcfg_cbie, hartSupports,
    EStateM.run_bind, EStateM.run_pure, EStateM.run_get,
    PreSail.readReg, sailInitMisa, simp_sail]

private theorem to_bits_checked_zero_char (l : Nat)
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (to_bits_checked (l := l) 0).run σ = .ok (0#l) σ := by
  simp [to_bits_checked, simp_sail]

/-- A successful `sail_model_init` run establishes exactly the seed facts
needed by the following initializer and reset phases. -/
theorem sail_model_init_seed
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hinit : (sail_model_init ()).run σ = .ok () σ') :
    SailInitSeed σ' := by
  unfold sail_model_init at hinit
  simp +decide [simp_sail, sailInitMisa,
    legalize_senvcfg_zero_char, legalize_mseccfg_zero_char,
    legalize_menvcfg_zero_char, to_bits_checked_zero_char,
    Std.ExtDHashMap.get?_insert] at hinit
  cases hinit
  constructor <;>
    simp +decide [sailInitMisa, initMstatus, initPmaRegions,
      Std.ExtDHashMap.get?_insert, hartSupports, simp_sail]

end Vsa.Sim
