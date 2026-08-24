import Vsa.Sim.InitGoodCommon
import Vsa.Sim.InitValues

/-! # Reset PMP characterization for `init_good` -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

namespace Vsa.Sim

/-- Updating the reset PMP vector with another zero entry is identity. -/
theorem vectorUpdate_initPmpcfg (i : Nat) :
    vectorUpdate initPmpcfg i (0#8) = initPmpcfg := by
  simp [Sail.vectorUpdate, vectorUpdate, initPmpcfg, Vector.set!,
    Array.set!, Array.setIfInBounds]

/-- `reset_pmp` is state-preserving when `pmpcfg_n` is already reset. -/
theorem reset_pmp_zero_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hcfg : σ.regs.get? Register.pmpcfg_n = some initPmpcfg) :
    (reset_pmp ()).run σ = .ok () σ := by
  unfold reset_pmp
  simp only [EStateM.run, forIn, ForIn.forIn, ForIn'.forIn',
    bind, Bind.bind, EStateM.bind, pure, EStateM.pure]
  rw [forIn'_const_estate _ () _ σ ?hbody]
  case hbody =>
    intro i hi c
    cases c
    have hget : initPmpcfg[i]! = (0#8 : BitVec 8) := by
      unfold initPmpcfg
      exact getElem!_replicate_int 64 (0#8) i rfl
    have hentry :
        _update_Pmpcfg_ent_L
          (_update_Pmpcfg_ent_A initPmpcfg[i]!
            (pmpAddrMatchType_encdec_forwards PmpAddrMatchType.OFF)) 0#1 =
          (0#8 : BitVec 8) := by
      rw [hget]
      apply BitVec.eq_of_toNat_eq
      decide
    have hvupdate :
        vectorUpdate initPmpcfg i
          (_update_Pmpcfg_ent_L
            (_update_Pmpcfg_ent_A initPmpcfg[i]!
              (pmpAddrMatchType_encdec_forwards PmpAddrMatchType.OFF)) 0#1) =
          initPmpcfg := by
      rw [hentry]
      exact vectorUpdate_initPmpcfg i.toNat
    have hins : σ.regs.insert Register.pmpcfg_n initPmpcfg = σ.regs :=
      regs_insert_eq_self σ.regs Register.pmpcfg_n initPmpcfg hcfg
    simp only [bind, Bind.bind, EStateM.bind,
      PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
      hcfg, hvupdate, PreSail.writeReg, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, hins,
      pure, EStateM.pure]

end Vsa.Sim
