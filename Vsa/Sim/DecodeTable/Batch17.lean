import Vsa.Elf
import Vsa.Sim.InitValues

/-! Decode table batch 17 — exit-path extension (generated; regenerate via
/tmp/gen_batch17.py over experiments/exit_path_words.txt, do not hand-edit).
One lemma per unique 32-bit instruction word on the error/exit path
(`main`, `_write`, `__swrite`, `_write_r`, `_lseek_r`, `stdio_exit_handler`,
`_fwalk_sglue`, `vfprintf`) that the interp_run-rooted reachability sweep
missed (M3-setjmp-longjmp.md §1.5.1). Uniform template stabilized in
Vsa/Sim/DecodePilot.lean, identical to Batch01-16. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodeTable

theorem decode_00012623
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00012623#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x00c#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 4)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_0001b817
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0001b817#32).run σ =
      .ok (LeanRV64DExecutable.instruction.UTYPE (0x0001b#20, LeanRV64DExecutable.regidx.Regidx 0x10#5, LeanRV64DExecutable.uop.AUIPC)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00060893
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00060893#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x11#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00068313
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00068313#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x06#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00088613
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00088613#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x11#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00093903
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00093903#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x12#5, LeanRV64DExecutable.regidx.Regidx 0x12#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_000a80e7
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x000a80e7#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JALR (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x15#5, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_000b0b1b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x000b0b1b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x16#5, LeanRV64DExecutable.regidx.Regidx 0x16#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00179493
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00179493#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIOP (0x01#6, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.sop.SLLI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00349493
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00349493#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIOP (0x03#6, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.sop.SLLI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_009404b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x009404b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.rop.ADD)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00c10593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00c10593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x00c#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00c12603
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00c12603#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x00c#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, false, 4)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_00c586b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00c586b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.rop.ADD)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01018613
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01018613#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x03#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01059783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01059783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 2)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01071783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01071783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 2)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01093403
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01093403#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x12#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01241783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01241783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x012#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 2)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01271583
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01271583#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x012#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, false, 2)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01378863
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01378863#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0010#13, LeanRV64DExecutable.regidx.Regidx 0x13#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.bop.BEQ)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_01656b33
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01656b33#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x16#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x16#5, LeanRV64DExecutable.rop.OR)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_02060463
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02060463#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0028#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.bop.BEQ)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_02069863
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02069863#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0030#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_02818513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02818513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x028#12, LeanRV64DExecutable.regidx.Regidx 0x03#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_02fbf063
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02fbf063#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0020#13, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x17#5, LeanRV64DExecutable.bop.BGEU)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_04100513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x04100513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x041#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_04600513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x04600513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x046#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_04f05a63
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x04f05a63#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0054#13, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.bop.BGE)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_0b840413
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0b840413#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x0b8#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_10000693
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x10000693#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x100#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_1007f693
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x1007f693#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x100#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.iop.ANDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_10100713
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x10100713#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x101#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_11010513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x11010513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x110#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_1f010613
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x1f010613#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x1f0#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_2e113c23
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x2e113c23#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x2f8#12, LeanRV64DExecutable.regidx.Regidx 0x01#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_2e813823
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x2e813823#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x2f0#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_2f013403
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x2f013403#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x2f0#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_2f813083
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x2f813083#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x2f8#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x01#5, false, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_30010113
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x30010113#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x300#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_314010ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x314010ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x001314#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_38d010ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x38d010ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x001b8c#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_3ad010ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x3ad010ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x001bac#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_404010ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x404010ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x001404#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_40f484b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x40f484b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.rop.SUB)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_46018413
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x46018413#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x460#12, LeanRV64DExecutable.regidx.Regidx 0x03#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_4dc0106f
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x4dc0106f#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x0014dc#21, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_61c50513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x61c50513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x61c#12, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_6400806f
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x6400806f#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x008640#21, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_874fe0ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x874fe0ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1fe074#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_ae1fc06f
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xae1fc06f#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1fcae0#21, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_b1def0ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xb1def0ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1efb1c#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_c39ef0ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xc39ef0ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1efc38#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_caf83423
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xcaf83423#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0xca8#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x10#5, 8)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_cdc58593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xcdc58593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xcdc#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_d0010113
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xd0010113#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xd00#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_d55ff0ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xd55ff0ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1ffd54#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_e05ff0ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xe05ff0ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x1ffe04#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_fa0912e3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfa0912e3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x1fa4#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x12#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_fb858593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfb858593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfb8#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_fc941ce3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfc941ce3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x1fd8#13, LeanRV64DExecutable.regidx.Regidx 0x09#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_fd858593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfd858593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfd8#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

theorem decode_fed596e3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfed596e3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x1fec#13, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.bop.BNE)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards_matches, encdec_iop_backwards_matches,
    encdec_bop_backwards_matches, encdec_uop_backwards_matches,
    encdec_csrop_backwards_matches, bool_bit_backwards_matches,
    width_enc_backwards_matches,
    encdec_reg_backwards, encdec_iop_backwards, encdec_bop_backwards,
    encdec_uop_backwards, encdec_csrop_backwards, encdec_cbop_backwards,
    encdec_sop_backwards, bool_bit_backwards, width_enc_backwards,
    EStateM.bind, pure, EStateM.pure]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; decide)
    | decide
    | omega

end Vsa.Sim.DecodeTable
