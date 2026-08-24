import Vsa.Elf
import Vsa.Sim.InitValues

/-! Decode-table PILOT: one lemma per reachable mnemonic (65), uniform
tactic template. The template is stabilized here before mass generation
of the full 8187-word table (PLAN-InterpSim.md Layer 0 item 4). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Vsa.Sim.DecodePilot

-- add
theorem decode_00a78533
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00a78533#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.rop.ADD)) σ := by
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

-- addi
theorem decode_00158593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00158593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x001#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.ADDI)) σ := by
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

-- addiw
theorem decode_0017071b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0017071b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0x001#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5)) σ := by
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

-- addw
theorem decode_01b78e3b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01b78e3b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x1b#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x1c#5, LeanRV64DExecutable.ropw.ADDW)) σ := by
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

-- and
theorem decode_00b577b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00b577b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.rop.AND)) σ := by
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

-- andi
theorem decode_00377713
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00377713#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x003#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.iop.ANDI)) σ := by
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

-- auipc
theorem decode_07800717
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x07800717#32).run σ =
      .ok (LeanRV64DExecutable.instruction.UTYPE (0x07800#20, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.uop.AUIPC)) σ := by
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

-- beq
theorem decode_00e78663
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00e78663#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x000c#13, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.bop.BEQ)) σ := by
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

-- beqz
theorem decode_02078063
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02078063#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0020#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.bop.BEQ)) σ := by
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

-- bge
theorem decode_0086d463
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0086d463#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0008#13, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.bop.BGE)) σ := by
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

-- bgeu
theorem decode_fca77ee3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfca77ee3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x1fdc#13, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.bop.BGEU)) σ := by
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

-- bgez
theorem decode_fe0558e3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfe0558e3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x1ff0#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.bop.BGE)) σ := by
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

-- bgtz
theorem decode_00f04e63
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00f04e63#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x001c#13, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.bop.BLT)) σ := by
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

-- blez
theorem decode_17305263
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x17305263#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0164#13, LeanRV64DExecutable.regidx.Regidx 0x13#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.bop.BGE)) σ := by
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

-- blt
theorem decode_5ef744e3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x5ef744e3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0de8#13, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.bop.BLT)) σ := by
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

-- bltu
theorem decode_02a76663
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02a76663#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x002c#13, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.bop.BLTU)) σ := by
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

-- bltz
theorem decode_06054063
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x06054063#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0060#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.bop.BLT)) σ := by
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

-- bne
theorem decode_02e79463
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x02e79463#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x0028#13, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.bop.BNE)) σ := by
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

-- bnez
theorem decode_00079663
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00079663#32).run σ =
      .ok (LeanRV64DExecutable.instruction.BTYPE (0x000c#13, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.bop.BNE)) σ := by
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

-- j
theorem decode_0000006f
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0000006f#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x000000#21, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
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

-- jal
theorem decode_20d060ef
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x20d060ef#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JAL (0x006a0c#21, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
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

-- jalr
theorem decode_000b00e7
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x000b00e7#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JALR (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x16#5, LeanRV64DExecutable.regidx.Regidx 0x01#5)) σ := by
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

-- jr
theorem decode_00078067
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00078067#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JALR (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
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

-- lbu
theorem decode_0005c783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0005c783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, true, 1)) σ := by
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

-- ld
theorem decode_00813083
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00813083#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x008#12, LeanRV64DExecutable.regidx.Regidx 0x02#5, LeanRV64DExecutable.regidx.Regidx 0x01#5, false, 8)) σ := by
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

-- lh
theorem decode_01041703
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01041703#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, false, 2)) σ := by
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

-- lhu
theorem decode_01045783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01045783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, true, 2)) σ := by
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

-- li
theorem decode_00000513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00000513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
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

-- lui
theorem decode_00002737
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00002737#32).run σ =
      .ok (LeanRV64DExecutable.instruction.UTYPE (0x00002#20, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.uop.LUI)) σ := by
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

-- lw
theorem decode_0007a783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0007a783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, false, 4)) σ := by
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

-- lwu
theorem decode_00056783
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00056783#32).run σ =
      .ok (LeanRV64DExecutable.instruction.LOAD (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, true, 4)) σ := by
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

-- mv
theorem decode_00060513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00060513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.ADDI)) σ := by
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

-- neg
theorem decode_40b005b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x40b005b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.rop.SUB)) σ := by
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

-- negw
theorem decode_41b00dbb
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x41b00dbb#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x1b#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x1b#5, LeanRV64DExecutable.ropw.SUBW)) σ := by
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

-- not
theorem decode_fff5c593
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0xfff5c593#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0xfff#12, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.iop.XORI)) σ := by
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

-- or
theorem decode_00e7e7b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00e7e7b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.rop.OR)) σ := by
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

-- ori
theorem decode_0017e793
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0017e793#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x001#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.iop.ORI)) σ := by
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

-- ret
theorem decode_00008067
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00008067#32).run σ =
      .ok (LeanRV64DExecutable.instruction.JALR (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x01#5, LeanRV64DExecutable.regidx.Regidx 0x00#5)) σ := by
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

-- sb
theorem decode_00070023
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00070023#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, 1)) σ := by
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

-- sd
theorem decode_00113423
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00113423#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x008#12, LeanRV64DExecutable.regidx.Regidx 0x01#5, LeanRV64DExecutable.regidx.Regidx 0x02#5, 8)) σ := by
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

-- seqz
theorem decode_0017b793
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0017b793#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x001#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.iop.SLTIU)) σ := by
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

-- sext.w
theorem decode_0007861b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0007861b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ADDIW (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5)) σ := by
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

-- sgtz
theorem decode_00b025b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00b025b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.rop.SLT)) σ := by
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

-- sh
theorem decode_00e41823
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00e41823#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x010#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x08#5, 2)) σ := by
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

-- sll
theorem decode_00661633
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00661633#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x06#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.rop.SLL)) σ := by
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

-- slli
theorem decode_03071713
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x03071713#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIOP (0x30#6, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.sop.SLLI)) σ := by
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

-- slliw
theorem decode_0017979b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0017979b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIWOP (0x01#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.sopw.SLLIW)) σ := by
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

-- sllw
theorem decode_008a973b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x008a973b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x08#5, LeanRV64DExecutable.regidx.Regidx 0x15#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.ropw.SLLW)) σ := by
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

-- slt
theorem decode_0138a733
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0138a733#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x13#5, LeanRV64DExecutable.regidx.Regidx 0x11#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.rop.SLT)) σ := by
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

-- slti
theorem decode_00352513
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00352513#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x003#12, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.iop.SLTI)) σ := by
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

-- sltiu
theorem decode_00863613
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00863613#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x008#12, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.iop.SLTIU)) σ := by
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

-- sltu
theorem decode_00e7b733
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00e7b733#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.rop.SLTU)) σ := by
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

-- snez
theorem decode_00b035b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00b035b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x00#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.rop.SLTU)) σ := by
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

-- srai
theorem decode_42065713
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x42065713#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIOP (0x20#6, LeanRV64DExecutable.regidx.Regidx 0x0c#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.sop.SRAI)) σ := by
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

-- sraiw
theorem decode_4023531b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x4023531b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIWOP (0x02#5, LeanRV64DExecutable.regidx.Regidx 0x06#5, LeanRV64DExecutable.regidx.Regidx 0x06#5, LeanRV64DExecutable.sopw.SRAIW)) σ := by
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

-- srl
theorem decode_00d75733
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00d75733#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0d#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.rop.SRL)) σ := by
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

-- srli
theorem decode_01f75793
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01f75793#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIOP (0x1f#6, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.sop.SRLI)) σ := by
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

-- srliw
theorem decode_01f7591b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x01f7591b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.SHIFTIWOP (0x1f#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x12#5, LeanRV64DExecutable.sopw.SRLIW)) σ := by
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

-- srlw
theorem decode_00fad53b
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00fad53b#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x15#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.ropw.SRLW)) σ := by
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

-- sub
theorem decode_40f50533
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x40f50533#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.rop.SUB)) σ := by
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

-- subw
theorem decode_40f705bb
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x40f705bb#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPEW (LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.ropw.SUBW)) σ := by
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

-- sw
theorem decode_00f52023
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00f52023#32).run σ =
      .ok (LeanRV64DExecutable.instruction.STORE (0x000#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0a#5, 4)) σ := by
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

-- xor
theorem decode_00a5c7b3
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00a5c7b3#32).run σ =
      .ok (LeanRV64DExecutable.instruction.RTYPE (LeanRV64DExecutable.regidx.Regidx 0x0a#5, LeanRV64DExecutable.regidx.Regidx 0x0b#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.rop.XOR)) σ := by
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

-- xori
theorem decode_00174713
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00174713#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x001#12, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.regidx.Regidx 0x0e#5, LeanRV64DExecutable.iop.XORI)) σ := by
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

-- zext.b
theorem decode_0ff7f793
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0ff7f793#32).run σ =
      .ok (LeanRV64DExecutable.instruction.ITYPE (0x0ff#12, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.regidx.Regidx 0x0f#5, LeanRV64DExecutable.iop.ANDI)) σ := by
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

end Vsa.Sim.DecodePilot
