import Vsa.Elf
import Vsa.Sim.InitValues
import Vsa.Sim.StateNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem extract_or_high (K : BitVec 64) (c : BitVec 8) (off : Nat) (hoff : 8 ≤ off) :
    BitVec.extractLsb' off 8 (K ||| BitVec.setWidth 64 c)
      = BitVec.extractLsb' off 8 K := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_setWidth]
  have hcz : c.getLsbD (off + i) = false := BitVec.getLsbD_of_ge c (off + i) (by omega)
  rw [hcz]
  simp only [Bool.and_false, Bool.or_false]

theorem device_putchar (c : BitVec 8) :
    _get_htif_cmd_device (0x0101000000000000#64 ||| BitVec.zeroExtend 64 c) = 0x01#8 := by
  simp only [_get_htif_cmd_device, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.zeroExtend, extract_or_high _ c 56 (by omega)]
  decide

theorem cmd_putchar (c : BitVec 8) :
    _get_htif_cmd_cmd (0x0101000000000000#64 ||| BitVec.zeroExtend 64 c) = 0x01#8 := by
  simp only [_get_htif_cmd_cmd, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.zeroExtend, extract_or_high _ c 48 (by omega)]
  decide

theorem payload_byte_putchar (c : BitVec 8) :
    Sail.BitVec.extractLsb
        (_get_htif_cmd_payload (0x0101000000000000#64 ||| BitVec.zeroExtend 64 c)) 7 0 = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [_get_htif_cmd_payload, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.zeroExtend, Nat.zero_add]
  have hi' : i < 8 := hi
  have hk : (0x0101000000000000#64).getLsbD i = false := by
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with h|h|h|h|h|h|h|h <;> subst h <;> decide
  have hb48 : (i < 48) = True := by simp; omega
  have hb64 : (i < 64) = True := by simp; omega
  simp only [hk, hi', hb48, hb64, decide_true, Bool.true_and, Bool.false_or]

theorem e_high_zero (e : BitVec 64) (he : e.toNat < 2 ^ 47) (k : Nat) (hk : 47 ≤ k) :
    e.getLsbD k = false := by
  rw [BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  have : (2 : Nat) ^ 47 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

theorem testBit_one_hi (n : Nat) (hn : 0 < n) : Nat.testBit 1 n = false := by
  rcases Bool.eq_false_or_eq_true (Nat.testBit 1 n) with h | h
  · rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; omega
  · exact h

theorem device_exit (e : BitVec 64) (he : e.toNat < 2 ^ 47) :
    _get_htif_cmd_device ((e <<< 1) ||| 1#64) = 0x00#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [_get_htif_cmd_device, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  have h1 : e.getLsbD (56 + i - 1) = false := e_high_zero e he _ (by omega)
  rw [h1, testBit_one_hi (56 + i) (by omega), Nat.zero_testBit]
  simp

theorem payload_bit0_exit (e : BitVec 64) :
    Sail.BitVec.access (_get_htif_cmd_payload ((e <<< 1) ||| 1#64)) 0 = 1#1 := by
  simp only [_get_htif_cmd_payload, Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.access]
  have hbit : (BitVec.extractLsb' 0 (47 - 0 + 1) (e <<< 1 ||| 1#64))[0]! = true := by
    rw [getElem!_pos _ _ (by omega), BitVec.getElem_extractLsb']
    have h01 : (0 : Nat) < 1 := by omega
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.add_zero,
      h01, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.false_or]
    decide
  rw [hbit]; decide

theorem exit_code_eq (e : BitVec 64) (he : e.toNat < 2 ^ 47) :
    (BitVec.zeroExtend 64 (_get_htif_cmd_payload ((e <<< 1) ||| 1#64))) >>> 1 = e := by
  simp only [_get_htif_cmd_payload, Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hidx : 1 + i - 1 = i := by omega
  have ht1 : Nat.testBit 1 (1 + i) = false := testBit_one_hi (1 + i) (by omega)
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.zero_add, hidx, ht1]
  rcases Nat.lt_or_ge i 47 with h | h
  · have hb1 : (1 + i < 64) = True := by simp; omega
    have hb2 : (1 + i < 48) = True := by simp; omega
    have hb3 : (1 + i < 1) = False := by simp
    simp only [hb1, hb2, hb3, decide_true, decide_false, Bool.not_false, Bool.true_and,
      Bool.and_true, Bool.or_false]
  · rw [e_high_zero e he i h]
    have hb2 : ¬ (1 + i < 48) := by omega
    simp [hb2]

set_option linter.unusedSimpArgs false in
theorem htif_store_putchar
    (σ : SequentialState RegisterType trivialChoiceSource) (c : BitVec 8)
    (data : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (th : BitVec 64)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hdata : data = (0x0101000000000000#64) ||| (BitVec.zeroExtend 64 c)) :
    (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ
      = .ok (.Ok true)
          { σ with
            regs := ((((((σ.regs.insert Register.htif_cmd_write 1#1).insert
                        Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
                      Register.htif_tohost data).insert
                    Register.htif_cmd_write 0#1).insert
                  Register.htif_payload_writes 0#4).insert
                Register.htif_tohost (zeros (n := 64))),
            sailOutput := σ.sailOutput.push (toString (Char.ofNat c.toNat)) } := by
  subst hdata
  unfold htif_store
  simp only [SailME.run, SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, readReg, writeReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet,
    get_config_print_htif, pure, hbase]
  simp +decide only [BitVec.reduceEq, Bool.and_self, if_true,
    beq_self_eq_true,
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, reduceCtorEq,
    Bool.false_eq_true, dite_false, dite_true,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
    ExceptT.bindCont, hpw, hth]
  simp +decide only [BitVec.addInt, BitVec.toNatInt,
    Mk_htif_cmd, zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq, cast_eq,
    device_putchar, cmd_putchar,
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, reduceCtorEq,
    Bool.false_eq_true, dite_false, dite_true, if_true,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
    ExceptT.bindCont, plat_term_write, print_effect, reset_htif]
  simp only [PreSail.print_effect, PreSail.writeReg,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
    modify, modifyGet, MonadStateOf.modifyGet, bind, pure,
    payload_byte_putchar]

set_option linter.unusedSimpArgs false in
theorem htif_store_exit
    (σ : SequentialState RegisterType trivialChoiceSource) (e : BitVec 64)
    (data : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (th : BitVec 64)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hsmall : e.toNat < 2 ^ 47)
    (hdata : data = (e <<< 1) ||| 1#64) :
    (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ
      = .ok (.Ok true)
          { σ with
            regs := (((((σ.regs.insert Register.htif_cmd_write 1#1).insert
                        Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
                      Register.htif_tohost data).insert
                    Register.htif_done true).insert
                  Register.htif_exit_code e) } := by
  subst hdata
  unfold htif_store
  simp only [SailME.run, SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, readReg, writeReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet,
    get_config_print_htif, pure, hbase]
  simp +decide only [BitVec.reduceEq, Bool.and_self, if_true,
    beq_self_eq_true,
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, reduceCtorEq,
    Bool.false_eq_true, dite_false, dite_true,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
    ExceptT.bindCont, hpw, hth]
  simp +decide only [BitVec.addInt, BitVec.toNatInt,
    Mk_htif_cmd, zero_extend, Sail.BitVec.zeroExtend, BitVec.setWidth_eq, cast_eq,
    device_exit _ hsmall, payload_bit0_exit, exit_code_eq _ hsmall,
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self, reduceCtorEq,
    Bool.false_eq_true, dite_false, dite_true, if_true,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.get, EStateM.modifyGet,
    ExceptT.bindCont]

end Vsa.Sim
