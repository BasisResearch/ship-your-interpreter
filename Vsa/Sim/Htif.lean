import Vsa.Elf
import Vsa.Sim.InitValues
import Vsa.Sim.StateNF

/-!
# Layer 0, item 5 — HTIF `htif_store` characterization

Characterizes the two dispatch outcomes of the HTIF console-mailbox store
`htif_store paddr 8 data` at the `tohost` address (`PLAN-InterpSim.md`
§Layer 0 item 5; `experiments/M2-htif-path.md`):

- `htif_store_putchar`: an 8-byte store of a term-write command word
  `0x0101000000000000 ||| zeroExtend c` latches `tohost`, then dispatches the
  console-`putchar` of byte `c`: it pushes exactly `String.singleton
  (Char.ofNat c.toNat)` to `sailOutput` and runs `reset_htif`. The register
  spine is the two phase-A writes followed by `reset_htif`'s three writes.
- `htif_store_exit`: an 8-byte store of the syscall-exit word `(e <<< 1) ||| 1`
  (with `e.toNat < 2^47`, so the device byte stays `0`) latches `tohost`, then
  sets `htif_done := true` and `htif_exit_code := e`, leaving `sailOutput`
  untouched.

Both are proved at the `htif_store` level — the cleanest reusable interface,
so the Layer-3 store-instruction lemmas can consume the register/`sailOutput`
footprint directly (the lift to `checked_mem_write`/`mem_write_value` is left
as remaining work; see the module footer).

Chain-of-custody of the monad plumbing follows `Vsa/Sim/Hooks.lean`
(`translateAddr_machine_fetch`): a single big `simp only` peel of the
`SailME.run`/`EStateM`/`ExceptT` spine, threading the phase-A `writeReg`s
through the subsequent `readReg`s via the `seval_state` `get?_insert` lemmas
(the register-key disequalities are `Register` constructor disequalities,
discharged by `+decide`). `writeReg` and `print_effect` `modify` distinct
`SequentialState` fields, so their state-updates commute automatically inside
the peel (no separate commuting lemma is needed — the record-update spine keeps
them apart). The bit-level command decoding avoids `bv_decide` (forbidden here);
it routes through the `extract_or_high` helper (byte `c` never reaches bits
`≥ 8`) plus `decide` on the resulting concrete extractions, and the exit
`((e<<<1)|1)>>>1 = e` fact through `getLsbD` reasoning under the width bound.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- A width-8 field extracted at offset `off ≥ 8` from `K ||| zeroExtend c`
(with `c : BitVec 8`) is independent of `c`: the console byte only ever reaches
bits `[0,8)`, so it drops out of the device/cmd fields (`[56,64)` / `[48,56)`).
The single load-bearing bit-fact behind the concrete device/cmd decodings. -/
theorem extract_or_high (K : BitVec 64) (c : BitVec 8) (off : Nat) (hoff : 8 ≤ off) :
    BitVec.extractLsb' off 8 (K ||| BitVec.setWidth 64 c)
      = BitVec.extractLsb' off 8 K := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_setWidth]
  have hcz : c.getLsbD (off + i) = false := BitVec.getLsbD_of_ge c (off + i) (by omega)
  rw [hcz]
  simp only [Bool.and_false, Bool.or_false]

/-- Device byte of the console-putchar command word is `0x01` regardless of the
payload byte `c`. -/
theorem device_putchar (c : BitVec 8) :
    _get_htif_cmd_device (0x0101000000000000#64 ||| BitVec.zeroExtend 64 c) = 0x01#8 := by
  simp only [_get_htif_cmd_device, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.zeroExtend, extract_or_high _ c 56 (by omega)]
  decide

/-- Command byte of the console-putchar command word is `0x01` (write), for any `c`. -/
theorem cmd_putchar (c : BitVec 8) :
    _get_htif_cmd_cmd (0x0101000000000000#64 ||| BitVec.zeroExtend 64 c) = 0x01#8 := by
  simp only [_get_htif_cmd_cmd, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.zeroExtend, extract_or_high _ c 48 (by omega)]
  decide

/-- The low byte of the console-putchar payload is exactly `c`. -/
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

/-- High bits of an exit code fitting in 47 bits are zero: any bit `k ≥ 47` of
`e` is `false` when `e.toNat < 2^47`. The bound that keeps the exit command's
device byte `[63:56]` (and every bit `≥ 47`) at `0`. -/
theorem e_high_zero (e : BitVec 64) (he : e.toNat < 2 ^ 47) (k : Nat) (hk : 47 ≤ k) :
    e.getLsbD k = false := by
  rw [BitVec.getLsbD]
  apply Nat.testBit_lt_two_pow
  have : (2 : Nat) ^ 47 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- `Nat.testBit 1 n = false` for `n > 0` (only bit 0 of `1` is set): used to
kill the `|||1` low-bit contribution above bit 0 in the exit-word decoding. -/
theorem testBit_one_hi (n : Nat) (hn : 0 < n) : Nat.testBit 1 n = false := by
  rcases Bool.eq_false_or_eq_true (Nat.testBit 1 n) with h | h
  · rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; omega
  · exact h

/-- Device byte of the syscall-exit command word `(e <<< 1) ||| 1` is `0x00`
(syscall-proxy) when `e.toNat < 2^47`: bits `[56,64)` come from `e`'s bits
`[55,63)`, all zero under the bound; `|||1` only touches bit 0. -/
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

/-- Bit 0 of the syscall-exit command payload is `1` (the exit-request bit),
for any `e`: `((e <<< 1) ||| 1)` has bit 0 set by the `|||1`. -/
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

/-- The exit code recovered by `htif_store` is exactly `e`:
`(zero_extend payload) >>> 1 = e` when `e.toNat < 2^47`, where the payload is
`(e <<< 1) ||| 1` truncated to 48 bits. The shift drops the injected low bit
and the bound keeps the whole word inside the 48-bit payload window. -/
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
