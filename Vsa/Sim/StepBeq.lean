import Vsa.Sim.Skeleton
import Vsa.Sim.StepAddi

/-!
# M2 branch-class validation — `step_beq` for a concrete BGEU

Step-characterization for the concrete branch word `0x0062f863`
(`bgeu t0, t1, +16` = `bgeu x5, x6, +16`, taken from `_start` at
`0x8000001c`, disassembly at `experiments/disasm.txt:15`). This validates
the generalized `try_step` skeleton (`hnextPC₃ = some npc`) on the control-flow
class: the two source GPRs (`t0 = x5`, `t1 = x6`), the two branch outcomes
(taken ⇒ `nextPC := pc + sext 16` via `jump_to`/`set_next_pc`; not-taken ⇒
`nextPC := pc + 4` unchanged from the `run_hart_active` prelude write), and the
skeleton's PC-insert following the branch-chosen `nextPC`.

Pipeline (mirrors the ADDI pipeline of `StepAddi.lean`):
1. `decode_bgeu_t0_t1` — decode `0x0062f863` ⇒ `BTYPE (16, x6, x5, BGEU)`.
2. `rX_bits_x5` / `rX_bits_x6` — the two source GPR reads.
3. `execute_bgeu_taken` / `execute_bgeu_nottaken` — the BTYPE execute clause,
   both outcomes. The taken clause reads `PC` (for the target) and `misa` (the
   forced `Ext_Zca` read inside `jump_to`), and writes `nextPC := pc + sext 16`
   via `set_next_pc`; the not-taken clause leaves state untouched.
4. `try_step_beq_taken` / `try_step_beq_nottaken` — the skeleton instantiations.

The `+16` offset target is 4-aligned (so `jump_to`'s `assert target[0]==0` and the
`pc[1]`-guarded misaligned-fetch check both discharge from `pc.toNat % 4 = 0`).
The GPR values are universally quantified with the comparison outcome
(`zopz0zKzJ_u v1 v2`, i.e. `t0 ≥u t1`) taken as a hypothesis.

Reuses `StepAddi`'s frame helpers (`get?_afterPrelude`, `get?_afterNextPC`,
`mem_afterPrelude`, `mem_afterNextPC`) via the `Vsa.Sim.StepAddi` import.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Decode -/

/-- Decode of `0x0062f863` = `bgeu t0, t1, +16`: `BTYPE (imm=16, rs2=x6, rs1=x5,
BGEU)`. Same staged shape as `decode_spike_addi` (misa consulted only via
`currentlyEnabled`/`get_xLPE`). -/
theorem decode_bgeu_t0_t1
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x0062f863#32).run σ =
      .ok (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5,
        regidx.Regidx 0x05#5, bop.BGEU)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards, encdec_bop_backwards,
    EStateM.bind, pure, EStateM.pure]
  constructor
  · apply BitVec.eq_of_toNat_eq; decide
  · apply BitVec.eq_of_toNat_eq; decide

/-! ## Source GPR reads (`t0 = x5`, `t1 = x6`) -/

/-- `x5` (`t0`) reads the pinned value, touching no state. -/
theorem rX_bits_x5 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x5 = some v) :
    (rX_bits (regidx.Regidx 0x05#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-- `x6` (`t1`) reads the pinned value, touching no state. -/
theorem rX_bits_x6 (σ : SequentialState RegisterType trivialChoiceSource)
    (v : BitVec 64) (h : σ.regs.get? Register.x6 = some v) :
    (rX_bits (regidx.Regidx 0x06#5)).run σ = .ok v σ := by
  simp only [rX_bits, rX, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    regval_from_reg, Sail.BitVec.toNatInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, h]

/-! ## Branch target alignment -/

/-- The branch target `pc + sext 16` is 4-aligned when `pc` is (so `jump_to`'s
address checks discharge). `sext (0x010#13) = 16#64` and `4 ∣ 2^64`. -/
theorem bgeu_target_align (pc : BitVec 64) (halign : pc.toNat % 4 = 0) :
    (pc + sign_extend (m:=64) (0x010#13 : BitVec 13)).toNat % 4 = 0 := by
  have hs : sign_extend (m:=64) (0x010#13 : BitVec 13) = (16#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs, BitVec.toNat_add]
  have hd : (4 : Nat) ∣ 2^64 := ⟨2^62, by decide⟩
  rw [Nat.mod_mod_of_dvd _ hd]
  have h16 : (16#64).toNat = 16 := by decide
  omega

/-! ## Execute characterization of the BTYPE clause (both outcomes) -/

/-- **Taken** BGEU execute clause: computes `taken = (t0 ≥u t1) = true`, then
`jump_to (pc + sext 16)` ⇒ `set_next_pc` writes `nextPC := pc + sext 16`. Reads
`PC` (target base) and `misa` (the `Ext_Zca` read forced inside `jump_to`, whose
value is short-circuited by `pc[1] = 0`). Result state is the single `nextPC`
insert. -/
theorem execute_bgeu_taken (σ : SequentialState RegisterType trivialChoiceSource)
    (pc v1 v2 : BitVec 64) (vmisa : RegisterType Register.misa)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hx5 : σ.regs.get? Register.x5 = some v1)
    (hx6 : σ.regs.get? Register.x6 = some v2)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) :
    (execute (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5,
        regidx.Regidx 0x05#5, bop.BGEU))).run σ
      = .ok RETIRE_SUCCESS {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m:=64) (0x010#13 : BitVec 13))} := by
  have h5 := rX_bits_x5 σ v1 hx5
  have h6 := rX_bits_x6 σ v2 hx6
  simp only [EStateM.run] at h5 h6
  have htgt := bgeu_target_align pc halign
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [h5]
  simp only [h6, hv, if_true]
  simp only [bind, EStateM.bind, PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, hpc]
  unfold jump_to
  simp only [ext_control_check_pc, LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.bind, EStateM.pure, pure, Pure.pure]
  simp only [LeanRV64DExecutable.assert, PreSail.assert, hb0, beq_self_eq_true, if_true,
    EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, pure, Pure.pure]
  rw [hzca, hb1, show bit_to_bool (0#1 : BitVec 1) = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false,
    set_next_pc, redirect_callback, PreSail.writeReg,
    Bind.bind, EStateM.bind, EStateM.pure, EStateM.map, ExceptT.bindCont, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure]

/-- **Not-taken** BGEU execute clause: `taken = (t0 ≥u t1) = false`, so the
`if taken` guard picks `pure RETIRE_SUCCESS` — no `nextPC` write, state unchanged.
Reads only the two source GPRs. -/
theorem execute_bgeu_nottaken (σ : SequentialState RegisterType trivialChoiceSource)
    (v1 v2 : BitVec 64)
    (hx5 : σ.regs.get? Register.x5 = some v1)
    (hx6 : σ.regs.get? Register.x6 = some v2)
    (hv : zopz0zKzJ_u v1 v2 = false) :
    (execute (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5,
        regidx.Regidx 0x05#5, bop.BGEU))).run σ = .ok RETIRE_SUCCESS σ := by
  have h5 := rX_bits_x5 σ v1 hx5
  have h6 := rX_bits_x6 σ v2 hx6
  simp only [EStateM.run] at h5 h6
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [h5]
  simp only [h6, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## Byte/word facts for the fetch path -/

/-- The little-endian word `0x0062f863` from code bytes `0x63 0xf8 0x62 0x00`. -/
theorem bgeu_bytes_word :
    (((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8) = (0x0062f863#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The BGEU word is non-RVC: its low two bits are `0b11`. -/
theorem bgeu_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## The skeleton's `σ₃` for each branch outcome -/

/-- Taken `σ₃`: `afterNextPC (afterPrelude σ) pc` (which already holds
`nextPC := pc+4` from the `run_hart_active` prelude write) with `nextPC`
overwritten by `jump_to`'s `set_next_pc` to the branch target `pc + sext 16`. -/
abbrev sigma3_taken (σ : MState) (pc : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
      (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))}

/-- Not-taken `σ₃`: the execute clause leaves state untouched, so `σ₃` is exactly
the `run_hart_active` prelude state `afterNextPC (afterPrelude σ) pc` (nextPC = pc+4). -/
abbrev sigma3_nottaken (σ : MState) (pc : BitVec 64) : MState :=
  afterNextPC (afterPrelude σ) pc

/-! ## Shared discharge of the skeleton's instruction-generic hypotheses

`dispatch` / `fetch` / `decode` / `lpad` run on `afterPrelude σ` and are identical
for any word at a good pc; only the code bytes and the decoded `ast` differ from
ADDI. These four `have`s are reproduced inline in each step lemma (the fetch
bytes are the BGEU bytes `0x63 0xf8 0x62 0x00`). -/

/-- **`try_step` on the taken BGEU** (skeleton instantiation, `npc := pc + sext 16`).

`try_step u true` on a `GoodState` at a code pc holding the four BGEU bytes, with
`t0 ≥u t1` (taken), reduces to `pure false` with `nextPC`/`PC` at the branch target
`pc + sext 16` (plus `minstret_increment := true`, `minstret := minstret+1`). -/
theorem try_step_beq_taken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_taken σ pc) with regs := (sigma3_taken σ pc).regs.insert Register.PC (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))}) : MState) with
            regs := (({(sigma3_taken σ pc) with regs := (sigma3_taken σ pc).regs.insert Register.PC (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  have hdisp : (dispatchInterrupt Privilege.Machine).run (afterPrelude σ)
      = .ok none (afterPrelude σ) :=
    dispatch_none (afterPrelude σ) vmip vmeip vseip _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mie)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmeip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hseip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mideleg)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
  have hfetch : (fetch ()).run (afterPrelude σ)
      = .ok (FetchResult.F_Base ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))) (afterPrelude σ) := by
    have := fetch_F_Base (afterPrelude σ) pc (0x63#8) (0xf8#8) (0x62#8) (0x00#8)
      _ _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hpc)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pma_regions)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpcfg_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpaddr_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.htif_tohost_base)
      hlo hhi halign
      (by rw [mem_afterPrelude]; exact hb0) (by rw [mem_afterPrelude]; exact hb1)
      (by rw [mem_afterPrelude]; exact hb2) (by rw [mem_afterPrelude]; exact hb3)
      bgeu_notrvc
    exact this
  have hdec : (ext_decode ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))).run (afterPrelude σ)
      = .ok (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU)) (afterPrelude σ) := by
    rw [show ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8)) = (0x0062f863#32 : BitVec 32) from bgeu_bytes_word]
    exact decode_bgeu_t0_t1 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  -- execute (taken) on afterNextPC (afterPrelude σ) pc ⇒ sigma3_taken
  have hexec : (execute (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_taken σ pc) :=
    execute_bgeu_taken (afterNextPC (afterPrelude σ) pc) pc v1 v2 _
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx5)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx6)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa)
      halign hv
  -- postlude read-backs on sigma3_taken
  have hhart₃ : (sigma3_taken σ pc).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.hart_state = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.hart_state) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_taken σ pc).regs.get? Register.nextPC = some (pc + sign_extend (m := 64) (0x010#13 : BitVec 13)) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_taken σ pc).regs.get? Register.minstret_increment = some true := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_taken σ pc).regs.get? Register.minstret = some vminstret := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))
    ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))
    (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU))
    (sigma3_taken σ pc) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-- **`try_step` on the not-taken BGEU** (skeleton instantiation, `npc := pc + 4`).

`try_step u true` on a `GoodState` at a code pc holding the four BGEU bytes, with
`¬(t0 ≥u t1)` (not taken), reduces to `pure false` with `nextPC`/`PC` at the
fall-through `pc + 4` (the `run_hart_active` prelude write, undisturbed by the
execute clause). -/
theorem try_step_beq_nottaken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = false) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_nottaken σ pc) with regs := (sigma3_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3_nottaken σ pc) with regs := (sigma3_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  have hdisp : (dispatchInterrupt Privilege.Machine).run (afterPrelude σ)
      = .ok none (afterPrelude σ) :=
    dispatch_none (afterPrelude σ) vmip vmeip vseip _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mie)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hmeip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hseip)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mideleg)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
  have hfetch : (fetch ()).run (afterPrelude σ)
      = .ok (FetchResult.F_Base ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))) (afterPrelude σ) := by
    have := fetch_F_Base (afterPrelude σ) pc (0x63#8) (0xf8#8) (0x62#8) (0x00#8)
      _ _ _
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hpc)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mstatus)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pma_regions)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpcfg_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.pmpaddr_n)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.htif_tohost_base)
      hlo hhi halign
      (by rw [mem_afterPrelude]; exact hb0) (by rw [mem_afterPrelude]; exact hb1)
      (by rw [mem_afterPrelude]; exact hb2) (by rw [mem_afterPrelude]; exact hb3)
      bgeu_notrvc
    exact this
  have hdec : (ext_decode ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))).run (afterPrelude σ)
      = .ok (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU)) (afterPrelude σ) := by
    rw [show ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8)) = (0x0062f863#32 : BitVec 32) from bgeu_bytes_word]
    exact decode_bgeu_t0_t1 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  -- execute (not taken) on afterNextPC (afterPrelude σ) pc ⇒ state unchanged
  have hexec : (execute (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_nottaken σ pc) :=
    execute_bgeu_nottaken (afterNextPC (afterPrelude σ) pc) v1 v2
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx5)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx6)
      hv
  -- postlude read-backs on sigma3_nottaken (= afterNextPC (afterPrelude σ) pc)
  have hhart₃ : (sigma3_nottaken σ pc).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    show (afterNextPC (afterPrelude σ) pc).regs.get? Register.hart_state = _
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_nottaken σ pc).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_nottaken σ pc).regs.get? Register.minstret_increment = some true := by
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_nottaken σ pc).regs.get? Register.minstret = some vminstret := by
    show (afterNextPC (afterPrelude σ) pc).regs.get? Register.minstret = _
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    ((((0x00#8).append (0x62#8)).append (0xf8#8)).append (0x63#8))
    (instruction.BTYPE (0x010#13, regidx.Regidx 0x06#5, regidx.Regidx 0x05#5, bop.BGEU))
    (sigma3_nottaken σ pc) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## `Machine.Step` wrappers (no clock tick) with `GoodState` preservation

The branch write-set is `{minstret_increment, nextPC, PC, minstret}` — note no GPR
`rd` is written (branches have no destination register), so unlike ADDI there is
no `x10` key. The taken/not-taken final states differ in shape (the taken `σ₃`
carries an extra `nextPC := target` insert), so each outcome gets its own
`sigmaPost`, frame lemma, and `GoodState`/`htif_done` re-establishment. -/

/-- Taken final state (skeleton `σ₅`): the write chain
`minstret_increment := true`, `nextPC := pc+4`, `nextPC := target`, `PC := target`,
`minstret := v+1`, with `target = pc + sext 16`. -/
abbrev sigmaPost_taken (σ : MState) (pc vminstret : BitVec 64) : MState :=
  {(({(sigma3_taken σ pc) with regs := (sigma3_taken σ pc).regs.insert Register.PC (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))}) : MState) with
    regs := (({(sigma3_taken σ pc) with regs := (sigma3_taken σ pc).regs.insert Register.PC (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Not-taken final state (skeleton `σ₅`): the write chain
`minstret_increment := true`, `nextPC := pc+4`, `PC := pc+4`, `minstret := v+1`. -/
abbrev sigmaPost_nottaken (σ : MState) (pc vminstret : BitVec 64) : MState :=
  {(({(sigma3_nottaken σ pc) with regs := (sigma3_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_nottaken σ pc) with regs := (sigma3_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Read-back of a register outside the taken write-set `{minstret, PC, nextPC,
minstret_increment}` through the taken write chain equals reading from `σ`. -/
theorem get?_sigmaPost_taken (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_taken σ pc vminstret).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_taken σ pc).regs.insert Register.PC (pc + sign_extend (m := 64) (0x010#13 : BitVec 13))).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h4, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R h4 h5

/-- Read-back of a register outside the not-taken write-set `{minstret, PC, nextPC,
minstret_increment}` through the not-taken write chain equals reading from `σ`. -/
theorem get?_sigmaPost_nottaken (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_nottaken σ pc vminstret).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (afterNextPC (afterPrelude σ) pc).regs.get? R = _
  exact get?_afterNextPC σ pc R h4 h5

/-- `GoodState` is preserved by the taken BGEU step (the write-set is disjoint from
every pinned field; the `∃`-fields — including the mutated `nextPC`/`PC`/`minstret`
/`minstret_increment` — hold at their new values). -/
theorem goodstate_sigmaPost_taken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost_taken σ pc vminstret) := by
  constructor
  case cur_privilege => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.cur_privilege
  case misa => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.misa
  case mstatus => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mstatus
  case mie => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mie
  case mseccfg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mseccfg
  case satp => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.satp
  case mtvec => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mtvec
  case mideleg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mideleg
  case medeleg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.medeleg
  case hart_state => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.hart_state
  case htif_done => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done
  case htif_tohost => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost
  case htif_tohost_base => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost_base
  case elp => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.elp
  case pmpcfg_n => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpaddr_n
  case pma_regions => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pma_regions
  case menvcfg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.menvcfg
  case mcountinhibit => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mcountinhibit
  case mcyclecfg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mcyclecfg
  case minstretcfg => rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.minstretcfg
  case mip => obtain ⟨v, hv⟩ := hG.mip; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_meip => obtain ⟨v, hv⟩ := hG.sig_meip; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_seip => obtain ⟨v, hv⟩ := hG.sig_seip; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtime => obtain ⟨v, hv⟩ := hG.mtime; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtimecmp => obtain ⟨v, hv⟩ := hG.mtimecmp; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mcycle => obtain ⟨v, hv⟩ := hG.mcycle; exact ⟨v, by rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case minstret => exact ⟨BitVec.addInt vminstret 1, by
    show ((((sigma3_taken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case minstret_increment => exact ⟨true, by
    show ((((sigma3_taken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case nextPC => exact ⟨pc + sign_extend (m := 64) (0x010#13 : BitVec 13), by
    show ((((sigma3_taken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case PC => exact ⟨pc + sign_extend (m := 64) (0x010#13 : BitVec 13), by
    show ((((sigma3_taken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]⟩

/-- `GoodState` is preserved by the not-taken BGEU step. -/
theorem goodstate_sigmaPost_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost_nottaken σ pc vminstret) := by
  constructor
  case cur_privilege => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.cur_privilege
  case misa => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.misa
  case mstatus => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mstatus
  case mie => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mie
  case mseccfg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mseccfg
  case satp => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.satp
  case mtvec => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mtvec
  case mideleg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mideleg
  case medeleg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.medeleg
  case hart_state => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.hart_state
  case htif_done => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done
  case htif_tohost => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost
  case htif_tohost_base => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost_base
  case elp => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.elp
  case pmpcfg_n => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpaddr_n
  case pma_regions => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.pma_regions
  case menvcfg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.menvcfg
  case mcountinhibit => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mcountinhibit
  case mcyclecfg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.mcyclecfg
  case minstretcfg => rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.minstretcfg
  case mip => obtain ⟨v, hv⟩ := hG.mip; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_meip => obtain ⟨v, hv⟩ := hG.sig_meip; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_seip => obtain ⟨v, hv⟩ := hG.sig_seip; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtime => obtain ⟨v, hv⟩ := hG.mtime; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtimecmp => obtain ⟨v, hv⟩ := hG.mtimecmp; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mcycle => obtain ⟨v, hv⟩ := hG.mcycle; exact ⟨v, by rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case minstret => exact ⟨BitVec.addInt vminstret 1, by
    show ((((sigma3_nottaken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case minstret_increment => exact ⟨true, by
    show ((((sigma3_nottaken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case nextPC => exact ⟨BitVec.addInt pc 4, by
    show ((((sigma3_nottaken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case PC => exact ⟨BitVec.addInt pc 4, by
    show ((((sigma3_nottaken σ pc).regs.insert Register.PC _).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]⟩

/-- `htif_done` reads back `false` on the taken final state (not in the write-set). -/
theorem htif_done_sigmaPost_taken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : (sigmaPost_taken σ pc vminstret).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_taken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done

/-- `htif_done` reads back `false` on the not-taken final state. -/
theorem htif_done_sigmaPost_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : (sigmaPost_nottaken σ pc vminstret).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done

/-! ## `stepOnce` and `Machine.Step` (no clock tick) -/

/-- `stepOnce u u` on the taken BGEU (`i+1 ≠ 2`): `try_step` (⇒ `false`, branch
target written to PC), then continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_beq_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_taken σ pc vminstret) := by
  have hts := try_step_beq_taken σ u pc vminstret v1 v2 hG hpc hminstret hx5 hx6 hb0 hb1 hb2 hb3 hlo hhi halign hv
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_taken σ pc vminstret hG
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = false := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_eq_false_iff_ne]
    exact htick
  simp only [htick', Bool.false_eq_true, if_false, EStateM.pure]

/-- `stepOnce u u` on the not-taken BGEU (`i+1 ≠ 2`): `try_step` (⇒ `false`,
`pc+4` written to PC), then continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_beq_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = false) (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_nottaken σ pc vminstret) := by
  have hts := try_step_beq_nottaken σ u pc vminstret v1 v2 hG hpc hminstret hx5 hx6 hb0 hb1 hb2 hb3 hlo hhi halign hv
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_nottaken σ pc vminstret hG
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = false := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_eq_false_iff_ne]
    exact htick
  simp only [htick', Bool.false_eq_true, if_false, EStateM.pure]

/-- **`step_beq` (taken, no clock tick).** One architectural step of the Sail
model on the taken BGEU, wrapped as `Vsa.Machine.Step`, with `GoodState`
preserved. `σ'` is the branch write chain (PC/nextPC at `pc + sext 16`). -/
theorem step_beq_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_taken σ pc vminstret, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_taken σ pc vminstret) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_beq_taken_notick σ i u pc vminstret v1 v2 hG hpc hminstret hx5 hx6 hb0 hb1 hb2 hb3 hlo hhi halign hv htick),
   goodstate_sigmaPost_taken σ pc vminstret hG⟩

/-- **`step_beq` (not taken, no clock tick).** As above on the fall-through: `σ'`
holds PC/nextPC at `pc + 4`. -/
theorem step_beq_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v1 v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx5 : σ.regs.get? Register.x5 = some v1) (hx6 : σ.regs.get? Register.x6 = some v2)
    (hb0 : σ.mem[pc.toNat]? = some (0x63#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0xf8#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x62#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = false) (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_nottaken σ pc vminstret, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_nottaken σ pc vminstret) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_beq_nottaken_notick σ i u pc vminstret v1 v2 hG hpc hminstret hx5 hx6 hb0 hb1 hb2 hb3 hlo hhi halign hv htick),
   goodstate_sigmaPost_nottaken σ pc vminstret hG⟩

end Vsa.Sim
