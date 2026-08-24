import Vsa.Sim.Skeleton

/-!
# M1 GATE — `step_addi` end-to-end

The go/no-go gate of `PLAN-InterpSim.md` §Layer 0: one full architectural step
of the Sail RV64D model, driven entirely through the proved Layer-0 lemma
interfaces, for the spike word `0x00000513` = `addi x10, x0, 0` (little-endian
code bytes `0x13 0x05 0x00 0x00`).

`stepOnce i u` (`Vsa/Elf.lean`) on a `GoodState`:
1. reads `htif_done = false` ⇒ take the `try_step` branch;
2. `try_step u true` reduces (via `try_step_execute_char`) to `pure false` with
   the five-write state chain `σ₅` (minstret_increment, nextPC, x10, PC, minstret);
3. `stepped = false` ⇒ skip `cycle_count`;
4. reads `htif_done` again (still `false` — untouched by the step) ⇒ continue;
5. `i+1 == plat_insns_per_tick (= 2)`? — the two lemmas below split on this:
   `step_addi_notick` (`i+1 ≠ 2`, no clock tick) and `step_addi_tick`
   (`i+1 = 2`, splices `tick_clock` via `tick_clock_char`).

The four `try_step_execute_char` step-hypotheses are discharged by rewriting the
proved `dispatch_none` / `fetch_F_Base` / `decode_spike_addi` /
`execute_addi_x0_x10` lemmas onto the insert-chain states; their `σ.regs.get?`
side conditions come from the `GoodState` projections framed through the
`minstret_increment := true` (and, for execute, `nextPC := pc+4`) inserts via
`seval_state` read-over-write (none of the read registers is written).

`GoodState σ'` is re-established by constructing the record: the ~30 pinned
fields read through the write chain (none of `minstret_increment`, `nextPC`,
`x10`, `PC`, `minstret`, or the tick registers `mcycle`/`mtime`/`mip` is pinned),
and the `∃`-fields with their new values, all discharged by `goodstate_step_frame`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Reading a register `R ≠ minstret_increment` through the prelude write is the
same as reading it from `σ`. Frames every `GoodState`/mem hypothesis of the
delegated dispatch/fetch/decode/lpad lemmas onto `afterPrelude σ`. -/
theorem get?_afterPrelude (σ : MState) (R : Register)
    (hne : (Register.minstret_increment == R) = false) :
    (afterPrelude σ).regs.get? R = σ.regs.get? R := by
  show (σ.regs.insert Register.minstret_increment true).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne, dif_neg, reduceCtorEq, not_false_eq_true]

/-- The prelude write leaves memory untouched. -/
theorem mem_afterPrelude (σ : MState) : (afterPrelude σ).mem = σ.mem := rfl

/-- Reading a register `R ∉ {minstret_increment, nextPC}` through the prelude and
`nextPC := pc+4` writes is the same as reading it from `σ`. -/
theorem get?_afterNextPC (σ : MState) (pc : BitVec 64) (R : Register)
    (hne1 : (Register.nextPC == R) = false)
    (hne2 : (Register.minstret_increment == R) = false) :
    (afterNextPC (afterPrelude σ) pc).regs.get? R = σ.regs.get? R := by
  show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne1, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterPrelude σ R hne2

/-- The prelude + nextPC writes leave memory untouched. -/
theorem mem_afterNextPC (σ : MState) (pc : BitVec 64) :
    (afterNextPC (afterPrelude σ) pc).mem = σ.mem := rfl

/-- The little-endian spike word `addi x10, x0, 0` = `0x00000513`, assembled from
the four code bytes `0x13 0x05 0x00 0x00`. -/
theorem addi_bytes_word :
    (((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8) = (0x00000513#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The spike word is non-RVC: its low two bits are `0b11`. -/
theorem addi_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The state after `execute (addi x10, x0, 0)` in the skeleton: the prelude +
`nextPC := pc+4` state with `x10 := 0 + sext 0x000`. This is the skeleton's `σ₃`
for ADDI. -/
abbrev sigma3 (σ : MState) (pc : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.x10
      (0#64 + sign_extend (m := 64) (0x000#12 : BitVec 12))}

/-- **`try_step` on the ADDI spike, end-to-end** (skeleton instantiation).

`try_step u true` on a `GoodState` at a code pc holding the four ADDI bytes
reduces to `pure false` with the explicit five-write chain
`minstret_increment := true`, `nextPC := pc+4`, `x10 := 0 + sext 0`,
`PC := pc+4`, `minstret := minstret+1`. -/
theorem try_step_addi
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some (0x13#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x05#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3 σ pc) with regs := (sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3 σ pc) with regs := (sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  -- dispatch on afterPrelude σ
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
  -- fetch on afterPrelude σ (bytes framed through mem, unchanged)
  have hfetch : (fetch ()).run (afterPrelude σ)
      = .ok (FetchResult.F_Base ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8))) (afterPrelude σ) := by
    have := fetch_F_Base (afterPrelude σ) pc (0x13#8) (0x05#8) (0x00#8) (0x00#8)
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
      addi_notrvc
    exact this
  -- decode on afterPrelude σ
  have hdec : (ext_decode ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8))).run (afterPrelude σ)
      = .ok (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI)) (afterPrelude σ) := by
    rw [show ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8)) = (0x00000513#32 : BitVec 32) from addi_bytes_word]
    exact decode_spike_addi (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
  -- landing-pad on afterPrelude σ
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  -- execute on afterNextPC (afterPrelude σ) pc ⇒ σ₃
  have hexec : (execute (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3 σ pc) :=
    execute_addi_x0_x10 (afterNextPC (afterPrelude σ) pc) (0x000#12)
  -- postlude read-backs on σ₃
  have hhart₃ : (sigma3 σ pc).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.hart_state = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.hart_state) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3 σ pc).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3 σ pc).regs.get? Register.minstret_increment = some true := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3 σ pc).regs.get? Register.minstret = some vminstret := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.minstret) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hminstret
  -- assemble the skeleton
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4) ((((0x00#8).append (0x00#8)).append (0x05#8)).append (0x13#8))
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x0a#5, iop.ADDI))
    (sigma3 σ pc) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-- The `try_step`-final state (the skeleton's `σ₅`) for the ADDI spike:
`minstret_increment := true`, `nextPC := pc+4`, `x10 := 0 + sext 0`, `PC := pc+4`,
`minstret := minstret+1`. -/
abbrev sigmaPost (σ : MState) (pc vminstret : BitVec 64) : MState :=
  {(({(sigma3 σ pc) with regs := (sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3 σ pc) with regs := (sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Reading a register outside the five written keys `{minstret, PC, x10, nextPC,
minstret_increment}` through the ADDI step's write chain is the same as reading
it from `σ`. Frames the whole `GoodState` record onto `sigmaPost`. -/
theorem get?_sigmaPost (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false)
    (h2 : (Register.PC == R) = false)
    (h3 : (Register.x10 == R) = false)
    (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost σ pc vminstret).regs.get? R = σ.regs.get? R := by
  show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R h4 h5

/-- `GoodState` is preserved by the ADDI step: none of the five written registers
(`minstret_increment`, `nextPC`, `x10`, `PC`, `minstret`) is a pinned field, and
the `∃`-fields hold at their new values. -/
theorem goodstate_sigmaPost (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost σ pc vminstret) := by
  constructor
  case cur_privilege => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.cur_privilege
  case misa => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.misa
  case mstatus => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mstatus
  case mie => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mie
  case mseccfg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mseccfg
  case satp => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.satp
  case mtvec => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mtvec
  case mideleg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mideleg
  case medeleg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.medeleg
  case hart_state => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.hart_state
  case htif_done => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done
  case htif_tohost => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost
  case htif_tohost_base => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_tohost_base
  case elp => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.elp
  case pmpcfg_n => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.pmpaddr_n
  case pma_regions => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.pma_regions
  case menvcfg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.menvcfg
  case mcountinhibit => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mcountinhibit
  case mcyclecfg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.mcyclecfg
  case minstretcfg => rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hG.minstretcfg
  case mip => obtain ⟨v, hv⟩ := hG.mip; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_meip => obtain ⟨v, hv⟩ := hG.sig_meip; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_seip => obtain ⟨v, hv⟩ := hG.sig_seip; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtime => obtain ⟨v, hv⟩ := hG.mtime; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case mtimecmp => obtain ⟨v, hv⟩ := hG.mtimecmp; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case minstret => exact ⟨BitVec.addInt vminstret 1, by
    show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case minstret_increment => exact ⟨true, by
    show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case mcycle => obtain ⟨v, hv⟩ := hG.mcycle; exact ⟨v, by rw [get?_sigmaPost σ pc vminstret _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hv⟩
  case nextPC => exact ⟨BitVec.addInt pc 4, by
    show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.x10 == Register.nextPC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case PC => exact ⟨BitVec.addInt pc 4, by
    show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]⟩

/-- `htif_done` is untouched by the ADDI step (none of the five writes, nor the
tick writes, is `htif_done`): it reads back `false` on `sigmaPost`. -/
theorem htif_done_sigmaPost (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : (sigmaPost σ pc vminstret).regs.get? Register.htif_done = some false := by
  show ((((sigma3 σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_done) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_done) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.x10 _).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.x10 == Register.htif_done) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_done

/-- `stepOnce u u` on the ADDI spike (no clock tick: `i+1 ≠ 2`): reads
`htif_done = false`, runs `try_step` (⇒ `false`, no `cycle_count`), reads
`htif_done` again (still `false`), and continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_addi_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some (0x13#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x05#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost σ pc vminstret) := by
  have hts := try_step_addi σ u pc vminstret hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost σ pc vminstret hG
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  -- stepped = false ⇒ pure (); read htif_done again on sigmaPost (= false)
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  -- i+1 == 2? — no tick
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = false := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_eq_false_iff_ne]
    exact htick
  simp only [htick', Bool.false_eq_true, if_false, EStateM.pure]

/-- The `stepOnce`-final state on the tick path: `sigmaPost` followed by the
`tick_clock` write chain (`mcycle += 1`, `mtime += 1`, `mip`'s MTI bit). -/
noncomputable abbrev sigmaTick (σ : MState) (pc vminstret vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost σ pc vminstret) with
    regs := (((((sigmaPost σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- `stepOnce (u) u` on the ADDI spike when `i+1 = 2` (clock tick): as
`stepOnce_addi_notick`, but the trailing `i+1 == 2` guard fires, splicing
`tick_clock` (via `tick_clock_char`) and resetting the tick counter to `0`. -/
theorem stepOnce_addi_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some (0x13#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x05#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_addi σ u pc vminstret hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost σ pc vminstret hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost σ pc vminstret hG
  -- tick_clock on sigmaPost via tick_clock_char (control regs projected from hGp)
  have htc := tick_clock_char (sigmaPost σ pc vminstret) vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
  simp only [EStateM.run] at htc
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  -- i+1 == 2 ⇒ tick_clock
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = true := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_iff_eq]
    exact htick
  simp only [htick', if_true, EStateM.bind]
  rw [htc]
  rfl

/-- **M1 GATE — `step_addi` (no clock tick).** One architectural step of the
Sail model on the ADDI spike, wrapped as `Vsa.Machine.Step`, with `GoodState`
preserved. `σ'` is the explicit five-write chain. -/
theorem step_addi_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some (0x13#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x05#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost σ pc vminstret, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost σ pc vminstret) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_addi_notick σ i u pc vminstret hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaPost σ pc vminstret hG⟩

/-- **M1 GATE — `step_addi` (with clock tick).** As `step_addi_notick`, on the
`i+1 = 2` boundary: the tick counter resets to `0` and `σ''` additionally carries
the `tick_clock` write chain. `GoodState` is preserved (the tick touches only
`mcycle`/`mtime`/`mip`, all `∃`-fields). -/
theorem step_addi_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64)
    (vminstret vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some (0x13#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x05#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0x00#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick σ pc vminstret vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_addi_tick σ i u pc vminstret vmip vmtime vmtimecmp vmcycle hG hpc hminstret
      hmip hmtime hmtimecmp hmcycle hb0 hb1 hb2 hb3 hlo hhi halign htick), ?_⟩
  -- GoodState: tick writes only mcycle/mtime/mip (∃-fields); the rest reads
  -- through the tick chain to `sigmaPost`, which is Good.
  have hGp := goodstate_sigmaPost σ pc vminstret hG
  have hframe : ∀ (R : Register),
      (Register.mip == R) = false → (Register.mtime == R) = false → (Register.mcycle == R) = false →
      (sigmaTick σ pc vminstret vmip vmtime vmtimecmp vmcycle).regs.get? R = (sigmaPost σ pc vminstret).regs.get? R := by
    intro R h1 h2 h3
    show (((((sigmaPost σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip _)).get? R = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]
  constructor
  case cur_privilege => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.cur_privilege
  case misa => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.misa
  case mstatus => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mstatus
  case mie => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mie
  case mseccfg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mseccfg
  case satp => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.satp
  case mtvec => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mtvec
  case mideleg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mideleg
  case medeleg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.medeleg
  case hart_state => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.hart_state
  case htif_done => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.htif_done
  case htif_tohost => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.htif_tohost
  case htif_tohost_base => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.htif_tohost_base
  case elp => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.elp
  case pmpcfg_n => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.pmpcfg_n
  case pmpaddr_n => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.pmpaddr_n
  case pma_regions => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.pma_regions
  case menvcfg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.menvcfg
  case mcountinhibit => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mcountinhibit
  case mcyclecfg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.mcyclecfg
  case minstretcfg => rw [hframe _ (by decide) (by decide) (by decide)]; exact hGp.minstretcfg
  case sig_meip => obtain ⟨v, hv⟩ := hGp.sig_meip; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case mtimecmp => obtain ⟨v, hv⟩ := hGp.mtimecmp; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case minstret => obtain ⟨v, hv⟩ := hGp.minstret; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case minstret_increment => obtain ⟨v, hv⟩ := hGp.minstret_increment; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case nextPC => obtain ⟨v, hv⟩ := hGp.nextPC; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case PC => obtain ⟨v, hv⟩ := hGp.PC; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  case sig_seip => obtain ⟨v, hv⟩ := hGp.sig_seip; exact ⟨v, by rw [hframe _ (by decide) (by decide) (by decide)]; exact hv⟩
  -- the three tick-written registers
  case mcycle => exact ⟨BitVec.addInt vmcycle 1, by
    show (((((sigmaPost σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip _)).get? Register.mcycle = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.mip == Register.mcycle) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.mtime == Register.mcycle) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case mtime => exact ⟨BitVec.addInt vmtime 1, by
    show (((((sigmaPost σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip _)).get? Register.mtime = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.mip == Register.mtime) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]⟩
  case mip => exact ⟨_, by
    show (((((sigmaPost σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip _)).get? Register.mip = _
    rw [Std.ExtDHashMap.get?_insert_self]⟩

end Vsa.Sim
