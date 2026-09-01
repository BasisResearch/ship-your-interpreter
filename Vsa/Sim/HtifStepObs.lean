import Vsa.Sim.ErrorTail
import Vsa.Sim.HtifLift
import Vsa.Sim.Tick

/-!
# Step-level observation layer for the HTIF console-putchar store (`HtifStepObs`)

The `_write` loop's `sd a5,-856(a6)` to `tohost@0x8001ad00` performs a
console-putchar HTIF transition: the store appends one character to
`sailOutput`, leaves MEMORY UNCHANGED, and — unlike the exit store — the
machine CONTINUES (`htif_done` stays `false`: the putchar register tower
inserts `htif_cmd_write`/`htif_payload_writes`/`htif_tohost` but never
`htif_done`), so `stepOnce` takes the `.inr` continue path and the clock-tick
bookkeeping applies exactly as in `StepStore.lean`.

Layers here (models: `experiments/probe-trystep-putchar.lean` for the
`try_step` level; `Vsa/Sim/StepStore.lean` for the `stepOnce`/`Step` pair;
`Vsa/Sim/StepObs.lean` for the parity-absorbing wrapper;
`Vsa/Sim/ErrorTail.lean` for the tohost `stepOnce` unfold discipline):

1. `sigmaPutcharP` / `exec_sd_tohost_putchar` — the execute post-state
   (6-insert HTIF tower + `sailOutput.push`) and the execute equation.
2. `sigmaPutcharFinal` / `try_step_tohost_putchar` — the `try_step`-final
   state (`PC := pc+4`, `minstret += 1`) and the full `try_step` run.
3. `stepOnce_tohost_putchar_notick` / `sigmaTick_putchar` /
   `stepOnce_tohost_putchar_tick` — the continue-path `stepOnce` pair.
4. `step_tohost_putchar_notick` / `step_tohost_putchar_tick` — the
   `Vsa.Machine.Step` wrappers.
5. `stepObs_tohost_putchar` — the parity-absorbing observational wrapper.

## `GoodState` — re-added post-amendment

`GoodState.htif_tohost` (`Vsa/Sim/GoodState.lean`) is now presence-only
(`∃ v, …`), so `GoodState` SURVIVES the putchar store: the machine's putchar
transition (`mem_write_value_tohost_putchar`, `Vsa/Sim/HtifLift.lean`) ends
its insert tower with `htif_tohost := zeros (n := 64)`, which witnesses the
`∃`. `goodstate_sigmaPutcharFinal` / `goodstate_sigmaTick_putchar` establish
it field-by-field (untouched registers through the `get?_sigmaPutcharFinal`
frame; the touched registers' `GoodState` fields are all `∃`-shaped and take
their new values as witnesses), and the `step_*`/`stepObs_*` conclusions
carry the `GoodState` conjunct, mirroring `step_store_notick`/`_tick`.

(Historical: pre-amendment the field PINNED the post-init value
`BitVec.ofNat 64 tohostAddr`, making `GoodState` of the post-state provably
false — machine-checked as `not_goodState_sigmaPutcharFinal`, logged in
`experiments/observations.md` (`goodstate-htif-tohost-overpin`), then fixed
by amendment. The tick case still derives `tick_clock_char`'s control reads
from `GoodState σ` through the write frame, which needs no post-state
`GoodState`.)
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The execute post-state of the putchar `sd` (probe lift) -/

/-- The `execute`-post-state of the console-putchar `sd a5,tohost` store: `σ₂`
(the skeleton's `afterNextPC (afterPrelude σ) pc`) with the putchar HTIF
register tower (6 inserts over 3 registers, ending `htif_payload_writes := 0`,
`htif_tohost := zeros`) and one character pushed onto `sailOutput`. This is the
`mem_write_value_tohost_putchar` post-state threaded through
`vmem_write_addr_w` / `execute_STORE_char`. -/
abbrev sigmaPutcharP (σ : MState) (pc : BitVec 64) (data : BitVec 64) (c : BitVec 8) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_cmd_write 0#1).insert
          Register.htif_payload_writes 0#4).insert
        Register.htif_tohost (zeros (n := 64))),
    sailOutput := (afterNextPC (afterPrelude σ) pc).sailOutput.push
      (toString (Char.ofNat c.toNat)) }

/-- Register read-back through the putchar 6-insert tower: `R` outside
`{htif_tohost, htif_payload_writes, htif_cmd_write}` reads as on `σ₂`. -/
theorem get?_sigmaPutcharP (σ : MState) (pc data : BitVec 64) (c : BitVec 8) (R : Register)
    (h1 : (Register.htif_tohost == R) = false)
    (h2 : (Register.htif_payload_writes == R) = false)
    (h3 : (Register.htif_cmd_write == R) = false) :
    (sigmaPutcharP σ pc data c).regs.get? R = (afterNextPC (afterPrelude σ) pc).regs.get? R := by
  show ((((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
              Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
            Register.htif_tohost data).insert
          Register.htif_cmd_write 0#1).insert
        Register.htif_payload_writes 0#4).insert
      Register.htif_tohost (zeros (n := 64))).get? R) = _
  rw [Std.ExtDHashMap.get?_insert]; simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]

/-- `execute (STORE (imm, rs2, rs1, 8))` at `σ₂` for the console-putchar
`sd a5,tohost` store: effective address `tohostAddr`, store data the putchar
command word `0x0101…00 ||| c`, post-state `sigmaPutcharP σ pc data c`.
Assembled from `execute_STORE_char` + `vmem_write_addr_w` (w = 8) with
`mem_write_value_tohost_putchar` as the abstract `mem_write_value` step. -/
theorem exec_sd_tohost_putchar
    (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigmaPutcharP σ pc data c) := by
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have hpaddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  have hpw₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_payload_writes = some (0#4) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpw
  have hth₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost = some th := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hth
  have hmwv := mem_write_value_tohost_putchar (afterNextPC (afterPrelude σ) pc) c data
    initMstatus initPmpaddr th hpriv hmstatus (by decide) hpma hcfg hpaddr hbase hpw₂ hth₂ hputc
  have hatohost : (BitVec.ofNat 64 tohostAddr).toNat = tohostAddr := by
    simp only [tohostAddr]; decide
  have htr := translateAddr_machine_store (afterNextPC (afterPrelude σ) pc)
    (BitVec.ofNat 64 tohostAddr) initMstatus hpriv hmstatus (by decide)
  have hea := mem_write_ea_8 (afterNextPC (afterPrelude σ) pc) (BitVec.ofNat 64 tohostAddr)
    initMstatus initPmpaddr hpriv hmstatus (by decide) hpma hcfg hpaddr
    (by rw [hatohost]; exact (by decide : (0x80000000 : Nat) ≤ tohostAddr))
    (by rw [hatohost]; exact (by decide : tohostAddr + 8 ≤ 0x100000000))
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
  have hwval : (BitVec.setWidth (8 * 8)
      (Sail.BitVec.extractLsb data (((8 : Nat) *i 8) -i 1).toNat 0)) = data := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_setWidth]
    have key : ∀ W : Nat, W = 64 →
        (BitVec.ofNat W (data.toNat >>> 0)).toNat % 2 ^ (8 * 8) = data.toNat := by
      intro W hW; subst hW
      simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat]
      have : data.toNat < 2 ^ 64 := data.isLt
      have h1 : data.toNat % 2 ^ 64 = data.toNat := by omega
      rw [h1]; omega
    exact key ((((8 : Nat) *i 8) -i 1).toNat - 0 + 1) (by decide)
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaPutcharP σ pc data c)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaPutcharP σ pc data c) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

/-! ## The `try_step`-final state and its read-backs -/

/-- The `try_step`-final state of the putchar `sd a5,tohost` store:
`sigmaPutcharP` with `PC := npc` and `minstret := vminstret+1`. -/
abbrev sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8) : MState :=
  {(({(sigmaPutcharP σ pc data c) with
        regs := (sigmaPutcharP σ pc data c).regs.insert Register.PC npc}) : MState) with
    regs := ((({(sigmaPutcharP σ pc data c) with
        regs := (sigmaPutcharP σ pc data c).regs.insert Register.PC npc}) : MState).regs.insert
          Register.minstret (BitVec.addInt vminstret 1))}

/-- Read-back of `R` outside the putchar write-set `{minstret, PC, htif_tohost,
htif_payload_writes, htif_cmd_write, nextPC, minstret_increment}` through the
whole putchar write chain equals reading from `σ`. -/
theorem get?_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (R : Register)
    (hms : (Register.minstret == R) = false) (hpc : (Register.PC == R) = false)
    (hth : (Register.htif_tohost == R) = false)
    (hpw : (Register.htif_payload_writes == R) = false)
    (hcw : (Register.htif_cmd_write == R) = false)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? R = σ.regs.get? R := by
  show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]; simp only [hms, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]; simp only [hpc, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [get?_sigmaPutcharP σ pc data c R hth hpw hcw]
  exact get?_afterNextPC σ pc R hnpc hmi

/-- **The continue-path crux**: `htif_done` reads `false` on the putchar final
state — the putchar tower never touches `htif_done` (unlike the exit tower), so
the read frames through to `hG.htif_done`. -/
theorem htif_done_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (hG : GoodState σ) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPutcharFinal σ pc npc vminstret data c _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]
  exact hG.htif_done

/-- `PC` reads `npc` on the putchar final state. -/
theorem get?_PC_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.PC = some npc := by
  show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `minstret` reads `vminstret + 1` on the putchar final state. -/
theorem get?_minstret_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.minstret
      = some (BitVec.addInt vminstret 1) := by
  show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `htif_payload_writes` reads `0` on the putchar final state (the mailbox is
re-armed — exactly the `hpw` hypothesis the NEXT putchar store consumes). -/
theorem get?_payload_writes_sigmaPutcharFinal (σ : MState)
    (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.htif_payload_writes
      = some (0#4) := by
  show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)).get? Register.htif_payload_writes = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_payload_writes) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_payload_writes) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
              Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
            Register.htif_tohost data).insert
          Register.htif_cmd_write 0#1).insert
        Register.htif_payload_writes 0#4).insert
      Register.htif_tohost (zeros (n := 64))).get? Register.htif_payload_writes) = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.htif_tohost == Register.htif_payload_writes) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `htif_tohost` reads `zeros` on the putchar final state (the model clears
the mailbox after consuming the command). Post-amendment this `zeros` value is
the witness for the presence-only `GoodState.htif_tohost` field. -/
theorem get?_htif_tohost_sigmaPutcharFinal (σ : MState)
    (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? Register.htif_tohost
      = some (zeros (n := 64)) := by
  show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)).get? Register.htif_tohost = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_tohost) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_tohost) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
              Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
            Register.htif_tohost data).insert
          Register.htif_cmd_write 0#1).insert
        Register.htif_payload_writes 0#4).insert
      Register.htif_tohost (zeros (n := 64))).get? Register.htif_tohost) = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- Memory is untouched by the putchar store (regs + sailOutput updates only). -/
theorem mem_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).mem = σ.mem := rfl

/-- The putchar final state's console output is `σ`'s with ONE character pushed
(the prelude/nextPC/postlude writes are all regs-only, so this is `rfl`). -/
theorem sailOutput_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) :
    (sigmaPutcharFinal σ pc npc vminstret data c).sailOutput
      = σ.sailOutput.push (toString (Char.ofNat c.toNat)) := rfl

/-- **`GoodState` survives the putchar store** (post-amendment:
`GoodState.htif_tohost` is presence-only, witnessed by the tower's final
`zeros` write). Every field whose register is OUTSIDE the putchar write-set
`{minstret, PC, htif_tohost, htif_payload_writes, htif_cmd_write, nextPC,
minstret_increment}` reads through the `get?_sigmaPutcharFinal` frame; the
touched registers with `GoodState` fields (`minstret`, `PC`, `htif_tohost`,
`nextPC`, `minstret_increment`) are all `∃`-shaped and take their new values
as witnesses (`htif_cmd_write`/`htif_payload_writes` have no `GoodState`
field). Cannot chain `GoodState.insert_nonpinned` here because `isNonPinned`
still classifies `htif_tohost` as pinned. Model: `goodstate_sigmaPost_store`
(`Vsa/Sim/StepStore.lean`). -/
theorem goodstate_sigmaPutcharFinal (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) (hG : GoodState σ) :
    GoodState (sigmaPutcharFinal σ pc npc vminstret data c) := by
  have P := get?_sigmaPutcharFinal σ pc npc vminstret data c
  constructor
  case cur_privilege =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.cur_privilege
  case misa =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.misa
  case mstatus =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mstatus
  case mie =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mie
  case mseccfg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mseccfg
  case satp =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.satp
  case mtvec =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mtvec
  case mideleg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mideleg
  case medeleg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.medeleg
  case hart_state =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.hart_state
  case htif_done =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.htif_done
  case htif_tohost =>
    exact ⟨_, get?_htif_tohost_sigmaPutcharFinal σ pc npc vminstret data c⟩
  case htif_tohost_base =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.htif_tohost_base
  case elp =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.elp
  case pmpcfg_n =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.pmpcfg_n
  case pmpaddr_n =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.pmpaddr_n
  case pma_regions =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.pma_regions
  case menvcfg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.menvcfg
  case mcountinhibit =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mcountinhibit
  case mcyclecfg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mcyclecfg
  case minstretcfg =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.minstretcfg
  case mip =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mip
  case sig_meip =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.sig_meip
  case sig_seip =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.sig_seip
  case mtime =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mtime
  case mtimecmp =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mtimecmp
  case minstret =>
    exact ⟨_, get?_minstret_sigmaPutcharFinal σ pc npc vminstret data c⟩
  case minstret_increment =>
    refine ⟨true, ?_⟩
    show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
        Register.minstret (BitVec.addInt vminstret 1)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC
        (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  case mcycle =>
    rw [P _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hG.mcycle
  case nextPC =>
    refine ⟨BitVec.addInt pc 4, ?_⟩
    show (((sigmaPutcharP σ pc data c).regs.insert Register.PC npc).insert
        Register.minstret (BitVec.addInt vminstret 1)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.minstret == Register.nextPC) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.PC == Register.nextPC) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC
        (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  case PC =>
    exact ⟨npc, get?_PC_sigmaPutcharFinal σ pc npc vminstret data c⟩

/-! ## `try_step` on the putchar store (probe lift) -/

/-- **`try_step` on the console-putchar `sd a5,tohost` store.** The store runs
the putchar HTIF transition (`exec_sd_tohost_putchar`: register tower +
`sailOutput.push`, memory untouched); the `try_step` postlude writes
`PC := pc+4` and `minstret := vminstret+1`. Returns `false` — and `htif_done`
stays `false`, so the machine CONTINUES (unlike the exit store). -/
theorem try_step_tohost_putchar
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ = .ok false (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) := by
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
      = .ok (FetchResult.F_Base (((b3.append b2).append b1).append b0)) (afterPrelude σ) :=
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3 _ _ _
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
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec := exec_sd_tohost_putchar σ pc imm rs2 rs1 v1 vdata data c th
    hG hrs1 hrs2 haddr hdataeq hpw hth hputc
  have hhart₃ : (sigmaPutcharP σ pc data c).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigmaPutcharP σ pc data c).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigmaPutcharP σ pc data c).regs.get? Register.minstret_increment = some true := by
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigmaPutcharP σ pc data c).regs.get? Register.minstret = some vminstret := by
    rw [get?_sigmaPutcharP σ pc data c _ (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0) (instruction.STORE (imm, rs2, rs1, 8))
    (sigmaPutcharP σ pc data c) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## `stepOnce` (no clock tick) -/

/-- `stepOnce i u` on the putchar store (`i+1 ≠ 2`): `try_step` performs the
store (⇒ `false`, one character pushed, `PC := pc+4`); the re-checked
`htif_done` is STILL `false` (`htif_done_sigmaPutcharFinal`), so `stepOnce`
takes the `.inr` continue path, exactly like `stepOnce_store_notick`. -/
theorem stepOnce_tohost_putchar_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ
      = .ok (.inr (i + 1, u + 1)) (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) := by
  have hts := try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
    b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
    hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG
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

/-! ## Tick state and `stepOnce` (with clock tick) -/

/-- Putchar tick final state: `sigmaPutcharFinal` + `tick_clock` writes
(`mcycle += 1`, `mtime += 1`, `mip`'s MTI bit from `mtimecmp ≤u mtime+1`).
Clone of `sigmaTick_store`. -/
noncomputable abbrev sigmaTick_putchar
    (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPutcharFinal σ pc npc vminstret data c) with
    regs := (((sigmaPutcharFinal σ pc npc vminstret data c).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))}

/-- GPR/PC read-back through the putchar tick chain drops to
`sigmaPutcharFinal` (the three tick inserts are on `mcycle`/`mtime`/`mip`). -/
theorem get?_sigmaTick_putchar (σ : MState) (pc npc vminstret data : BitVec 64) (c : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_putchar σ pc npc vminstret data c vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPutcharFinal σ pc npc vminstret data c).regs.get? R := by
  show (((((sigmaPutcharFinal σ pc npc vminstret data c).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, dif_neg, reduceCtorEq, not_false_eq_true]

/-- `GoodState` survives the putchar tick state: the three tick writes
(`mcycle`/`mtime`/`mip`) are non-pinned inserts over the (now-`GoodState`)
putchar final state. Model: `step_store_tick`'s `GoodState` component
(`Vsa/Sim/StepStore.lean`). -/
theorem goodstate_sigmaTick_putchar (σ : MState) (pc npc vminstret data : BitVec 64)
    (c : BitVec 8) (vmip vmtime vmtimecmp vmcycle : BitVec 64) (hG : GoodState σ) :
    GoodState (sigmaTick_putchar σ pc npc vminstret data c vmip vmtime vmtimecmp vmcycle) := by
  have hGp := goodstate_sigmaPutcharFinal σ pc npc vminstret data c hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-- `stepOnce i u` on the putchar store when `i+1 = 2` (clock tick): as
`stepOnce_tohost_putchar_notick`, but the trailing tick guard fires, splicing
`tick_clock` (via `tick_clock_char`) and resetting the counter to `0`. The
`tick_clock_char` control reads are derived from `GoodState σ` THROUGH the
putchar write frame. -/
theorem stepOnce_tohost_putchar_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1))
          (sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_tohost_putchar σ u pc vminstret w imm rs2 rs1 v1 vdata data c th
    b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
    hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG
  -- tick_clock control reads on the (non-GoodState) post-state, via the frame.
  have htc := tick_clock_char (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c)
    vmip vmtime vmtimecmp vmcycle
    (by rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hG.cur_privilege)
    (by rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hG.mcountinhibit)
    (by rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hG.mcyclecfg)
    (by rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hG.menvcfg)
    (by rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hG.misa)
    hmip hmtime hmtimecmp hmcycle
    (by obtain ⟨v, hv⟩ := hG.sig_meip
        exact ⟨v, by
          rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hv⟩)
    (by obtain ⟨v, hv⟩ := hG.sig_seip
        exact ⟨v, by
          rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hv⟩)
  simp only [EStateM.run] at htc
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = true := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_iff_eq]
    exact htick
  simp only [htick', if_true, EStateM.bind]
  rw [htc]
  rfl

/-! ## `Machine.Step` wrappers

Like `step_store_notick`/`_tick`, these return `GoodState` of the final state
alongside the step (re-added post-amendment: `GoodState.htif_tohost` is
presence-only, so the putchar tower preserves `GoodState`). -/

/-- **`step` on the putchar store (no clock tick)**, wrapped as
`Vsa.Machine.Step`, with `GoodState` preserved. -/
theorem step_tohost_putchar_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c, i + 1, u + 1⟩
    ∧ GoodState (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_tohost_putchar_notick σ i u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c hG⟩

/-- **`step` on the putchar store (with clock tick)**, on the `i+1 = 2`
boundary: counter resets to `0`, the final state carries the `tick_clock`
write chain. `GoodState` preserved (the tick touches only
`mcycle`/`mtime`/`mip`). -/
theorem step_tohost_putchar_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c vmip vmtime vmtimecmp vmcycle,
        0, u + 1⟩
    ∧ GoodState (sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
        vmip vmtime vmtimecmp vmcycle) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_tohost_putchar_tick σ i u pc vminstret w imm rs2 rs1 v1 vdata data c th
      b0 b1 b2 b3 vmip vmtime vmtimecmp vmcycle hG hpc hminstret
      hmip hmtime hmtimecmp hmcycle hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
     vmip vmtime vmtimecmp vmcycle hG⟩

/-! ## The parity-agnostic observational wrapper -/

/-- **The putchar observational step** (clone of `stepObs_store`'s `by_cases`
structure): for any tick parity `i < 2`, one `Vsa.Machine.Step` whose
successor is a `GoodState`, pushes ONE character onto the console, leaves
memory unchanged, advances `PC` to `pc+4`, re-arms the HTIF mailbox
(`htif_payload_writes = 0`, `htif_tohost` present), and frames every register
outside the putchar+postlude+tick write-set. The `GoodState σ'` conjunct is
re-added post-amendment (`GoodState.htif_tohost` is presence-only, so the
putchar tower preserves `GoodState` — `goodstate_sigmaPutcharFinal` /
`goodstate_sigmaTick_putchar`). -/
theorem stepObs_tohost_putchar
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (c : BitVec 8) (th : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hputc : data = (0x0101000000000000#64) ||| BitVec.zeroExtend 64 c)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧
      GoodState σ' ∧
      σ'.mem = σ.mem ∧
      σ'.sailOutput = σ.sailOutput.push (toString (Char.ofNat c.toNat)) ∧
      σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) ∧
      (∃ vm', σ'.regs.get? Register.minstret = some vm') ∧
      σ'.regs.get? Register.htif_payload_writes = some (0#4) ∧
      (∃ th', σ'.regs.get? Register.htif_tohost = some th') ∧
      (∀ R : Register,
        (Register.PC == R) = false → (Register.minstret == R) = false →
        (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
        (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
        (Register.htif_tohost == R) = false →
        (Register.mip == R) = false → (Register.mtime == R) = false →
        (Register.mcycle == R) = false →
        σ'.regs.get? R = σ.regs.get? R) := by
  by_cases htick : i + 1 = 2
  · -- tick boundary: clock-noise witnesses from GoodState σ, through the frame.
    obtain ⟨vmip, hmip0⟩ := hG.mip
    obtain ⟨vmtime, hmtime0⟩ := hG.mtime
    obtain ⟨vmtimecmp, hmtimecmp0⟩ := hG.mtimecmp
    obtain ⟨vmcycle, hmcycle0⟩ := hG.mcycle
    have hmip : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mip = some vmip := by
      rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmip0
    have hmtime : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtime = some vmtime := by
      rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmtime0
    have hmtimecmp : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mtimecmp = some vmtimecmp := by
      rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmtimecmp0
    have hmcycle : (sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c).regs.get? Register.mcycle = some vmcycle := by
      rw [get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmcycle0
    obtain ⟨hstep, hG'⟩ := step_tohost_putchar_tick σ i u pc vminstret w imm rs2 rs1
      v1 vdata data c th
      b0 b1 b2 b3 vmip vmtime vmtimecmp vmcycle hG hpc hminstret
      hmip hmtime hmtimecmp hmcycle hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, 0, hstep, by decide, hG', rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [get?_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
        vmip vmtime vmtimecmp vmcycle Register.PC (by decide) (by decide) (by decide)]
      exact get?_PC_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c
    · exact ⟨BitVec.addInt vminstret 1, by
        rw [get?_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
          vmip vmtime vmtimecmp vmcycle Register.minstret (by decide) (by decide) (by decide)]
        exact get?_minstret_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c⟩
    · rw [get?_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
        vmip vmtime vmtimecmp vmcycle Register.htif_payload_writes (by decide) (by decide) (by decide)]
      exact get?_payload_writes_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c
    · exact ⟨zeros (n := 64), by
        rw [get?_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
          vmip vmtime vmtimecmp vmcycle Register.htif_tohost (by decide) (by decide) (by decide)]
        exact get?_htif_tohost_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c⟩
    · intro R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [get?_sigmaTick_putchar σ pc (BitVec.addInt pc 4) vminstret data c
        vmip vmtime vmtimecmp vmcycle R h10 h9 h8]
      exact get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c R h2 h1 h7 h6 h5 h4 h3
  · obtain ⟨hstep, hG'⟩ := step_tohost_putchar_notick σ i u pc vminstret w imm rs2 rs1
      v1 vdata data c th
      b0 b1 b2 b3 hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hputc
      hb0 hb1 hb2 hb3 hlo hhi halign htick
    refine ⟨_, i + 1, hstep, by omega, hG', rfl, rfl,
      get?_PC_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c,
      ⟨BitVec.addInt vminstret 1,
        get?_minstret_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c⟩,
      get?_payload_writes_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c,
      ⟨zeros (n := 64),
        get?_htif_tohost_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c⟩, ?_⟩
    intro R h1 h2 h3 h4 h5 h6 h7 _ _ _
    exact get?_sigmaPutcharFinal σ pc (BitVec.addInt pc 4) vminstret data c R h2 h1 h7 h6 h5 h4 h3

#print axioms goodstate_sigmaPutcharFinal
#print axioms goodstate_sigmaTick_putchar
#print axioms try_step_tohost_putchar
#print axioms stepOnce_tohost_putchar_notick
#print axioms stepOnce_tohost_putchar_tick
#print axioms step_tohost_putchar_notick
#print axioms step_tohost_putchar_tick
#print axioms stepObs_tohost_putchar

end Vsa.Sim
