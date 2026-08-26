import Vsa.Sim.ErrorTail
import Vsa.Sim.TermSimClose

/-!
# Layer 8 — the CLEAN-EXIT(0) entry bridge: discharging `hEntryHalts`

`TermSimClose.termSimClosed` reduces `InterpSim.term_sim` to a single named
residual `hEntryHalts` (the M6 program-entry bridge):

```
∀ p c out st' t,
  Loaded L p c → st'.out = out →
  mExecSeq initSt 0 0 p st' .normal t → Halts c out 0
```

i.e. given the top-level statement loop executed the program to `st'` with
`.normal` status (the `mExecSeq` datum, produced by the `term_sim` recursor from
the M4 case bundle), the machine halts with **exit code 0** printing
`out = st'.out`.  This file supplies the two halves:

* **the clean-exit tail** (`.normal` → `interp_run` returns 0 → `main` returns 0
  → crt0 `j exit` → `_exit` forms `(0<<<1)|1` in `a5` → `sd a5,tohost` →
  HTIF halt with code 0), and
* **the prologue bridge** (`Loaded L p c` → the machine at `interp_run` entry
  reaches the top-level statement-loop head so the `mExecSeq` motive applies).

## The exit-0 vs exit-70 path — what we reuse

The runtime-error path (`Vsa/Sim/ErrorSim.lean` / `Vsa/Sim/ErrorTail.lean`)
already decoded the SIBLING exit(70) chain.  The clean path is its exit-0 twin:

* **`main` returns 0, not 70** (`li a0,0` where the error arm does `li a0,70`);
* **the `beqz a0` at the `setjmp` continuation is NOT taken** (the clean path
  never longjmps back — `a0 = 0` at the continuation), where the error arm takes
  `bnez a0`;
* **`_exit` forms `(0<<<1)|1 = 1` in `a5`**, not `(70<<<1)|1`;
* the crt0 `j exit` and `_exit` `sd a5,tohost` store site are **the same
  instructions**; only the payload word (`a5`) and the latched exit code differ.

Concretely: `Vsa/Sim/ErrorTail.lean`'s exit-store bridge (`sigmaExit`,
`exec_sd_tohost_exit`, `try_step_tohost_exit`, `stepOnce_tohost_exit`,
`exitStoreHalts`) is written for exit code `70`.  Its `mem_write_value_tohost_exit`
core (`Vsa/Sim/HtifLift.lean`) is already **generic in the exit code `e`** (via
`e.toNat < 2^47` and `data = (e<<<1)|1`).  §1 below re-derives those four steps
parameterized over an arbitrary `e` (the `70`-specific `by decide` bounds become
the standing `hsmall : e.toNat < 2^47` hypothesis), then §2 specializes at
`e = 0` to obtain `exitStoreHalts0` (the exit-store → HTIF-halt-**0** bridge).

§3 assembles the clean-exit tail by MIRRORING `errorTailHalts`: a tail-chain
residual `ExitTailChain0` (the `interp_run`-normal-return / `main` / crt0 / exit
span — the exit-0 twin of `ErrorTailChain`) composed with `exitStoreHalts0`.
§4 states the prologue bridge and assembles `entryHalts`, shaped to discharge
`termSimClosed`'s `hEntryHalts`, conditional only on the same
M6-layout/`SnprintfContract`-style residuals the exit-70 path carries.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.Refine (Layout Loaded)
open Vsa.While (initSt Program Status ExecSeq)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The exit-store bridge, generic in the exit code `e`

Verbatim re-derivation of `Vsa/Sim/ErrorTail.lean`'s exit-store steps, but with the
literal exit code `70` replaced by an arbitrary `e : BitVec 64` (with the device
byte-zero bound `e.toNat < 2^47` threaded as `hsmall`).  The `mem_write_value`
core (`mem_write_value_tohost_exit`) is already `e`-generic, so only the ghost
post-state (`sigmaExitG`) and the outer `stepOnce` return code change. -/

/-- `sigmaExit` generic in the latched exit code `e`.  The execute-post-state of
the `sd a5,tohost` store: `σ₂ = afterNextPC (afterPrelude σ) pc` with the five HTIF
inserts, `htif_exit_code := e`. -/
abbrev sigmaExitG (σ : MState) (pc : BitVec 64) (data e : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_done true).insert
          Register.htif_exit_code e}

/-- `exec_sd_tohost_exit` generic in the exit code `e`. -/
theorem exec_sd_tohost_G
    (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigmaExitG σ pc data e) := by
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
  -- `mem_write_value` at tohost → the HTIF exit transition (post-state = sigmaExitG).
  have hmwv := mem_write_value_tohost_exit (afterNextPC (afterPrelude σ) pc) e data
    initMstatus initPmpaddr th hpriv hmstatus (by decide) hpma hcfg hpaddr hbase hpw₂ hth₂ hsmall hexit
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
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaExitG σ pc data e)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaExitG σ pc data e) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

/-- `sigmaExitFinal` generic in the exit code `e`. -/
abbrev sigmaExitFinalG (σ : MState) (pc npc vminstret data e : BitVec 64) : MState :=
  {(({(sigmaExitG σ pc data e) with
        regs := (sigmaExitG σ pc data e).regs.insert Register.PC npc}) : MState) with
    regs := ((({(sigmaExitG σ pc data e) with
        regs := (sigmaExitG σ pc data e).regs.insert Register.PC npc}) : MState).regs.insert
          Register.minstret (BitVec.addInt vminstret 1))}

/-- `try_step_tohost_exit` generic in the exit code `e`. -/
theorem try_step_tohost_G
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
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
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ = .ok false (sigmaExitFinalG σ pc (BitVec.addInt pc 4) vminstret data e) := by
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
  have hexec := exec_sd_tohost_G σ pc imm rs2 rs1 v1 vdata data e th
    hG hrs1 hrs2 haddr hdataeq hpw hth hsmall hexit
  have hframe : ∀ R : Register,
      (Register.htif_exit_code == R) = false → (Register.htif_done == R) = false →
      (Register.htif_tohost == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_cmd_write == R) = false →
      (sigmaExitG σ pc data e).regs.get? R = (afterNextPC (afterPrelude σ) pc).regs.get? R := by
    intro R h1 h2 h3 h4 h5
    show (((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_done true).insert
          Register.htif_exit_code e).get? R) = _
    rw [Std.ExtDHashMap.get?_insert]; simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h3, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h4, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert]; simp only [h5, dif_neg, reduceCtorEq, not_false_eq_true]
  have hhart₃ : (sigmaExitG σ pc data e).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigmaExitG σ pc data e).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigmaExitG σ pc data e).regs.get? Register.minstret_increment = some true := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigmaExitG σ pc data e).regs.get? Register.minstret = some vminstret := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0) (instruction.STORE (imm, rs2, rs1, 8))
    (sigmaExitG σ pc data e) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-- `htif_done` reads `true` on the generic exit-store post-state. -/
theorem htif_done_sigmaExitG_final (σ : MState) (pc npc vminstret data e : BitVec 64) :
    (sigmaExitFinalG σ pc npc vminstret data e).regs.get? Register.htif_done = some true := by
  show (((((sigmaExitG σ pc data e).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)))).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
          Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
        Register.htif_tohost data).insert
      Register.htif_done true).insert
    Register.htif_exit_code e).get? Register.htif_done = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.htif_exit_code == Register.htif_done) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `htif_exit_code` reads `e` on the generic exit-store post-state. -/
theorem htif_exit_code_sigmaExitG_final (σ : MState) (pc npc vminstret data e : BitVec 64) :
    (sigmaExitFinalG σ pc npc vminstret data e).regs.get? Register.htif_exit_code = some e := by
  show (((((sigmaExitG σ pc data e).regs.insert Register.PC npc).insert
      Register.minstret (BitVec.addInt vminstret 1)))).get? Register.htif_exit_code = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.htif_exit_code) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.PC == Register.htif_exit_code) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true]
  show ((((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
          Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
        Register.htif_tohost data).insert
      Register.htif_done true).insert
    Register.htif_exit_code e).get? Register.htif_exit_code = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `sailOutput` unchanged by the generic exit-store `try_step`-final state. -/
theorem sailOutput_sigmaExitG_final (σ : MState) (pc npc vminstret data e : BitVec 64) :
    (sigmaExitFinalG σ pc npc vminstret data e).sailOutput = σ.sailOutput := rfl

/-- `stepOnce_tohost_exit` generic in the exit code `e`: the exit-store `stepOnce`
halts with code `e.toNat`. -/
theorem stepOnce_tohost_G
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data e : BitVec 64) (th : BitVec 64)
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
    (hsmall : e.toNat < 2 ^ 47)
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (stepOnce i u).run σ
      = .ok (.inl (some e.toNat, u + 1)) (sigmaExitFinalG σ pc (BitVec.addInt pc 4) vminstret data e) := by
  have hts := try_step_tohost_G σ u pc vminstret w imm rs2 rs1 v1 vdata data e th b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hsmall hexit
    hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hdone' := htif_done_sigmaExitG_final σ pc (BitVec.addInt pc 4) vminstret data e
  have hcode' := htif_exit_code_sigmaExitG_final σ pc (BitVec.addInt pc 4) vminstret data e
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get,
    hdone', if_true, hcode']

/-! ## §2. The clean-exit(0) store-site predicate and halt bridge

Specialize §1 at `e = 0`: the `_exit` prologue formed `(0<<<1)|1 = 1` in `a5`, so
the store data is `1`, the latched exit code is `0`.  `ExitStorePre0` is the
exit-0 twin of `ErrorTail.ExitStorePreExit`; `exitStoreHalts0` is the exit-0 twin
of `exitStoreHalts`. -/

/-- The clean-exit `sd a5,tohost` store-site predicate: everything
`stepOnce_tohost_G` (at `e = 0`) consumes, plus `output σ = out`.  Differs from
`ErrorTail.ExitStorePreExit` only in the store data `vdata = (0<<<1)|1` (vs
`(70<<<1)|1`). -/
def ExitStorePre0 (out : String) (c : Config) : Prop :=
  ∃ (pc vminstret : BitVec 64) (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata th : BitVec 64) (b0 b1 b2 b3 : BitVec 8),
    GoodState c.σ ∧
    c.σ.regs.get? Register.PC = some pc ∧
    c.σ.regs.get? Register.minstret = some vminstret ∧
    (((b3.append b2).append b1).append b0) = w ∧
    Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2) ∧
    (ext_decode w).run (afterPrelude c.σ)
      = .ok (instruction.STORE (imm, rs2, rs1, 8)) (afterPrelude c.σ) ∧
    (rX_bits rs1).run (afterNextPC (afterPrelude c.σ) pc)
      = .ok v1 (afterNextPC (afterPrelude c.σ) pc) ∧
    (rX_bits rs2).run (afterNextPC (afterPrelude c.σ) pc)
      = .ok vdata (afterNextPC (afterPrelude c.σ) pc) ∧
    v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr ∧
    vdata = (0#64 <<< 1) ||| 1#64 ∧
    c.σ.regs.get? Register.htif_payload_writes = some (0#4) ∧
    c.σ.regs.get? Register.htif_tohost = some th ∧
    c.σ.mem[pc.toNat]? = some b0 ∧
    c.σ.mem[pc.toNat + 1]? = some b1 ∧
    c.σ.mem[pc.toNat + 2]? = some b2 ∧
    c.σ.mem[pc.toNat + 3]? = some b3 ∧
    0x80000000 ≤ pc.toNat ∧
    pc.toNat + 4 ≤ tohostAddr ∧
    pc.toNat % 4 = 0 ∧
    output c.σ = out

/-- **The clean-exit(0) store → HTIF-halt bridge.**  From an `ExitStorePre0 out c`
configuration (the `_exit` `sd a5,tohost` with `a5 = (0<<<1)|1`), the machine halts
with exit code **0** printing `out` in a single `stepOnce`.  Exit-0 twin of
`ErrorTail.exitStoreHalts`; `0 < 2^47` supplies `hsmall`, and the returned code
`(0#64).toNat = 0` gives exactly `Halted _ 0`. -/
theorem exitStoreHalts0 (out : String) :
    ∀ c, ExitStorePre0 out c → ∃ c' σf, Steps c c' ∧ Halted c' 0 σf ∧ output σf = out := by
  intro c hpre
  obtain ⟨pc, vminstret, w, imm, rs2, rs1, v1, vdata, th, b0, b1, b2, b3,
    hG, hpc, hminstret, hword, hnotrvc, hdec, hrs1, hrs2, haddr, hdataeq, hpw, hth,
    hb0, hb1, hb2, hb3, hlo, hhi, halign, hout⟩ := hpre
  have hstep := stepOnce_tohost_G c.σ c.tick c.steps pc vminstret w imm rs2 rs1
    v1 vdata ((0#64 <<< 1) ||| 1#64) (0#64) th b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth (by decide) rfl
    hb0 hb1 hb2 hb3 hlo hhi halign
  -- normalize the returned code `(0#64).toNat` to the literal `0`.
  rw [show BitVec.toNat (0#64 : BitVec 64) = 0 from by decide] at hstep
  refine ⟨c, sigmaExitFinalG c.σ pc (BitVec.addInt pc 4) vminstret ((0#64 <<< 1) ||| 1#64) (0#64),
    Steps.refl c, ?_, ?_⟩
  · have : c = ⟨c.σ, c.tick, c.steps⟩ := rfl
    rw [this]
    exact Halted.mk hstep
  · show output (sigmaExitFinalG c.σ pc (BitVec.addInt pc 4) vminstret _ _) = out
    unfold output
    rw [sailOutput_sigmaExitG_final]
    exact hout

/-! ## §3. The clean-exit tail — MIRROR of `errorTailHalts`

The exit-0 twin of `ErrorTail.ErrorTailChain`: from the `interp_run` NORMAL-return
continuation (the statement loop finished with `.normal`, `a0 = 0` at the
`setjmp`-continuation so the `beqz a0` is NOT taken — the error arm's `bnez a0`
sibling), the machine runs the `interp_run`-return / `main` (`li a0,0`; ret) / crt0
(`j exit`) / `_exit`-prologue span to the clean-exit store site `ExitStorePre0`.
Held opaque here (the decode span is the exit-0 twin of the exit-70 `ExitPathSeg`
battery, to be discharged by the same seg machinery), exactly as `ErrorTailChain`
holds the error span opaque. -/

/-- **The interp_run-normal-return / main / crt0 / exit span**, as a `Triple`
residual (exit-0 twin of `ErrorTailChain`).  From the clean interp_run-return
continuation config `ra0` (the statement loop finished `.normal`, `a0 = 0`), the
machine runs finitely to the clean-exit store site `ExitStorePre0 out`.  The
`beqz a0`-not-taken (vs the error arm's `bnez a0`) and `main`'s `li a0,0` (vs
`li a0,70`) are the exit-0 differences; the crt0 `j exit` / `_exit` prologue are
shared with the error path. -/
structure ExitTailChain0 (ra0 : BitVec 64) (out : String) : Prop where
  chain :
    Triple
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra0 ∧
        c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64))
      (ExitStorePre0 out)

/-- **The clean-exit tail.**  From the `interp_run` normal-return continuation
`ra0` (statement loop finished `.normal`, `a0 = 0`, `GoodState`, tick-bounded),
threading the interp_run-return/main/crt0/exit span (`HT`) and the exit-0 store →
HTIF-halt bridge (`exitStoreHalts0`), the machine halts with exit code **0**
printing `out`: `Halts c out 0`.  This is the exit-0 twin of `errorTailHalts`'s
composition (`ExitStoreHalts` discharged concretely by `exitStoreHalts0`). -/
theorem cleanExitTail
    (ra0 : BitVec 64) (out : String)
    (HT : ExitTailChain0 ra0 out)
    (c : Config)
    (hcont : GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some ra0 ∧
      c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64)) :
    Halts c out 0 := by
  -- 1. interp_run-cont / main / crt0 / exit span → the `_exit` store site.
  obtain ⟨c1, hs1, hpre1⟩ := HT.chain c hcont
  -- 2. exit store → HTIF halt with code 0.
  obtain ⟨c2, σf, hs2, hh2, ho2⟩ := exitStoreHalts0 out c1 hpre1
  exact halts_of_steps_halted (hs1.trans hs2) hh2 ho2

/-! ## §4. The program-entry bridge — `entryHalts`

`termSimClosed`'s `hEntryHalts` residual: from `Loaded L p c`, `st'.out = out`, and
the whole-program `mExecSeq initSt 0 0 p st' .normal t` simulation datum, land
`Halts c out 0`.

`entryHalts` assembles it via TWO named residuals — the same shape the exit-70
path carries:

* **`hPrologue`** (the prologue bridge): `Loaded L p c` transports the machine from
  the `interp_run` entry through the statement loop (consuming the `mExecSeq`
  `SegEntry → SegExit` simulation Triple), landing at the `interp_run`
  normal-return continuation config `ra0` with `a0 = 0` and the console output
  equal to `st'.out`.  This is the M6 `Loaded ↔ SegEntry` unification + statement-
  loop drive (the exit-0 twin of the exit-70 path's `runtime_error_spec`
  precondition + `hre`), held as a hypothesis.
* **`ExitTailChain0`** (the tail span, §3), discharged concretely by
  `cleanExitTail` into `exitStoreHalts0`.

Composing `hPrologue` (→ the `.normal`-return continuation) with `cleanExitTail`
(→ `Halts c out 0`) discharges `hEntryHalts` verbatim. -/

/-- **`hEntryHalts` discharged** (conditional on the prologue-bridge + tail-span
residuals).  Exactly the shape `termSimClosed`'s `hEntryHalts` hypothesis demands:
given `Loaded L p c`, `st'.out = out`, and the whole-program normal `mExecSeq`
datum, the machine halts cleanly with exit code 0 printing `out`.

The prologue bridge `hPrologue` consumes `Loaded` together with the `mExecSeq`
simulation Triple (`∀`-closed over the layout ghosts, exactly the `mExecSeq`
motive shape) and returns the `interp_run` normal-return continuation config
(`GoodState`, tick-bounded, `PC = ra0`, `a0 = 0`) with `output = out`; the tail
span `hChain` + `cleanExitTail` carry it to the clean HTIF halt. -/
theorem entryHalts (L : Layout)
    (hPrologue :
      ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
        (t : Vsa.While.ExecSeq initSt 0 0 p st' Vsa.While.Status.normal),
        Loaded L p c → st'.out = out →
        Vsa.Sim.TermSimAssembly.mExecSeq initSt 0 0 p st' Vsa.While.Status.normal t →
        ∃ (ra0 : BitVec 64) (c1 : Config),
          Steps c c1 ∧ ExitTailChain0 ra0 out ∧
          (GoodState c1.σ ∧ c1.tick < 2 ∧
            c1.σ.regs.get? Register.PC = some ra0 ∧
            c1.σ.regs.get? Register.x10 = some (0#64 : BitVec 64))) :
    ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
      (t : Vsa.While.ExecSeq initSt 0 0 p st' Vsa.While.Status.normal),
      Loaded L p c → st'.out = out →
      Vsa.Sim.TermSimAssembly.mExecSeq initSt 0 0 p st' Vsa.While.Status.normal t →
      Halts c out 0 := by
  intro p c out st' t hL hout hm
  obtain ⟨ra0, c1, hs, hChain, hcont⟩ := hPrologue p c out st' t hL hout hm
  -- the tail from the normal-return continuation lands the clean halt.
  have htail : Halts c1 out 0 := cleanExitTail ra0 out hChain c1 hcont
  -- prepend the prologue run `Steps c c1`.
  obtain ⟨c', σf, hs', hh', ho'⟩ := htail
  exact halts_of_steps_halted (hs.trans hs') hh' ho'

end Vsa.Sim
