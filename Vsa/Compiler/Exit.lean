import Vsa.Sim.ErrorTail

/-!
# The HTIF exit store at any exit code

`Vsa/Sim/ErrorTail.lean` proves that the `sd …, tohost` of the syscall-exit word
halts the machine in one `stepOnce`, for the interpreter's error code `70`.
Compiled programs also exit with code `0`, so the same four lemmas are stated
here for an arbitrary code `e` below `2^47` (the device byte stays zero).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps Halted Halts output)

namespace Vsa.Sim

abbrev sigmaExitE (e : BitVec 64) (σ : MState) (pc : BitVec 64) (data : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (((((afterNextPC (afterPrelude σ) pc).regs.insert Register.htif_cmd_write 1#1).insert
                Register.htif_payload_writes (0#4 + BitVec.ofInt 4 1)).insert
              Register.htif_tohost data).insert
            Register.htif_done true).insert
          Register.htif_exit_code e}

/-- `execute (STORE (imm, rs2, rs1, 8))` at `σ₂ = afterNextPC (afterPrelude σ) pc`
for the `_exit` `sd a5,tohost` store: the effective address `v1 + sign_extend imm`
is `tohostAddr`, the store data `vdata` is the syscall-exit word `(e<<<1)|1`, and
the post-state is `sigmaExitE e σ pc data`.  Assembled from `execute_STORE_char` +
`vmem_write_addr_w` (w = 8) with `mem_write_value_tohost_exit` as the abstract
`mem_write_value` post-state. -/
theorem exec_sd_tohost_exitE (e : BitVec 64) (he : e.toNat < 2 ^ 47)
    (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (th : BitVec 64)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok v1 (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (haddr : v1 + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hdataeq : vdata = data)
    (hpw : σ.regs.get? Register.htif_payload_writes = some (0#4))
    (hth : σ.regs.get? Register.htif_tohost = some th)
    (hexit : data = (e <<< 1) ||| 1#64) :
    (execute (instruction.STORE (imm, rs2, rs1, 8))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigmaExitE e σ pc data) := by
  -- σ₂ control-plane read-backs through the prelude / nextPC frame.
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
  -- the bound keeping the exit device byte zero: `e < 2^47`.
  have hsmall : e.toNat < 2 ^ 47 := he
  -- `mem_write_value` at tohost → the HTIF exit transition (post-state = sigmaExitE).
  have hmwv := mem_write_value_tohost_exit (afterNextPC (afterPrelude σ) pc) e data
    initMstatus initPmpaddr th hpriv hmstatus (by decide) hpma hcfg hpaddr hbase hpw₂ hth₂ hsmall hexit
  -- the abstract lower-chain hypotheses for vmem_write_addr_w at a = tohostAddr.
  have hatohost : (BitVec.ofNat 64 tohostAddr).toNat = tohostAddr := by
    simp only [tohostAddr]; decide
  have htr := translateAddr_machine_store (afterNextPC (afterPrelude σ) pc)
    (BitVec.ofNat 64 tohostAddr) initMstatus hpriv hmstatus (by decide)
  have hea := mem_write_ea_8 (afterNextPC (afterPrelude σ) pc) (BitVec.ofNat 64 tohostAddr)
    initMstatus initPmpaddr hpriv hmstatus (by decide) hpma hcfg hpaddr
    (by rw [hatohost]; exact (by decide : (0x80000000 : Nat) ≤ tohostAddr))
    (by rw [hatohost]; exact (by decide : tohostAddr + 8 ≤ 0x100000000))
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
  -- collapse the extract-of-data on the width-8 store word.
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
  -- vmem_write_addr on the tohost address, w = 8, post-state = sigmaExitE.
  have hwrite := vmem_write_addr_w (afterNextPC (afterPrelude σ) pc) (sigmaExitE e σ pc data)
    (BitVec.ofNat 64 tohostAddr) 8 data initMstatus (by decide) (by decide)
    (by rw [hatohost]; exact (by decide : tohostAddr % 8 = 0))
    (by rw [hatohost]; exact (by decide : (tohostAddr + (8 - 1)) / 4096 = tohostAddr / 4096))
    hmstatus hpriv (by decide) htr hea hmwv hwval
  -- `execute_STORE_char`, with `hwrite` at a = v1 + sign_extend imm = tohostAddr.
  have hchar := execute_STORE_char imm rs2 rs1 8 v1 vdata (afterNextPC (afterPrelude σ) pc)
    initMstatus (0#64) (sigmaExitE e σ pc data) (by decide)
    hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      rw [haddr, hdataeq, hwval]
      exact hwrite)
  simp only [execute]
  exact hchar

/-! ## The `try_step`-final state for the exit store

`sigmaExitFinalE e σ pc npc vminstret data` is the skeleton `σ₅` for the exit store:
`sigmaExitE` (execute post-state) with `PC := npc` and `minstret := vminstret+1`. -/

/-- The `try_step`-final state of the exit `sd a5,tohost` store. -/
abbrev sigmaExitFinalE (e : BitVec 64) (σ : MState) (pc npc vminstret data : BitVec 64) : MState :=
  {(({(sigmaExitE e σ pc data) with
        regs := (sigmaExitE e σ pc data).regs.insert Register.PC npc}) : MState) with
    regs := ((({(sigmaExitE e σ pc data) with
        regs := (sigmaExitE e σ pc data).regs.insert Register.PC npc}) : MState).regs.insert
          Register.minstret (BitVec.addInt vminstret 1))}

/-- **`try_step` on the exit `sd a5,tohost` store.**  The store latches the HTIF
exit registers (`htif_done := true`, `htif_exit_code := e`) via
`exec_sd_tohost_exitE`; the `try_step` postlude writes `PC := pc+4` and
`minstret := vminstret+1`.  Returns `false`. -/
theorem try_step_tohost_exitE (e : BitVec 64) (he : e.toNat < 2 ^ 47)
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (th : BitVec 64)
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
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ = .ok false (sigmaExitFinalE e σ pc (BitVec.addInt pc 4) vminstret data) := by
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
  have hexec := exec_sd_tohost_exitE e he σ pc imm rs2 rs1 v1 vdata data th
    hG hrs1 hrs2 haddr hdataeq hpw hth hexit
  -- postlude read-backs on σ₃ = sigmaExitE (through the five HTIF inserts).
  have hframe : ∀ R : Register,
      (Register.htif_exit_code == R) = false → (Register.htif_done == R) = false →
      (Register.htif_tohost == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_cmd_write == R) = false →
      (sigmaExitE e σ pc data).regs.get? R = (afterNextPC (afterPrelude σ) pc).regs.get? R := by
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
  have hhart₃ : (sigmaExitE e σ pc data).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigmaExitE e σ pc data).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigmaExitE e σ pc data).regs.get? Register.minstret_increment = some true := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide,
      dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigmaExitE e σ pc data).regs.get? Register.minstret = some vminstret := by
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide),
      get?_afterNextPC σ pc _ (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0) (instruction.STORE (imm, rs2, rs1, 8))
    (sigmaExitE e σ pc data) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## The exit-store `stepOnce` halts

`stepOnce i u` on the `_exit` `sd a5,tohost` store: `try_step` performs the store
(⇒ `false`, HTIF exit latched), then the *same* `stepOnce` re-checks `htif_done`
(`Elf.lean:86`) — now `true` — and returns `.inl (some e, u+1)`.  This is a
`Halted` node.  No `tick_clock`. -/

/-- `htif_done` reads `true` on the exit-store post-state (`sigmaExitE`): the store
latched `htif_done := true`; the `try_step` postlude (`PC`/`minstret`) and the two
HTIF inserts leave it in place. -/
theorem htif_done_sigmaExit_finalE (e : BitVec 64) (σ : MState) (pc npc vminstret data : BitVec 64) :
    (sigmaExitFinalE e σ pc npc vminstret data).regs.get? Register.htif_done = some true := by
  show (((((sigmaExitE e σ pc data).regs.insert Register.PC npc).insert
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

/-- `htif_exit_code` reads `e` on the exit-store post-state (`sigmaExitE`). -/
theorem htif_exit_code_sigmaExit_finalE (e : BitVec 64) (σ : MState) (pc npc vminstret data : BitVec 64) :
    (sigmaExitFinalE e σ pc npc vminstret data).regs.get? Register.htif_exit_code = some e := by
  show (((((sigmaExitE e σ pc data).regs.insert Register.PC npc).insert
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

/-- `sailOutput` is unchanged by the exit-store `try_step`-final state: the store
touches only HTIF control registers, the postlude only `PC`/`minstret`; none write
`sailOutput`. -/
theorem sailOutput_sigmaExit_finalE (e : BitVec 64) (σ : MState) (pc npc vminstret data : BitVec 64) :
    (sigmaExitFinalE e σ pc npc vminstret data).sailOutput = σ.sailOutput := rfl

/-- **The exit-store `stepOnce` halts (`Elf.lean:86`).**  `stepOnce i u` runs
`try_step` (performing the store, latching HTIF exit), then re-checks `htif_done`
— now `true` — and returns `.inl (some e, u+1)`.  So the whole `stepOnce` is a
single halting node with exit code `e` in the post-state `sigmaExitFinalE`. -/
theorem stepOnce_tohost_exitE (e : BitVec 64) (he : e.toNat < 2 ^ 47)
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : regidx)
    (v1 vdata data : BitVec 64) (th : BitVec 64)
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
    (hexit : data = (e <<< 1) ||| 1#64)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (stepOnce i u).run σ
      = .ok (.inl (some e.toNat, u + 1)) (sigmaExitFinalE e σ pc (BitVec.addInt pc 4) vminstret data) := by
  have hts := try_step_tohost_exitE e he σ u pc vminstret w imm rs2 rs1 v1 vdata data th b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hrs1 hrs2 haddr hdataeq hpw hth hexit
    hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hdone' := htif_done_sigmaExit_finalE e σ pc (BitVec.addInt pc 4) vminstret data
  have hcode' := htif_exit_code_sigmaExit_finalE e σ pc (BitVec.addInt pc 4) vminstret data
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, if_false]
  rw [hts]
  simp only [Bool.false_eq_true, if_false, EStateM.pure, EStateM.bind, EStateM.get,
    hdone', if_true, hcode']

end Vsa.Sim
