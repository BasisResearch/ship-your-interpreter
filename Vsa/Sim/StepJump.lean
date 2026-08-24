import Vsa.Sim.Skeleton
import Vsa.Sim.ExecuteJump
import Vsa.Sim.Frame

/-!
# M2 jump-class validation — `step_jal` / `step_jalr` (step level)

Step-characterization lemmas (`Machine.Step` + `GoodState` preservation, tick and
notick variants) for the JAL and JALR instruction classes, including the
`rd = x0` pseudo forms (`j`/`jr`/`ret`). These compose the generic
`ExecuteJump.lean` execute clauses (`execute_jal_char` / `execute_jal_x0_char` /
`execute_jalr_char` / `execute_jalr_x0_char`) through the `try_step` skeleton
(`try_step_execute_char`), exactly as `StepAddi.lean` / `StepBeq.lean` do for
ADDI / BGEU.

## Symbolic word + decode hypothesis

Unlike `StepAddi`/`StepBeq` (which bake in a concrete spike word and prove its
decode), these lemmas keep the instruction word `w : BitVec 32` **symbolic**,
taking the four little-endian fetch bytes (`σ.mem[pc.toNat + k]? = some bₖ`, whose
`append` in fetch's big-endian order is `w`), the non-RVC fact
`extractLsb w 1 0 = 0b11#2`, and the decode fact
`(ext_decode w).run (afterPrelude σ) = .ok (JAL …/JALR …) (afterPrelude σ)`, all as
parameters, so a `DecodeTable` entry (concrete word, decode proof, `rd`/`rs1`)
plugs in downstream.

## The staged link value (skeleton subtlety)

The skeleton stages `nextPC := pc+4` **before** execute (`afterNextPC`). On the
skeleton's `σ₂` the staged `nextPC` value is `BitVec.addInt pc 4`, so
`ExecuteJump`'s `hnpc : σ₂.regs.get? nextPC = some link` forces
`link = BitVec.addInt pc 4` — the JAL/JALR link (`rd := pc+4`) comes out right
automatically. Execute overwrites `nextPC := target`, and the skeleton's postlude
sets `PC := target`; PC ends at the target, not pc+4.

## `rd` framing

For the non-`x0` forms `rd` is a GPR (non-pinned): the caller supplies the
`wX_bits rd` write as `hwr` (a `wX_bits_xN` fact), `NonPinned rd_reg`, and the
disequalities of `rd_reg` from the machine-mutated `∃`-registers it is read
through (`nextPC`, `minstret`, `minstret_increment`) — all `(by decide)` for a
concrete `rd_reg = xN`. `GoodState` is re-established with `Frame.lean`'s
`GoodState.insert_nonpinned` / `goodstate_frame`. The `x0` forms bake in the
`wX_bits_zero` no-op via the `_x0` execute variants (no `rd` write).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## JAL (rd ≠ x0) ---------------------------------------------------------- -/

/-- `σ₃` after `execute (JAL (imm, rd))` in the skeleton (non-`x0`): the prelude +
`nextPC := pc+4` state (`σ₂`) with `nextPC := pc + sext imm` overwritten, then
`rd_reg := link` (`link = pc+4`). -/
abbrev sigma3_jal (σ : MState) (pc : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
        (pc + sign_extend (m := 64) imm)} : MState) with
    regs := (({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
        (pc + sign_extend (m := 64) imm)} : MState)).regs.insert rd_reg link}

/-- Read-back of a register `R` distinct from `rd_reg` and `nextPC` through
`sigma3_jal`'s two-insert chain: equals reading `R` on `σ` (for
`minstret_increment` and `nextPC ≠ R`), delegating to the `afterNextPC`/
`afterPrelude` frame lemmas of `StepAddi.lean`. -/
theorem get?_sigma3_jal_pinned (σ : MState) (pc : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (hrd : (rd_reg == R) = false)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigma3_jal σ pc imm rd_reg link).regs.get? R = σ.regs.get? R := by
  show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} : MState)).regs.insert rd_reg link).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hnpc, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R hnpc hmi

/-- **`try_step` on a symbolic JAL word** (`rd ≠ x0`). -/
theorem try_step_jal
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link)) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
            regs := (({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec : (execute (instruction.JAL (imm, rd))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_jal σ pc imm rd_reg link) :=
    execute_jal_char imm rd (BitVec.addInt pc 4) pc _ (afterNextPC (afterPrelude σ) pc) _
      (by show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
          rw [Std.ExtDHashMap.get?_insert_self])
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa)
      htgt hwr
  have hhart₃ : (sigma3_jal σ pc imm rd_reg link).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigma3_jal_pinned σ pc imm rd_reg _ _ hrd_hart (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigma3_jal σ pc imm rd_reg link).regs.get? Register.nextPC = some (pc + sign_extend (m := 64) imm) := by
    show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} : MState)).regs.insert rd_reg _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [hrd_npc, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_jal σ pc imm rd_reg link).regs.get? Register.minstret_increment = some true := by
    show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} : MState)).regs.insert rd_reg _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [hrd_mi, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_jal σ pc imm rd_reg link).regs.get? Register.minstret = some vminstret := by
    rw [get?_sigma3_jal_pinned σ pc imm rd_reg _ _ hrd_ms (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (pc + sign_extend (m := 64) imm)
    (((b3.append b2).append b1).append b0)
    (instruction.JAL (imm, rd))
    (sigma3_jal σ pc imm rd_reg link) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## JALR (rd ≠ x0) ---------------------------------------------------------

JALR's execute is `execute_jalr_char`: it additionally reads `rs1` (via
`rX_bits rs1`), and the branch target is `BitVec.update (rs1 + sext imm) 0 0#1`
(bit 0 cleared). The post-state shape mirrors JAL's — `nextPC := target` then
`rd_reg := link` — but the target is the JALR one, so we reuse the same
`sigma3_jal`-style two-insert `abbrev` specialized to that target. -/

/-- `σ₃` after `execute (JALR (imm, rs1, rd))` in the skeleton (non-`x0`): the
prelude + `nextPC := pc+4` state (`σ₂`) with `nextPC := target` overwritten
(`target = BitVec.update (rs1 + sext imm) 0 0#1`), then `rd_reg := link`
(`link = pc+4`). -/
abbrev sigma3_jalr (σ : MState) (pc : BitVec 64) (tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt} : MState) with
    regs := (({(afterNextPC (afterPrelude σ) pc) with
      regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt} : MState)).regs.insert rd_reg link}

/-- Read-back of `R` distinct from `rd_reg` and `nextPC` through `sigma3_jalr`'s
two-insert chain: equals reading `R` on `σ` (for `minstret_increment` and
`nextPC ≠ R`), delegating to the `afterNextPC` frame lemma. (Identical body to
`get?_sigma3_jal_pinned` — the target value is irrelevant to the read-back.) -/
theorem get?_sigma3_jalr_pinned (σ : MState) (pc : BitVec 64) (tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (hrd : (rd_reg == R) = false)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigma3_jalr σ pc tgt rd_reg link).regs.get? R = σ.regs.get? R := by
  show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt} : MState)).regs.insert rd_reg link).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hrd, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hnpc, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R hnpc hmi

/-- **`try_step` on a symbolic JALR word** (`rd ≠ x0`). Mirrors `try_step_jal`;
`hrs1` supplies the `rX_bits rs1` read (JALR's extra source), `htgt` the alignment
side condition on the bit-0-cleared target, and `hwr` the `rd := link` write. The
control-plane pins (`hpriv`/`hsec`) come from `GoodState`; the target is
`BitVec.update (vrs1 + sext imm) 0 0#1`. -/
theorem try_step_jalr
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link)) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) with regs := (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.insert Register.PC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}) : MState) with
            regs := (({(sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) with regs := (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.insert Register.PC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec : (execute (instruction.JALR (imm, rs1, rd))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) :=
    execute_jalr_char imm rs1 rd (BitVec.addInt pc 4) vrs1 (afterNextPC (afterPrelude σ) pc) _
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg)
      (by show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
          rw [Std.ExtDHashMap.get?_insert_self])
      hrs1 htgt hwr
  have hhart₃ : (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigma3_jalr_pinned σ pc _ rd_reg _ _ hrd_hart (by decide) (by decide)]
    exact hG.hart_state
  have hnextPC₃ : (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.nextPC = some (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) := by
    show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)} : MState)).regs.insert rd_reg _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [hrd_npc, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.minstret_increment = some true := by
    show ((({(afterNextPC (afterPrelude σ) pc) with regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)} : MState)).regs.insert rd_reg _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [hrd_mi, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.minstret = some vminstret := by
    rw [get?_sigma3_jalr_pinned σ pc _ rd_reg _ _ hrd_ms (by decide) (by decide)]
    exact hminstret
  exact try_step_execute_char σ u pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)
    (((b3.append b2).append b1).append b0)
    (instruction.JALR (imm, rs1, rd))
    (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## `x0` pseudo forms (`j = jal x0`, `jr`/`ret = jalr x0`) -----------------

The `rd = x0` execute lemmas (`execute_jal_x0_char` / `execute_jalr_x0_char`)
conclude a **single** `nextPC := target` insert (the `wX_bits x0` write is a
`wX_bits_zero` no-op) — a DIFFERENT `σ₃` shape than the two-insert `sigma3_jal` /
`sigma3_jalr` (which carry the extra `rd_reg := link` write). So we cover them
with their own single-insert `σ₃` (`sigma3_jump_x0`, shared by both x0 forms —
only the target differs) and dedicated `try_step` lemmas. -/

/-- `σ₃` after `execute (JAL/JALR x0)` in the skeleton: `afterNextPC (afterPrelude
σ) pc` with `nextPC := tgt` overwritten. No `rd` write (the `x0` write is a
no-op). Shared by `j` (tgt = pc + sext imm) and `jr`/`ret` (tgt = bit-0-cleared
rs1+sext imm). -/
abbrev sigma3_jump_x0 (σ : MState) (pc : BitVec 64) (tgt : BitVec 64) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt}

/-- Read-back of `R ∉ {nextPC}` through `sigma3_jump_x0`'s single insert equals
reading `R` on `σ` (given `nextPC ≠ R` and `minstret_increment ≠ R`). -/
theorem get?_sigma3_jump_x0_pinned (σ : MState) (pc : BitVec 64) (tgt : BitVec 64)
    (R : Register)
    (hnpc : (Register.nextPC == R) = false)
    (hmi : (Register.minstret_increment == R) = false) :
    (sigma3_jump_x0 σ pc tgt).regs.get? R = σ.regs.get? R := by
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC tgt).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hnpc, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R hnpc hmi

/-- **`try_step` on a symbolic `j` word** (`jal x0`). As `try_step_jal` but the
`rd = x0` write is elided (via `execute_jal_x0_char`), so `σ₃` is the single
`nextPC := pc + sext imm` insert `sigma3_jump_x0`. -/
theorem try_step_j
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)) with regs := (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
            regs := (({(sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)) with regs := (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec : (execute (instruction.JAL (imm, regidx.Regidx 0x00#5))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)) :=
    execute_jal_x0_char imm (BitVec.addInt pc 4) pc _ (afterNextPC (afterPrelude σ) pc)
      (by show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
          rw [Std.ExtDHashMap.get?_insert_self])
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa)
      htgt
  have hhart₃ : (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigma3_jump_x0_pinned σ pc _ _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.get? Register.nextPC = some (pc + sign_extend (m := 64) imm) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.get? Register.minstret_increment = some true := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)).regs.get? Register.minstret = some vminstret := by
    rw [get?_sigma3_jump_x0_pinned σ pc _ _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (pc + sign_extend (m := 64) imm)
    (((b3.append b2).append b1).append b0)
    (instruction.JAL (imm, regidx.Regidx 0x00#5))
    (sigma3_jump_x0 σ pc (pc + sign_extend (m := 64) imm)) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-- **`try_step` on a symbolic `jr`/`ret` word** (`jalr x0`). As `try_step_jalr`
but the `rd = x0` write is elided (via `execute_jalr_x0_char`), so `σ₃` is the
single `nextPC := target` insert `sigma3_jump_x0`. -/
theorem try_step_jr
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) with regs := (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.insert Register.PC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}) : MState) with
            regs := (({(sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) with regs := (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.insert Register.PC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
    fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      hnotrvc
  have hdec' : (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  have hexec : (execute (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) :=
    execute_jalr_x0_char imm rs1 (BitVec.addInt pc 4) vrs1 (afterNextPC (afterPrelude σ) pc)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.misa)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg)
      (by show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
          rw [Std.ExtDHashMap.get?_insert_self])
      hrs1 htgt
  have hhart₃ : (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    rw [get?_sigma3_jump_x0_pinned σ pc _ _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.nextPC = some (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.minstret_increment = some true := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((σ.regs.insert Register.minstret_increment true).insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.minstret = some vminstret := by
    rw [get?_sigma3_jump_x0_pinned σ pc _ _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)
    (((b3.append b2).append b1).append b0)
    (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5))
    (sigma3_jump_x0 σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## `sigmaPost` states and their `GoodState` / `htif_done` read-backs

Four final-state (`σ₅`) shapes, one per jump form. The `_jal` / `_jalr` shapes
carry the `rd := link` write; the `_j` / `_jr` (x0) shapes do not. Each is the
skeleton write-chain `sigma3_… → PC := target → minstret := v+1`. `GoodState` is
one `goodstate_frame` line; `htif_done` reads back `false` through the chain. -/

/-- JAL (rd≠x0) final state. -/
abbrev sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {(({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
    regs := (({(sigma3_jal σ pc imm rd_reg link) with regs := (sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- JALR (rd≠x0) final state. -/
abbrev sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) : MState :=
  {(({(sigma3_jalr σ pc tgt rd_reg link) with regs := (sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt}) : MState) with
    regs := (({(sigma3_jalr σ pc tgt rd_reg link) with regs := (sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- `j` / `jr` (x0) final state (single-insert `σ₃`). -/
abbrev sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) : MState :=
  {(({(sigma3_jump_x0 σ pc tgt) with regs := (sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt}) : MState) with
    regs := (({(sigma3_jump_x0 σ pc tgt) with regs := (sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Read-back of `R` outside the JAL write-set `{minstret, PC, rd_reg, nextPC,
minstret_increment}` through the JAL write chain equals reading from `σ`. -/
theorem get?_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_sigma3_jal_pinned σ pc imm rd_reg link R h3 h4 h5

/-- Read-back of `R` outside the JALR write-set through the JALR write chain. -/
theorem get?_sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_jalr σ pc tgt rd_reg link).regs.insert Register.PC tgt).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_sigma3_jalr_pinned σ pc tgt rd_reg link R h3 h4 h5

/-- Read-back of `R` outside the x0 write-set `{minstret, PC, nextPC,
minstret_increment}` through the x0 write chain. -/
theorem get?_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_jump_x0 σ pc tgt).regs.insert Register.PC tgt).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_sigma3_jump_x0_pinned σ pc tgt R h4 h5

/-- `GoodState` preserved by the JAL step (write-set disjoint from every pinned
field, given `rd_reg` non-pinned). -/
theorem goodstate_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (hrd : NonPinned rd_reg) (link : RegisterType rd_reg)
    (hG : GoodState σ) : GoodState (sigmaPost_jal σ pc vminstret imm rd_reg link) :=
  -- chain (innermost→outermost): minstret_increment, nextPC, nextPC, rd_reg, PC, minstret.
  -- `rd_reg` is a variable, so `goodstate_frame`'s `by decide` cannot discharge it;
  -- supply `hrd` explicitly for that insert.
  ((((((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (by decide) _).insert_nonpinned (r := rd_reg) hrd link).insert_nonpinned
    (by decide) _).insert_nonpinned (by decide) _)

/-- `GoodState` preserved by the JALR step. -/
theorem goodstate_sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (hrd : NonPinned rd_reg) (link : RegisterType rd_reg)
    (hG : GoodState σ) : GoodState (sigmaPost_jalr σ pc vminstret tgt rd_reg link) :=
  ((((((hG.insert_nonpinned (by decide) _).insert_nonpinned (by decide) _).insert_nonpinned
    (by decide) _).insert_nonpinned (r := rd_reg) hrd link).insert_nonpinned
    (by decide) _).insert_nonpinned (by decide) _)

/-- `GoodState` preserved by the x0 (`j`/`jr`) step. -/
theorem goodstate_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost_jump_x0 σ pc vminstret tgt) := by
  goodstate_frame hG

/-- `htif_done` reads back `false` on the JAL final state. -/
theorem htif_done_sigmaPost_jal (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (hrd : NonPinned rd_reg) (link : RegisterType rd_reg)
    (hG : GoodState σ) : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_jal σ pc vminstret imm rd_reg link _ (by decide) (by decide)
    (pin_of_isNonPinned hrd (by decide)) (by decide) (by decide)]
  exact hG.htif_done

/-- `htif_done` reads back `false` on the JALR final state. -/
theorem htif_done_sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (hrd : NonPinned rd_reg) (link : RegisterType rd_reg)
    (hG : GoodState σ) : (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_jalr σ pc vminstret tgt rd_reg link _ (by decide) (by decide)
    (pin_of_isNonPinned hrd (by decide)) (by decide) (by decide)]
  exact hG.htif_done

/-- `htif_done` reads back `false` on the x0 (`j`/`jr`) final state. -/
theorem htif_done_sigmaPost_jump_x0 (σ : MState) (pc vminstret tgt : BitVec 64)
    (hG : GoodState σ) : (sigmaPost_jump_x0 σ pc vminstret tgt).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_jump_x0 σ pc vminstret tgt _ (by decide) (by decide) (by decide) (by decide)]
  exact hG.htif_done

/-! ## `stepOnce` (no clock tick) -------------------------------------------- -/

/-- `stepOnce i u` on a JAL (`i+1 ≠ 2`): `try_step` (⇒ `false`, branch target
written to PC), then continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_jal_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_jal σ pc vminstret imm rd_reg link) := by
  have hts := try_step_jal σ u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
    hrd_npc hrd_mi hrd_ms hrd_hart hwr
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG
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

/-- `stepOnce i u` on a JALR (`i+1 ≠ 2`). -/
theorem stepOnce_jalr_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1))
      (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) := by
  have hts := try_step_jalr σ u pc vminstret vrs1 w imm rs1 rd rd_reg link b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
    hrd_npc hrd_mi hrd_ms hrd_hart hwr
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
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

/-- `stepOnce i u` on a `j` (`jal x0`, `i+1 ≠ 2`). -/
theorem stepOnce_j_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1))
      (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)) := by
  have hts := try_step_j σ u pc vminstret w imm b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG
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

/-- `stepOnce i u` on a `jr`/`ret` (`jalr x0`, `i+1 ≠ 2`). -/
theorem stepOnce_jr_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1))
      (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) := by
  have hts := try_step_jr σ u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG
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

/-! ## Tick states and `stepOnce` (with clock tick)

On the `i+1 = 2` boundary the model splices `tick_clock` (`Tick.lean`) over the
`sigmaPost` state, writing `mcycle`, `mtime`, `mip`. Built explicitly (not peeled
from an abbrev) per the record-update let-bomb gotcha. -/

/-- JAL tick final state: `sigmaPost_jal` + `tick_clock` writes. -/
noncomputable abbrev sigmaTick_jal
    (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_jal σ pc vminstret imm rd_reg link) with
    regs := (((((sigmaPost_jal σ pc vminstret imm rd_reg link).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- JALR tick final state. -/
noncomputable abbrev sigmaTick_jalr
    (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_jalr σ pc vminstret tgt rd_reg link) with
    regs := (((((sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- `j`/`jr` (x0) tick final state. -/
noncomputable abbrev sigmaTick_jump_x0
    (σ : MState) (pc vminstret tgt : BitVec 64)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_jump_x0 σ pc vminstret tgt) with
    regs := (((((sigmaPost_jump_x0 σ pc vminstret tgt).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- `stepOnce i u` on a JAL when `i+1 = 2` (clock tick). -/
theorem stepOnce_jal_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_jal σ pc vminstret imm rd_reg link vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_jal σ u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
    hrd_npc hrd_mi hrd_ms hrd_hart hwr
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG
  have htc := tick_clock_char (sigmaPost_jal σ pc vminstret imm rd_reg link) vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
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

/-- `stepOnce i u` on a JALR when `i+1 = 2` (clock tick). -/
theorem stepOnce_jalr_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_jalr σ u pc vminstret vrs1 w imm rs1 rd rd_reg link b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
    hrd_npc hrd_mi hrd_ms hrd_hart hwr
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
  have htc := tick_clock_char (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
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

/-- `stepOnce i u` on a `j` (`jal x0`) when `i+1 = 2` (clock tick). -/
theorem stepOnce_j_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_j σ u pc vminstret w imm b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG
  have htc := tick_clock_char (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)) vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
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

/-- `stepOnce i u` on a `jr`/`ret` (`jalr x0`) when `i+1 = 2` (clock tick). -/
theorem stepOnce_jr_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_jr σ u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
    hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG
  have htc := tick_clock_char (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) vmip vmtime vmtimecmp vmcycle
    hGp.cur_privilege hGp.mcountinhibit hGp.mcyclecfg hGp.menvcfg hGp.misa
    hmip hmtime hmtimecmp hmcycle hGp.sig_meip hGp.sig_seip
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

/-! ## `Machine.Step` wrappers ------------------------------------------------ -/

/-- **`step_jal` (no clock tick).** One architectural step on a JAL (`rd ≠ x0`),
wrapped as `Vsa.Machine.Step`, with `GoodState` preserved. -/
theorem step_jal_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_jal σ pc vminstret imm rd_reg link, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_jal σ pc vminstret imm rd_reg link) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_jal_notick σ i u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick),
   goodstate_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG⟩

/-- **`step_jalr` (no clock tick).** -/
theorem step_jalr_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_jalr_notick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick),
   goodstate_sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG⟩

/-- **`step_j` (`jal x0`, no clock tick).** -/
theorem step_j_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm), i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_j_notick σ i u pc vminstret w imm b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt htick),
   goodstate_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG⟩

/-- **`step_jr` / `ret` (`jalr x0`, no clock tick).** -/
theorem step_jr_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1), i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_jr_notick σ i u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
      hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt htick),
   goodstate_sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG⟩

/-- **`step_jal` (with clock tick).** As `step_jal_notick` on the `i+1 = 2`
boundary: tick counter resets to `0`, `σ''` carries the `tick_clock` write chain.
`GoodState` preserved (tick touches only `mcycle`/`mtime`/`mip`). -/
theorem step_jal_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, rd)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (pc + sign_extend (m := 64) imm)}
        = .ok () (sigma3_jal σ pc imm rd_reg link))
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_jal σ pc vminstret imm rd_reg link vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_jal σ pc vminstret imm rd_reg link vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_jal_tick σ i u pc vminstret w imm rd rd_reg link b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick), ?_⟩
  have hGp := goodstate_sigmaPost_jal σ pc vminstret imm rd_reg hrd link hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-- **`step_jalr` (with clock tick).** -/
theorem step_jalr_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_jalr_tick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick), ?_⟩
  have hGp := goodstate_sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-- **`step_j` (`jal x0`, with clock tick).** -/
theorem step_j_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (w : BitVec 32) (imm : BitVec 21) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm)).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JAL (imm, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_j_tick σ i u pc vminstret w imm b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec htgt htick), ?_⟩
  have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) imm) hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-- **`step_jr` / `ret` (`jalr x0`, with clock tick).** -/
theorem step_jr_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 : regidx) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)).regs.get? Register.mcycle = some vmcycle)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_jr_tick σ i u pc vminstret vrs1 w imm rs1 b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt htick), ?_⟩
  have hGp := goodstate_sigmaPost_jump_x0 σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

end Vsa.Sim
