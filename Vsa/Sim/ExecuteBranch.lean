import Vsa.Sim.Fetch

/-!
# M2 branch-class validation — generic execute characterizations for BTYPE

Execute-clause characterizations of the model's `BTYPE` branch class over an
arbitrary symbolic `SequentialState`, generalizing the concrete BGEU pattern of
`Vsa/Sim/StepBeq.lean` (`execute_bgeu_taken`/`execute_bgeu_nottaken`) to the five
remaining branch operations `{BEq, BNe, BLt, BGe, BLtu}` and to arbitrary
register indices / immediates / values (the hypothesis-style register-access
convention of `Vsa/Sim/ExecuteAlu.lean`).

## The BTYPE clause (`execute_BTYPE`, InstsEnd.lean:7018)

```
let taken ← match op with
  | BEQ  => pure ((← rX_bits rs1) == (← rX_bits rs2))
  | BNE  => pure ((← rX_bits rs1) != (← rX_bits rs2))
  | BLT  => pure (zopz0zI_s  (← rX_bits rs1) (← rX_bits rs2))   -- signed <
  | BGE  => pure (zopz0zKzJ_s (← rX_bits rs1) (← rX_bits rs2))  -- signed ≥
  | BLTU => pure (zopz0zI_u  (← rX_bits rs1) (← rX_bits rs2))   -- unsigned <
  | BGEU => pure (zopz0zKzJ_u (← rX_bits rs1) (← rX_bits rs2))  -- unsigned ≥ (StepBeq)
if taken then jump_to ((← readReg PC) + sign_extend imm) else pure RETIRE_SUCCESS
```

So the two source GPRs are read in order (`rs1` then `rs2`), both
state-preserving, then—on the taken branch—`PC` (target base) and `misa` (the
`Ext_Zca` read forced inside `jump_to`, short-circuited by `target[1] = 0`).

## Design (mirrors ExecuteAlu + StepBeq)

Each op gets a **taken** and a **not-taken** lemma, generic over
`(imm : BitVec 13) (rs1 rs2 : regidx)` and the read values `(v1 v2 : BitVec 64)`:

* `hrs1 : (rX_bits rs1).run σ = .ok v1 σ`, `hrs2 : (rX_bits rs2).run σ = .ok v2 σ`
  — the two state-preserving source reads (both at the original `σ`);
* taken lemmas additionally take `hpc`, `hmisa`, and the **target** alignment
  `htgt : (pc + sign_extend imm).toNat % 4 = 0` (branch immediates encode
  `imm[0] = 0`, so the target is 4-aligned whenever `pc` is; we take it as a
  hypothesis to stay generic over `imm`);
* the branch-outcome trigger is the Bool guard the match arm reduces to, as a
  `= true` / `= false` hypothesis — mirroring StepBeq's `hle : zopz0zKzJ_u … = …`.

Taken conclusion: `nextPC := pc + sign_extend imm` (single insert). Not-taken
conclusion: state unchanged. Both tail in `RETIRE_SUCCESS`.

The proof spine is exactly StepBeq's `execute_bgeu_taken`/`_nottaken` with the
concrete `rX_bits_x5/x6` splices replaced by the generic `hrs1/hrs2`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Shared taken/not-taken tactic templates

The only per-op variation is the constructor `bop.Bxx`, the guard's reduced
Bool expression, and the simp lemma that collapses that guard once `hrs2`/`hv`
are spliced (`if_true` / `Bool.false_eq_true, if_false`). We inline the full
proof per op rather than a meta-template to keep each theorem self-contained and
its residual goal legible. -/

/-! ## BEQ (`v1 = v2` ⇒ guard `v1 == v2`) -/

/-- **Taken** BEQ: `(v1 == v2) = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_beq_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : (v1 == v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

/-- **Not-taken** BEQ: `(v1 == v2) = false` ⇒ state unchanged. -/
theorem execute_btype_beq_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : (v1 == v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## BNE (`v1 ≠ v2` ⇒ guard `v1 != v2`) -/

/-- **Taken** BNE: `(v1 != v2) = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_bne_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : (v1 != v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

/-- **Not-taken** BNE: `(v1 != v2) = false` ⇒ state unchanged. -/
theorem execute_btype_bne_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : (v1 != v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## BLT (signed `<` ⇒ guard `zopz0zI_s v1 v2`) -/

/-- **Taken** BLT: `zopz0zI_s v1 v2 = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_blt_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zI_s v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLT))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

/-- **Not-taken** BLT: `zopz0zI_s v1 v2 = false` ⇒ state unchanged. -/
theorem execute_btype_blt_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : zopz0zI_s v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLT))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## BGE (signed `≥` ⇒ guard `zopz0zKzJ_s v1 v2`) -/

/-- **Taken** BGE: `zopz0zKzJ_s v1 v2 = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_bge_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zKzJ_s v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGE))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

/-- **Not-taken** BGE: `zopz0zKzJ_s v1 v2 = false` ⇒ state unchanged. -/
theorem execute_btype_bge_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : zopz0zKzJ_s v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGE))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## BLTU (unsigned `<` ⇒ guard `zopz0zI_u v1 v2`) -/

/-- **Taken** BLTU: `zopz0zI_u v1 v2 = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_bltu_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zI_u v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLTU))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} := by
  simp only [EStateM.run] at hrs1 hrs2
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, if_true]
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

/-- **Not-taken** BLTU: `zopz0zI_u v1 v2 = false` ⇒ state unchanged. -/
theorem execute_btype_bltu_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : zopz0zI_u v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLTU))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

end Vsa.Sim
