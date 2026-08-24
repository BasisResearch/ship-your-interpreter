import Vsa.Sim.Fetch
import Vsa.Sim.InitValues
import Vsa.Sim.RegAccess

/-!
# M2 jump-class validation — generic execute characterizations for JAL/JALR

Execute-clause characterizations of the model's `JAL` and `JALR` classes over an
arbitrary symbolic `SequentialState`, in the hypothesis-style register-access
convention of `Vsa/Sim/ExecuteAlu.lean` and the `jump_to`/alignment machinery of
`Vsa/Sim/ExecuteBranch.lean`. These cover the binary's `jal`/`j`/`jalr`/`jr`/`ret`
/`call` pseudo-forms — the largest instruction class.

## The JAL clause (`execute_JAL`, InstsEnd.lean:6800)

```
let link_address ← get_next_pc ()          -- readReg nextPC
match ← jump_to ((← readReg PC) + sext imm) with
| Retire_Success () => wX_bits rd link_address; pure (Retire_Success ())
| failure => pure failure
```

So JAL reads, in order: `nextPC` (the link value `pc+4` staged by the
`run_hart_active` prelude), then `PC` (target base), then `misa` (the forced
`Ext_Zca` read inside `jump_to`, short-circuited by `target[1] = 0`). On success
it writes `nextPC := PC + sext imm` (via `jump_to`'s `set_next_pc`) then
`rd := link_address`, in that program order.

## The JALR clause (`execute_JALR`, InstsEnd.lean:6789)

```
update_elp_state rs1                        -- Zicfilp-guarded elp write (no-op here)
let link_address ← get_next_pc ()           -- readReg nextPC
let target ← (← rX_bits rs1) + sext imm
match ← jump_to (BitVec.update target 0 0#1) with   -- clear bit 0
| Retire_Success () => wX_bits rd link_address; pure (Retire_Success ())
| failure => pure failure
```

`update_elp_state` guards its `elp` write on `currentlyEnabled Ext_Zicfilp`, which
at the pinned control-plane values (`misa = initMisa`, `cur_privilege = Machine`,
`mseccfg = 0`) is `false` (`get_xLPE Machine = MLPE(mseccfg) = 0`), so it is a
state-preserving no-op reading only `{misa, cur_privilege, mseccfg}`. JALR then
reads `nextPC` (link), `rs1` (target base), and `misa` (Zca in `jump_to`). The
target has bit 0 cleared by `BitVec.update target 0 0#1`; the alignment side
condition is on that cleared target. On success it writes `nextPC := target'`
then `rd := link_address`.

## Design

Both `execute_*_char` lemmas thread the state through the two writes:
`jump_to`'s `nextPC := target` insert lands first (giving `σ₁`), and the `rd`
write is stated as a hypothesis `hwr` **at `σ₁`** so the caller supplies the real
`x<rd>` insert (or, for `rd = x0`, the `wX_bits_zero` no-op — see the `_x0`
variants). The link value is the read `nextPC` value.

## rd = x0 (`j` / `jr`)

`jal x0` (the `j` pseudo, and `jr`/`ret` = `jalr x0`) writes `x0`, which
`wX_bits_zero` shows is a state-preserving no-op. Those callers use the same
`hwr` slot with `wX_bits_zero`, so no separate lemma is needed — but for caller
convenience the `_x0` variants below bake the `x0` write in, concluding `σ₁`
directly (no `hwr` hypothesis).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `update_elp_state` no-op (JALR prelude)

Under the pinned control-plane values, `update_elp_state rs1` is a
state-preserving no-op: `currentlyEnabled Ext_Zicfilp` is `false` (its `get_xLPE
Machine` factor reads `mseccfg = 0` ⇒ `MLPE = 0`, and the `Zicsr` factor needs no
register), so the `if` picks `pure ()`. Reads only `{cur_privilege, mseccfg}`. -/
theorem update_elp_state_noop (σ : SequentialState RegisterType trivialChoiceSource)
    (rs1 : regidx)
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg)) :
    (update_elp_state rs1).run σ = .ok () σ := by
  simp only [update_elp_state]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg]
  simp only [show bool_bit_backwards (_get_Seccfg_MLPE (0#64)) = false from by decide,
    Bool.false_eq_true, if_false, EStateM.pure]

/-! ## `get_next_pc` read (the link value)

`get_next_pc () = readReg nextPC`, state-preserving. -/
theorem get_next_pc_char (σ : SequentialState RegisterType trivialChoiceSource)
    (link : BitVec 64) (h : σ.regs.get? Register.nextPC = some link) :
    (get_next_pc ()).run σ = .ok link σ := by
  simp only [get_next_pc, PreSail.readReg, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get, h]

/-! ## JAL -/

/-- **JAL** execute clause (`rd ≠ x0`). Reads `nextPC` (link), `PC` (target base),
`misa` (Zca in `jump_to`). Writes `nextPC := pc + sext imm` then `rd := link`.

The target `pc + sext imm` is 4-aligned (`htgt`), so `jump_to`'s `assert
target[0]==0` and the `target[1]`-guarded misaligned check both discharge; the
resulting `σ₁ = {σ with nextPC := target}` is the state for the `rd` write `hwr`. -/
theorem execute_jal_char
    (imm : BitVec 21) (rd : regidx) (link pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hwr : (wX_bits rd link).run
        {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)}
        = .ok () σ') :
    (execute (instruction.JAL (imm, rd))).run σ = .ok RETIRE_SUCCESS σ' := by
  have hlink := get_next_pc_char σ link hnpc
  simp only [EStateM.run] at hlink hwr
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_JAL, EStateM.run, bind, EStateM.bind, pure]
  rw [hlink]
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
  simp only [RETIRE_SUCCESS, EStateM.bind, EStateM.pure]
  rw [hwr]

/-! ## JALR -/

/-- **JALR** execute clause (`rd ≠ x0`). Runs the `update_elp_state` no-op prelude
(reads `cur_privilege`, `mseccfg`), then reads `nextPC` (link), `rs1` (target
base), `misa` (Zca in `jump_to`). The target is `(rs1 + sext imm)` with bit 0
cleared (`BitVec.update _ 0 0#1`); the alignment side condition `htgt` is on that
cleared target. Writes `nextPC := target'` then `rd := link`.

Requires the same control-plane pins as decode (`misa = initMisa`,
`cur_privilege = Machine`, `mseccfg = 0`) to discharge the Zicfilp-guarded
`update_elp_state`. -/
theorem execute_jalr_char
    (imm : BitVec 12) (rs1 rd : regidx) (link vrs1 : BitVec 64)
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg))
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hrs1 : (rX_bits rs1).run σ = .ok vrs1 σ)
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hwr : (wX_bits rd link).run
        {σ with regs := σ.regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () σ') :
    (execute (instruction.JALR (imm, rs1, rd))).run σ = .ok RETIRE_SUCCESS σ' := by
  have help := update_elp_state_noop σ rs1 hpriv hsec
  have hlink := get_next_pc_char σ link hnpc
  simp only [EStateM.run] at help hlink hrs1 hwr
  have hb0 := access_bit0 _ htgt
  have hb1 := access_bit1 _ htgt
  have hzca := currentlyEnabled_Zca σ _ hmisa
  simp only [EStateM.run] at hzca
  simp only [execute, execute_JALR, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    help, hlink, hrs1]
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
  simp only [RETIRE_SUCCESS, EStateM.bind, EStateM.pure]
  rw [hwr]

/-! ## rd = x0 convenience variants (`j` / `jr` / `ret`)

`jal x0` (the `j` pseudo — 856 words) and `jalr x0` (`jr` / `ret`) write `x0`,
which `wX_bits_zero` shows is a state-preserving no-op. These variants bake that
in, concluding the single `nextPC := target` insert (`σ₁`) directly, so callers
need supply no `hwr`. -/

/-- **`j` pseudo** (`jal x0`): as `execute_jal_char` with the `rd = x0` write
elided (state-preserving). Result is the single `nextPC := pc + sext imm` insert. -/
theorem execute_jal_x0_char
    (imm : BitVec 21) (link pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0) :
    (execute (instruction.JAL (imm, regidx.Regidx 0x00#5))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)} :=
  execute_jal_char imm (regidx.Regidx 0x00#5) link pc vmisa σ _ hnpc hpc hmisa htgt
    (wX_bits_zero _ link)

/-- **`jr` / `ret`** (`jalr x0`): as `execute_jalr_char` with the `rd = x0` write
elided. Result is the single `nextPC := target'` insert (`target'` = rs1 + sext
imm, bit 0 cleared). -/
theorem execute_jalr_x0_char
    (imm : BitVec 12) (rs1 : regidx) (link vrs1 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : σ.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg))
    (hnpc : σ.regs.get? Register.nextPC = some link)
    (hrs1 : (rX_bits rs1).run σ = .ok vrs1 σ)
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0) :
    (execute (instruction.JALR (imm, rs1, regidx.Regidx 0x00#5))).run σ
      = .ok RETIRE_SUCCESS
          {σ with regs := σ.regs.insert Register.nextPC (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)} :=
  execute_jalr_char imm rs1 (regidx.Regidx 0x00#5) link vrs1 σ _ hmisa hpriv hsec hnpc hrs1 htgt
    (wX_bits_zero _ link)

end Vsa.Sim
