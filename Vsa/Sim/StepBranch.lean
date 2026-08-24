import Vsa.Sim.Skeleton
import Vsa.Sim.StepAddi
import Vsa.Sim.StepBeq
import Vsa.Sim.ExecuteBranch
import Vsa.Sim.Frame

/-!
# M2 branch-class validation — generic `step_branch` for all six BTYPE ops

Step-characterization (`Machine.Step` + `GoodState` preservation) for the entire
branch class, generalizing `Vsa/Sim/StepBeq.lean` (which did BGEU only, notick
only) to all six operations `{BEQ, BNE, BLT, BGE, BLTU, BGEU}` and adding the
missing **tick** variants (StepBeq has none).

## Factoring: generic over `op`, abstract `hexec`

The skeleton `try_step_execute_char` (`Skeleton.lean`) is already
instruction-generic: it takes the decoded `ast` and the execute step `hexec` as
an abstract `.run`-form hypothesis. The five taken-execute clauses of
`ExecuteBranch.lean` all produce the **identical** post-state shape (a single
`nextPC := pc + sign_extend imm` insert), and the not-taken ones are all
state-identity. So we prove **one** generic pair

* `try_step_branch_taken` — parameterized by `(imm, rs2, rs1, op)`, `w`, a
  symbolic decode fact `hdec`, and an abstract execute hypothesis
  `hexec : (execute ast).run … = .ok RETIRE_SUCCESS <single nextPC insert>`;
* `try_step_branch_nottaken` — same, with `hexec` producing state-identity;

plus their `stepOnce`/`Step` wrappers, both **notick** and **tick**. Each
concrete op is then a one-line instantiation supplying the `ExecuteBranch`
execute lemma as `hexec`. The `hexec`-builder `example`s at the end confirm all
six `ExecuteBranch` taken/not-taken clauses land in exactly the
`sigma3_branch_{taken,nottaken}` shape the generic lemmas consume, so each of the
six ops plugs into `step_branch_*` as a one-liner (the concrete registers /
immediate / decoded word are supplied downstream from the DecodeTable).

This is the STRONGLY-PREFERRED factoring of the task: the abstract-`hexec`
plumbing composes cleanly with the skeleton because the skeleton never inspects
`ast`; only the caller-supplied `hdec`/`hexec` mention it.

## Symbolic decode + fetch bytes

`hdec` is kept symbolic: we take `w : BitVec 32`, the four little-endian code
bytes `b0..b3` with `w = append …` and a `hword` bridge, and
`hdec : (ext_decode w).run (afterPrelude σ) = .ok (BTYPE …) (afterPrelude σ)` as
a parameter — so the 10,399-entry DecodeTable plugs in downstream. The fetch
byte hypotheses stay `σ.mem[pc+k]? = some b` as in StepBeq. The non-RVC fact
(`extractLsb w 1 0 = 0b11`) is a parameter too.

## Naming

`sigma3_branch_taken σ pc imm` / `sigma3_branch_nottaken σ pc` are the
op-independent generalizations of StepBeq's `sigma3_taken`/`sigma3_nottaken`
(BGEU-specialized to `imm = 0x010`). `sigmaPost_branch_taken` /
`sigmaPost_branch_nottaken` are the final `try_step` states; `GoodState` on them
is discharged by the `goodstate_frame` tactic (`Frame.lean`). The tick states
reuse `sigmaTick`-style chains but are built explicitly (the let-bomb gotcha,
Frame.lean §Record-update let bombs).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The skeleton's `σ₃` for each branch outcome (op-independent) -/

/-- Taken `σ₃`: `afterNextPC (afterPrelude σ) pc` (holding `nextPC := pc+4` from
the prelude) with `nextPC` overwritten by `jump_to`'s `set_next_pc` to the branch
target `pc + sign_extend imm`. Op-independent (all taken clauses share this). -/
abbrev sigma3_branch_taken (σ : MState) (pc : BitVec 64) (imm : BitVec 13) : MState :=
  {(afterNextPC (afterPrelude σ) pc) with
    regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
      (pc + sign_extend (m := 64) imm)}

/-- Not-taken `σ₃`: the execute clause leaves state untouched, so `σ₃` is exactly
the prelude state `afterNextPC (afterPrelude σ) pc` (nextPC = pc+4). -/
abbrev sigma3_branch_nottaken (σ : MState) (pc : BitVec 64) : MState :=
  afterNextPC (afterPrelude σ) pc

/-! ## Generic BGEU execute clauses

`ExecuteBranch.lean` covers `{BEQ, BNE, BLT, BGE, BLTU}` generically; BGEU exists
only in the *concrete* `execute_bgeu_*` of `StepBeq.lean` (specialized to `x5`/`x6`
and `imm = 0x010`). We add the generic BGEU clauses here (same template as
`ExecuteBranch`), so the whole six-op class has generic `hexec` builders. -/

/-- **Taken** BGEU: `zopz0zKzJ_u v1 v2 = true` ⇒ `jump_to (pc + sext imm)`. -/
theorem execute_btype_bgeu_taken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 pc : BitVec 64)
    (vmisa : RegisterType Register.misa)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hpc : σ.regs.get? Register.PC = some pc)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hv : zopz0zKzJ_u v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run σ
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

/-- **Not-taken** BGEU: `zopz0zKzJ_u v1 v2 = false` ⇒ state unchanged. -/
theorem execute_btype_bgeu_nottaken
    (imm : BitVec 13) (rs1 rs2 : regidx) (v1 v2 : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hrs2 : (rX_bits rs2).run σ = .ok v2 σ)
    (hv : zopz0zKzJ_u v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run σ
      = .ok RETIRE_SUCCESS σ := by
  simp only [EStateM.run] at hrs1 hrs2
  simp only [execute, execute_BTYPE, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [hrs1]
  simp only [hrs2, hv, Bool.false_eq_true, if_false, EStateM.pure]

/-! ## Generic `try_step` on a taken branch (abstract `hexec`)

The instruction-specific work is delegated: `hdec` (the decode) and `hexec` (the
taken execute clause, producing the single-`nextPC` post-state). Everything else
is the shared skeleton prelude/postlude, paid once. -/

/-- **`try_step` on a taken branch**, generic over `(imm, rs2, rs1, op)` and the
abstract execute hypothesis `hexec`. `try_step u true` on a `GoodState` at a code
pc holding the four instruction bytes reduces to `pure false` with `nextPC`/`PC`
at the branch target `pc + sign_extend imm` (plus `minstret += 1`). -/
theorem try_step_branch_taken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
            regs := (({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
      = .ok (FetchResult.F_Base (((b3.append b2).append b1).append b0)) (afterPrelude σ) := by
    exact fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  -- postlude read-backs on sigma3_branch_taken
  have hhart₃ : (sigma3_branch_taken σ pc imm).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.hart_state = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.hart_state) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_branch_taken σ pc imm).regs.get? Register.nextPC = some (pc + sign_extend (m := 64) imm) := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_branch_taken σ pc imm).regs.get? Register.minstret_increment = some true := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_branch_taken σ pc imm).regs.get? Register.minstret = some vminstret := by
    show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? Register.minstret = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (pc + sign_extend (m := 64) imm)
    (((b3.append b2).append b1).append b0)
    (instruction.BTYPE (imm, rs2, rs1, op))
    (sigma3_branch_taken σ pc imm) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-- **`try_step` on a not-taken branch**, generic over `(imm, rs2, rs1, op)` and
the abstract state-identity execute hypothesis. `try_step u true` reduces to
`pure false` with `nextPC`/`PC` at the fall-through `pc + 4`. -/
theorem try_step_branch_nottaken
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0) :
    (try_step u true).run σ
      = .ok false
          {(({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
            regs := (({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)} := by
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
      = .ok (FetchResult.F_Base (((b3.append b2).append b1).append b0)) (afterPrelude σ) := by
    exact fetch_F_Base (afterPrelude σ) pc b0 b1 b2 b3
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
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ) := by
    rw [hword]; exact hdec
  have hlpad : (is_landing_pad_expected ()).run (afterPrelude σ) = .ok false (afterPrelude σ) :=
    is_landing_pad_expected_false (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.elp)
  -- postlude read-backs on sigma3_branch_nottaken (= afterNextPC (afterPrelude σ) pc)
  have hhart₃ : (sigma3_branch_nottaken σ pc).regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()) := by
    show (afterNextPC (afterPrelude σ) pc).regs.get? Register.hart_state = _
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.hart_state
  have hnextPC₃ : (sigma3_branch_nottaken σ pc).regs.get? Register.nextPC = some (BitVec.addInt pc 4) := by
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.nextPC = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hinc₃ : (sigma3_branch_nottaken σ pc).regs.get? Register.minstret_increment = some true := by
    show ((afterPrelude σ).regs.insert Register.nextPC (BitVec.addInt pc 4)).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert]
    simp only [show (Register.nextPC == Register.minstret_increment) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
    show (σ.regs.insert Register.minstret_increment true).get? Register.minstret_increment = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hminstret₃ : (sigma3_branch_nottaken σ pc).regs.get? Register.minstret = some vminstret := by
    show (afterNextPC (afterPrelude σ) pc).regs.get? Register.minstret = _
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hminstret
  exact try_step_execute_char σ u pc (BitVec.addInt pc 4)
    (((b3.append b2).append b1).append b0)
    (instruction.BTYPE (imm, rs2, rs1, op))
    (sigma3_branch_nottaken σ pc) vminstret
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    hdisp hfetch hdec' hlpad hexec hhart₃ hnextPC₃ hinc₃ hminstret₃

/-! ## Final `try_step` states and their `GoodState` (via `goodstate_frame`) -/

/-- Taken final state (skeleton `σ₅`): the write chain `minstret_increment := true`,
`nextPC := pc+4`, `nextPC := target`, `PC := target`, `minstret := v+1`. -/
abbrev sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) : MState :=
  {(({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState) with
    regs := (({(sigma3_branch_taken σ pc imm) with regs := (sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Not-taken final state (skeleton `σ₅`): `minstret_increment := true`,
`nextPC := pc+4`, `PC := pc+4`, `minstret := v+1`. -/
abbrev sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) : MState :=
  {(({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState) with
    regs := (({(sigma3_branch_nottaken σ pc) with regs := (sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)}) : MState).regs.insert Register.minstret (BitVec.addInt vminstret 1)}

/-- Read-back of a register outside the taken write-set `{minstret, PC, nextPC,
minstret_increment}` through the taken write chain equals reading from `σ`. -/
theorem get?_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_taken σ pc vminstret imm).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_branch_taken σ pc imm).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show ((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC _).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h4, dif_neg, reduceCtorEq, not_false_eq_true]
  exact get?_afterNextPC σ pc R h4 h5

/-- Read-back of a register outside the not-taken write-set through the not-taken
write chain equals reading from `σ`. -/
theorem get?_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64) (R : Register)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false) :
    (sigmaPost_branch_nottaken σ pc vminstret).regs.get? R = σ.regs.get? R := by
  show ((((sigma3_branch_nottaken σ pc).regs.insert Register.PC (BitVec.addInt pc 4)).insert Register.minstret (BitVec.addInt vminstret 1))).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (afterNextPC (afterPrelude σ) pc).regs.get? R = _
  exact get?_afterNextPC σ pc R h4 h5

/-- `GoodState` is preserved by the taken branch step (write-set disjoint from
every pinned field). One line via `goodstate_frame`. -/
theorem goodstate_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (hG : GoodState σ) : GoodState (sigmaPost_branch_taken σ pc vminstret imm) := by
  goodstate_frame hG

/-- `GoodState` is preserved by the not-taken branch step. -/
theorem goodstate_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : GoodState (sigmaPost_branch_nottaken σ pc vminstret) := by
  goodstate_frame hG

/-- `htif_done` reads back `false` on the taken final state. -/
theorem htif_done_sigmaPost_branch_taken (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (hG : GoodState σ) : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_branch_taken σ pc vminstret imm _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done

/-- `htif_done` reads back `false` on the not-taken final state. -/
theorem htif_done_sigmaPost_branch_nottaken (σ : MState) (pc vminstret : BitVec 64)
    (hG : GoodState σ) : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.htif_done = some false := by
  rw [get?_sigmaPost_branch_nottaken σ pc vminstret _ (by decide) (by decide) (by decide) (by decide)]; exact hG.htif_done

/-! ## `stepOnce` (no clock tick) -/

/-- `stepOnce i u` on a taken branch (`i+1 ≠ 2`): `try_step` (⇒ `false`, branch
target written to PC), then continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_branch_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_branch_taken σ pc vminstret imm) := by
  have hts := try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_branch_taken σ pc vminstret imm hG
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

/-- `stepOnce i u` on a not-taken branch (`i+1 ≠ 2`): `try_step` (⇒ `false`,
`pc+4` written to PC), then continues with `(.inr (i+1, u+1))`. -/
theorem stepOnce_branch_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) (sigmaPost_branch_nottaken σ pc vminstret) := by
  have hts := try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_branch_nottaken σ pc vminstret hG
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

On the `i+1 = 2` boundary the model splices `tick_clock` (`Tick.lean`), writing
`mcycle`, `mtime`, `mip` over the `sigmaPost` state. The tick states are built
explicitly (not peeled from a `noncomputable abbrev`) to sidestep the
record-update let-bomb (Frame.lean §Record-update let bombs). -/

/-- Taken tick final state: `sigmaPost_branch_taken` followed by the `tick_clock`
writes (`mcycle += 1`, `mtime += 1`, `mip`'s MTI bit from `mtimecmp ≤u mtime+1`). -/
noncomputable abbrev sigmaTick_branch_taken
    (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 13)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_branch_taken σ pc vminstret imm) with
    regs := (((((sigmaPost_branch_taken σ pc vminstret imm).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- Not-taken tick final state: `sigmaPost_branch_nottaken` followed by the
`tick_clock` writes. -/
noncomputable abbrev sigmaTick_branch_nottaken
    (σ : MState) (pc vminstret : BitVec 64)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {(sigmaPost_branch_nottaken σ pc vminstret) with
    regs := (((((sigmaPost_branch_nottaken σ pc vminstret).regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1))))))}

/-- `stepOnce i u` on a taken branch when `i+1 = 2` (clock tick): as
`stepOnce_branch_taken_notick`, but the trailing `i+1 == 2` guard fires, splicing
`tick_clock` (via `tick_clock_char`) and resetting the tick counter to `0`. -/
theorem stepOnce_branch_taken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_branch_taken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_branch_taken σ pc vminstret imm hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_branch_taken σ pc vminstret imm hG
  have htc := tick_clock_char (sigmaPost_branch_taken σ pc vminstret imm) vmip vmtime vmtimecmp vmcycle
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

/-- `stepOnce i u` on a not-taken branch when `i+1 = 2` (clock tick). -/
theorem stepOnce_branch_nottaken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ
      = .ok (.inr (0, u + 1)) (sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  have hts := try_step_branch_nottaken σ u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
    hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign
  simp only [EStateM.run] at hts
  have hGp := goodstate_sigmaPost_branch_nottaken σ pc vminstret hG
  have hhtif := hG.htif_done
  have hhtif' := htif_done_sigmaPost_branch_nottaken σ pc vminstret hG
  have htc := tick_clock_char (sigmaPost_branch_nottaken σ pc vminstret) vmip vmtime vmtimecmp vmcycle
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

/-! ## `Machine.Step` wrappers -/

/-- **`step_branch` (taken, no clock tick).** One architectural step on a taken
branch, wrapped as `Vsa.Machine.Step`, with `GoodState` preserved. -/
theorem step_branch_taken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_branch_taken σ pc vminstret imm, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_branch_taken σ pc vminstret imm) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_branch_taken_notick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaPost_branch_taken σ pc vminstret imm hG⟩

/-- **`step_branch` (not taken, no clock tick).** -/
theorem step_branch_nottaken_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨sigmaPost_branch_nottaken σ pc vminstret, i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_branch_nottaken σ pc vminstret) :=
  ⟨Vsa.Machine.Step.mk
    (stepOnce_branch_nottaken_notick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      hG hpc hminstret hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick),
   goodstate_sigmaPost_branch_nottaken σ pc vminstret hG⟩

/-- **`step_branch` (taken, with clock tick).** As `step_branch_taken_notick` on
the `i+1 = 2` boundary: tick counter resets to `0`, `σ''` carries the `tick_clock`
write chain. `GoodState` preserved (tick touches only `mcycle`/`mtime`/`mip`). -/
theorem step_branch_taken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_taken σ pc vminstret imm).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_branch_taken σ pc vminstret imm vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_branch_taken_tick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick), ?_⟩
  have hGp := goodstate_sigmaPost_branch_taken σ pc vminstret imm hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-- **`step_branch` (not taken, with clock tick).** -/
theorem step_branch_nottaken_tick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (imm : BitVec 13) (rs1 rs2 : regidx) (op : bop)
    (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmip : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mip = some vmip)
    (hmtime : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtime = some vmtime)
    (hmtimecmp : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : (sigmaPost_branch_nottaken σ pc vminstret).regs.get? Register.mcycle = some vmcycle)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.BTYPE (imm, rs2, rs1, op)) (afterPrelude σ))
    (hexec : (execute (instruction.BTYPE (imm, rs2, rs1, op))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc))
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (sigmaTick_branch_nottaken σ pc vminstret vmip vmtime vmtimecmp vmcycle) := by
  refine ⟨Vsa.Machine.Step.mk
    (stepOnce_branch_nottaken_tick σ i u pc vminstret imm rs1 rs2 op w b0 b1 b2 b3
      vmip vmtime vmtimecmp vmcycle hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hword hnotrvc hdec hexec hb0 hb1 hb2 hb3 hlo hhi halign htick), ?_⟩
  have hGp := goodstate_sigmaPost_branch_nottaken σ pc vminstret hG
  exact ((hGp.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

/-! ## Per-op `hexec` builders — the one-line instantiation for all six ops

Each `example` builds the abstract `hexec` the generic `step_branch_*` lemmas
consume, from the corresponding `ExecuteBranch` clause, at the skeleton state
`afterNextPC (afterPrelude σ) pc`. The post-state produced by every taken clause
is **syntactically** `sigma3_branch_taken σ pc imm` (single `nextPC` insert), and
every not-taken clause is `sigma3_branch_nottaken σ pc` (state-identity) — so
these type-check by `exact` with no massaging, confirming the factoring covers
`{BEQ, BNE, BLT, BGE, BLTU, BGEU}` for both outcomes. A downstream caller writes,
e.g., `step_branch_taken_notick … (hexec := execute_btype_bge_taken … )` in one
line. (`hrs1`/`hrs2` come from the per-register `rX_bits_x*` battery, `hpc`/`hmisa`
from `GoodState` framed onto `afterNextPC (afterPrelude σ) pc`, and `htgt` from
the branch immediate's `imm[0] = 0`.) -/

section HexecBuilders
variable (σ : MState) (pc v1 v2 : BitVec 64) (imm : BitVec 13) (rs1 rs2 : regidx)
  (vmisa : RegisterType Register.misa)
  (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc) = .ok v1 (afterNextPC (afterPrelude σ) pc))
  (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc) = .ok v2 (afterNextPC (afterPrelude σ) pc))
  (hpc : (afterNextPC (afterPrelude σ) pc).regs.get? Register.PC = some pc)
  (hmisa : (afterNextPC (afterPrelude σ) pc).regs.get? Register.misa = some vmisa)
  (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)

/-- BEQ taken plugs into `sigma3_branch_taken`. -/
example (hv : (v1 == v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_beq_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BEQ not-taken plugs into `sigma3_branch_nottaken`. -/
example (hv : (v1 == v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BEQ))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_beq_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-- BNE taken. -/
example (hv : (v1 != v2) = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_bne_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BNE not-taken. -/
example (hv : (v1 != v2) = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BNE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bne_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-- BLT taken. -/
example (hv : zopz0zI_s v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLT))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_blt_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BLT not-taken. -/
example (hv : zopz0zI_s v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLT))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_blt_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-- BGE taken. -/
example (hv : zopz0zKzJ_s v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_bge_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BGE not-taken. -/
example (hv : zopz0zKzJ_s v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGE))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bge_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-- BLTU taken. -/
example (hv : zopz0zI_u v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLTU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_bltu_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BLTU not-taken. -/
example (hv : zopz0zI_u v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BLTU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bltu_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

/-- BGEU taken (the StepBeq op, now generic). -/
example (hv : zopz0zKzJ_u v1 v2 = true) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_taken σ pc imm) :=
  execute_btype_bgeu_taken imm rs1 rs2 v1 v2 pc vmisa _ hrs1 hrs2 hpc hmisa htgt hv

/-- BGEU not-taken. -/
example (hv : zopz0zKzJ_u v1 v2 = false) :
    (execute (instruction.BTYPE (imm, rs2, rs1, bop.BGEU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS (sigma3_branch_nottaken σ pc) :=
  execute_btype_bgeu_nottaken imm rs1 rs2 v1 v2 _ hrs1 hrs2 hv

end HexecBuilders

end Vsa.Sim
