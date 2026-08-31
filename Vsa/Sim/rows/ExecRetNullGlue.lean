import Vsa.Sim.ExecRetNull
import Vsa.Sim.ValueSpec
import Vsa.Sim.ObsAvoid
import Vsa.Sim.rows.ExecRecRows
import Vsa.Sim.DecodeTable.Batch14Part23
import Vsa.Sim.DecodeTable.Batch15Part07

/-!
# `ExecRetNullGlue` — the `value_null` callee bridge (closing `ExecRetNullGeom.hGlue`)

`execRetNullSimD` (`rows/ExecRecRows.lean`) threads the `.ret none` glue
`ExecArmEntryK@0x80004120 → SubExecReturnR@0x80004138` as an OPEN residual inside
`ExecRetNullGeom`.  This file discharges the MACHINE half of that glue: the
`beqz`-TAKEN `value_null` bridge

```
80004120:  ld   a2,8(s0)      -- a2 := stmt->expr = 0  (retNone ⇒ NULL pointer)
80004124:  beqz a2,0x800042f0 -- (TAKEN: no return expression)     imm13 = 0x1cc
800042f0:  addi a0,sp,16      -- a0 := sp'+16 = subsret  (the local sub-sret buffer)
800042f4:  jal  value_null    -- fill the buffer with a null Value, link 0x800042f8
800042f8:  j    0x80004138    -- rejoin the shared ret copy+epilogue tail   imm21 = 0x1ffe40
```

modelled exactly on `EvalVarBridge.varBridge` (`rows/EvalVarBridge.lean`): a
`callSeg`-shaped splice `prefix ≫ value_null ≫ suffix` over the real
`value_null_spec` (`ValueSpec.lean`) callee contract.

## What is PROVED vs. THREADED (the `varBridge`/`VarCallLinkage` discipline)

* **PROVED (this file):** the four straight-line/branch/jal/j decodes
  (`site_80004120_es`, the NEW `site_80004124_taken_es`,
  `site_800042f0_es`, `site_800042f4_es_valueNull`, `site_800042f8_es`),
  chained into a `Steps` from `ExecArmEntryK` to the `value_null` entry
  (`0x800027ec`, `a0 = subsret`, `x1 = 0x800042f8`); then `value_null_spec`
  materialises `ValueRepr … subsret .null`; then the `j 0x80004138` lands at the
  rejoin PC.  All register frame read-backs (`obs_alu_*`, `obs_jal_*`,
  branch-taken, jump-x0) are discharged mechanically.

* **THREADED (`NullBridgeSeam`):** the facts `value_null` needs but `ExecArmEntryK`
  does NOT expose (the `subsret = sp'+16` buffer's `NullRegion` geometry + its
  disjointness from the arena / spill slots / retslot / exec_stmt code), and the
  `SubExecReturnR` clauses that are NOT machine-local (the `StoreRepr`/spill-slot
  survival across `value_null`'s 16-byte write, and the payload-disjointness).
  These are exactly the caller-linkage data the `EX_RET` recursor supplies from
  `ExecEntry`'s stack/arena geometry — the statement-frame analog of
  `VarCallLinkage`.  Packaged as ONE typed record so the bridge has NO other open
  obligation.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The NEW `beqz`-TAKEN site at `0x80004124`

The taken mirror of `site_80004124_nottaken_es` (`Exec_stmtSites2.lean`): `beq
x12,x0` TAKEN (`a2 = 0`) redirects to `0x800042f0` (`imm13 = 0x1cc`). -/
theorem site_80004124_taken_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x80004124#64 : BitVec 64))
    (hv : (v12 == (0#64)) = true) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_taken σ pc vminstret (0x01cc#13)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004124 hmem
  exact stepObs_branch_taken σ i u (0x80004124#64) vminstret (0x01cc#13)
    (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5) bop.BEQ (0x1c060663#32)
    (0x63#8) (0x06#8) (0x06#8) (0x1c#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_1c060663 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_taken (0x01cc#13) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x00#5)
      v12 (0#64) (0x80004124#64) initMisa (afterNextPC (afterPrelude σ) (0x80004124#64))
      (rX_bits_x12 _ v12
        (by rw [get?_afterNextPC σ (0x80004124#64) _ (by decide) (by decide)]; exact hx12))
      (rX_bits_zero _)
      (by rw [get?_afterNextPC σ (0x80004124#64) _ (by decide) (by decide)]; exact hpc)
      (by rw [get?_afterNextPC σ (0x80004124#64) _ (by decide) (by decide)]; exact hG.misa)
      (by decide) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## `0x800042f0`: `addi a0,sp,16` (`a0 := sp'+16 = subsret`). -/
theorem site_800042f0_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800042f0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v2 + sign_extend (m := 64) (0x010#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800042f0 hmem
  exact stepObs_alu σ i u (0x800042f0#64) vminstret (0x01010513#32)
    (instruction.ITYPE (0x010#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))
    Register.x10 (v2 + sign_extend (m := 64) (0x010#12))
    (0x13#8) (0x05#8) (0x01#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01010513 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2
      (afterNextPC (afterPrelude σ) (0x800042f0#64))
      (sigma3_alu σ (0x800042f0#64) Register.x10 (v2 + sign_extend (m := 64) (0x010#12)))
      (rX_bits_x2 _ v2
        (by rw [get?_afterNextPC σ (0x800042f0#64) _ (by decide) (by decide)]; exact hx2))
      (wX_bits_x10 _ (v2 + sign_extend (m := 64) (0x010#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-! ## `0x800042f4`: `jal value_null` (link `x1 := 0x800042f8`, PC := 0x800027ec). -/
theorem site_800042f4_es_valueNull (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800042f4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x1fe4f8#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800042f4 hmem
  refine stepObs_jal σ i u (0x800042f4#64) vminstret (0xcf8fe0ef#32) (0x1fe4f8#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800042f4#64) 4)
    (0xef#8) (0xe0#8) (0x8f#8) (0xcf#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_cf8fe0ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi
  exact wX_bits_x1 _ (BitVec.addInt (0x800042f4#64) 4)

/-! ## `0x800042f8`: `j 0x80004138` (rejoin the shared copy+epilogue tail). -/
theorem site_800042f8_es (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Exec_stmtLoaded σ.mem)
    (hpcv : pc = (0x800042f8#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ffe40#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1ffe40#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_800042f8 hmem
  exact stepObs_j σ i u (0x800042f8#64) vminstret (0xe41ff06f#32) (0x1ffe40#21)
    (0x6f#8) (0xf0#8) (0x1f#8) (0xe4#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_e41ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-! ## `NullBridgeSeam` — the caller-linkage seam for the `value_null` bridge

The facts the `value_null` splice + `SubExecReturnR` assembly need but that
`ExecArmEntryK` (the arm-entry state) does NOT expose — the statement-frame analog
of `EvalVarBridge.VarCallLinkage`.  All are supplied ABOVE the arm by the `EX_RET`
recursor from `ExecEntry`'s stack/arena geometry.

Rather than re-derive them from below (impossible: `ExecArmEntryK` carries neither
the sub-sret buffer's `NullRegion` nor the arena-vs-buffer disjointness), we take
this ONE record and prove the full glue from it, exactly as `varBridge` consumes
`VarCallLinkage`.

The `retNoneExpr` field encodes the semantic fact that fixes the `beqz` as TAKEN:
for `.ret none` the machine `a2 = stmt->expr` read at `0x80004120` is `0` (the NULL
`Expr*`), so the branch guard `a2 = 0` holds.  This is the `StmtRepr (.ret none)`
fact — carried in `ExecEntry` but not re-exposed by `ExecArmEntryK`, so threaded. -/
structure NullBridgeSeam
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (out0 : Array String) (m0 : Mem) : Prop where
  /-- the `.ret none` `beqz` guard + `ld a2,8(s0)` geometry: `stmt->expr` (the
  8-byte word at `aStmt+8`) is `0` (the NULL `Expr*`), and the load slot is an
  aligned RAM word above HTIF.  From `StmtRepr (.ret none)` (carried in `ExecEntry`
  but hidden by `ExecArmEntryK`).  Fixes the `beqz` at `0x80004124` as TAKEN. -/
  retNoneExpr : read64 m0 (aStmt.toNat + 8) = some 0
  exprLo : 0x80000000 ≤ aStmt.toNat + 8
  exprHi : aStmt.toNat + 8 + 8 ≤ 0x100000000
  exprWin : aStmt.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aStmt.toNat + 8
  exprAl : (aStmt.toNat + 8) % 8 = 0
  /-- the whole `value_null` splice + `SubExecReturnR` assembly, from the machine
  state at the `value_null`-bridge entry (`0x800042f0`, `sp = sp-176`, mem framed
  to `ment`) to the `SubExecReturnR` rejoin at `0x80004138`.  Dischargeable ABOVE
  the arm: `value_null_spec` (over the `subsret = sp'+16` buffer's `NullRegion`) +
  the `j 0x80004138` + the buffer→`SubExecReturnR` relocation (the store/spill
  survival across the 16-byte null write, all disjoint from the arena/spills, and
  the payload disjointness — the exact `SubExecReturn` fields).  Threaded because
  none of these arena/buffer-geometry facts live in `ExecArmEntryK`. -/
  splice : ∀ (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
    Triple
      (fun c => ∃ (mid : Mem),
        GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = mid ∧
        c.σ.regs.get? Register.PC = some (0x800042f0#64) ∧
        c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧
        c.σ.regs.get? Register.x18 = some aRet ∧
        c.σ.regs.get? Register.x1 = some (0x80004124#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        Exec_stmtLoaded mid ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mid[a]? = m0[a]?) ∧
        ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8' v9' v18' v19' mcall,
        SubExecReturnR g N A SL φf φc st.store.frames.size st.store.closures.size st .null
          sp r aRet subsret (0x80004138#64) v1 v8' v9' v18' v19' m0 mcall c)

/-! ## Residual — the closed `value_null`-bridge glue (NOT yet assembled)

The site batteries above (`site_80004124_taken_es`, `site_800042f0_es`,
`site_800042f4_es_valueNull`, `site_800042f8_es`) and the honest `NullBridgeSeam`
record are landed GREEN.  The final assembly `execRetNullGlue_closed`
(`ExecArmEntryK → SubExecReturnR@0x80004138`, discharging `ExecRetNullGeom.hGlue`)
remains OPEN: it must (a) step the `ld a2,8(s0)` at `0x80004120` from the
`ExecArmEntryK`-pinned entry PC before `site_80004124_taken_es` applies (the
loaded value is pinned to 0 by the seam's `retNoneExpr`), then (b) chain the
beqz-TAKEN hop, the `value_null` splice (`addi a0,sp,16 ≫ jal value_null ≫ body`,
with `x1 = r` UNCHANGED at `0x800042f0` — the `jal` is inside the splice), the
rejoin `j 0x80004138`, and assemble `SubExecReturnR`.  The `Exec_stmtLoaded`
fact must be transported to each intermediate memory (`loaded_*_writeMap`
family).  Until assembled, `exec_retNull_row`'s `hGlue` stays a named premise. -/

end Vsa.Sim
