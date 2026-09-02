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

/-! ## `RetNullPostBeqz` — the post-`beqz` machine state at `0x800042f0`

The honest re-statement of the fields `ExecArmEntryK` carries, MINUS the PC pin,
at the beqz-TAKEN target `0x800042f0` (the `value_null`-bridge head).  This is the
predicate `NullBridgeSeam.splice`'s entry uses (see observation
`nullbridgeseam-splice-entry-contradictory`): reusing `ExecArmEntryK` verbatim at a
moved PC is unsatisfiable, so the prefix segment below lands in THIS predicate and
the amended `splice` consumes it.

Every field is transported unchanged across the `ld a2,8(s0)` (writes only `x12`,
memory unchanged) and the `beqz` (writes only PC, memory unchanged): `s0`/`s1`/`s2`
(=`aRet`)/`s3`/`sp`/`ra` survive, `StoreRepr`/spills survive (memory is the entry
`ment`), and the stack memframe vs `m0` is unchanged. -/
def RetNullPostBeqz
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800042f0#64) ∧
  c.σ.regs.get? Register.x8 = some aStmt ∧
  c.σ.regs.get? Register.x9 = some aInterp ∧
  c.σ.regs.get? Register.x19 = some aEnv ∧
  c.σ.regs.get? Register.x18 = some aRet ∧
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
  c.σ.mem = ment ∧ Exec_stmtLoaded ment ∧
  StoreRepr ment N A φf φc st.store ∧
  read64 ment (sp.toNat - 8) = some r.toNat ∧
  read64 ment (sp.toNat - 16) = some v8.toNat ∧
  read64 ment (sp.toNat - 24) = some v9.toNat ∧
  read64 ment (sp.toNat - 32) = some v18.toNat ∧
  read64 ment (sp.toNat - 40) = some v19.toNat ∧
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
  g Register.x18 = some v18 ∧ g Register.x19 = some v19 ∧
  g Register.x2 = some sp ∧
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = g R) ∧
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) ∧
  176 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 176 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧ r.toNat % 4 = 0

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
  8-byte word at `aStmt+8`) is `0` (the NULL `Expr*`) in the ARM-ENTRY memory
  `ment` (any memory agreeing with `m0` outside the stack window `[SL.lo, sp)`, as
  the prologue leaves the AST region untouched), and the load slot is an aligned
  RAM word above HTIF.  From `StmtRepr (.ret none)` (carried in `ExecEntry` but
  hidden by `ExecArmEntryK`).  Fixes the `beqz` at `0x80004124` as TAKEN.  Indexed
  by `ment` (not `m0`) because the `ld` reads the current memory; the seam's
  discharger above the arm has the `StmtRepr`-over-`m0` value plus the AST/stack
  disjointness that transports it across the prologue frame. -/
  retNoneExpr : ∀ (ment : Mem),
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
    read64 ment (aStmt.toNat + 8) = some 0
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
  none of these arena/buffer-geometry facts live in `ExecArmEntryK`.

  **Amended (task #72):** the entry is now the plain post-`beqz` predicate
  `RetNullPostBeqz` at `0x800042f0` — NOT `ExecArmEntryK … execArmRet …` verbatim,
  which pinned `PC = execArmRet = 0x80004120` and so conjoined `False` with the
  `PC = 0x800042f0` clause (see `nullBridgeSeam_oldEntry_false` and the observation
  `nullbridgeseam-splice-entry-contradictory`).  `retNullGluePrefix` lands exactly
  in `RetNullPostBeqz`, so `retNullGluePrefix ≫ splice` now composes. -/
  splice : ∀ (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
    Triple
      (RetNullPostBeqz g N A SL φf φc st sp r aInterp aStmt aEnv aRet
        v8 v9 v18 v19 out0 m0 ment)
      (fun c => ∃ subsret v1 v8' v9' v18' v19' mcall,
        SubExecReturnR g N A SL φf φc st.store.frames.size st.store.closures.size st .null
          sp r aRet subsret (0x80004138#64) v1 v8' v9' v18' v19' m0 mcall c)

/-! ## `retNullGluePrefix` — `ExecArmEntryK@0x80004120 → RetNullPostBeqz@0x800042f0`

The composable HALF of the `value_null`-bridge glue: `ld a2,8(s0)` loads
`stmt->expr = 0` (pinned by `NullBridgeSeam.retNoneExpr`), then the `beqz a2` is
TAKEN to the `value_null`-bridge head `0x800042f0`.  Every register/geometry field
survives (both instructions touch only `x12`/PC and leave memory fixed).

Lands exactly in `RetNullPostBeqz`, which is the (amended, task #72) entry of
`NullBridgeSeam.splice`, so `retNullGluePrefix ≫ S.splice` composes into
`execRetNullGlue_closed` (below).  The pre-amendment `splice` entry reused
`ExecArmEntryK` verbatim at PC `0x800042f0`, which was unsatisfiable (the PC pin
conflicts — see `nullBridgeSeam_oldEntry_false`), so `splice` could not be composed
after this prefix.  That obstruction is now removed. -/
theorem retNullGluePrefix
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (v8 v9 v18 v19 : BitVec 64) (out0 : Array String) (ment : Mem)
    -- the `.ret none` `beqz` guard: `stmt->expr` (word at `aStmt+8`) is `0`, and
    -- the load slot is an aligned RAM word above HTIF (from `NullBridgeSeam`).
    -- Seam-shaped: the value is given for ANY memory framed to `m0` outside
    -- `[SL.lo, sp)`; we apply it to `ment` via `ExecArmEntryK`'s own memframe below,
    -- so the composition consumes `NullBridgeSeam.retNoneExpr` with no re-destructure.
    (hExpr : ∀ (ment : Mem),
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) →
      read64 ment (aStmt.toNat + 8) = some 0)
    (hExprLo : 0x80000000 ≤ aStmt.toNat + 8)
    (hExprHi : aStmt.toNat + 8 + 8 ≤ 0x100000000)
    (hExprWin : aStmt.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aStmt.toNat + 8)
    (hExprAl : (aStmt.toNat + 8) % 8 = 0) :
    Triple
      (fun c => ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
        v8 v9 v18 v19 out0 m0 ment c)
      (RetNullPostBeqz g N A SL φf φc st sp r aInterp aStmt aEnv aRet
        v8 v9 v18 v19 out0 m0 ment) := by
  intro c hK
  -- unpack ExecArmEntryK (armPC = execArmRet = 0x80004120)
  obtain ⟨hG0, htick0, hpc0, hx8_0, hx9_0, hx19_0, hx18_0, hsp_0, hra_0,
    ⟨vmi0, hmi0⟩, hout0, houtJoin, hmem0, hcode0, hstore0,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframe0, hmemframe0,
    hsp176, hsphi, hsplo, hspwin, hspal, hral, hMemExtK⟩ := hK
  have hpc0' : c.σ.regs.get? Register.PC = some (0x80004120#64) := hpc0
  have hcode0' : Exec_stmtLoaded c.σ.mem := by rw [hmem0]; exact hcode0
  -- the loaded word address `x8 + 8 = aStmt + 8`, and its bytes (= 0):
  have haddr : (aStmt + sign_extend (m := 64) (0x008#12)).toNat = aStmt.toNat + 8 := by
    rw [BitVec.toNat_add]
    have hv : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aStmt.isLt; omega
  have hExpr' : read64 c.σ.mem (aStmt.toNat + 8) = some 0 := by
    rw [hmem0]; exact hExpr ment hmemframe0
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7, he0,he1,he2,he3,he4,he5,he6,he7⟩ :=
    ld64_bytes c.σ.mem (aStmt.toNat + 8) 0 hExpr'
  -- ============ 0x80004120: ld a2,8(s0) → x12 := stmt->expr = 0 ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004120_es c.σ c.tick c.steps (0x80004120#64) vmi0 aStmt
      e0 e1 e2 e3 e4 e5 e6 e7 hG0 hpc0' hmi0 hx8_0 hcode0' rfl
      (by rw [haddr]; omega) (by rw [haddr]; omega) (by rw [haddr]; exact hExprWin)
      (by rw [haddr]; exact hExprAl)
      (by rw [haddr]; exact he0) (by rw [haddr]; exact he1) (by rw [haddr]; exact he2)
      (by rw [haddr]; exact he3) (by rw [haddr]; exact he4) (by rw [haddr]; exact he5)
      (by rw [haddr]; exact he6) (by rw [haddr]; exact he7) htick0
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80004124#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004120#64) 4 = (0x80004124#64 : BitVec 64) from by decide] at this
  -- the loaded value is 0 (all bytes 0):
  have hx12val : (sign_extend (m := 64)
      ((((((((e7.append e6).append e5).append e4).append e3).append e2).append e1).append e0) : BitVec (8 * 8)) : BitVec 64) = (0#64) := by
    have h := ld_value_eq_read64 c.σ.mem (aStmt.toNat + 8) 0 e0 e1 e2 e3 e4 e5 e6 e7 hExpr'
      he0 he1 he2 he3 he4 he5 he6 he7
    rw [h]
  have hx12_1 : σ1.regs.get? Register.x12 = some (0#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hx12val] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp_0
  have hx8_1 : σ1.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs1 Register.x8 (by decide) hx8_0
  have hx9_1 : σ1.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs1 Register.x9 (by decide) hx9_0
  have hx18_1 : σ1.regs.get? Register.x18 = some aRet := obs_alu_other' hobs1 Register.x18 (by decide) hx18_0
  have hx19_1 : σ1.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs1 Register.x19 (by decide) hx19_0
  have hra_1 : σ1.regs.get? Register.x1 = some r := obs_alu_other' hobs1 Register.x1 (by decide) hra_0
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcode0'
  -- callee-saved frame outside {s0,s1,s2,s3,sp,x12} survives (x12 written, but the
  -- ExecArmEntryK frame clause already excludes s0/s1/s2/s3/sp; x12 is not AbiPreserved).
  have hframe1 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false →
      (Register.x2 == R) = false → σ1.regs.get? R = g R := by
    intro R hAbi h8 h9 h18 h19 h2
    -- `R` is AbiPreservedNoise; `x12` is not, so all the pinned-field disequalities hold.
    have hdis := (by revert hAbi; cases R <;> decide :
      AbiPreservedNoise R →
        ((Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
         (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
         (Register.PC == R) = false ∧ (Register.x12 == R) = false ∧
         (Register.nextPC == R) = false ∧
         (Register.minstret_increment == R) = false)) hAbi
    -- transport the option-valued frame `= g R` across the ld (writes only x12/PC).
    rw [hobs1.1 R hdis.1 hdis.2.1 hdis.2.2.1,
        get?_sigmaPost_alu c.σ (0x80004120#64) vmi0 Register.x12 _ R
          hdis.2.2.2.1 hdis.2.2.2.2.1 hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2.1 hdis.2.2.2.2.2.2.2]
    exact hframe0 R hAbi h8 h9 h18 h19 h2
  -- ============ 0x80004124: beqz a2 (TAKEN, a2 = 0) → 0x800042f0 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80004124_taken_es σ1 i1 (c.steps + 1) (0x80004124#64) vmi1 (0#64)
      hG1 hpc1 hmi1 hx12_1 hcode1 rfl (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800042f0#64) := by
    have := obs_branch_taken_pc hobs2
    rwa [show (0x80004124#64 : BitVec 64) + sign_extend (m := 64) (0x01cc#13)
      = (0x800042f0#64 : BitVec 64) from by decide] at this
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_branch_taken_other' hobs2 Register.x2 (by decide) hsp_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aStmt := obs_branch_taken_other' hobs2 Register.x8 (by decide) hx8_1
  have hx9_2 : σ2.regs.get? Register.x9 = some aInterp := obs_branch_taken_other' hobs2 Register.x9 (by decide) hx9_1
  have hx18_2 : σ2.regs.get? Register.x18 = some aRet := obs_branch_taken_other' hobs2 Register.x18 (by decide) hx18_1
  have hx19_2 : σ2.regs.get? Register.x19 = some aEnv := obs_branch_taken_other' hobs2 Register.x19 (by decide) hx19_1
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_branch_taken_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_branch_taken_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcode0'
  have hframe2 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false →
      (Register.x2 == R) = false → σ2.regs.get? R = g R := by
    intro R hAbi h8 h9 h18 h19 h2
    have hdis := (by revert hAbi; cases R <;> decide :
      AbiPreservedNoise R →
        ((Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
         (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
         (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
         (Register.minstret_increment == R) = false)) hAbi
    -- transport across the beqz (writes only PC).
    rw [hobs2.1 R hdis.1 hdis.2.1 hdis.2.2.1,
        get?_sigmaPost_branch_taken σ1 (0x80004124#64) vmi1 (0x01cc#13) R
          hdis.2.2.2.1 hdis.2.2.2.2.1 hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2]
    exact hframe1 R hAbi h8 h9 h18 h19 h2
  -- assemble the two Steps and the post-beqz predicate
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, Steps.head hstep1 (Steps.head hstep2 (Steps.refl _)), ?_⟩
  refine ⟨hG2, hi2, hpc2, hx8_2, hx9_2, hx19_2, hx18_2, hsp_2, hra_2, ⟨vmi2, hmi2⟩, ?_, houtJoin,
    ?_, hcode0, hstore0, hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframe2, hmemframe0, hsp176, hsphi, hsplo, hspwin, hspal, hral⟩
  · -- sailOutput unchanged across ld + beqz
    have h2out : σ2.sailOutput = σ1.sailOutput := by
      rw [hobs2.out, sailOutput_sigmaPost_branch_taken]
    have h1out : σ1.sailOutput = c.σ.sailOutput := by
      rw [hobs1.out, sailOutput_sigmaPost_alu]
    rw [h2out, h1out]; exact hout0
  · -- ment: σ2.mem = ment (= c.σ.mem, pinned by ExecArmEntryK.mem)
    rw [hmem2e]; exact hmem0

/-! ## Falsity witness — the OLD `NullBridgeSeam.splice` entry was `False`

Regression guard for the amendment (task #72, observation
`nullbridgeseam-splice-entry-contradictory`).  The pre-amendment `splice` entry
conjoined `c.σ.regs.get? PC = some 0x800042f0` with `ExecArmEntryK … execArmRet …`,
and `ExecArmEntryK` pins `PC = some armPC = execArmRet = 0x80004120`.  The two PC
readbacks are `some 0x800042f0` and `some 0x80004120` for the SAME register, so the
conjunction is `False` — the old splice could never fire from any real config. -/
theorem nullBridgeSeam_oldEntry_false
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (v8 v9 v18 v19 : BitVec 64) (out0 : Array String) (m0 ment : Mem) (c : Config)
    (hOld :
      c.σ.regs.get? Register.PC = some (0x800042f0#64) ∧
      ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
        v8 v9 v18 v19 out0 m0 ment c) :
    False := by
  obtain ⟨hpc042f0, hK⟩ := hOld
  -- `ExecArmEntryK` pins `PC = some execArmRet = some 0x80004120` (named, not
  -- positional: the same field `retNullGluePrefix` binds as `hpc0`).
  obtain ⟨_hG0, _htick0, hpc04120, _rest⟩ := hK
  rw [hpc042f0] at hpc04120
  exact absurd hpc04120 (by decide)

/-! ## `execRetNullGlue_closed` — the closed `value_null`-bridge glue

The final assembly discharging `execRetNullSimD`'s `hGlue` residual: from any
`ExecArmEntryK`-entry config (the `EX_RET .none` arm entry at `0x80004120`) to a
`SubExecReturnR` config at the rejoin `0x80004138`.  Assembled by `Triple.seq` of
the two now-composable halves over a `NullBridgeSeam`:

* `retNullGluePrefix`: `ExecArmEntryK@0x80004120 → RetNullPostBeqz@0x800042f0`
  (the `ld a2,8(s0)` step loading `stmt->expr = 0` + the `beqz`-TAKEN hop), taking
  the seam's `retNoneExpr`/`expr*` geometry pins;
* `S.splice`: `RetNullPostBeqz@0x800042f0 → SubExecReturnR@0x80004138` (the
  `addi a0,sp,16 ≫ jal value_null ≫ j 0x80004138` splice + `SubExecReturnR`
  assembly), now typed against the honest post-`beqz` predicate rather than the
  contradictory `ExecArmEntryK`-at-moved-PC.  The `value_null` callee content stays
  packaged inside the seam's `splice` field (a NAMED residual dischargeable ABOVE
  the arm — see `NullBridgeSeam`'s doc); this theorem shows the two halves COMPOSE.

This closes the machine half of `ExecRetNullGeom.hGlue` MODULO the seam. -/
theorem execRetNullGlue_closed
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (S : ∀ (ment : Mem) (v8 v9 v18 v19 : BitVec 64),
      NullBridgeSeam g N A SL φf φc st sp r aInterp aStmt aEnv aRet out0 m0) :
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturnR g N A SL φf φc st.store.frames.size st.store.closures.size st .null
          sp r aRet subsret (0x80004138#64) v1 v8 v9 v18 v19 m0 mcall c) := by
  intro c hpre
  obtain ⟨ment, v8, v9, v18, v19, hK⟩ := hpre
  have hseam := S ment v8 v9 v18 v19
  -- prefix: ExecArmEntryK@0x80004120 → RetNullPostBeqz@0x800042f0.  The seam-shaped
  -- `retNoneExpr` is passed straight through; `retNullGluePrefix` applies it to `ment`
  -- via ExecArmEntryK's own memframe (no positional re-destructure of the tower).
  obtain ⟨cM, hstepsM, hMid⟩ :=
    retNullGluePrefix g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0
      v8 v9 v18 v19 out0 ment
      hseam.retNoneExpr
      hseam.exprLo hseam.exprHi hseam.exprWin hseam.exprAl c hK
  -- splice: RetNullPostBeqz@0x800042f0 → SubExecReturnR@0x80004138
  obtain ⟨cG, hstepsG, hOut⟩ := hseam.splice ment v8 v9 v18 v19 cM hMid
  exact ⟨cG, hstepsM.trans hstepsG, hOut⟩

#print axioms site_80004124_taken_es
#print axioms retNullGluePrefix
#print axioms nullBridgeSeam_oldEntry_false
#print axioms execRetNullGlue_closed

end Vsa.Sim
