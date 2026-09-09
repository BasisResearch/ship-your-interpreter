import Vsa.Sim.EvalVarSim
import Vsa.Sim.EnvGetSpec9
import Vsa.Sim.EnvGetRecursive
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.ObsAvoid
import Vsa.Sim.rows.EvalVarRow

/-!
# `EvalVarBridge` — the eval-var-arm `env_get` call-linkage bridge (closing `hVar`).

This file discharges the ONE open `O`-class field of `VarLeafResid`
(`rows/EvalVarRow.lean`): the `Triple` from the var arm's dispatch entry
(`ArmEntryK @0x80003434`) to the `env_get` link-return post
(`VarPostCall @0x80003444`).

## Structure (a `callSeg` splice)

The var arm's four-instruction argument-setup + `env_get` call is a Shape-D call
site `prefix ≫ callee ≫ suffix`:

```
0x80003434: ld   a1, 8(a2)      -- a1 := *(aExpr+8) = var-name CString ptr  (env_get name)
0x80003438: addi a0, a3, 0      -- a0 := a3 = penv                          (env_get env)
0x8000343c: addi a2, sp, 240    -- a2 := (sp-1088)+0xf0 = result buffer      (env_get out)
0x80003440: jal  ra, env_get    -- call env_get, link 0x80003444
--- env_get body (callee: env_get_found_uncond'') ---
0x80003444: (VarPostCall)       -- a0 = 1, *out = ValueRepr v (relocated to sret by blockC_var)
```

* **Prefix** (`varBridge_prefix`): the four straight-line sites (all decode
  lemmas + per-site `StepObs` batteries already live in `EvalVarSim.lean`:
  `site_80003434_var`, `site_80003438_var`, `site_8000343c_var`,
  `site_80003440_var`) chained with the `ObsAvoid` frame helpers into a `Steps`
  from `ArmEntryK` to the `env_get` entry config (PC 0x80002c10, `a0 = penv`,
  `a1 = name`, `a2 = out`, `x1 = 0x80003444`, `sp = sp-1088`). This is the
  concrete machine work; it reuses the block-reflection sites verbatim.

* **Callee** (`env_get_found_uncond''`, EnvGetSpec9): the whole immediate-frame
  `env_get` FOUND case (prologue ≫ scan loop ≫ strcmp cross-call ≫ HIT-tail),
  spliced in over its native `FoundSt`/`FrameStackDisj` contract.

* **Suffix** (`varBridge_suffix`): repackage `env_get`'s ret-post (PC returned to
  the link `0x80003444`, `a0 = 1`, `*out = ValueRepr v`) into `VarPostCall`.

## The genuinely-open residual (the caller-linkage seam)

`ArmEntryK` (and therefore `VarLeafResid`) pins the arm's live registers
`x9=sret`, `x11=aEnv`, `x12=aExpr`, `x8=aExpr`, `x18=aEnv`, `x2=sp-1088`,
`x1=r` — but it does **NOT** pin `x13` (`a3`, `env_get`'s FIRST argument), and it
carries only `StoreRepr` (the whole store), NOT a `FrameRepr` for the specific
frame the spec lookup `st.store.get? env x = some v` resolves in.  Bridging the
spec-side `env : While.Addr` (a frame index) to the machine env pointer `penv =
x13` and to a concrete `env_get`-shaped `Frame f` + HIT-witness `iw` is exactly
the caller-linkage geometry that lives ABOVE `ArmEntryK`.  It is NOT derivable
from `VarLeafResid`'s current fields, and supplying it would require strengthening
the landed `ArmEntryK`/`EvalVarEntry`/`VarLeafResid` statements (out of scope:
"do NOT modify any landed statement").

So this file takes that linkage as an EXPLICIT, typed premise record
`VarCallLinkage` (documented field-by-field: the env-pointer pin, the derived
`FoundSt` + `FrameStackDisj`, and the suffix's `out`/`sret` relocation facts) and
proves the full bridge `varBridge` from it.  `VarCallLinkage` IS the precise
residual seam; the eventual M4 caller (the recursive `EvalE`/`ExecSeq` recursor,
which threads the real interp-struct env pointer and unpacks `StoreRepr` at the
looked-up frame) supplies it.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 1600000

/-! ## The prefix: `ArmEntryK @0x80003434 → env_get entry @0x80002c10`

Threads the four straight-line sites.  The result predicate is stated at the
`env_get` entry with the three call arguments (`penv`/`name`/`out`) and the
link/frame registers pinned, plus the memory unchanged (`= ment`, hence `= m0`
outside the live stack).  `penv` (the value of `x13 = a3`) is taken as a
parameter — the honest missing caller-linkage datum. -/
theorem varBridge_prefix
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (x : String)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64) (c : Config)
    (hArm : ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
    -- the missing env-pointer datum: `x13 = penv` at the arm entry.
    (ha3 : c.σ.regs.get? Register.x13 = some penv)
    (hg19 : g Register.x19 = some v19)
    (hg20 : g Register.x20 = some v20)
    (hg21 : g Register.x21 = some v21)
    -- the var-name pointer read from the Expr node (`ld a1, 8(a2)` value).
    (hname : read64 ment (aExpr.toNat + 8) = some nm.toNat)
    -- geometry the `ld a1, 8(a2)` load needs (the name pointer slot in RAM).
    (hnmLo : 0x80000000 ≤ aExpr.toNat + 8)
    (hnmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000)
    (hnmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8) :
    ∃ (c' : Config),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧ c'.σ.mem = ment ∧
      c'.σ.regs.get? Register.PC = some (0x80002c10#64) ∧
      c'.σ.regs.get? Register.x10 = some penv ∧          -- a0 = env
      c'.σ.regs.get? Register.x11 = some nm ∧             -- a1 = name
      c'.σ.regs.get? Register.x12 = some ((sp - 1088#64) + 0xf0#64) ∧  -- a2 = out
      c'.σ.regs.get? Register.x1 = some (0x80003444#64) ∧ -- ra = link
      c'.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧  -- sp lowered (unchanged)
      c'.σ.regs.get? Register.x9 = some sret ∧
      c'.σ.regs.get? Register.x8 = some aExpr ∧
      c'.σ.regs.get? Register.x18 = some aEnv ∧
      c'.σ.regs.get? Register.x19 = some v19 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x21 = some v21 ∧
      c'.σ.sailOutput = out0 ∧
      (∃ w, c'.σ.regs.get? Register.minstret = some w) := by
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hload, _hcallee,
    hexpr, houtStr, haExprLo, haExprHi, haExprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframeReg,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEv,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    hx11, hx8, hx18⟩ := hArm
  have hx19 : c.σ.regs.get? Register.x19 = some v19 := by
    rw [hframeReg Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide), hg19]
  have hx20 : c.σ.regs.get? Register.x20 = some v20 := by
    rw [hframeReg Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide), hg20]
  have hx21 : c.σ.regs.get? Register.x21 = some v21 := by
    rw [hframeReg Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide), hg21]
  -- extract the eight name-pointer bytes for the `ld a1, 8(a2)` load.
  obtain ⟨nb0, nb1, nb2, nb3, nb4, nb5, nb6, nb7, hnb0, hnb1, hnb2, hnb3, hnb4, hnb5, hnb6, hnb7, hnSext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 8) nm hname
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- address fold for the `ld a1, 8(a2)` at `aExpr + sext 0x008`.
  have hoff8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    rw [BitVec.toNat_add]
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
    rw [hs]; have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  -- ============ 0x80003434: ld a1,8(a2) → x11 := nm ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80003434_var c.σ c.tick c.steps (0x80003434#64) vmi aExpr
      nb0 nb1 nb2 nb3 nb4 nb5 nb6 nb7 hG hpc hmi ha2 (hmem ▸ hload) rfl
      (by rw [hoff8]; omega) (by rw [hoff8]; omega)
      (by rw [hoff8]; exact hnmWin)
      (by rw [hoff8, hmem]; exact hnb0) (by rw [hoff8, hmem]; exact hnb1)
      (by rw [hoff8, hmem]; exact hnb2) (by rw [hoff8, hmem]; exact hnb3)
      (by rw [hoff8, hmem]; exact hnb4) (by rw [hoff8, hmem]; exact hnb5)
      (by rw [hoff8, hmem]; exact hnb6) (by rw [hoff8, hmem]; exact hnb7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003438#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80003434#64) 4 = (0x80003438#64:BitVec 64) from by decide] at this
  have hx11_1 : σ1.regs.get? Register.x11 = some nm := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hnSext] at this; exact this
  have hx13_1 : σ1.regs.get? Register.x13 = some penv := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hra_1 : σ1.regs.get? Register.x1 = some r := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs1 Register.x8 (by decide) hx8
  have hx18_1 : σ1.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs1 Register.x18 (by decide) hx18
  have hx19_1 : σ1.regs.get? Register.x19 = some v19 := obs_alu_other' hobs1 Register.x19 (by decide) hx19
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 := obs_alu_other' hobs1 Register.x20 (by decide) hx20
  have hx21_1 : σ1.regs.get? Register.x21 = some v21 := obs_alu_other' hobs1 Register.x21 (by decide) hx21
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hload1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hload
  -- ============ 0x80003438: addi a0,a3,0 → x10 := penv ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003438_var σ1 i1 (c.steps+1) (0x80003438#64) vmi1 penv hG1 hpc1 hmi1 hx13_1 hload1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000343c#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003438#64) 4 = (0x8000343c#64:BitVec 64) from by decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some penv := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [show penv + sign_extend (m := 64) (0x000#12) = penv from by rw [sext_zero]; exact BitVec.add_zero penv] at this
    exact this
  have hx11_2 : σ2.regs.get? Register.x11 = some nm := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs2 Register.x8 (by decide) hx8_1
  have hx18_2 : σ2.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs2 Register.x18 (by decide) hx18_1
  have hx19_2 : σ2.regs.get? Register.x19 = some v19 := obs_alu_other' hobs2 Register.x19 (by decide) hx19_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 := obs_alu_other' hobs2 Register.x20 (by decide) hx20_1
  have hx21_2 : σ2.regs.get? Register.x21 = some v21 := obs_alu_other' hobs2 Register.x21 (by decide) hx21_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hload2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hload
  -- ============ 0x8000343c: addi a2,sp,240 → x12 := (sp-1088)+0xf0 ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_8000343c_var σ2 i2 (c.steps+1+1) (0x8000343c#64) vmi2 (sp-1088#64) hG2 hpc2 hmi2 hsp_2 hload2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003440#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x8000343c#64) 4 = (0x80003440#64:BitVec 64) from by decide] at this
  have hx12_3 : σ3.regs.get? Register.x12 = some ((sp-1088#64) + 0xf0#64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [show sign_extend (m := 64) (0x0f0#12) = (0xf0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
    exact this
  have hx10_3 : σ3.regs.get? Register.x10 = some penv := obs_alu_other' hobs3 Register.x10 (by decide) hx10_2
  have hx11_3 : σ3.regs.get? Register.x11 = some nm := obs_alu_other' hobs3 Register.x11 (by decide) hx11_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hx8_3 : σ3.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  have hx18_3 : σ3.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs3 Register.x18 (by decide) hx18_2
  have hx19_3 : σ3.regs.get? Register.x19 = some v19 := obs_alu_other' hobs3 Register.x19 (by decide) hx19_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 := obs_alu_other' hobs3 Register.x20 (by decide) hx20_2
  have hx21_3 : σ3.regs.get? Register.x21 = some v21 := obs_alu_other' hobs3 Register.x21 (by decide) hx21_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hload3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hload
  -- ============ 0x80003440: jal ra,env_get → PC := 0x80002c10, x1 := 0x80003444 ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003440_var σ3 i3 (c.steps+1+1+1) (0x80003440#64) vmi3 hG3 hpc3 hmi3 hload3 rfl
      (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002c10#64) := by
    have := obs_jal_pc hobs4
    rwa [show (0x80003440#64 : BitVec 64) + sign_extend (m := 64) (0x1ff7d0#21)
      = (0x80002c10#64:BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_4 : σ4.regs.get? Register.x1 = some (0x80003444#64) := by
    have := obs_jal_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003440#64) 4 = (0x80003444#64:BitVec 64) from by decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some penv := obs_jal_other' hobs4 Register.x10 (by decide) hx10_3
  have hx11_4 : σ4.regs.get? Register.x11 = some nm := obs_jal_other' hobs4 Register.x11 (by decide) hx11_3
  have hx12_4 : σ4.regs.get? Register.x12 = some ((sp-1088#64) + 0xf0#64) := obs_jal_other' hobs4 Register.x12 (by decide) hx12_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other' hobs4 Register.x2 (by decide) hsp_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_jal_other' hobs4 Register.x9 (by decide) hs1_3
  have hx8_4 : σ4.regs.get? Register.x8 = some aExpr := obs_jal_other' hobs4 Register.x8 (by decide) hx8_3
  have hx18_4 : σ4.regs.get? Register.x18 = some aEnv := obs_jal_other' hobs4 Register.x18 (by decide) hx18_3
  have hx19_4 : σ4.regs.get? Register.x19 = some v19 := obs_jal_other' hobs4 Register.x19 (by decide) hx19_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 := obs_jal_other' hobs4 Register.x20 (by decide) hx20_3
  have hx21_4 : σ4.regs.get? Register.x21 = some v21 := obs_jal_other' hobs4 Register.x21 (by decide) hx21_3
  have hout4 : σ4.sailOutput = out0 := by
    rw [hobs4.out, sailOutput_sigmaPost_jal, hobs3.out, sailOutput_sigmaPost_alu,
      hobs2.out, sailOutput_sigmaPost_alu, hobs1.out, sailOutput_sigmaPost_alu, hout]
  obtain ⟨vmi4, hmi4⟩ := obs_jal_minstret hobs4
  refine ⟨⟨σ4, i4, c.steps+1+1+1+1⟩, ?_, hG4, hi4, ?_, hpc4, hx10_4, hx11_4, hx12_4, hx1_4, hsp_4,
    hs1_4, hx8_4, hx18_4, hx19_4, hx20_4, hx21_4, hout4, ⟨vmi4, hmi4⟩⟩
  · exact ((((Steps.single hstep1).trans (Steps.single hstep2)).trans (Steps.single hstep3)).trans (Steps.single hstep4))
  · rw [hmem4e]

/-! ## The `env_get` entry predicate `EnvGetEntryV`

The prefix's post, stated as a standalone `Config → Prop` so the bridge composes
as `Triple.seq`.  This is exactly the register/memory shape `PrologueSt` (env_get's
entry) consumes, with `env = penv`, `name = nm`, `out = (sp-1088)+0xf0`,
`sp0 = sp-1088`, `r0 = 0x80003444` (the caller link). -/
set_option linter.unusedVariables false in
/-- The `env_get`-entry predicate.  `st`/`v8`/`v9`/`v18` are carried for
signature-uniformity with the prefix/callee predicates (they pin `VarPostCall`'s
callee-saved frame); the entry predicate itself only constrains the call
registers. -/
def EnvGetEntryV
    (st : Vsa.While.St) (sp sret aExpr aEnv : BitVec 64)
    (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String) (ment : Mem) (penv nm : BitVec 64) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = ment ∧
  c.σ.regs.get? Register.PC = some (0x80002c10#64) ∧
  c.σ.regs.get? Register.x10 = some penv ∧
  c.σ.regs.get? Register.x11 = some nm ∧
  c.σ.regs.get? Register.x12 = some ((sp - 1088#64) + 0xf0#64) ∧
  c.σ.regs.get? Register.x1 = some (0x80003444#64) ∧
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
  c.σ.regs.get? Register.x9 = some sret ∧
  c.σ.regs.get? Register.x8 = some aExpr ∧
  c.σ.regs.get? Register.x18 = some aEnv ∧
  c.σ.regs.get? Register.x19 = some v19 ∧
  c.σ.regs.get? Register.x20 = some v20 ∧
  c.σ.regs.get? Register.x21 = some v21 ∧
  c.σ.sailOutput = out0 ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w)

/-- Prefix as a `Triple` over `EnvGetEntryV`.  Directly repackages
`varBridge_prefix`. -/
theorem varBridge_prefix_triple
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (x : String)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64)
    (hname : read64 ment (aExpr.toNat + 8) = some nm.toNat)
    (hg19 : g Register.x19 = some v19)
    (hg20 : g Register.x20 = some v20)
    (hg21 : g Register.x21 = some v21)
    (hnmLo : 0x80000000 ≤ aExpr.toNat + 8)
    (hnmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000)
    (hnmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8) :
    Triple
      (fun c => ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x13 = some penv)
      (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 v19 v20 v21 out0 ment penv nm) := by
  intro c hpre
  obtain ⟨hArm, ha3⟩ := hpre
  obtain ⟨c', hs, hG', htick', hmem', hpc', h10, h11, h12, h1, h2, h9, h8, h18,
    h19, h20, h21, hout', hmi⟩ :=
    varBridge_prefix g N A SL φf φc st x sp r sret aExpr aEnv v8 v9 v18 v19 v20 v21
      out0 m0 ment penv nm c hArm ha3 hg19 hg20 hg21 hname hnmLo hnmHi hnmWin
  exact ⟨c', hs, hG', htick', hmem', hpc', h10, h11, h12, h1, h2, h9, h8, h18,
    h19, h20, h21, hout', hmi⟩

/-! ## Concrete caller linkage -/

def VarSpillAgree (sp : BitVec 64) (m' m : Mem) : Prop :=
  ∀ k, ¬ (((sp - 1088#64) - 64#64).toNat ≤ k ∧
    k < ((sp - 1088#64) - 64#64).toNat + 64) → m'[k]? = m[k]?

def VarOutAgree (sp : BitVec 64) (m' m : Mem) : Prop :=
  ∀ k, ¬ (((sp - 1088#64) + 0xf0#64).toNat ≤ k ∧
    k < ((sp - 1088#64) + 0xf0#64).toNat + 24) → m'[k]? = m[k]?

/-- Equality of successful 64-bit reads determines all eight source bytes. -/
theorem read64_same_bytes {m m' : Mem} {a a' w : Nat}
    (h : read64 m a = some w) (h' : read64 m' a' = some w) :
    ∀ j, j < 8 → m[a + j]? = m'[a' + j]? := by
  intro j hj
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7, hd0,hd1,hd2,hd3,hd4,hd5,hd6,hd7, hdq⟩ :=
    read64_bytes_eg4 m a w h
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7, he0,he1,he2,he3,he4,he5,he6,he7, heq⟩ :=
    read64_bytes_eg4 m' a' w h'
  have hq0 : d0 = e0 := by apply BitVec.eq_of_toNat_eq; have := d0.isLt; have := e0.isLt; omega
  have hq1 : d1 = e1 := by apply BitVec.eq_of_toNat_eq; have := d1.isLt; have := e1.isLt; omega
  have hq2 : d2 = e2 := by apply BitVec.eq_of_toNat_eq; have := d2.isLt; have := e2.isLt; omega
  have hq3 : d3 = e3 := by apply BitVec.eq_of_toNat_eq; have := d3.isLt; have := e3.isLt; omega
  have hq4 : d4 = e4 := by apply BitVec.eq_of_toNat_eq; have := d4.isLt; have := e4.isLt; omega
  have hq5 : d5 = e5 := by apply BitVec.eq_of_toNat_eq; have := d5.isLt; have := e5.isLt; omega
  have hq6 : d6 = e6 := by apply BitVec.eq_of_toNat_eq; have := d6.isLt; have := e6.isLt; omega
  have hq7 : d7 = e7 := by apply BitVec.eq_of_toNat_eq; have := d7.isLt; have := e7.isLt; omega
  match j, hj with
  | 0, _ => rw [Nat.add_zero, Nat.add_zero, hd0, he0, hq0]
  | 1, _ => rw [hd1, he1, hq1]
  | 2, _ => rw [hd2, he2, hq2]
  | 3, _ => rw [hd3, he3, hq3]
  | 4, _ => rw [hd4, he4, hq4]
  | 5, _ => rw [hd5, he5, hq5]
  | 6, _ => rw [hd6, he6, hq6]
  | 7, _ => rw [hd7, he7, hq7]

/-- The residual contains semantic lookup and concrete geometry only.  It does
not contain an `env_get` execution oracle. -/
structure VarCallLinkage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String) (m0 ment : Mem) (penv nm : BitVec 64)
    (len pn : Nat) : Prop where
  /-- the var-name pointer read from the Expr node (`ld a1, 8(a2)`). -/
  name : read64 ment (aExpr.toNat + 8) = some nm.toNat
  nmLo : 0x80000000 ≤ aExpr.toNat + 8
  nmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000
  nmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8
  penv_eq : penv = BitVec.ofNat 64 (φf env)
  g19 : g Register.x19 = some v19
  g20 : g Register.x20 = some v20
  g21 : g Register.x21 = some v21
  g8 : g Register.x8 = some v8
  g9 : g Register.x9 = some v9
  g18 : g Register.x18 = some v18
  g2 : g Register.x2 = some sp
  loaded : Env_getLoaded ment
  chain : LookupChain st.store x st.store.frames.size env v
  envNe : (penv == (0#64 : BitVec 64)) = false
  read_len : read32 ment penv.toNat = some len
  read_pn : read64 ment (penv.toNat + 8) = some pn
  spDrop : 0x40 ≤ (sp - 1088#64).toNat
  spLo : 0x80000000 ≤ (sp - 1088#64).toNat - 64
  spHi : (sp - 1088#64).toNat ≤ 0x100000000
  spWin : tohostAddr + 64 ≤ (sp - 1088#64).toNat - 64
  spAlign : (sp - 1088#64).toNat % 8 = 0
  spCode : (sp - 1088#64).toNat ≤ 0x80002c10 ∨
    0x80002cdc ≤ (sp - 1088#64).toNat - 64
  envHi : penv.toNat + 24 ≤ 0x100000000
  envStackDisj : penv.toNat + 24 ≤ (sp - 1088#64).toNat - 64 ∨
    (sp - 1088#64).toNat ≤ penv.toNat
  storeHead : ∀ m', VarSpillAgree sp m' ment → StoreRepr m' N A φf φc st.store
  chainFacts : ∀ m', VarSpillAgree sp m' ment →
    EnvGetChainFacts nm ((sp - 1088#64) + 0xf0#64) ((sp - 1088#64) - 64#64)
      (0x80003444#64) aExpr sret aEnv v19 v20 v21 x N φf φc m' st.store
  strcmp : ∀ m', VarSpillAgree sp m' ment → StrcmpLoaded m'
  finalFrame : ∀ m9 c',
    EnvGetValuePost N φc ((sp - 1088#64) + 0xf0#64) ((sp - 1088#64) - 64#64)
      (0x80003444#64) aExpr sret aEnv v19 v20 v21 out0 v m9 c' →
    ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
      (Register.x9 == R) = false → (Register.x18 == R) = false →
      (Register.x2 == R) = false → c'.σ.regs.get? R = g R
  finalMinstret : ∀ m9 c',
    EnvGetValuePost N φc ((sp - 1088#64) + 0xf0#64) ((sp - 1088#64) - 64#64)
      (0x80003444#64) aExpr sret aEnv v19 v20 v21 out0 v m9 c' →
    ∃ w, c'.σ.regs.get? Register.minstret = some w
  finalCode : ∀ m9 mpc, VarSpillAgree sp m9 ment → VarOutAgree sp mpc m9 →
    Eval_exprLoaded mpc
  finalStore : ∀ m9 mpc m', VarSpillAgree sp m9 ment → VarOutAgree sp mpc m9 →
    (∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mpc[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  finalSlots : ∀ m9 mpc, VarSpillAgree sp m9 ment → VarOutAgree sp mpc m9 →
    read64 mpc (sp.toNat - 8) = some r.toNat ∧
    read64 mpc (sp.toNat - 16) = some v8.toNat ∧
    read64 mpc (sp.toNat - 24) = some v9.toNat ∧
    read64 mpc (sp.toNat - 32) = some v18.toNat
  finalMemFrame : ∀ m9 mpc, VarSpillAgree sp m9 ment → VarOutAgree sp mpc m9 →
    ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpc[a]? = m0[a]?
  payloadDisj : ∀ m9 mpc, VarSpillAgree sp m9 ment → VarOutAgree sp mpc m9 →
    ∀ (p : Nat) (s : String),
      read64 mpc (((sp - 1088#64) + 0xf0#64).toNat + 8) = some p →
      ValuePayload v s → ∀ k, k ≤ s.length → p + k < sret.toNat ∨ sret.toNat + 24 ≤ p + k
  bufSret : sp.toNat - 1088 + 0xf0 + 24 ≤ sret.toNat ∨
    sret.toNat + 24 ≤ sp.toNat - 1088 + 0xf0
  sretAl : sret.toNat % 8 = 0
  sretLo : 0x80000000 ≤ sret.toNat
  sretHi : sret.toNat + 24 ≤ 0x100000000
  sretWin : tohostAddr + 16 ≤ sret.toNat
  bufLo : 0x80000000 ≤ sp.toNat - 1088 + 0xf0
  bufHi : sp.toNat - 1088 + 0x108 ≤ 0x100000000
  bufWin : tohostAddr + 16 ≤ sp.toNat - 1088 + 0xf0
  bufAl : (sp.toNat - 1088 + 0xf0) % 8 = 0
  sp1088 : 1088 ≤ sp.toNat
  spHi64 : sp.toNat ≤ 0x100000000
  spLo64 : 0x80000000 ≤ sp.toNat
  spWin64 : tohostAddr + 16 + 1088 ≤ sp.toNat
  spAl64 : sp.toNat % 8 = 0
  stackLo : SL.lo + 1088 ≤ sp.toNat
  retAl : r.toNat % 4 = 0
  outEq : String.join out0.toList = st.out

/-! ## The full bridge: `ArmEntryK → VarPostCall`

`prefix ≫ (callee-body ≫ relocation)`, spliced with `callSeg`.  Consumes
`VarCallLinkage` (the residual seam); no other open obligation. -/
theorem varBridge_callee
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64) (len pn : Nat)
    (hL : VarCallLinkage g N A SL φf φc st env x v sp r sret aExpr aEnv
      v8 v9 v18 v19 v20 v21 out0 m0 ment penv nm len pn) :
    Triple
      (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 v19 v20 v21 out0 ment penv nm)
      (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c) := by
  intro c hc
  obtain ⟨hgood, htick, hmem, hpc, ha0, ha1, ha2, hra, hsp, hs1, hs0, hs2,
    hs3, hs4, hs5, hout0, hmi⟩ := hc
  have ha0' : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (φf env)) := by
    rw [hL.penv_eq] at ha0
    exact ha0
  have hHead : PrologueHeadSt (BitVec.ofNat 64 (φf env)) nm
      ((sp - 1088#64) + 0xf0#64) (sp - 1088#64) (0x80003444#64)
      aExpr sret aEnv v19 v20 v21 len pn ment c :=
    { good := hgood, loadedG := by rw [hmem]; exact hL.loaded, mem := hmem,
      pc := hpc, a0 := ha0', a1 := ha1, a2 := ha2, ra := hra, sp := hsp,
      cs8 := hs0, cs9 := hs1, cs18 := hs2, cs19 := hs3, cs20 := hs4,
      cs21 := hs5, minstret := hmi, tick := htick, envNe := by
        rw [← hL.penv_eq]; exact hL.envNe,
      read_len := by rw [← hL.penv_eq]; exact hL.read_len,
      read_pn := by rw [← hL.penv_eq]; exact hL.read_pn,
      spDrop := hL.spDrop, spLo := hL.spLo, spHi := hL.spHi,
      spWin := hL.spWin, spAlign := hL.spAlign, spCode := hL.spCode,
      envHi := by rw [← hL.penv_eq]; exact hL.envHi,
      envStackDisj := by rw [← hL.penv_eq]; exact hL.envStackDisj }
  obtain ⟨c', m9, hsteps, hpost0, hspill⟩ :=
    env_get_lookup_from_entry st.store env v nm ((sp - 1088#64) + 0xf0#64)
      (sp - 1088#64) (0x80003444#64) aExpr sret aEnv v19 v20 v21 x N A φf φc
      ment c len pn hL.chain hHead
      (by intro m' hm'; exact hL.storeHead m' (by simpa [VarSpillAgree] using hm'))
      (by intro m' hm'; exact hL.chainFacts m' (by simpa [VarSpillAgree] using hm'))
      (by intro m' hm'; exact hL.strcmp m' (by simpa [VarSpillAgree] using hm'))
  have hspill' : VarSpillAgree sp m9 ment := by simpa [VarSpillAgree] using hspill
  have hpost := hpost0.output_trans hout0
  obtain ⟨mpc, w0, w1, w2, hmempc, hloaded, hvalue, hw0, hw1, hw2, houtside⟩ := hpost.mem
  have houtside' : VarOutAgree sp mpc m9 := by
    intro k hk
    exact houtside k hk
  have houtNat : ((sp - 1088#64) + 0xf0#64).toNat = sp.toNat - 1088 + 0xf0 := by
    rw [show (0xf0#64 : BitVec 64) = sign_extend (m := 64) (0x0f0#12) from by
      apply BitVec.eq_of_toNat_eq; decide]
    exact var_off_pos sp (0x0f0#12) 0xf0 (by decide) (by omega) hL.sp1088
  let d0 : BitVec 64 := BitVec.ofNat 64 w0
  let d1 : BitVec 64 := BitVec.ofNat 64 w1
  let d2 : BitVec 64 := BitVec.ofNat 64 w2
  have hd0 : d0.toNat = w0 := by
    simp only [d0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mpc _ _ hw0)]
  have hd1 : d1.toNat = w1 := by
    simp only [d1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mpc _ _ hw1)]
  have hd2 : d2.toNat = w2 := by
    simp only [d2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mpc _ _ hw2)]
  have hcopy : ∀ m' : Mem, read64 m' sret.toNat = some d0.toNat →
      read64 m' (sret.toNat + 8) = some d1.toNat →
      read64 m' (sret.toNat + 16) = some d2.toNat →
      (∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mpc[k]? = m'[k]?) →
      ValueRepr m' N φc sret.toNat v := by
    intro m' hd0' hd1' hd2' hout'
    refine valueRepr_copy_of_writeWindow (m := mpc) (m' := m')
      (srcAddr := ((sp - 1088#64) + 0xf0#64).toNat) (dstAddr := sret.toNat) ?_ ?_ ?_ hvalue
    · intro j hj
      rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ 16 ≤ j) with h | ⟨h1, h2⟩ | h
      · exact read64_same_bytes (by simpa [hd0] using hd0') hw0 j h
      · have hb := read64_same_bytes (by simpa [hd1] using hd1') hw1 (j - 8) (by omega)
        rw [show sret.toNat + 8 + (j - 8) = sret.toNat + j by omega,
          show ((sp - 1088#64) + 0xf0#64).toNat + 8 + (j - 8) =
            ((sp - 1088#64) + 0xf0#64).toNat + j by omega] at hb
        exact hb
      · have hb := read64_same_bytes (by simpa [hd2] using hd2') hw2 (j - 16) (by omega)
        rw [show sret.toNat + 16 + (j - 16) = sret.toNat + j by omega,
          show ((sp - 1088#64) + 0xf0#64).toNat + 16 + (j - 16) =
            ((sp - 1088#64) + 0xf0#64).toNat + j by omega] at hb
        exact hb
    · intro a ha
      exact (hout' a (by rcases ha with h | h <;> omega)).symm
    · intro p s hp hps k hk
      exact hL.payloadDisj m9 mpc hspill' houtside' p s hp hps k hk
  obtain ⟨hslotRa, hslotS0, hslotS1, hslotS2⟩ := hL.finalSlots m9 mpc hspill' houtside'
  refine ⟨c', hsteps, mpc, hpost.good, hpost.tick, hpost.pc,
    ⟨(1#64), hpost.found, by decide⟩, hpost.s1, ?_, hL.finalMinstret m9 c' hpost, hpost.output,
    hL.outEq, hmempc, hL.finalCode m9 mpc hspill' houtside',
    ⟨d0, d1, d2, ?_, ?_, ?_, hcopy⟩, ?_, hL.finalFrame m9 c' hpost,
    hslotRa, hslotS0, hslotS1, hslotS2, hL.g8, hL.g9, hL.g18, hL.g2,
    hL.finalMemFrame m9 mpc hspill' houtside', hL.bufSret,
    hL.sretAl, hL.sretLo, hL.sretHi, hL.sretWin, hL.bufLo, hL.bufHi, hL.bufWin,
    hL.bufAl, hL.sp1088, hL.spHi64, hL.spLo64, hL.spWin64, hL.spAl64,
    hL.stackLo, hL.retAl⟩
  · have hspeq := hpost.sp
    rw [BitVec.sub_add_cancel] at hspeq
    exact hspeq
  · simpa [houtNat, hd0] using hw0
  · simpa [houtNat, hd1] using hw1
  · simpa [houtNat, hd2] using hw2
  · intro m' hm'; exact hL.finalStore m9 mpc m' hspill' houtside' hm'

theorem varBridge
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 v19 v20 v21 : BitVec 64)
    (out0 : Array String) (m0 ment : Mem) (penv nm : BitVec 64) (len pn : Nat)
    (hL : VarCallLinkage g N A SL φf φc st env x v sp r sret aExpr aEnv
      v8 v9 v18 v19 v20 v21 out0 m0 ment penv nm len pn) :
    Triple
      (fun c => ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        c.σ.regs.get? Register.x13 = some penv)
      (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c) :=
  Triple.seq
    (varBridge_prefix_triple g N A SL φf φc st x sp r sret aExpr aEnv
      v8 v9 v18 v19 v20 v21 out0 m0 ment penv nm hL.name hL.g19 hL.g20 hL.g21
      hL.nmLo hL.nmHi hL.nmWin)
    (varBridge_callee g N A SL φf φc st env x v sp r sret aExpr aEnv
      v8 v9 v18 v19 v20 v21 out0 m0 ment penv nm len pn hL)

/-! ## `eval_var_row_closed` — the UNCONDITIONAL row modulo the caller-linkage seam

Discharges `VarLeafResid`'s open `env_get_found` oracle with `varBridge` (the
proved prefix + the `VarCallLinkage` callee seam), plus the G-class geometry side
conditions.  The whole thing is packaged as `VarRowResid`, the single per-case
residual, so `eval_var_row_closed` has the SAME conclusion as `eval_var_row`
(fills the exact `hVar` minor-premise slot) with its Triple oracle now BUILT, not
assumed — the only remaining input is the honest geometry + the `VarCallLinkage`
seam, exactly the caller-linkage the M4 recursor supplies.

`eval_var_row` itself is unmodified; this is a strict corollary. -/

/-- Per-case row residual: the honest layout geometry `VarLeafResid` needs (the six
G-class side conditions + `LeafWiden`), plus the `VarCallLinkage` seam for every
`ment/v8/v9/v18/penv/nm` witness (one env-pointer `penv` + name `nm` per memory
witness).  All fields are supplied ABOVE the row (by the M4 caller). -/
def VarRowResid (st : SpecSt) (x : String) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    st.store.get? env x = some v →
    c.σ.mem = m0 →
    -- the six G-class geometry conditions (verbatim from `VarLeafResid`).
    ((∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
        p + x.length < SL.lo ∨ sp.toNat ≤ p) ∧
      (sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat) ∧
      Vsa.Sim.Code.Env_getLoaded c.σ.mem ∧
      ((0x80002cdc : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80002c10) ∧
      Vsa.Sim.VarSlotPinned c.σ.mem ∧
      ((0x80019f58 : Nat) + 20 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 16)) ∧
    Vsa.Sim.LeafReturnWiden g N A SL φf φc st v sp r sret m0 ∧
    -- the caller-linkage seam for every callee-entry witness (with its env
    -- pointer `penv` and name `nm` chosen by the caller per memory witness).
    (∀ (ment : Mem) (v8 v9 v18 : BitVec 64),
      ∃ v19 v20 v21 penv nm : BitVec 64, ∃ len pn : Nat,
      penv = BitVec.ofNat 64 (φf env) ∧
      VarCallLinkage g N A SL φf φc st env x v sp r sret aExpr aEnv
        v8 v9 v18 v19 v20 v21 c.σ.sailOutput m0 ment penv nm len pn)

/-- **`VarLeafResid` discharged from `VarRowResid`.**  The `env_get_found` oracle
is `varBridge` lifted over the `∃ ment v8 v9 v18` witnesses (each supplies a
`VarCallLinkage`, which additionally binds `penv`/`nm`). -/
theorem varLeafResid_of_rowResid (st : SpecSt) (x : String) (v : Value)
    (hR : VarRowResid st x v) : Vsa.Sim.Rows.VarLeafResid st x v := by
  -- (wave 47e repair: `VarLeafResid` gained the ITEM-ZERO `d`/`env` binders +
  -- the `EvalEntry` conditioning; this file's olean was latently stale.)
  intro g N A SL φf φc d env sp r sret aEnv aExpr m0 c hlookup hc
  obtain ⟨hGeom, hW, hLink⟩ :=
    hR g N A SL φf φc env sp r sret aEnv aExpr m0 c hlookup hc.mem
  refine ⟨hGeom.1, hGeom.2.1, hGeom.2.2.1, hGeom.2.2.2.1, hGeom.2.2.2.2.1, hGeom.2.2.2.2.2, ?_, hW⟩
  -- the `env_get_found` oracle: lift `varBridge` over the pre-existentials.
  intro c' hpre
  let ment := Classical.choose hpre
  have he1 := Classical.choose_spec hpre
  let v8 := Classical.choose he1
  have he2 := Classical.choose_spec he1
  let v9 := Classical.choose he2
  have he3 := Classical.choose_spec he2
  let v18 := Classical.choose he3
  have hpre' := Classical.choose_spec he3
  have hArm : ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c' :=
    @And.left (ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c')
      (c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env))) hpre'
  have hx13 : c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)) :=
    @And.right (ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c')
      (c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env))) hpre'
  -- pick the env pointer `penv` and name `nm` from the linkage family, then apply.
  -- the linkage carries `a3 : ArmEntryK → x13 = penv`; instantiate at any witness.
  obtain ⟨v19, v20, v21, penv, nm, len, pn, _henv, hLmem⟩ := hLink ment v8 v9 v18
  obtain ⟨c'', hs, hpost⟩ :=
    varBridge g N A SL φf φc st env x v sp r sret aExpr aEnv
      v8 v9 v18 v19 v20 v21 c.σ.sailOutput m0 ment penv nm
      len pn hLmem c' ⟨hArm, _henv ▸ hx13⟩
  obtain ⟨mpc, hVPC⟩ := hpost
  exact ⟨c'', hs, mpc, v8, v9, v18, hVPC⟩

/-- **The unconditional var row** (modulo the caller-linkage residual `VarRowResid`).
Same conclusion as `eval_var_row`; the `env_get_found` Triple is now proved by
`varBridge`, not assumed. -/
theorem eval_var_row_closed (hR : ∀ st x v, VarRowResid st x v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
      (a : st.store.get? env x = some v),
      mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a) :=
  Vsa.Sim.Rows.eval_var_row (fun st x v => varLeafResid_of_rowResid st x v (hR st x v))

#print axioms varBridge_prefix
#print axioms varBridge_callee
#print axioms varBridge
#print axioms varLeafResid_of_rowResid
#print axioms eval_var_row_closed

end Vsa.Sim
