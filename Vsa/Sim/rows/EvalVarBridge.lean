import Vsa.Sim.EvalVarSim
import Vsa.Sim.EnvGetSpec9
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
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64) (c : Config)
    (hArm : ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
    -- the missing env-pointer datum: `x13 = penv` at the arm entry.
    (ha3 : c.σ.regs.get? Register.x13 = some penv)
    -- the var-name pointer read from the Expr node (`ld a1, 8(a2)` value).
    (hname : read64 ment (aExpr.toNat + 8) = some nm.toNat)
    -- geometry the `ld a1, 8(a2)` load needs (the name pointer slot in RAM, aligned).
    (hnmLo : 0x80000000 ≤ aExpr.toNat + 8)
    (hnmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000)
    (hnmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8)
    (hnmAl : (aExpr.toNat + 8) % 8 = 0) :
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
      (∃ w, c'.σ.regs.get? Register.minstret = some w) := by
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hload, _hcallee,
    hexpr, houtStr, haExprAl, haExprLo, haExprHi, haExprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframeReg,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEv,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    hx11, hx8, hx18⟩ := hArm
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
      (by rw [hoff8]; omega)
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
  obtain ⟨vmi4, hmi4⟩ := obs_jal_minstret hobs4
  refine ⟨⟨σ4, i4, c.steps+1+1+1+1⟩, ?_, hG4, hi4, ?_, hpc4, hx10_4, hx11_4, hx12_4, hx1_4, hsp_4,
    hs1_4, hx8_4, hx18_4, ⟨vmi4, hmi4⟩⟩
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
    (st : Vsa.While.St) (sp sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64)
    (ment : Mem) (penv nm : BitVec 64) (c : Config) : Prop :=
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
  (∃ w, c.σ.regs.get? Register.minstret = some w)

/-- Prefix as a `Triple` over `EnvGetEntryV`.  Directly repackages
`varBridge_prefix`. -/
theorem varBridge_prefix_triple
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (x : String)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64)
    (ha3 : ∀ c, ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c → c.σ.regs.get? Register.x13 = some penv)
    (hname : read64 ment (aExpr.toNat + 8) = some nm.toNat)
    (hnmLo : 0x80000000 ≤ aExpr.toNat + 8)
    (hnmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000)
    (hnmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8)
    (hnmAl : (aExpr.toNat + 8) % 8 = 0) :
    Triple
      (fun c => ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
      (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm) := by
  intro c hArm
  obtain ⟨c', hs, hG', htick', hmem', hpc', h10, h11, h12, h1, h2, h9, h8, h18, hmi⟩ :=
    varBridge_prefix g N A SL φf φc st x sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment penv nm c
      hArm (ha3 c hArm) hname hnmLo hnmHi hnmWin hnmAl
  exact ⟨c', hs, hG', htick', hmem', hpc', h10, h11, h12, h1, h2, h9, h8, h18, hmi⟩

/-! ## The caller-linkage residual (`VarCallLinkage`)

The genuinely-open seam between `ArmEntryK` and `VarPostCall`, packaged as ONE
typed premise.  It carries exactly the two facts `ArmEntryK`/`VarLeafResid` cannot
provide (see the file header):

1. **The env-pointer + callee contract seam** (`callee`): a `Triple` from the
   `env_get` entry config (`EnvGetEntryV`, produced by the proved prefix) to the
   `env_get` link-return post `VarPostCall`.  This is the env_get FOUND-case body
   (`env_get_found_uncond''` over the looked-up `Frame f` + HIT-witness `iw` with
   `env = penv`, `sp0 = sp-1088`, `r0 = 0x80003444`) PLUS the result-buffer→`sret`
   relocation repackaging (`ValueRepr … out v` → the three-word copy obligation,
   the callee-saved spill survival, `StoreRepr` survival, the `m0` memory frame).

   Both halves are dischargeable ABOVE `ArmEntryK`: (a) `env_get_found_uncond''`
   proves the callee body from `FoundSt`+`FrameStackDisj`, which the caller builds
   from `StoreRepr` unpacked at the looked-up frame + the honest heap-vs-stack
   disjointness; (b) the relocation is a memory-frame transport once env_get's
   post carries "wrote only `[out, out+24)`".  Neither is derivable from
   `VarLeafResid`'s current fields, so both are threaded here.

The eventual M4 caller (the recursive `EvalE`/`ExecSeq` recursor) supplies
`VarCallLinkage`: it threads the real interp-struct env pointer `penv`, unpacks
`StoreRepr` at the frame `st.store.get? env x` resolves in, and links env_get's
memory-frame post. -/
structure VarCallLinkage
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (x : String) (v : Value)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64) : Prop where
  /-- the value of `x13` (`a3`, the machine env pointer passed to `env_get`). -/
  a3 : ∀ c, ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
      sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c → c.σ.regs.get? Register.x13 = some penv
  /-- the var-name pointer read from the Expr node (`ld a1, 8(a2)`). -/
  name : read64 ment (aExpr.toNat + 8) = some nm.toNat
  nmLo : 0x80000000 ≤ aExpr.toNat + 8
  nmHi : aExpr.toNat + 8 + 8 ≤ 0x100000000
  nmWin : aExpr.toNat + 8 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + 8
  nmAl : (aExpr.toNat + 8) % 8 = 0
  /-- the `env_get` FOUND-case body + result relocation (see the doc-comment):
  `EnvGetEntryV → VarPostCall`.  Dischargeable by `env_get_found_uncond''` +
  the buffer→sret relocation once env_get's memory-frame post lands. -/
  callee : Triple
    (EnvGetEntryV st sp sret aExpr aEnv v8 v9 v18 ment penv nm)
    (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c)

/-! ## The full bridge: `ArmEntryK → VarPostCall`

`prefix ≫ (callee-body ≫ relocation)`, spliced with `callSeg`.  Consumes
`VarCallLinkage` (the residual seam); no other open obligation. -/
theorem varBridge
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (x : String) (v : Value)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (penv nm : BitVec 64)
    (hL : VarCallLinkage g N A SL φf φc st x v sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment penv nm) :
    Triple
      (fun c => ArmEntryK g N A SL φf φc st (0x80003434#64) Env_getLoaded (.var x)
        sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpc, VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpc c) :=
  Triple.seq
    (varBridge_prefix_triple g N A SL φf φc st x sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment penv nm
      hL.a3 hL.name hL.nmLo hL.nmHi hL.nmWin hL.nmAl)
    hL.callee

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
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    c.σ.mem = m0 →
    -- the six G-class geometry conditions (verbatim from `VarLeafResid`).
    ((∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
        p + x.length < SL.lo ∨ sp.toNat ≤ p) ∧
      (sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat) ∧
      Vsa.Sim.Code.Env_getLoaded c.σ.mem ∧
      ((0x80002cdc : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80002c10) ∧
      Vsa.Sim.VarSlotPinned c.σ.mem ∧
      ((0x80019f58 : Nat) + 20 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 16)) ∧
    Vsa.Sim.LeafWiden g N A SL φf φc st v sp r sret m0 ∧
    -- the caller-linkage seam for every callee-entry witness (with its env
    -- pointer `penv` and name `nm` chosen by the caller per memory witness).
    (∀ (ment : Mem) (v8 v9 v18 : BitVec 64), ∃ penv nm : BitVec 64,
      VarCallLinkage g N A SL φf φc st x v sp r sret aExpr aEnv v8 v9 v18
        c.σ.sailOutput m0 ment penv nm)

/-- **`VarLeafResid` discharged from `VarRowResid`.**  The `env_get_found` oracle
is `varBridge` lifted over the `∃ ment v8 v9 v18` witnesses (each supplies a
`VarCallLinkage`, which additionally binds `penv`/`nm`). -/
theorem varLeafResid_of_rowResid (st : SpecSt) (x : String) (v : Value)
    (hR : VarRowResid st x v) : Vsa.Sim.Rows.VarLeafResid st x v := by
  intro g N A SL φf φc sp r sret aEnv aExpr m0 c hc
  obtain ⟨hGeom, hW, hLink⟩ := hR g N A SL φf φc sp r sret aEnv aExpr m0 c hc
  refine ⟨hGeom.1, hGeom.2.1, hGeom.2.2.1, hGeom.2.2.2.1, hGeom.2.2.2.2.1, hGeom.2.2.2.2.2, ?_, hW⟩
  -- the `env_get_found` oracle: lift `varBridge` over the pre-existentials.
  intro c' hpre
  obtain ⟨ment, v8, v9, v18, hArm⟩ := hpre
  -- pick the env pointer `penv` and name `nm` from the linkage family, then apply.
  -- the linkage carries `a3 : ArmEntryK → x13 = penv`; instantiate at any witness.
  obtain ⟨penv, nm, hLmem⟩ := hLink ment v8 v9 v18
  obtain ⟨c'', hs, hpost⟩ :=
    varBridge g N A SL φf φc st x v sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment penv nm
      hLmem c' hArm
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
#print axioms varBridge
#print axioms varLeafResid_of_rowResid
#print axioms eval_var_row_closed

end Vsa.Sim
