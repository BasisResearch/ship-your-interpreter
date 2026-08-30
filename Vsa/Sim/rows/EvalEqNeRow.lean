import Vsa.Sim.EvalBinSim3
import Vsa.Sim.EvalEqNeArm
import Vsa.Sim.EqNeTailSites
import Vsa.Sim.EqNeDispatchSeg
import Vsa.Sim.BoolBoxEpilogue
import Vsa.Sim.EvalNotSim
import Vsa.Sim.LoopStep
import Vsa.Sim.rows.EvalMulRow
import Vsa.Sim.rows.IntPostEpilogue

/-!
# `EvalEqNeRow` — Wave-D M4 rows: `evalEqSim` / `evalNeSim`

The `EvalE.binary .eq` and `.ne` value cases.  Both compose
`blockB_binary ≫ blockC_eq/ne ≫ blockD_v_rec`, and `blockC_eq`/`blockC_ne` are thin
instantiations of the SHARED parameterized core `blockC_eqne`.

`blockC_eqne` runs, from the `value_equal` RETURN config (`VeReturn`, at the frame
base `sp-1088`, `x10 = cond (vl.equal vr) 1 0`):

  `[middle] ; jal value_bool ; ld s3,0x418(sp) ; j 0x800033ec`  →  `PreEpilogueVD .bool`

where the ONLY op-specific pieces are (all passed as PARAMETERS):

* the middle stage (`value_equal` return → `value_bool` entry), factored into three
  op-parameterised site shapes:
  - `EqNeFirstSite firstPC bwOf` — `mv a1,a0` (eq, `bwOf = id`) vs `seqz a1,a0`
    (ne, `bwOf = seqz`); writes `x11 := bwOf x10`,
  - `EqNeSecondSite secondPC` — `mv a0,s1` (byte-identical across arms),
  - `EqNeJalVboolSite jalPC jImm'` — `jal value_bool`;
* the box params (`ldPC`/`jPC`/`jImm`/`ldS3`/`jExit`), and
* the boxed value `bres` + the bridge `(bwOf (cond …) != 0#64) = bres`.

The value box + epilogue is the SHARED `boolBoxEpilogue` (`Vsa/Sim/BoolBoxEpilogue.lean`),
the eq/ne analogue of `intBoxEpilogue`.  So eq and ne share EVERYTHING in `blockC_eqne`
+ `boolBoxEpilogue`, differing only in `firstSite`/`bwOf`, the three middle-site PCs,
the box constants, and `bres`.

The `jal value_equal` dispatch front + the operand copies (bufa holds `ValueRepr vl`,
bufb holds `ValueRepr vr`, copied by the `#derive_case` dispatch block) + the
`value_equal` caller obligations (`str`-witness, `StrcmpLoaded`/`MaskPinned`/`JumpTable`,
`r%4=0`, `φc`/native injectivity) + `value_equal`'s `sailOutput` invariance (which its
contract does not thread) are threaded as the `blockC` bridge caller residual through
`evalEqNeSim`'s `hblockC` hypothesis — exactly as `evalDivSim` stays conditional on its
caller linkage.  `blockC_eq`/`blockC_ne` consume the `value_equal`-return `VeReturn` +
the shared `EqNeBoxPre` transport bundle.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `JumpTable` transfer through an agreeing memory -/

/-- `JumpTable` transfers to any memory agreeing on the jump-table region
`[0x80019ef8, 0x80019ef8+24)`. -/
theorem jumpTable_of_agree (m1 m2 : Mem)
    (hagree : ∀ a, 0x80019ef8 ≤ a → a < 0x80019ef8 + 24 → m2[a]? = m1[a]?)
    (h : JumpTable m1) : JumpTable m2 := by
  obtain ⟨a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, d0,d1,d2,d3, e0,e1,e2,e3, f0,f1,f2,f3⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hagree _ (by decide) (by decide)]; assumption)

/-! ## `veReturn` — the `value_equal` return config the middle consumes

After `jal value_equal` returns (`ve_str_post`), the machine is at
`BitVec.update (link + 0) 0 0` (the `jal` link), `x10 = cond (vl.equal vr) 1 0`,
`x2 = sp` (frame base), memory agrees with the `value_equal`-entry mem off
`[sp-16, sp)`, and callee-saved (`NotWrittenVEStr`) survive.  We bundle the fields
the middle + box need. -/
structure VeReturn
    (g : (R : Register) → Option (RegisterType R))
    (fbase sret : BitVec 64) (vl vr : Value) (link : BitVec 64)
    (out0 : Array String) (mEnt : Mem) (c : Config) : Prop where
  hG : GoodState c.σ
  hpc : c.σ.regs.get? Register.PC = some (BitVec.update (link + sign_extend (m := 64) (0x000#12)) 0 0#1)
  hx10 : c.σ.regs.get? Register.x10 = some (cond (Value.equal vl vr) (1#64) (0#64))
  hx9 : c.σ.regs.get? Register.x9 = some sret
  hsp : c.σ.regs.get? Register.x2 = some fbase
  hmi : ∃ w, c.σ.regs.get? Register.minstret = some w
  htick : c.tick < 2
  hout : c.σ.sailOutput = out0
  -- memory agrees with the value_equal-entry mem off the scratch window `[fbase-16, fbase)`
  hmemframe : ∀ a, ¬ (fbase.toNat - 16 ≤ a ∧ a < fbase.toNat) → c.σ.mem[a]? = mEnt[a]?
  hMemExt : MemExtends mEnt c.σ.mem
  -- callee-saved (`NotWrittenVEStr`), EXCEPT `x9` (= sret, above) and `x19` (arm-clobbered),
  -- collapse to eval `g`
  hframe : ∀ R : Register, NotWrittenVEStr R →
    (Register.x9 == R) = false → (Register.x19 == R) = false → c.σ.regs.get? R = g R

/-! ## Op-parameterised middle-stage site shapes

The `value_equal` return runs three shuffle instructions before `jal value_bool`.
Only the FIRST differs (`mv a1,a0` for eq, `seqz a1,a0` for ne); both write `x11`
from `x10`, so we parameterise by the site (of the shared `EqNeFirstSite` shape) and
the resulting word `bw`.  The second (`mv a0,s1`) and third (`jal value_bool`) are
byte-identical across arms up to PC, parameterised by their PCs. -/

/-- The first middle site (`mv/seqz a1,a0`): writes `x11 := bwOf x10`, at `firstPC`,
landing `firstPC+4`.  `bwOf` is `id` for eq (`mv`), `seqz` for ne. -/
abbrev EqNeFirstSite (firstPC : BitVec 64) (bwOf : BitVec 64 → BitVec 64) : Prop :=
  ∀ (σ : MState) (i u : Nat) (pc vminstret v10 : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some pc →
    σ.regs.get? Register.minstret = some vminstret →
    σ.regs.get? Register.x10 = some v10 →
    Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = firstPC → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (bwOf v10))

/-- The `mv a0,s1` site: writes `x10 := x9 + 0`, at `secondPC`, landing `secondPC+4`. -/
abbrev EqNeSecondSite (secondPC : BitVec 64) : Prop :=
  ∀ (σ : MState) (i u : Nat) (pc vminstret v9 : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some pc →
    σ.regs.get? Register.minstret = some vminstret →
    σ.regs.get? Register.x9 = some v9 →
    Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = secondPC → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10
        (v9 + sign_extend (m := 64) (0x000#12)))

/-- The `jal value_bool` site: links `x1 := jalPC+4`, jumps to `0x800027f8`
(`= jalPC + sext jImm`), at `jalPC`. -/
abbrev EqNeJalVboolSite (jalPC : BitVec 64) (jImm : BitVec 21) : Prop :=
  ∀ (σ : MState) (i u : Nat) (pc vminstret : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some pc →
    σ.regs.get? Register.minstret = some vminstret →
    Vsa.Sim.Code.Eval_exprLoaded σ.mem → pc = jalPC → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret jImm Register.x1 (BitVec.addInt pc 4))

/-! ## `blockC_eqne` — SHARED core: `[middle] ≫ boolBoxEpilogue`

From the `value_equal` return config `cR` (a `VeReturn` at the frame base
`sp - 1088`, `x10 = cond (vl.equal vr) 1 0`), run the op-specific middle
(`mv/seqz a1,a0 ; mv a0,s1 ; jal value_bool`, supplied as the three parameterised
site lemmas + the first-site word map `bwOf`) to reach the `value_bool` entry, then
hand off to `boolBoxEpilogue` for the box + epilogue, producing
`PreEpilogueVD .bool bres`.  eq/ne share this ENTIRE proof; they differ only in the
`firstSite`/`bwOf` (mv vs seqz), the three site PCs, the box constants, and `bres`. -/
theorem blockC_eqne
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfm φcm φf' φc' : Addr → Nat)
    (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (bres : Bool) (out0 : Array String)
    (m0 mEnt : Mem) (cR : Config) (link : BitVec 64)
    -- middle-stage sites (op-specific)
    (firstPC secondPC jalPC : BitVec 64) (bwOf : BitVec 64 → BitVec 64) (jImm' : BitVec 21)
    (firstSite : EqNeFirstSite firstPC bwOf) (secondSite : EqNeSecondSite secondPC)
    (jalVboolSite : EqNeJalVboolSite jalPC jImm')
    -- box params (op-specific)
    (ldPC jPC : BitVec 64) (jImm : BitVec 21)
    (ldS3 : LdS3Site ldPC) (jExit : JExitSite jPC jImm)
    -- middle wiring facts
    (hfirstAfter : BitVec.addInt firstPC 4 = secondPC)
    (hsecondAfter : BitVec.addInt secondPC 4 = jalPC)
    (hjalTgt : (jalPC + sign_extend (m := 64) jImm') = (0x800027f8#64 : BitVec 64))
    (hlink0 : BitVec.update (link + sign_extend (m := 64) (0x000#12)) 0 0#1 = firstPC)
    (hboxLink : BitVec.addInt jalPC 4 = ldPC)
    -- box wiring facts
    (hldPCupdate : BitVec.update (ldPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = ldPC)
    (hldAfter : BitVec.addInt ldPC 4 = jPC)
    (hjTgt : (jPC + sign_extend (m := 64) jImm) = (0x800033ec#64 : BitVec 64))
    (hjTgtAl : (jPC + sign_extend (m := 64) jImm).toNat % 4 = 0)
    (hldPCeq : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40)
    (hlinkAl : (BitVec.update (ldPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    -- the boolean bridge: bw fed to value_bool boxes to `bres`
    (hval_bridge : (bwOf (cond (Value.equal vl vr) (1#64) (0#64)) != 0#64) = bres)
    -- === the `value_equal` return config ===
    (hcR : VeReturn g (sp - 1088#64) sret vl vr link out0 mEnt cR)
    (hVboolEnt : Value_boolLoaded mEnt)
    (hcodeEnt : Eval_exprLoaded mEnt)
    (hBoolRegion : BoolRegion sret)
    -- === the arm's transport of `mEnt` back to `c`/`m0`/store/geometry ===
    (hpfm : PhiExtends φf φfm st'.store.frames.size)
    (hpcm : PhiExtends φc φcm st'.store.closures.size)
    (hpf' : PhiExtends φfm φf' st''.store.frames.size)
    (hpc' : PhiExtends φcm φc' st''.store.closures.size)
    (houtStr : String.join out0.toList = st''.out)
    (hSurvSL0 : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mEnt[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store)
    (hs3Ent : read64 mEnt (sp.toNat - 40) = some w19.toNat)
    (hslotRa0 : read64 mEnt (sp.toNat - 8) = some r.toNat)
    (hslotS00 : read64 mEnt (sp.toNat - 16) = some v8.toNat)
    (hslotS10 : read64 mEnt (sp.toNat - 24) = some v9.toNat)
    (hslotS20 : read64 mEnt (sp.toNat - 32) = some v18.toNat)
    (hgv8 : g Register.x8 = some v8) (hgv9 : g Register.x9 = some v9)
    (hgv18 : g Register.x18 = some v18) (hgv2 : g Register.x2 = some sp)
    (hgx19 : g Register.x19 = some v19) (hw19 : w19 = v19)
    (hMemExt0 : MemExtends m0 mEnt)
    (hmemframe0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mEnt[a]? = m0[a]?)
    (hsretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat)
    (hsretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat)
    (hsretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi)
    (hSLlo40 : SL.lo ≤ sp.toNat - 40) (hSLlo32 : SL.lo ≤ sp.toNat - 32)
    (hSLloSp : SL.lo + 1104 ≤ sp.toNat) (hspSLhi : sp.toNat ≤ SL.hi)
    (hsp1088 : 1088 ≤ sp.toNat) (hspRam : sp.toNat ≤ 0x100000000)
    (hspLo : 0x80000000 ≤ sp.toNat) (hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat)
    (hsp8 : sp.toNat % 8 = 0) (hraAl : r.toNat % 4 = 0)
    (hldLo : 0x80000000 ≤ (sp.toNat - 40))
    (hldHiRam : (sp.toNat - 40) + 8 ≤ 0x100000000)
    (hldHtif : (sp.toNat - 40) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (sp.toNat - 40))
    (hldAl : (sp.toNat - 40) % 8 = 0) :
    ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat) (cfin : Config),
      Steps cR cfin ∧
      PhiExtends φf φfm' st'.store.frames.size ∧
      PhiExtends φc φcm' st'.store.closures.size ∧
      PhiExtends φfm' φfe st''.store.frames.size ∧
      PhiExtends φcm' φce st''.store.closures.size ∧
      PreEpilogueVD g N A SL φfe φce st'' (.bool bres) sp r sret v8 v9 v18 out0 m0 mpre cfin := by
  obtain ⟨hGR, hpcR, hx10R, hx9R, hspR, ⟨vmiR, hmiR⟩, htickR, houtR, hmemframeR, hMemExtR, hframeR⟩ := hcR
  have hpcR' : cR.σ.regs.get? Register.PC = some firstPC := by rw [hpcR, hlink0]
  have hfb : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]; have h : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h]; have := sp.isLt; omega
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- code loaded on cR.σ.mem (agrees with mEnt off [sp-1088-16, sp-1088))
  have hcodeR : Eval_exprLoaded cR.σ.mem := by
    refine loaded_eval_expr_agreeP mEnt cR.σ.mem (fun k hk => ?_) hcodeEnt
    -- code region [0x80003164,0x80003fe0) is BELOW tohostAddr ≤ framebase-16 (window)
    refine (hmemframeR k ?_).symm
    rw [hfb]; rw [htoh] at hspHtif; rintro ⟨h1, h2⟩; omega
  -- === middle 1: mv/seqz a1,a0 → x11 := bwOf x10 ===
  obtain ⟨τ1, j1, ht1, hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    firstSite cR.σ cR.tick cR.steps firstPC vmiR (cond (Value.equal vl vr) (1#64) (0#64))
      hGR hpcR' hmiR hx10R hcodeR rfl htickR
  have hstepτ1 : Step cR ⟨τ1, j1, cR.steps + 1⟩ := by cases cR; exact ht1
  have hmemτ1e : τ1.mem = cR.σ.mem := hmemτ1
  have hpcτ1 : τ1.regs.get? Register.PC = some secondPC := by
    have := obs_alu_pc hoτ1; rwa [hfirstAfter] at this
  have hx11τ1 : τ1.regs.get? Register.x11 = some (bwOf (cond (Value.equal vl vr) (1#64) (0#64))) :=
    obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx9τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9R
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspR
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = cR.σ.sailOutput := by rw [hoτ1.out, sailOutput_sigmaPost_alu]
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcodeR
  -- === middle 2: mv a0,s1 → x10 := sret ===
  obtain ⟨τ2, j2, ht2, hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    secondSite τ1 j1 (cR.steps + 1) secondPC vmiτ1 sret hGτ1 hpcτ1 hmiτ1 hx9τ1 hcodeτ1 rfl hj1
  have hstepτ2 : Step ⟨τ1, j1, cR.steps + 1⟩ ⟨τ2, j2, cR.steps + 1 + 1⟩ := ht2
  have hmemτ2e : τ2.mem = cR.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some jalPC := by
    have := obs_alu_pc hoτ2; rwa [hsecondAfter] at this
  have hx10τ2 : τ2.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hoτ2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12)) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hx11τ2 : τ2.regs.get? Register.x11 = some (bwOf (cond (Value.equal vl vr) (1#64) (0#64))) :=
    obs_alu_other hoτ2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ1
  have hx9τ2 : τ2.regs.get? Register.x9 = some sret := obs_alu_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_alu_minstret hoτ2
  have houtτ2 : τ2.sailOutput = cR.σ.sailOutput := by rw [hoτ2.out, sailOutput_sigmaPost_alu]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcodeR
  -- === middle 3: jal value_bool → x1 := jalPC+4 = ldPC, PC := 0x800027f8 ===
  obtain ⟨τ3, j3, ht3, hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    jalVboolSite τ2 j2 (cR.steps + 1 + 1) jalPC vmiτ2 hGτ2 hpcτ2 hmiτ2 hcodeτ2 rfl hj2
  have hstepτ3 : Step ⟨τ2, j2, cR.steps + 1 + 1⟩ ⟨τ3, j3, cR.steps + 1 + 1 + 1⟩ := ht3
  have hmemτ3e : τ3.mem = cR.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hoτ3; rwa [hjalTgt] at this
  have hlinkτ3 : τ3.regs.get? Register.x1 = some ldPC := by
    have := obs_jal_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hboxLink] at this
  have hx10τ3 : τ3.regs.get? Register.x10 = some sret := obs_jal_other hoτ3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ2
  have hx11τ3 : τ3.regs.get? Register.x11 = some (bwOf (cond (Value.equal vl vr) (1#64) (0#64))) :=
    obs_jal_other hoτ3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ2
  have hx9τ3 : τ3.regs.get? Register.x9 = some sret := obs_jal_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_jal_minstret hoτ3
  have houtτ3 : τ3.sailOutput = cR.σ.sailOutput := by rw [hoτ3.out, sailOutput_sigmaPost_jal]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcodeR
  have hVboolτ3 : Value_boolLoaded τ3.mem := by
    rw [hmemτ3e]
    refine loaded_bool_agreeP mEnt cR.σ.mem (fun a ha => ?_) hVboolEnt
    -- value_bool region [0x800027f8,0x8000280c) is BELOW tohostAddr ≤ framebase-16 (window)
    refine (hmemframeR a ?_).symm
    rw [hfb]; rw [htoh] at hspHtif; rintro ⟨h1, h2⟩; omega
  -- === bridge τ3 → boolBoxEpilogue's τ0 (= τ3) ===
  -- `cR.σ.mem` agrees with `mEnt` off `[framebase-16, framebase) = [sp-1104, sp-1088)`,
  -- which is disjoint from the restore slots `[sp-40, sp)` and, given `sret` geometry,
  -- from the sret window and outside SL only where mEnt already agrees with m0.
  -- Every mEnt-fact the box needs transports through this window agreement.
  have hcmR : ∀ a : Nat, ¬ (sp.toNat - 1104 ≤ a ∧ a < sp.toNat - 1088) →
      cR.σ.mem[a]? = mEnt[a]? := by
    intro a ha
    refine hmemframeR a ?_
    rw [hfb]; intro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
  -- slot reads (all above sp-40 ≥ sp-1088, so ∉ window)
  have hAgSlots : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mEnt cR.σ.mem := by
    intro k hk; exact (hcmR k (by omega)).symm
  have hAgS3 : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32) mEnt cR.σ.mem := by
    intro k hk; exact (hcmR k (by omega)).symm
  have hs3τ0 : read64 cR.σ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [← read64_agreeP hAgS3 (fun j hj => ⟨by omega, by omega⟩)]; exact hs3Ent
  have hslotRaτ0 : read64 cR.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa0
  have hslotS0τ0 : read64 cR.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS00
  have hslotS1τ0 : read64 cR.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS10
  have hslotS2τ0 : read64 cR.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS20
  -- store survival outside SL, phrased over cR.σ.mem
  have hSurvSLτ0 : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cR.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store := by
    refine fun m' hm' => hSurvSL0 m' (fun k hk => ?_)
    -- [sp-1104,sp-1088) ⊆ [SL.lo,SL.hi): so k ∉ SL ⇒ k ∉ window ⇒ mEnt[k]=cR[k]
    have hknw : ¬ (sp.toNat - 1104 ≤ k ∧ k < sp.toNat - 1088) := by
      rintro ⟨h1, h2⟩; exact hk ⟨by omega, by omega⟩
    exact (hcmR k hknw).symm.trans (hm' k hk)
  -- MemExtends m0 → cR.σ.mem
  have hMemExtτ0 : MemExtends m0 cR.σ.mem := hMemExt0.trans hMemExtR
  -- memory frame vs m0
  have hmemframeτ0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ cR.σ.mem[a]? = m0[a]? := by
    intro a ha hA
    have haw : ¬ (sp.toNat - 1104 ≤ a ∧ a < sp.toNat - 1088) := by
      intro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    rcases hmemframe0 a ha hA with h | h
    · exact Or.inl h
    · exact Or.inr ((hcmR a haw).trans h)
  -- frame collapse: τ3-config → g for R ∉ {x8,x9,x18,x2,x19}.  Collapse τ3 → cR via the three
  -- middle steps (each writes ∈ {x11,x10,x1}), then cR → g via VeReturn.hframe.
  have hframeGτ0 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (Register.x19 == R) = false → τ3.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2 h19ne
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have f_3 : τ3.regs.get? R = τ2.regs.get? R :=
      (hoτ3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (ne (X := Register.x1) (by decide)) hnpc' hmii')
    have f_2 : τ2.regs.get? R = τ1.regs.get? R :=
      (hoτ2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (X := Register.x10) (by decide)) hnpc' hmii')
    have f_1 : τ1.regs.get? R = cR.σ.regs.get? R :=
      (hoτ1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (X := Register.x11) (by decide)) hnpc' hmii')
    rw [f_3, f_2, f_1]
    refine hframeR R ⟨ne (X := Register.x1) (by decide), he2,
      ne (X := Register.x5) (by decide), ne (X := Register.x6) (by decide),
      ne (X := Register.x7) (by decide), ne (X := Register.x10) (by decide),
      ne (X := Register.x11) (by decide), ne (X := Register.x12) (by decide),
      ne (X := Register.x13) (by decide), ne (X := Register.x14) (by decide),
      ne (X := Register.x15) (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he9 h19ne
  -- === invoke the SHARED bool-box epilogue ===
  let cvb : Config := ⟨τ3, j3, cR.steps + 1 + 1 + 1⟩
  have hmemcvb : cvb.σ.mem = cR.σ.mem := hmemτ3e
  obtain ⟨mpre, φfm2, φcm2, φfe, φce, cfin, hStepsFin, hp1, hp2, hp3, hp4, hPre⟩ :=
    boolBoxEpilogue g N A SL φf φc φfm φcm φf' φc'
      st'.store.frames.size st'.store.closures.size
      st''.store.frames.size st''.store.closures.size st' st''
      sp r sret v8 v9 v18 v19 w19 (bwOf (cond (Value.equal vl vr) (1#64) (0#64))) bres out0 m0
      cvb ldPC ldPC jPC jImm
      (fun σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7 => ldS3 σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7)
      (fun σ i u pc vminstret => jExit σ i u pc vminstret)
      rfl hldPCupdate hldAfter hjTgt hjTgtAl hldPCeq
      hGτ3 hVboolτ3 hpcτ3 hx10τ3 hx11τ3 hlinkτ3 hx9τ3 hspτ3 ⟨vmiτ3, hmiτ3⟩ hj3
      (by rw [houtτ3]; exact houtR) hcodeτ3 hBoolRegion hlinkAl hval_bridge
      hpfm hpcm hpf' hpc' houtStr
      (by rw [hmemcvb]; exact hSurvSLτ0) (by rw [hmemcvb]; exact hs3τ0)
      (by rw [hmemcvb]; exact hslotRaτ0) (by rw [hmemcvb]; exact hslotS0τ0)
      (by rw [hmemcvb]; exact hslotS1τ0) (by rw [hmemcvb]; exact hslotS2τ0)
      hgv8 hgv9 hgv18 hgv2 hgx19 hw19 hframeGτ0
      (by rw [hmemcvb]; exact hMemExtτ0) (by rw [hmemcvb]; exact hmemframeτ0)
      hsretEvalCode hsretStk hsretInSL hSLlo40 hSLlo32
      hsp1088 hspRam hspLo hspHtif hsp8 hraAl
      hldLo hldHiRam hldHtif hldAl
  refine ⟨mpre, φfm2, φcm2, φfe, φce, cfin, ?_, hp1, hp2, hp3, hp4, hPre⟩
  have hchain : Steps cR cvb :=
    ((Steps.single hstepτ1).trans (Steps.single hstepτ2)).trans (Steps.single hstepτ3)
  exact hchain.trans hStepsFin

#print axioms blockC_eqne

/-! ## `EqNeBoxPre` — the shared post-`value_equal` residual bundle

The transport facts `blockC_eqne`/`boolBoxEpilogue` need at the `value_equal` return
config, EXCEPT the op-specific box constants / middle sites.  Shared by `blockC_eq`
and `blockC_ne`; the arm supplies the value_equal-return `VeReturn` + this bundle. -/
structure EqNeBoxPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc' : Addr → Nat)
    (st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (out0 : Array String) (m0 mEnt : Mem) : Prop where
  hVboolEnt : Value_boolLoaded mEnt
  hcodeEnt : Eval_exprLoaded mEnt
  hBoolRegion : BoolRegion sret
  houtStr : String.join out0.toList = st''.out
  hSurvSL0 : ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mEnt[k]? = m'[k]?) →
    StoreRepr m' N A φf' φc' st''.store
  hs3Ent : read64 mEnt (sp.toNat - 40) = some w19.toNat
  hslotRa0 : read64 mEnt (sp.toNat - 8) = some r.toNat
  hslotS00 : read64 mEnt (sp.toNat - 16) = some v8.toNat
  hslotS10 : read64 mEnt (sp.toNat - 24) = some v9.toNat
  hslotS20 : read64 mEnt (sp.toNat - 32) = some v18.toNat
  hgv8 : g Register.x8 = some v8
  hgv9 : g Register.x9 = some v9
  hgv18 : g Register.x18 = some v18
  hgv2 : g Register.x2 = some sp
  hgx19 : g Register.x19 = some v19
  hw19 : w19 = v19
  hMemExt0 : MemExtends m0 mEnt
  hmemframe0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mEnt[a]? = m0[a]?
  hsretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  hsretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  hsretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  hSLlo40 : SL.lo ≤ sp.toNat - 40
  hSLlo32 : SL.lo ≤ sp.toNat - 32
  hSLloSp : SL.lo + 1104 ≤ sp.toNat
  hspSLhi : sp.toNat ≤ SL.hi
  hsp1088 : 1088 ≤ sp.toNat
  hspRam : sp.toNat ≤ 0x100000000
  hspLo : 0x80000000 ≤ sp.toNat
  hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat
  hsp8 : sp.toNat % 8 = 0
  hraAl : r.toNat % 4 = 0

/-- ld-slot geometry the box needs (`[sp-40,sp-32)` in RAM, aligned, above HTIF). -/
theorem eqne_ld_geom (sp : BitVec 64) (hsp1088 : 1088 ≤ sp.toNat)
    (hspRam : sp.toNat ≤ 0x100000000) (hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat)
    (hsp8 : sp.toNat % 8 = 0) :
    0x80000000 ≤ (sp.toNat - 40) ∧ (sp.toNat - 40) + 8 ≤ 0x100000000 ∧
    ((sp.toNat - 40) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (sp.toNat - 40)) ∧
    (sp.toNat - 40) % 8 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by rw [htoh] at hspHtif; omega, by omega, Or.inr (by rw [htoh] at hspHtif ⊢; omega), by omega⟩

/-- The `ld s3,0x418(x2)` slot address at the frame base `sp-1088` = `sp-40`. -/
theorem eqne_ldPCeq (sp : BitVec 64) (hsp1088 : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
  spill_addr sp (0x418#12) 40 (by decide) (by decide) hsp1088

/-! ## `blockC_eq` / `blockC_ne` — thin instantiations of `blockC_eqne` -/

/-- **`blockC_eq`.**  From the `value_equal` return config (`x10 = cond (vl.equal vr)
1 0`) run the eq middle (`mv a1,a0 ; mv a0,s1 ; jal value_bool`) and box to
`.bool (vl.equal vr)`, producing `PreEpilogueVD`.  A thin instantiation of
`blockC_eqne` with the eq site lemmas + box constants. -/
theorem blockC_eq
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfm φcm φf' φc' : Addr → Nat) (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (out0 : Array String) (m0 mEnt : Mem) (cR : Config)
    (hpfm : PhiExtends φf φfm st'.store.frames.size)
    (hpcm : PhiExtends φc φcm st'.store.closures.size)
    (hpf' : PhiExtends φfm φf' st''.store.frames.size)
    (hpc' : PhiExtends φcm φc' st''.store.closures.size)
    (hcR : VeReturn g (sp - 1088#64) sret vl vr (0x80003720#64) out0 mEnt cR)
    (hBox : EqNeBoxPre g N A SL φf' φc' st'' sp r sret v8 v9 v18 v19 w19 out0 m0 mEnt) :
    ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat) (cfin : Config),
      Steps cR cfin ∧
      PhiExtends φf φfm' st'.store.frames.size ∧
      PhiExtends φc φcm' st'.store.closures.size ∧
      PhiExtends φfm' φfe st''.store.frames.size ∧
      PhiExtends φcm' φce st''.store.closures.size ∧
      PreEpilogueVD g N A SL φfe φce st'' (.bool (vl.equal vr)) sp r sret v8 v9 v18 out0 m0 mpre cfin := by
  obtain ⟨hgeo1, hgeo2, hgeo3, hgeo4⟩ := eqne_ld_geom sp hBox.hsp1088 hBox.hspRam hBox.hspHtif hBox.hsp8
  exact blockC_eqne g N A SL φf φc φfm φcm φf' φc' st' st''
    sp r sret v8 v9 v18 v19 w19 vl vr (vl.equal vr) out0 m0 mEnt cR (0x80003720#64)
    (0x80003720#64) (0x80003724#64) (0x80003728#64) (fun v => v + sign_extend (m := 64) (0x000#12))
    (0x1ff0d0#21)
    (fun σ i u pc vm v10 => site_80003720_ee σ i u pc vm v10)
    (fun σ i u pc vm v9 => site_80003724_ee σ i u pc vm v9)
    (fun σ i u pc vm => site_80003728_ee σ i u pc vm)
    (0x8000372c#64) (0x80003730#64) (0x1ffcbc#21)
    (fun σ i u pc vm v2 b0 b1 b2 b3 b4 b5 b6 b7 => site_8000372c_ee σ i u pc vm v2 b0 b1 b2 b3 b4 b5 b6 b7)
    (fun σ i u pc vm => site_80003730_ee σ i u pc vm)
    (by decide) (by decide) (by apply BitVec.eq_of_toNat_eq; decide) (by decide) (by decide)
    (by decide) (by decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (by decide) (eqne_ldPCeq sp hBox.hsp1088) (by decide)
    (by cases h : vl.equal vr <;>
        simp only [h, cond_true, cond_false] <;> decide)
    hcR hBox.hVboolEnt hBox.hcodeEnt hBox.hBoolRegion
    hpfm hpcm hpf' hpc' hBox.houtStr hBox.hSurvSL0 hBox.hs3Ent
    hBox.hslotRa0 hBox.hslotS00 hBox.hslotS10 hBox.hslotS20
    hBox.hgv8 hBox.hgv9 hBox.hgv18 hBox.hgv2 hBox.hgx19 hBox.hw19
    hBox.hMemExt0 hBox.hmemframe0 hBox.hsretEvalCode hBox.hsretStk hBox.hsretInSL
    hBox.hSLlo40 hBox.hSLlo32 hBox.hSLloSp hBox.hspSLhi hBox.hsp1088 hBox.hspRam
    hBox.hspLo hBox.hspHtif hBox.hsp8 hBox.hraAl hgeo1 hgeo2 hgeo3 hgeo4

/-- **`blockC_ne`.**  As `blockC_eq` but the ne middle (`seqz a1,a0` instead of `mv`)
and box to `.bool (!(vl.equal vr))`. -/
theorem blockC_ne
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfm φcm φf' φc' : Addr → Nat) (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64)
    (vl vr : Value) (out0 : Array String) (m0 mEnt : Mem) (cR : Config)
    (hpfm : PhiExtends φf φfm st'.store.frames.size)
    (hpcm : PhiExtends φc φcm st'.store.closures.size)
    (hpf' : PhiExtends φfm φf' st''.store.frames.size)
    (hpc' : PhiExtends φcm φc' st''.store.closures.size)
    (hcR : VeReturn g (sp - 1088#64) sret vl vr (0x80003770#64) out0 mEnt cR)
    (hBox : EqNeBoxPre g N A SL φf' φc' st'' sp r sret v8 v9 v18 v19 w19 out0 m0 mEnt) :
    ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat) (cfin : Config),
      Steps cR cfin ∧
      PhiExtends φf φfm' st'.store.frames.size ∧
      PhiExtends φc φcm' st'.store.closures.size ∧
      PhiExtends φfm' φfe st''.store.frames.size ∧
      PhiExtends φcm' φce st''.store.closures.size ∧
      PreEpilogueVD g N A SL φfe φce st'' (.bool (!(vl.equal vr))) sp r sret v8 v9 v18 out0 m0 mpre cfin := by
  obtain ⟨hgeo1, hgeo2, hgeo3, hgeo4⟩ := eqne_ld_geom sp hBox.hsp1088 hBox.hspRam hBox.hspHtif hBox.hsp8
  exact blockC_eqne g N A SL φf φc φfm φcm φf' φc' st' st''
    sp r sret v8 v9 v18 v19 w19 vl vr (!(vl.equal vr)) out0 m0 mEnt cR (0x80003770#64)
    (0x80003770#64) (0x80003774#64) (0x80003778#64)
    (fun v => zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))))
    (0x1ff080#21)
    (fun σ i u pc vm v10 => site_80003770_ee σ i u pc vm v10)
    (fun σ i u pc vm v9 => site_80003774_ee σ i u pc vm v9)
    (fun σ i u pc vm => site_80003778_ee σ i u pc vm)
    (0x8000377c#64) (0x80003780#64) (0x1ffc6c#21)
    (fun σ i u pc vm v2 b0 b1 b2 b3 b4 b5 b6 b7 => site_8000377c_ee σ i u pc vm v2 b0 b1 b2 b3 b4 b5 b6 b7)
    (fun σ i u pc vm => site_80003780_ee σ i u pc vm)
    (by decide) (by decide) (by apply BitVec.eq_of_toNat_eq; decide) (by decide) (by decide)
    (by decide) (by decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (by decide) (eqne_ldPCeq sp hBox.hsp1088) (by decide)
    (by cases h : vl.equal vr <;>
        simp only [h, cond_true, cond_false] <;> decide)
    hcR hBox.hVboolEnt hBox.hcodeEnt hBox.hBoolRegion
    hpfm hpcm hpf' hpc' hBox.houtStr hBox.hSurvSL0 hBox.hs3Ent
    hBox.hslotRa0 hBox.hslotS00 hBox.hslotS10 hBox.hslotS20
    hBox.hgv8 hBox.hgv9 hBox.hgv18 hBox.hgv2 hBox.hgx19 hBox.hw19
    hBox.hMemExt0 hBox.hmemframe0 hBox.hsretEvalCode hBox.hsretStk hBox.hsretInSL
    hBox.hSLlo40 hBox.hSLlo32 hBox.hSLloSp hBox.hspSLhi hBox.hsp1088 hBox.hspRam
    hBox.hspLo hBox.hspHtif hBox.hsp8 hBox.hraAl hgeo1 hgeo2 hgeo3 hgeo4

#print axioms blockC_eq
#print axioms blockC_ne

/-! ## `evalEqNeSim` — the shared `EvalE.binary .eq/.ne` recursive-case core

Composes `blockB_binary ≫ blockC ≫ blockD_v_rec` in the `EvalIH` motive shape, where
`blockC` is the op-specific dispatch + `value_equal` + box bridge (`blockC_eq` /
`blockC_ne`).  Because the eq/ne dispatch copies the operands into `value_equal`'s
buffers through a REFLECTED `#derive_case` block and `value_equal`'s contract does not
thread `sailOutput`, the `blockC` bridge is supplied as a caller residual
`hblockC` (the operand-copy read-back from the reflected dispatch + the `value_equal`
output invariance) — exactly as `evalDivSim` remains conditional on its caller
linkage.  Everything ELSE (the two IH sub-derivations, the `blockB`/`blockD` frame,
the store/φ threading) is shared and closed here. -/
theorem evalEqNeSim
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr)
    (op : BinOp) (vl vr : Value) (resVal : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl)
    (hIHr : EvalIH st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary op el er) st'' resVal)
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    -- the op-specific `blockC` bridge (dispatch + value_equal + box), threaded as
    -- the caller residual (operand-copy read-back + value_equal output invariance).
    (hblockC : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      String.join c2.σ.sailOutput.toList = st''.out →
      ∃ (c3 : Vsa.Machine.Config) (mpre : Mem) (φfe φce : Addr → Nat),
        Steps c2 c3 ∧
        PhiExtends φf φfe st''.store.frames.size ∧
        PhiExtends φc φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' resVal sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0⟩ := hpre
  -- === block B: two-operand head + IHs → TwoSubReturn @0x8000351c ===
  obtain ⟨c2, hs2, hTS⟩ :=
    blockB_binary gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0⟩
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  -- === block C: dispatch + value_equal + box → PreEpilogueVD @0x800033ec ===
  obtain ⟨c3, mpre, φfe, φce, hs3, hpfe, hpce, hPre⟩ := hblockC c2 hTS hOutC2
  -- === block D: shared epilogue → EvalExitD ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' resVal sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPre⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  -- store counts only grow (`st.store ≤ st''.store` across both sub-calls).
  have hmono := evalE_store_mono _hEvalE
  have hpfF : PhiExtends φf φfe st.store.frames.size := PhiExtends.mono hmono.1 hpfe
  have hpcF : PhiExtends φc φce st.store.closures.size := PhiExtends.mono hmono.2 hpce
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' resVal sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- **`evalEqSim`** — the `EvalE.binary .eq` recursive case, result `.bool (vl.equal vr)`. -/
theorem evalEqSim
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl) (hIHr : EvalIH st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary .eq el er) st'' (.bool (vl.equal vr)))
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    (hblockC : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      String.join c2.σ.sailOutput.toList = st''.out →
      ∃ (c3 : Vsa.Machine.Config) (mpre : Mem) (φfe φce : Addr → Nat),
        Steps c2 c3 ∧
        PhiExtends φf φfe st''.store.frames.size ∧
        PhiExtends φc φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (vl.equal vr)) sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .eq el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (vl.equal vr)) sp r sret m0) :=
  evalEqNeSim gouter gpre g N A SL φf φc st st' st'' d env el er .eq vl vr (.bool (vl.equal vr))
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hIHl hIHr _hEvalE hSizeF hSizeC hVlSurv hblockC

/-- **`evalNeSim`** — the `EvalE.binary .ne` recursive case, result `.bool (!(vl.equal vr))`. -/
theorem evalNeSim
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl) (hIHr : EvalIH st' d env er st'' vr)
    (_hEvalE : EvalE st d env (.binary .ne el er) st'' (.bool (!(vl.equal vr))))
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size)
    (hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) vl)
    (hblockC : ∀ c2 : Vsa.Machine.Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' vl vr sp r sret v8 v9 v18 m0 c2 →
      String.join c2.σ.sailOutput.toList = st''.out →
      ∃ (c3 : Vsa.Machine.Config) (mpre : Mem) (φfe φce : Addr → Nat),
        Steps c2 c3 ∧
        PhiExtends φf φfe st''.store.frames.size ∧
        PhiExtends φc φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (!(vl.equal vr))) sp r sret v8 v9 v18 c2.σ.sailOutput m0 mpre c3) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .ne el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (!(vl.equal vr))) sp r sret m0) :=
  evalEqNeSim gouter gpre g N A SL φf φc st st' st'' d env el er .ne vl vr (.bool (!(vl.equal vr)))
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0
    hIHl hIHr _hEvalE hSizeF hSizeC hVlSurv hblockC

#print axioms evalEqSim
#print axioms evalNeSim

end Vsa.Sim
