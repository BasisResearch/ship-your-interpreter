import Vsa.Sim.AllocRuns
import Vsa.Sim.HelperCallEnvDefine
import Vsa.Sim.rows.EnvDefinePrologueSaved
import Vsa.Sim.rows.EnvDefineDispatchExact
import Vsa.Sim.rows.EnvDefineUpdateExact
import Vsa.Sim.rows.EnvDefineTailFramed
import Vsa.Sim.Code.FixedImage_Env_define
import Vsa.Sim.Code.FixedImage_Strcmp
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.EnvCallBridge
import Vsa.Sim.MemPresence
import Vsa.Sim.ReprSurvival
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.ValueEqualSpec3

/-!
# `EnvDefineContractUpdate` — the `env_define` lanes composed at the contract seam

Composes the landed `env_define` lanes into the whole-function shape consumed by
the statement arms (`Vsa.Sim.HelperCallEnvDefine`): from `EnvDefineEntryState`
(the parametric call parked at `0x80002a5c`) through the prologue, the finite
name scan, and — when the name is already bound — the exact one-slot update and
the restore-and-`ret` epilogue, to the return at the link PC with the
`Store.define` result represented.  The exhaustive miss is exported as a named
state (`EnvDefineMissReady`) at the append/grow cap dispatch.

* `envDefinePrologueSeg`: the thirteen-instruction prologue as ONE reflected
  `#derive_case` seg.  The landed site-by-site prologue
  (`EnvDefSpec17.env_define_prologue`, `env_define_prologue_saved`) exports no
  register frame at `0x80002a90`, but the scan lane's entry carrier
  (`EnvDefineScanEntryFrame`) demands the global pointer and the complete ABI
  ghost there; the reflected seg supplies both through
  `frame_of_wrChain_avoids` (one `decide`).  Its write image is exactly
  `envDefineSpillMem`, so the landed spill carrier `envDefineSavedSpills_of_mem`
  is reused unchanged.
* `EnvDefineUpdateOracles`: the named entry-side facts the lanes consume;
  `EnvDefineUpdateOracles.of_entry` derives them from `EnvDefineMem` (the fixed
  text image, the slot geometry, the staged words, the arena/image separation)
  and `EnvDefineUpdateLedger`, the genuinely external facts (allocator
  invariant, ownership, uniqueness, scan string regions, alignment).
* `envDefineUpdateLane`: entry ⟶ `EnvDefineReturnCore` (hit case).
* `envDefineMissLane`: entry ⟶ `EnvDefineMissReady` (exhaustive miss on a
  non-empty frame).
* `EnvDefineReturnResiduals` + `EnvDefineReturnCore.toReturn`: the three return
  facts (`sailOutput`; the `x3`/`x4`/`x23`–`x27` frame; `a0` presence), named
  once; `envDefineUpdateLaneKeep` discharges them from the output-carrying scan
  frame (`EnvDefineScanFrame.out`) and the keep-set-framed update/epilogue rows
  (`rows/EnvDefineTailFramed.lean`), so `envDefineUpdateLane_full` closes
  `EnvDefineReturnState` with no residual hypothesis.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK MallocContract)
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded FixedTextLoaded)
open Vsa.While (Addr Value)

namespace Vsa.Sim

/-! ## 1. The prologue as one reflected seg -/

/- `0x80002a5c → 0x80002a90`: `addi sp,sp,-64`, the seven callee-saved spills plus
`ra`, the `lw s3,0(a0)` count load, and the three argument moves.  No terminator:
the `blez` at `0x80002a90` is the first block of `envDefineScanInitSeg`. -/
#derive_case envDefinePrologueSeg chain
  [(0x80002a5c#64, 0xfc010113#32),
   (0x80002a60#64, 0x01313c23#32),
   (0x80002a64#64, 0x00052983#32),
   (0x80002a68#64, 0x03213023#32),
   (0x80002a6c#64, 0x01413823#32),
   (0x80002a70#64, 0x01513423#32),
   (0x80002a74#64, 0x02113c23#32),
   (0x80002a78#64, 0x02813823#32),
   (0x80002a7c#64, 0x02913423#32),
   (0x80002a80#64, 0x01613023#32),
   (0x80002a84#64, 0x00050a13#32),
   (0x80002a88#64, 0x00058913#32),
   (0x80002a8c#64, 0x00060a93#32)]

@[simp] private theorem proLine0 : mkLine 0x80002a5c#64 0xfc010113#32 =
    ⟨0x80002a5c#64, 0xfc010113#32, 0x13#8, 0x01#8, 0x01#8, 0xfc#8, .addi, 2, 2, 0, 0xfc0#12⟩ := by rfl
@[simp] private theorem proLine1 : mkLine 0x80002a60#64 0x01313c23#32 =
    ⟨0x80002a60#64, 0x01313c23#32, 0x23#8, 0x3c#8, 0x31#8, 0x01#8, .sd, 0, 2, 19, 0x018#12⟩ := by rfl
@[simp] private theorem proLine2 : mkLine 0x80002a64#64 0x00052983#32 =
    ⟨0x80002a64#64, 0x00052983#32, 0x83#8, 0x29#8, 0x05#8, 0x00#8, .lw, 19, 10, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine3 : mkLine 0x80002a68#64 0x03213023#32 =
    ⟨0x80002a68#64, 0x03213023#32, 0x23#8, 0x30#8, 0x21#8, 0x03#8, .sd, 0, 2, 18, 0x020#12⟩ := by rfl
@[simp] private theorem proLine4 : mkLine 0x80002a6c#64 0x01413823#32 =
    ⟨0x80002a6c#64, 0x01413823#32, 0x23#8, 0x38#8, 0x41#8, 0x01#8, .sd, 0, 2, 20, 0x010#12⟩ := by rfl
@[simp] private theorem proLine5 : mkLine 0x80002a70#64 0x01513423#32 =
    ⟨0x80002a70#64, 0x01513423#32, 0x23#8, 0x34#8, 0x51#8, 0x01#8, .sd, 0, 2, 21, 0x008#12⟩ := by rfl
@[simp] private theorem proLine6 : mkLine 0x80002a74#64 0x02113c23#32 =
    ⟨0x80002a74#64, 0x02113c23#32, 0x23#8, 0x3c#8, 0x11#8, 0x02#8, .sd, 0, 2, 1, 0x038#12⟩ := by rfl
@[simp] private theorem proLine7 : mkLine 0x80002a78#64 0x02813823#32 =
    ⟨0x80002a78#64, 0x02813823#32, 0x23#8, 0x38#8, 0x81#8, 0x02#8, .sd, 0, 2, 8, 0x030#12⟩ := by rfl
@[simp] private theorem proLine8 : mkLine 0x80002a7c#64 0x02913423#32 =
    ⟨0x80002a7c#64, 0x02913423#32, 0x23#8, 0x34#8, 0x91#8, 0x02#8, .sd, 0, 2, 9, 0x028#12⟩ := by rfl
@[simp] private theorem proLine9 : mkLine 0x80002a80#64 0x01613023#32 =
    ⟨0x80002a80#64, 0x01613023#32, 0x23#8, 0x30#8, 0x61#8, 0x01#8, .sd, 0, 2, 22, 0x000#12⟩ := by rfl
@[simp] private theorem proLine10 : mkLine 0x80002a84#64 0x00050a13#32 =
    ⟨0x80002a84#64, 0x00050a13#32, 0x13#8, 0x0a#8, 0x05#8, 0x00#8, .addi, 20, 10, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine11 : mkLine 0x80002a88#64 0x00058913#32 =
    ⟨0x80002a88#64, 0x00058913#32, 0x13#8, 0x89#8, 0x05#8, 0x00#8, .addi, 18, 11, 0, 0x000#12⟩ := by rfl
@[simp] private theorem proLine12 : mkLine 0x80002a8c#64 0x00060a93#32 =
    ⟨0x80002a8c#64, 0x00060a93#32, 0x93#8, 0x0a#8, 0x06#8, 0x00#8, .addi, 21, 12, 0, 0x000#12⟩ := by rfl

/- The epilogue body lines (`envDefineEpilogueBody`), decoded once for the
terminator-fact lemma below. -/
@[simp] private theorem epiLine0 : mkLine 0x80002aec#64 0x03813083#32 =
    ⟨0x80002aec#64, 0x03813083#32, 0x83#8, 0x30#8, 0x81#8, 0x03#8, .ld, 1, 2, 0, 0x038#12⟩ := by rfl
@[simp] private theorem epiLine1 : mkLine 0x80002af0#64 0x03013403#32 =
    ⟨0x80002af0#64, 0x03013403#32, 0x03#8, 0x34#8, 0x01#8, 0x03#8, .ld, 8, 2, 0, 0x030#12⟩ := by rfl
@[simp] private theorem epiLine2 : mkLine 0x80002af4#64 0x02813483#32 =
    ⟨0x80002af4#64, 0x02813483#32, 0x83#8, 0x34#8, 0x81#8, 0x02#8, .ld, 9, 2, 0, 0x028#12⟩ := by rfl
@[simp] private theorem epiLine3 : mkLine 0x80002af8#64 0x02013903#32 =
    ⟨0x80002af8#64, 0x02013903#32, 0x03#8, 0x39#8, 0x01#8, 0x02#8, .ld, 18, 2, 0, 0x020#12⟩ := by rfl
@[simp] private theorem epiLine4 : mkLine 0x80002afc#64 0x01813983#32 =
    ⟨0x80002afc#64, 0x01813983#32, 0x83#8, 0x39#8, 0x81#8, 0x01#8, .ld, 19, 2, 0, 0x018#12⟩ := by rfl
@[simp] private theorem epiLine5 : mkLine 0x80002b00#64 0x01013a03#32 =
    ⟨0x80002b00#64, 0x01013a03#32, 0x03#8, 0x3a#8, 0x01#8, 0x01#8, .ld, 20, 2, 0, 0x010#12⟩ := by rfl
@[simp] private theorem epiLine6 : mkLine 0x80002b04#64 0x00813a83#32 =
    ⟨0x80002b04#64, 0x00813a83#32, 0x83#8, 0x3a#8, 0x81#8, 0x00#8, .ld, 21, 2, 0, 0x008#12⟩ := by rfl
@[simp] private theorem epiLine7 : mkLine 0x80002b08#64 0x00013b03#32 =
    ⟨0x80002b08#64, 0x00013b03#32, 0x03#8, 0x3b#8, 0x01#8, 0x00#8, .ld, 22, 2, 0, 0x000#12⟩ := by rfl
@[simp] private theorem epiLine8 : mkLine 0x80002b0c#64 0x04010113#32 =
    ⟨0x80002b0c#64, 0x04010113#32, 0x13#8, 0x01#8, 0x01#8, 0x04#8, .addi, 2, 2, 0, 0x040#12⟩ := by rfl

@[simp] private theorem sext0_64 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
@[simp] private theorem sext8_64 : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
@[simp] private theorem sext16_64 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
@[simp] private theorem sext24_64 : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
@[simp] private theorem sext32_64 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
@[simp] private theorem sext40_64 : (sign_extend (m := 64) (0x028#12) : BitVec 64).toNat = 40 := by decide
@[simp] private theorem sext48_64 : (sign_extend (m := 64) (0x030#12) : BitVec 64).toNat = 48 := by decide
@[simp] private theorem sext56_64 : (sign_extend (m := 64) (0x038#12) : BitVec 64).toNat = 56 := by decide

/-- The prologue's entry pin list: the registers its body reads (in `#derive_case`
key order). -/
def envDefinePrologueL (sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2 : BitVec 64) : GRegs :=
  [(2, sp), (19, s3), (10, a0), (18, s2), (20, s4), (21, s5), (1, ra), (8, s0), (9, s1),
   (22, s6), (11, a1), (12, a2)]

/-- ABI registers the prologue never writes (`sp` is rebased; `s2`–`s5` are
repurposed after their spill). -/
def PrologueKeep (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x2) && !(R == Register.x18) && !(R == Register.x19) &&
    !(R == Register.x20) && !(R == Register.x21)

theorem PrologueKeep.abi {R : Register} (h : PrologueKeep R = true) : AbiPreserved R = true := by
  simp only [PrologueKeep, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-- The prologue's write log, in program order. -/
theorem envDefinePrologueLog (sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2 : BitVec 64)
    (bs : List (BitVec 8)) (h64 : 64 ≤ sp.toNat) :
    (evalBlocks envDefinePrologueSeg
      (SegEvalState.init (envDefinePrologueL sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2) [bs])).log =
    [(sp.toNat - 64 + 24, 8, s3), (sp.toNat - 64 + 32, 8, s2), (sp.toNat - 64 + 16, 8, s4),
     (sp.toNat - 64 + 8, 8, s5), (sp.toNat - 64 + 56, 8, ra), (sp.toNat - 64 + 48, 8, s0),
     (sp.toNat - 64 + 40, 8, s1), (sp.toNat - 64, 8, s6)] := by
  have hlt := sp.isLt
  simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, stepLdsM, ldsRunM, wvalM,
    srcVal, lookupG, eraseG, eaddrM, envDefinePrologueL, sp_sub64]
  omega

/-- The prologue's write image is exactly the landed spill image. -/
theorem envDefinePrologueMem (m : Mem) (sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2 : BitVec 64)
    (bs : List (BitVec 8)) (h64 : 64 ≤ sp.toNat) :
    writeLog m (evalBlocks envDefinePrologueSeg
      (SegEvalState.init (envDefinePrologueL sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2) [bs])).log =
    envDefineSpillMem m (sp - 64#64).toNat ra s0 s1 s2 s3 s4 s5 s6 := by
  rw [envDefinePrologueLog sp s3 a0 s2 s4 s5 ra s0 s1 s6 a1 a2 bs h64, sp_sub64_toNat sp h64]
  rfl

/-- The epilogue's `ret` target is 4-aligned whenever the spilled return address is. -/
theorem envDefineEpilogueTermFacts (sp r s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (halign : r.toNat % 4 = 0) :
    TermFactsO (runGM envDefineEpilogueBody (envDefineEpilogueL sp)
      [envDefineWordBytes r, envDefineWordBytes s0, envDefineWordBytes s1,
       envDefineWordBytes s2, envDefineWordBytes s3, envDefineWordBytes s4,
       envDefineWordBytes s5, envDefineWordBytes s6]) envDefineEpilogueTerm := by
  unfold TermFactsO envDefineEpilogueTerm
  simp only [TermFactsT]
  have h1 : srcVal 1 (runGM envDefineEpilogueBody (envDefineEpilogueL sp)
      [envDefineWordBytes r, envDefineWordBytes s0, envDefineWordBytes s1,
       envDefineWordBytes s2, envDefineWordBytes s3, envDefineWordBytes s4,
       envDefineWordBytes s5, envDefineWordBytes s6]) = bytesVal .ld (envDefineWordBytes r) := by
    simp [envDefineEpilogueBody, runGM, stepGM, stepLdsM, wvalM, srcVal,
      envDefineEpilogueL, lookupG, eraseG]
  rw [h1, bytesVal_wordBytes, ret_tgt r halign]
  exact halign

/-- Clearing bit 0 of a 4-aligned address is the identity. -/
theorem bitvec_update_self (r : BitVec 64) (halign : r.toNat % 4 = 0) :
    Sail.BitVec.update r 0 0#1 = r := by
  have := ret_tgt r halign
  rwa [sext_zero, BitVec.add_zero] at this

theorem lpins4_of_agree {m m' : Mem} {a : Nat} {bs : List (BitVec 8)}
    (hag : ∀ k, k < 4 → m'[a + k]? = m[a + k]?) (h : LPins4 m a bs) : LPins4 m' a bs := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hag 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact h0
  · rw [hag 1 (by omega)]; exact h1
  · rw [hag 2 (by omega)]; exact h2
  · rw [hag 3 (by omega)]; exact h3


/- Memory-instruction facts stated against the seg's own register tower (the
`EnvDefineSpillImage.chainFacts` idiom): the memory tower is never unfolded. -/
private theorem stepMemM_alu {m : Mem} {a : MInstr} {L : GRegs} (hk : a.kind = .addi) :
    stepMemM m a L = m := by
  unfold stepMemM
  rw [hk]

private theorem stepMemM_sd_outside {m : Mem} {a : MInstr} {L : GRegs} (hk : a.kind = .sd)
    (x : Nat) (hx : x < (eaddrM a L).toNat ∨ (eaddrM a L).toNat + 8 ≤ x) :
    (stepMemM m a L)[x]? = m[x]? := by
  have h1 : stepMemM m a L = writeMap8 m (eaddrM a L).toNat (sdData_val (srcVal a.rs2 L)) := by
    unfold stepMemM wentryM
    rw [hk]
    rfl
  rw [h1]
  exact getElem_writeMap8_disjoint _ _ _ _ hx

private theorem eaddrM_toNat_sp (esp : BitVec 64) (off : Nat) {a : MInstr} {L : GRegs}
    (hsrc : srcVal a.rs1 L = esp + sign_extend (m := 64) (0xfc0#12))
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (h64 : 64 ≤ esp.toNat) (hoff : off < 64) :
    (eaddrM a L).toNat = esp.toNat - 64 + off := by
  have hlt := esp.isLt
  unfold eaddrM
  rw [hsrc, sp_sub64, BitVec.toNat_add, himm, sp_sub64_toNat esp h64, Nat.mod_eq_of_lt (by omega)]

private theorem envDefineMemFactsSd {m : Mem} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    (esp : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ esp.toNat - 64) (hhi : esp.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ esp.toNat - 64) (halign : esp.toNat % 16 = 0)
    (h64 : 64 ≤ esp.toNat)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = esp + sign_extend (m := 64) (0xfc0#12))
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 64) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hea := eaddrM_toNat_sp esp off hsrc himm h64 (by omega)
  unfold MemFacts
  rw [hk, hea]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem envDefineMemFactsLw {m : Mem} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    (env : BitVec 64)
    (hlo : 0x80000000 ≤ env.toNat) (hhi : env.toNat + 4 ≤ 0x100000000)
    (hhtif : env.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat)
    (hk : a.kind = .lw) (hsrc : srcVal a.rs1 L = env) (himm : a.imm = 0x000#12)
    (hp : LPins4 m env.toNat bs) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = env.toNat := by
    unfold eaddrM
    rw [hsrc, himm, sext0_64, BitVec.add_zero]
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hhtif⟩, hp⟩

private theorem lpins4_after_alu_sd {m : Mem} {a0 a1 : MInstr} {L0 L1 : GRegs} {base : Nat}
    {bs : List (BitVec 8)} (hk0 : a0.kind = .addi) (hk1 : a1.kind = .sd)
    (hout : base + 4 ≤ (eaddrM a1 L1).toNat ∨ (eaddrM a1 L1).toNat + 8 ≤ base)
    (hp : LPins4 m base bs) : LPins4 (stepMemM (stepMemM m a0 L0) a1 L1) base bs := by
  apply lpins4_of_agree _ hp
  intro k hk
  rw [stepMemM_sd_outside hk1 _ (by omega), stepMemM_alu hk0]

/-- The prologue's memory obligations: eight in-frame spills and the count load. -/
theorem envDefinePrologueChainFacts (m : Mem)
    (esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (bs : List (BitVec 8))
    (hcode : Env_defineLoaded m)
    (hlo : 0x80000000 ≤ esp.toNat - 64) (hhi : esp.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ esp.toNat - 64) (halign : esp.toNat % 16 = 0)
    (h64 : 64 ≤ esp.toNat)
    (henvLo : 0x80000000 ≤ aEnv.toNat) (henvHi : aEnv.toNat + 4 ≤ 0x100000000)
    (henvHtif : aEnv.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aEnv.toNat)
    (henvStack : aEnv.toNat + 4 ≤ esp.toNat - 64 ∨ esp.toNat ≤ aEnv.toNat)
    (hpins : LPins4 m aEnv.toNat bs) :
    ChainFacts m m (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv) [bs]
      envDefinePrologueSeg := by
  chain_facts hcode with "Vsa.Sim.Code.env_define_at_"
  · exact envDefineMemFactsSd esp 24 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · refine envDefineMemFactsLw aEnv henvLo henvHi henvHtif (by decide) (by rfl) (by decide) ?_
    refine lpins4_after_alu_sd (by decide) (by decide) ?_ hpins
    rw [eaddrM_toNat_sp esp 24 (by rfl) (by decide) h64 (by decide)]
    omega
  · exact envDefineMemFactsSd esp 32 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 16 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 8 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 56 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 48 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 40 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envDefineMemFactsSd esp 0 hlo hhi hhtif halign h64 (by decide) (by rfl) (by decide)
      (by decide) (by decide)

#print axioms envDefinePrologueChainFacts

/-- The prologue's entry state (the fields of `EnvDefineEntryState` it reads). -/
structure EnvDefineProloguePre (g : (R : Register) → Option (RegisterType R))
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80002a5c#64
  mem : c.σ.mem = m
  out : c.σ.sailOutput = out
  sp : c.σ.regs.get? Register.x2 = some esp
  a0 : c.σ.regs.get? Register.x10 = some aEnv
  a1 : c.σ.regs.get? Register.x11 = some aName
  a2 : c.σ.regs.get? Register.x12 = some pv
  ra : c.σ.regs.get? Register.x1 = some r
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R

/-- The prologue's exit state at `0x80002a90`: the exact spill image, the live
argument registers, the loaded count, and the untouched ABI frame. -/
structure EnvDefineProloguePost (g : (R : Register) → Option (RegisterType R))
    (esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (count : Nat)
    (m : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80002a90#64
  mem : c.σ.mem = envDefineSpillMem m (esp - 64#64).toNat r v8 v9 v18 v19 v20 v21 v22
  out : c.σ.sailOutput = out
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  sp : c.σ.regs.get? Register.x2 = some (esp - 64#64)
  a0 : c.σ.regs.get? Register.x10 = some aEnv
  s4 : c.σ.regs.get? Register.x20 = some aEnv
  s2 : c.σ.regs.get? Register.x18 = some aName
  s5 : c.σ.regs.get? Register.x21 = some pv
  s3 : c.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 count)
  keep : ∀ R, PrologueKeep R = true → c.σ.regs.get? R = g R

/-- **The framed prologue row.**  One reflected seg: the spill image, the loaded
count, and the untouched ABI frame all come off the seg outcome. -/
theorem envDefinePrologueFramed
    (g : (R : Register) → Option (RegisterType R))
    (esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (count : Nat)
    (m : Mem) (out : Array String) (SL : StackLayout)
    (hg8 : g Register.x8 = some v8) (hg9 : g Register.x9 = some v9)
    (hg18 : g Register.x18 = some v18) (hg19 : g Register.x19 = some v19)
    (hg20 : g Register.x20 = some v20) (hg21 : g Register.x21 = some v21)
    (hg22 : g Register.x22 = some v22)
    (hcode : Env_defineLoaded m)
    (hread : read32 m aEnv.toNat = some count) (hcountSigned : count < 2^31)
    (henvLo : 0x80000000 ≤ aEnv.toNat) (henvHi : aEnv.toNat + 4 ≤ 0x100000000)
    (henvHtif : aEnv.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aEnv.toNat)
    (henvStack : aEnv.toNat + 4 ≤ esp.toNat - 64 ∨ esp.toNat ≤ aEnv.toNat)
    (hsp : StackOK SL esp 1088)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000) (hwin : tohostAddr + 16 ≤ SL.lo) :
    Triple (EnvDefineProloguePre g esp aEnv aName pv r m out)
      (EnvDefineProloguePost g esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22 count m out) := by
  intro c h
  have hsp1 := hsp.1
  have hsp2 := hsp.2.1
  have hsp3 := hsp.2.2
  have h64 : 64 ≤ esp.toNat := by omega
  have hlt := esp.isLt
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes_ed m aEnv.toNat count hread
  let bs := [b0, b1, b2, b3]
  have hpins : LPins4 m aEnv.toNat bs :=
    ⟨by simpa [bs] using lpin_of_present hb0, by simpa [bs] using lpin_of_present hb1,
      by simpa [bs] using lpin_of_present hb2, by simpa [bs] using lpin_of_present hb3⟩
  have hcountWord : bytesVal .lw bs = BitVec.ofNat 64 count := by
    simpa [bytesVal, bs] using sext_count_ed b0 b1 b2 b3 count hcountSigned hrec
  have hx8 : c.σ.regs.get? Register.x8 = some v8 := (h.frame _ (by decide)).trans hg8
  have hx9 : c.σ.regs.get? Register.x9 = some v9 := (h.frame _ (by decide)).trans hg9
  have hx18 : c.σ.regs.get? Register.x18 = some v18 := (h.frame _ (by decide)).trans hg18
  have hx19 : c.σ.regs.get? Register.x19 = some v19 := (h.frame _ (by decide)).trans hg19
  have hx20 : c.σ.regs.get? Register.x20 = some v20 := (h.frame _ (by decide)).trans hg20
  have hx21 : c.σ.regs.get? Register.x21 = some v21 := (h.frame _ (by decide)).trans hg21
  have hx22 : c.σ.regs.get? Register.x22 = some v22 := (h.frame _ (by decide)).trans hg22
  have hL : GHolds c.σ (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv) :=
    ⟨by simpa [gprGet] using h.sp, by simpa [gprGet] using hx19, by simpa [gprGet] using h.a0,
      by simpa [gprGet] using hx18, by simpa [gprGet] using hx20, by simpa [gprGet] using hx21,
      by simpa [gprGet] using h.ra, by simpa [gprGet] using hx8, by simpa [gprGet] using hx9,
      by simpa [gprGet] using hx22, by simpa [gprGet] using h.a1, by simpa [gprGet] using h.a2,
      trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv) [bs]
      envDefinePrologueSeg := by
    rw [h.mem]
    exact envDefinePrologueChainFacts m esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22 bs hcode
      (by omega) (by omega) (by omega) hsp3 h64 henvLo henvHi henvHtif henvStack hpins
  obtain ⟨vm, hmi⟩ := h.good.minstret
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound envDefinePrologueSeg c.σ c.tick c.steps 0x80002a5c#64 vm
      (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv) [bs]
      h.good h.pc hmi hL
      (by show KeysOK [2, 19, 10, 18, 20, 21, 1, 8, 9, 22, 11, 12]; decide) hfacts
      (by show ChainOK 0x80002a5c#64 [2, 19, 10, 18, 20, 21, 1, 8, 9, 22, 11, 12]
            envDefinePrologueSeg
          decide)
      h.tick
  let c' : Config := ⟨σ', i', c.steps + evalBlocksFuel envDefinePrologueSeg⟩
  have reg (n : Nat) (v : BitVec 64)
      (hl : lookupG n (evalBlocks envDefinePrologueSeg
        (SegEvalState.init (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv)
          [bs])).regs = some v) :
      gprGet c'.σ n = some v := gholds_lookup _ hregs hl
  have hkeep : ∀ R, PrologueKeep R = true → c'.σ.regs.get? R = g R := by
    intro R hR
    exact (frame_of_wrChain_avoids (P := PrologueKeep)
      (by show ∀ rr ∈ noiseRegs, PrologueKeep rr = false; decide)
      (by show WrChainAvoids PrologueKeep envDefinePrologueSeg; decide) hframe R hR).trans
      (h.frame R (PrologueKeep.abi hR))
  refine ⟨c', hsteps, ?_⟩
  exact
    { good := hG'
      tick := hi'
      pc := by rw [hpc']; rfl
      mem := by
        show σ'.mem = _
        rw [hmem', h.mem, envDefinePrologueMem m esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv bs h64]
      out := hout.trans h.out
      minstret := hmi'
      sp := by
        simpa [gprGet] using reg 2 (esp - 64#64) (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64])
      a0 := by
        simpa [gprGet] using reg 10 aEnv (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64])
      s4 := by
        simpa [gprGet] using reg 20 aEnv (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64])
      s2 := by
        simpa [gprGet] using reg 18 aName (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64])
      s5 := by
        simpa [gprGet] using reg 21 pv (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64])
      s3 := by
        rw [← hcountWord]
        simpa [gprGet] using reg 19 (bytesVal .lw bs) (by
          simp [envDefinePrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefinePrologueL, sp_sub64, bs])
      keep := hkeep }

#print axioms envDefinePrologueFramed

/-! ## 2. The entry-side oracles -/

/-- Agreement with the entry memory outside the callee's stack window `[SL.lo, esp)`. -/
def AgreeBelow (SL : StackLayout) (esp : BitVec 64) (m m' : Mem) : Prop :=
  ∀ k, ¬ (SL.lo ≤ k ∧ k < esp.toNat) → m'[k]? = m[k]?

/-- The caller's ghost is total on the seven registers the prologue spills. -/
structure EnvDefineSavedPresent (g : (R : Register) → Option (RegisterType R)) : Prop where
  s0 : (g Register.x8).isSome = true
  s1 : (g Register.x9).isSome = true
  s2 : (g Register.x18).isSome = true
  s3 : (g Register.x19).isSome = true
  s4 : (g Register.x20).isSome = true
  s5 : (g Register.x21).isSome = true
  s6 : (g Register.x22).isSome = true

/-- **Runtime ownership at one memory**: the store (`HeapOwned`, with the stack
region inside the caller's write footprint), the staged value's payload and
the queried name's bytes, all over ONE shared-byte domain. -/
inductive EnvDefineOwned (A : Arena) (SL : StackLayout) (exts : List Extent) (m : Mem)
    (φf φc : Addr → Nat) (st : Vsa.While.St) (x : String) (aName pv : BitVec 64)
    (v : Value) : Prop where
  | intro (alloc : RuntimeOwnership.Allocations) (shared readable writes : Nat → Prop)
      (heap : RuntimeOwnership.HeapOwned A exts m φf φc alloc shared readable writes st.store)
      (stack : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
      (value : RuntimeOwnership.ValueOwned m shared pv.toNat v)
      (name : RuntimeOwnership.SharedCString m shared aName.toNat x)

/-- Ownership survives byte agreement on a footprint covering the arena, every
byte outside the stack region, and the staged value slot. -/
theorem EnvDefineOwned.transport {A : Arena} {SL : StackLayout} {exts : List Extent}
    {m m' : Mem} {φf φc : Addr → Nat} {st : Vsa.While.St} {x : String}
    {aName pv : BitVec 64} {v : Value} {P : Nat → Prop}
    (h : EnvDefineOwned A SL exts m φf φc st x aName pv v) (hag : AgreeP P m m')
    (hArena : ∀ k, A.lo ≤ k → k < A.hi → P k)
    (hOff : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → P k)
    (hSlot : ∀ k, valHeader pv.toNat k → P k) :
    EnvDefineOwned A SL exts m' φf φc st x aName pv v := by
  obtain ⟨alloc, shared, readable, writes, hheap, hstack, hval, hname⟩ := h
  have hs : ∀ k, shared k → P k := by
    intro k hk
    apply hOff
    intro hw
    exact hheap.immutable.outsideWrites k hk (hstack k hw.1 hw.2)
  have ha : ∀ role p n, RuntimeOwnership.Allocated alloc role p n →
      ∀ k, RuntimeOwnership.ExtentByte (p, n) k → P k := by
    intro role p n hpn k hk
    obtain ⟨_, hlo, hhi⟩ := hheap.ledger.arena.1 _ (hheap.ledger.live _ _ _ hpn)
    change p ≤ k ∧ k < p + n at hk
    exact hArena k (by simp only at hlo; omega) (by simp only at hhi; omega)
  exact ⟨alloc, shared, readable, writes, hheap.transport hag ha hs, hstack,
    hval.transport hag hSlot hs, hname.transport (fun k hk => hag k (hs k hk))⟩

/-- **The named entry-side facts the landed lanes need beyond `EnvDefineEntryState`.**
Each field names its supplier. -/
structure EnvDefineUpdateOracles (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) : Prop where
  /-- The global pointer at entry (pinned for the whole run; the caller's ABI frame). -/
  gp : g Register.x3 = some gpv
  /-- The caller's ghost is total on the seven spilled callee-saved registers
  (the C ABI register file; the caller's `GRegs` pins). -/
  present : EnvDefineSavedPresent g
  /-- The allocator's stack headroom fits under `env_define`'s 64-byte frame
  (`EnvDefineMem.stack` budgets 1088 bytes; concrete at M6). -/
  headroom_le : headroom + 64 ≤ 1088
  /-- The allocator invariant holds at the entry memory with the pinned `gp`
  (the caller's `MallocContract` state, carried by the interpreter invariant). -/
  ainv_entry : ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts
  /-- The allocator invariant reads only `gp` and bytes outside the callee's stack
  window (the `MallocContract` footprint discipline; every lane's `hAInvStable`). -/
  stack_hi : esp.toNat ≤ SL.hi
  /-- The run-global allocator ledger (`Vsa/Sim/AllocRuns.lean`). -/
  alloc : AllocLedger A SL gpv headroom maxReq M
  /-- Ledger geometry (`HeapOwnershipGeometry`; the interpreter's ownership invariant). -/
  heap : HeapArena A exts
  /-- The arena is RAM above the HTIF window and disjoint from `env_define`'s text
  (linker script, M6). -/
  arena_ram : 0x80000000 ≤ A.lo ∧ A.hi ≤ 0x100000000
  arena_code : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo
  /-- The caller's staged value slot `[esp+16, esp+40)` lies inside the stack region
  (the caller's own `StackOK`). -/
  slot_in_stack : esp.toNat + 40 ≤ SL.hi
  /-- `env_define` and `strcmp` text at entry (projections of `EnvDefineMem.text`,
  `gen_fixed_image.py`). -/
  code : Env_defineLoaded m
  strcmp_code : StrcmpLoaded m
  /-- Runtime ownership of the store, the staged value and the queried name at
  the entry memory (the interpreter's ownership invariant `HeapOwned`, with the
  stack region inside the caller's write footprint). -/
  owned : EnvDefineOwned A SL exts m φf φc st x aName pv v
  /-- The staged 24-byte slot is fully written (the caller's write log for its
  in-frame slot). -/
  value_words : ValueWordsTotal m pv.toNat
  /-- Binding names are unique in the target frame (source invariant `FrameNamesUnique`). -/
  unique : ∀ (h : env < st.store.frames.size), FrameUnique st.store.frames[env]
  /-- The scan's string regions at any memory agreeing below `esp`: the queried name
  string (AST region) and every bound name (arena) with their RAM/HTIF/`strcmp`
  bounds, plus the word-path mask rodata (fixed rodata image + `HeapArena`). -/
  names : ∀ (h : env < st.store.frames.size) (m' : Mem) (pn : Nat), AgreeBelow SL esp m m' →
    read64 m' (φf env + 8) = some pn → ScanNames m' pn aName x st.store.frames[env]
  /-- The values array is 8-aligned (allocator alignment recorded by the frame's
  creation contract, `env_new`/`realloc`). -/
  arrays_aligned : ∀ vals, read64 m (φf env + 16) = some vals → vals % 8 = 0
  /-- Survival of the defined store's representation under stack changes, at any
  memory the helper can return with (`StoreOwned.repr_transport` over the arena and
  AST footprints; the same clause `EnvDefineMem.store_survives` states at entry). -/
  define_survives : ∀ m1 : Mem,
    (∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) → m1[k]? = m[k]?) →
    StoreRepr m1 N A φf φc (st.store.define env x v) →
    ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m1[k]? = m'[k]?) →
      StoreRepr m' N A φf φc (st.store.define env x v)

/-- **The external ledger.**  The fields of `EnvDefineUpdateOracles` that
`EnvDefineMem` does not determine; each names its supplier. -/
structure EnvDefineUpdateLedger (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) : Prop where
  /-- The global pointer at entry (the interpreter's pinned `gp`; the caller's ABI
  frame). -/
  gp : g Register.x3 = some gpv
  /-- The caller's ghost is total on the seven spilled callee-saved registers
  (the caller's `GRegs` pins). -/
  present : EnvDefineSavedPresent g
  /-- The allocator invariant at the entry memory with the pinned `gp`
  (the caller's `MallocContract` state). -/
  ainv_entry : ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts
  /-- The allocator invariant reads only `gp` and bytes outside the callee's stack
  window (the `MallocContract` footprint discipline). -/
  stack_hi : esp.toNat ≤ SL.hi
  /-- The run-global allocator ledger (`Vsa/Sim/AllocRuns.lean`). -/
  alloc : AllocLedger A SL gpv headroom maxReq M
  /-- Ledger geometry (`HeapOwnershipGeometry`; the interpreter's ownership
  invariant). -/
  heap : HeapArena A exts
  /-- Runtime ownership of the store, the staged value's payload and the
  queried name's bytes at the entry memory (the interpreter's ownership
  invariant `HeapOwned`; the producer's `ValueOwned`; the parser's shared
  identifier bytes), with the stack region inside the caller's write footprint. -/
  owned : EnvDefineOwned A SL exts m φf φc st x aName pv v
  /-- Binding names are unique in the target frame (source invariant
  `FrameNamesUnique`). -/
  unique : ∀ (h : env < st.store.frames.size), FrameUnique st.store.frames[env]
  /-- The scan's string regions at any memory agreeing below `esp` (the rodata
  mask image, the `strcmp` region bounds of the queried and bound names, and the
  names-array slot geometry from `HeapArena`). -/
  names : ∀ (h : env < st.store.frames.size) (m' : Mem) (pn : Nat), AgreeBelow SL esp m m' →
    read64 m' (φf env + 8) = some pn → ScanNames m' pn aName x st.store.frames[env]
  /-- The values array is 8-aligned (allocator alignment recorded by the frame's
  creation contract). -/
  arrays_aligned : ∀ vals, read64 m (φf env + 16) = some vals → vals % 8 = 0
  /-- Survival of the defined store's representation under stack changes
  (`StoreOwned.repr_transport` over the arena and AST footprints after
  `HeapOwned.defineHit`). -/
  define_survives : ∀ m1 : Mem,
    (∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) → m1[k]? = m[k]?) →
    StoreRepr m1 N A φf φc (st.store.define env x v) →
    ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m1[k]? = m'[k]?) →
      StoreRepr m' N A φf φc (st.store.define env x v)

/-- The footprint discipline, DERIVED from the run-global ledger. -/
theorem EnvDefineUpdateLedger.ainv_stable
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    ∀ σa σb : MState,
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts → M.AInv σb exts :=
  L.alloc.ainv_stable esp L.stack_hi exts

/-- The same, for the derived oracles bundle. -/
theorem EnvDefineUpdateOracles.ainv_stable
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    ∀ σa σb : MState,
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts → M.AInv σb exts :=
  O.alloc.ainv_stable esp O.stack_hi exts

/-- The arena is RAM above the HTIF window, DERIVED from the ledger. -/
theorem EnvDefineUpdateOracles.arena_htif
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    tohostAddr + 16 ≤ A.lo := O.alloc.arena_htif

/-- **The oracles from the entry facts and the ledger.**  `code`/`strcmp_code`
are projections of the fixed text image, `slot_in_stack`/`value_words` are
`EnvDefineMem` fields, and `arena_code` follows from the arena/image separation. -/
theorem EnvDefineUpdateOracles.of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp aEnv aName pv r : BitVec 64} {m : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (hM : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts where
  gp := L.gp
  present := L.present
  headroom_le := L.alloc.headroom_le
  ainv_entry := L.ainv_entry
  stack_hi := L.stack_hi
  alloc := L.alloc
  heap := L.heap
  arena_ram := L.alloc.arena_ram
  arena_code := by
    rcases hM.arena_image with h | h
    · left; omega
    · right; omega
  slot_in_stack := hM.slot_in_stack
  code := Vsa.Sim.Code.FixedTextLoaded.Env_defineLoaded hM.text
  strcmp_code := Vsa.Sim.Code.FixedTextLoaded.StrcmpLoaded hM.text
  owned := L.owned
  value_words := hM.value_words
  unique := L.unique
  names := L.names
  arrays_aligned := L.arrays_aligned
  define_survives := L.define_survives

#print axioms EnvDefineUpdateOracles.of_entry

/-! ## 3. Transports through the prologue's spill window -/

theorem valueHeapOwned_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {exts : List Extent} {a : Nat} {v : Value}
    (hP : ∀ k, k < 8 → P (a + 8 + k)) (hv : ValueHeapOwned m exts a v) :
    ValueHeapOwned m' exts a v := by
  cases v with
  | str s =>
    obtain ⟨p, hp, hm⟩ := hv
    exact ⟨p, (read64_agreeP h hP).symm.trans hp, hm⟩
  | native f =>
    obtain ⟨p, hp, hm⟩ := hv
    exact ⟨p, (read64_agreeP h hP).symm.trans hp, hm⟩
  | null | bool | int | closure => trivial

/-- An allocator-owned payload is covered by any predicate holding on the arena. -/
theorem valuePayloadCovered_of_heapOwned {P : Nat → Prop} {A : Arena} {exts : List Extent}
    {m : Mem} {a : Nat} {v : Value} (harena : HeapArena A exts)
    (hP : ∀ k, A.lo ≤ k → k < A.hi → P k) (hv : ValueHeapOwned m exts a v) :
    ValuePayloadCovered P m a v := by
  cases v with
  | str s =>
    intro p hp k hk
    obtain ⟨p', hp', hm⟩ := hv
    have hpe : p = p' := Option.some.inj (hp.symm.trans hp')
    subst hpe
    obtain ⟨_, hlo, hhi⟩ := harena.1 _ hm
    exact hP _ (by simp only at hlo; omega) (by simp only at hhi; omega)
  | native f =>
    intro p hp k hk
    obtain ⟨p', hp', hm⟩ := hv
    have hpe : p = p' := Option.some.inj (hp.symm.trans hp')
    subst hpe
    obtain ⟨_, hlo, hhi⟩ := harena.1 _ hm
    exact hP _ (by simp only at hlo; omega) (by simp only at hhi; omega)
  | null | bool | int | closure => trivial

/-! ## 4. The return core and the named residuals -/

/-- The callee-saved registers the epilogue reloads. -/
def EnvDefineRestored (R : Register) : Bool :=
  R == Register.x8 || R == Register.x9 || R == Register.x18 || R == Register.x19 ||
    R == Register.x20 || R == Register.x21 || R == Register.x22

/-- `EnvDefineReturnState` minus the three facts the landed lanes' posts do not
export (see `EnvDefineReturnResiduals`). -/
structure EnvDefineReturnCore (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp r : BitVec 64) (m0 : Mem) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some r
  ra : cfg.σ.regs.get? Register.x1 = some r
  sp : cfg.σ.regs.get? Register.x2 = some esp
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  restored : ∀ R, EnvDefineRestored R = true → cfg.σ.regs.get? R = g R
  store : StoreRepr cfg.σ.mem N A φf φc (st.store.define env x v)
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc (st.store.define env x v)
  mem_frame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
    cfg.σ.mem[k]? = m0[k]?
  mem_extends : MemExtends m0 cfg.σ.mem

/-- **Named residuals of the landed lanes.**  The scan carriers
(`EnvDefineScanSt`/`EnvDefineScanFrame`) do not carry `sailOutput` past the
`strcmp` seam (whose post preserves it), and the update/epilogue rows
(`updateStoreLiveRow`, `envDefineEpilogueRow`) export only their written registers,
so the untouched `x3`, `x4`, `x23`–`x27` and the presence of `a0` are lost after
the hit.  Supplied by keep-set framing of those rows (`FramedSegPost.out`/`.keep`;
both segs write none of these registers — `WrChainAvoids` decides). -/
structure EnvDefineReturnResiduals (g : (R : Register) → Option (RegisterType R))
    (out : Array String) (cfg : Config) : Prop where
  out : cfg.σ.sailOutput = out
  rest : ∀ R, AbiPreserved R = true → EnvDefineRestored R = false → R ≠ Register.x2 →
    cfg.σ.regs.get? R = g R
  a0 : ∃ w, cfg.σ.regs.get? Register.x10 = some w

/-- A register of the `rest` clause is kept by the update/epilogue rows, untouched
by the prologue, and none of the scan's reseated `s0`/`s1`/`s6`. -/
theorem envDefineRest_facts (R : Register) (hA : AbiPreserved R = true)
    (hRes : EnvDefineRestored R = false) (h2 : R ≠ Register.x2) :
    EnvDefineTailKeep R = true ∧ PrologueKeep R = true ∧ R ≠ Register.x8 ∧
      R ≠ Register.x9 ∧ R ≠ Register.x22 := by
  cases R <;> simp_all [AbiPreserved, EnvDefineRestored, EnvDefineTailKeep, PrologueKeep]

/-- The contract's return state from the core and the residuals. -/
theorem EnvDefineReturnCore.toReturn
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {esp r : BitVec 64} {m0 : Mem} {out : Array String} {cfg : Config}
    (h : EnvDefineReturnCore g N A SL φf φc st env x v esp r m0 cfg)
    (hg2 : g Register.x2 = some esp)
    (hres : EnvDefineReturnResiduals g out cfg) :
    EnvDefineReturnState g N A SL φf φc st env x v esp r m0 out cfg where
  good := h.good
  tick := h.tick
  pc := h.pc
  ra := h.ra
  sp := h.sp
  minstret := h.minstret
  a0_defined := hres.a0
  out := hres.out
  frame := by
    intro R hR
    by_cases h2 : R = Register.x2
    · subst h2; exact h.sp.trans hg2.symm
    · cases hres' : EnvDefineRestored R with
      | true => exact h.restored R hres'
      | false => exact hres.rest R hR hres' h2
  store := h.store
  store_survives := h.store_survives
  mem_frame := h.mem_frame
  mem_extends := h.mem_extends

#print axioms EnvDefineReturnCore.toReturn

/-! ## 5. Prologue ≫ finite scan, from the contract entry -/

/-- The outer register snapshot the epilogue restores: the caller's ghost with
the link register pinned. -/
def envDefineSaved (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) :
    (R : Register) → Option (RegisterType R) :=
  fun R => if h : R = Register.x1 then some (h ▸ r) else g R

@[simp] theorem envDefineSaved_x1 (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) :
    envDefineSaved g r Register.x1 = some r := by
  simp [envDefineSaved]

theorem envDefineSaved_ne (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64)
    {R : Register} (h : R ≠ Register.x1) : envDefineSaved g r R = g R := by
  simp [envDefineSaved, h]

/-- The memory after the prologue: the entry memory with the eight spills. -/
abbrev envDefineScannedMem (m : Mem) (esp r v8 v9 v18 v19 v20 v21 v22 : BitVec 64) : Mem :=
  envDefineSpillMem m (esp - 64#64).toNat r v8 v9 v18 v19 v20 v21 v22

/-- Config-independent facts at the scanned memory `m0`: the entry-side facts
transported through the spill window, the frame data, and the ghost bookkeeping. -/
structure EnvDefineScanFacts (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
    (gm : (R : Register) → Option (RegisterType R)) : Prop where
  env_lt : env < st.store.frames.size
  env_addr : aEnv.toNat = φf env
  ra_align : r.toNat % 4 = 0
  /-- The caller's ghost holds its stack pointer (`EnvDefineEntryState.frame`). -/
  g_sp : g Register.x2 = some esp
  s0 : g Register.x8 = some v8
  s1 : g Register.x9 = some v9
  s2 : g Register.x18 = some v18
  s3 : g Register.x19 = some v19
  s4 : g Register.x20 = some v20
  s5 : g Register.x21 = some v21
  s6 : g Register.x22 = some v22
  /-- The scan's ABI ghost agrees with the caller's on every register the prologue
  and the scan initialisation leave untouched. -/
  gm_keep : ∀ R, PrologueKeep R = true → R ≠ Register.x22 → gm R = g R
  gm_sp : gm Register.x2 = some (esp - 64#64)
  count_signed : st.store.frames[env].vars.length < 2^31
  pn_read : read64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (φf env + 8) = some pn
  store0 : StoreRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N A φf φc st.store
  owned0 : EnvDefineOwned A SL exts (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
    φf φc st x aName pv v
  code0 : Env_defineLoaded (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
  text0 : FixedTextLoaded (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
  word0 : ValueWordRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φc pv.toNat v
  /-- The scan's ABI ghost holds the argument registers the prologue moved. -/
  gm_s2 : gm Register.x18 = some aName
  gm_s3 : gm Register.x19 = some (BitVec.ofNat 64 (st.store.frames[env]'env_lt).vars.length)
  gm_s4 : gm Register.x20 = some aEnv
  gm_s5 : gm Register.x21 = some pv
  /-- The scan's ABI ghost holds the names array the initialisation loads into `s6`. -/
  gm_s6 : gm Register.x22 = some (BitVec.ofNat 64 pn)
  names0 : ScanNames (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) pn aName x
    st.store.frames[env]
  /-- The scanned memory differs from the entry memory only in the spill window. -/
  mem_agree : ∀ a, (a < esp.toNat - 64 ∨ esp.toNat ≤ a) →
    (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)[a]? = m[a]?
  mem_extends : MemExtends m (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)

/-- **The prologue exit with the scanned-memory facts**: the framed prologue's
exit state, the config-independent facts at the spill memory over the scan's
initial ghost `envDefineScanBaseGhost c.regs pn`, the saved spill image, the
pinned `gp` and the allocator invariant.  Every miss lane (scan, empty frame)
starts here. -/
structure EnvDefinePrologueExit (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat) (c : Config) : Prop where
  facts : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
    v8 v9 v18 v19 v20 v21 v22 pn
    (envDefineScanBaseGhost (fun R => c.σ.regs.get? R) (BitVec.ofNat 64 pn))
  post : EnvDefineProloguePost g esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22
    (st.store.frames[env]'facts.env_lt).vars.length m out c
  saved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c
  gp : c.σ.regs.get? Register.x3 = some gpv
  ainv : M.AInv c.σ exts

/-- **Entry ⟶ prologue exit.**  The framed prologue seg and the landed spill
carrier, with the entry facts transported to the spill memory. -/
theorem envDefinePrologueExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (fun c => ∃ (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat),
        EnvDefinePrologueExit g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          v8 v9 v18 v19 v20 v21 v22 pn c) := by
  intro c h
  have F := h.facts
  obtain ⟨v8, hg8⟩ := Option.isSome_iff_exists.mp O.present.s0
  obtain ⟨v9, hg9⟩ := Option.isSome_iff_exists.mp O.present.s1
  obtain ⟨v18, hg18⟩ := Option.isSome_iff_exists.mp O.present.s2
  obtain ⟨v19, hg19⟩ := Option.isSome_iff_exists.mp O.present.s3
  obtain ⟨v20, hg20⟩ := Option.isSome_iff_exists.mp O.present.s4
  obtain ⟨v21, hg21⟩ := Option.isSome_iff_exists.mp O.present.s5
  obtain ⟨v22, hg22⟩ := Option.isSome_iff_exists.mp O.present.s6
  have hsp1 := F.stack.1
  have hsp2 := F.stack.2.1
  have hsp3 := F.stack.2.2
  have hramLo := F.stack_ram.1
  have hramHi := F.stack_ram.2
  have hwin := F.stack_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have h64 : 64 ≤ esp.toNat := by omega
  have hsp64 : (esp - 64#64).toNat = esp.toNat - 64 := sp_sub64_toNat esp h64
  have hAlo := O.arena_ram.1
  have hhr := O.headroom_le
  have hAhi := O.arena_ram.2
  have hAhtif := O.arena_htif
  have hAstack := F.arena_stack
  have henvLt : env < st.store.frames.size := F.env_valid
  have hget : st.store.frames[env]? = some st.store.frames[env] :=
    Array.getElem?_eq_some_iff.mpr ⟨henvLt, rfl⟩
  obtain ⟨henvArena, henvAlign⟩ := F.store.frames_arena env henvLt
  have henvNat : aEnv.toNat = φf env := by
    rw [F.env_addr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Arena.contains at henvArena; omega)]
  have hfr : FrameRepr m N φf φc (φf env) st.store.frames[env] := F.store.frames env henvLt
  obtain ⟨hcount, ⟨cap, hcap, hcaple⟩, ⟨pn, vals, hpn, hvals, _⟩, _⟩ := hfr
  obtain ⟨alloc, shared, readable, writes, hheap, hstackW, hvalO, hnameO⟩ := O.owned
  have hfo := hheap.store.frames env henvLt
  have hcapSigned : cap < 2^31 := hfo.capSigned hheap.ledger hcap hAhi
  have hlen : st.store.frames[env].vars.length < 2^31 := by omega
  obtain ⟨arr, harr⟩ := hfo.arrays
  have hpnEq : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have hcapEq : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans hcap)
  unfold Arena.contains at henvArena
  -- the framed prologue
  obtain ⟨c1, hs1, P⟩ := envDefinePrologueFramed g esp aEnv aName pv r v8 v9 v18 v19 v20 v21 v22
    st.store.frames[env].vars.length m out SL hg8 hg9 hg18 hg19 hg20 hg21 hg22 O.code
    (by rw [henvNat]; exact hcount) hlen (by omega) (by omega) (by right; omega)
    (by rcases hAstack with hA | hA
        · left; omega
        · right; omega)
    F.stack F.stack_ram F.stack_win c
    ⟨h.good, h.tick, h.pc, h.mem, h.out, h.sp, h.a0, h.a1, h.a2, h.ra, h.frame⟩
  -- the scanned memory and its transports
  have hagree : ∀ a, (a < esp.toNat - 64 ∨ esp.toNat ≤ a) →
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)[a]? = m[a]? := by
    intro a ha
    exact envDefineSpillMem_outside m _ a r v8 v9 v18 v19 v20 v21 v22 (by omega)
  have hAg : AgreeP (fun a => a < esp.toNat - 64 ∨ esp.toNat ≤ a) m
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    fun a ha => (hagree a ha).symm
  have hbelow : AgreeBelow SL esp m (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    fun k hk => hagree k (by omega)
  have harenaOut : ∀ k, A.lo ≤ k → k < A.hi → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk1 hk2
    rcases hAstack with hA | hA
    · left; omega
    · right; omega
  have hstore0 : StoreRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N A φf φc
      st.store :=
    F.store_survives _ (fun k hk => (hagree k (by omega)).symm)
  have hsharedOut : ∀ k, shared k → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk
    have hnw := hheap.immutable.outsideWrites k hk
    rcases Nat.lt_or_ge k (esp.toNat - 64) with h1 | h1
    · exact Or.inl h1
    · rcases Nat.lt_or_ge k esp.toNat with h2 | h2
      · exact absurd (hstackW k (by omega) (by omega)) hnw
      · exact Or.inr h2
  have howned : EnvDefineOwned A SL exts (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
      φf φc st x aName pv v :=
    O.owned.transport hAg harenaOut
      (fun k hk => by omega)
      (fun k hk => by have := F.pv_frame; unfold valHeader at hk; right; omega)
  have hcode0 : Env_defineLoaded (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    envDefineLoaded_of_agree m _ (fun a _ _ => hagree a (by omega)) O.code
  have hstrcmp0 : StrcmpLoaded (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    strcmpLoaded_of_agree m _ (fun a _ _ => hagree a (by omega)) O.strcmp_code
  have hpvNat := F.pv_frame
  have hhdr : ∀ k, valHeader pv.toNat k → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk
    unfold valHeader at hk
    right; omega
  have hword0 : ValueWordRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φc
      pv.toNat v :=
    ⟨valueRepr_agreeP hAg hhdr (hvalO.covered hsharedOut) F.value,
      RuntimeOwnership.valueWordsTotal_transport O.value_words hAg hhdr⟩
  have htext0 : FixedTextLoaded (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    F.text.transport (fun a _ ha => hagree a (by omega))
  have hpn0 : read64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (φf env + 8) =
      some pn := by
    rw [← read64_agreeP hAg (fun k hk => harenaOut _ (by omega) (by omega))]
    exact hpn
  have hnames0 : ScanNames (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) pn aName x
      st.store.frames[env] := O.names henvLt _ pn hbelow hpn0
  have hfr0 : FrameRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φf φc
      aEnv.toNat st.store.frames[env] := by
    rw [henvNat]; exact hstore0.frames env henvLt
  have hext : MemExtends m (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) := by
    have hw := memExtends_writeLog m (evalBlocks envDefinePrologueSeg
      (SegEvalState.init (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv)
        [[]])).log
    rw [envDefinePrologueMem m esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv [] h64] at hw
    exact hw
  -- the spill carrier and the scan entry frame at the prologue exit
  have hcode1 : Env_defineLoaded c1.σ.mem := by rw [P.mem]; exact hcode0
  have hstrcmp1 : StrcmpLoaded c1.σ.mem := by rw [P.mem]; exact hstrcmp0
  have hsaved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c1 :=
    envDefineSavedSpills_of_mem r v8 v9 v18 v19 v20 v21 v22 (envDefineSaved_x1 g r)
      ((envDefineSaved_ne g r (by decide)).trans hg8)
      ((envDefineSaved_ne g r (by decide)).trans hg9)
      ((envDefineSaved_ne g r (by decide)).trans hg18)
      ((envDefineSaved_ne g r (by decide)).trans hg19)
      ((envDefineSaved_ne g r (by decide)).trans hg20)
      ((envDefineSaved_ne g r (by decide)).trans hg21)
      ((envDefineSaved_ne g r (by decide)).trans hg22)
      P.mem hcode1 (by omega) (by omega) (by omega) (by omega)
      (envDefineEpilogueTermFacts (esp - 64#64) r v8 v9 v18 v19 v20 v21 v22 h.ra_align)
  have hx3 : c1.σ.regs.get? Register.x3 = some gpv := (P.keep _ (by decide)).trans O.gp
  have hainv1 : M.AInv c1.σ exts := by
    apply O.ainv_stable c.σ c1.σ ((h.frame _ (by decide)).trans (O.gp.trans hx3.symm))
    · intro a ha
      rw [h.mem, P.mem]
      exact (hagree a (by omega)).symm
    · exact O.ainv_entry c.σ ((h.frame _ (by decide)).trans O.gp) h.mem
  let gm0 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  refine ⟨c1, hs1, v8, v9, v18, v19, v20, v21, v22, pn, ?_⟩
  have hfacts : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
      v8 v9 v18 v19 v20 v21 v22 pn (envDefineScanBaseGhost gm0 (BitVec.ofNat 64 pn)) :=
    { env_lt := henvLt
      env_addr := henvNat
      ra_align := h.ra_align
      g_sp := (h.frame _ (by decide)).symm.trans h.sp
      s0 := hg8, s1 := hg9, s2 := hg18, s3 := hg19, s4 := hg20, s5 := hg21, s6 := hg22
      gm_keep := fun R hR h22 => by
        rw [envDefineScanBaseGhost_ne gm0 _ h22]
        exact P.keep R hR
      gm_sp := by
        rw [envDefineScanBaseGhost_ne gm0 _ (by decide)]
        exact P.sp
      count_signed := hlen
      pn_read := hpn0
      store0 := hstore0
      owned0 := howned
      code0 := hcode0
      text0 := htext0
      word0 := hword0
      gm_s2 := by
        rw [envDefineScanBaseGhost_ne gm0 _ (by decide)]
        exact P.s2
      gm_s3 := by
        rw [envDefineScanBaseGhost_ne gm0 _ (by decide)]
        exact P.s3
      gm_s4 := by
        rw [envDefineScanBaseGhost_ne gm0 _ (by decide)]
        exact P.s4
      gm_s5 := by
        rw [envDefineScanBaseGhost_ne gm0 _ (by decide)]
        exact P.s5
      gm_s6 := envDefineScanBaseGhost_x22 gm0 _
      names0 := hnames0
      mem_agree := hagree
      mem_extends := hext }
  exact ⟨hfacts, P, hsaved, hx3, hainv1⟩

#print axioms envDefinePrologueExit

/-- The state at either scan exit with the scanned-memory facts. -/
structure EnvDefineScanned (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
    (gm : (R : Register) → Option (RegisterType R)) (c : Config) : Prop where
  facts : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
    v8 v9 v18 v19 v20 v21 v22 pn gm
  result : EnvDefineScanFramedResult M exts out (envDefineSaved g r) gm aEnv aName pv
    (BitVec.ofNat 64 (st.store.frames[env]'facts.env_lt).vars.length) (BitVec.ofNat 64 pn)
    (esp - 64#64) (st.store.frames[env]'facts.env_lt) x
    (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) c

/-- **Entry ⟶ scan exit.**  The prologue exit (`envDefinePrologueExit`) and
the landed finite scan (`envDefineScanDispatchFramed`), on a non-empty frame. -/
theorem envDefineScanned
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hpos : ∀ (h : env < st.store.frames.size), 0 < st.store.frames[env].vars.length) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (fun c => ∃ (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
        (gm : (R : Register) → Option (RegisterType R)),
        EnvDefineScanned g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          v8 v9 v18 v19 v20 v21 v22 pn gm c) := by
  intro c h
  obtain ⟨c1, hs1, v8, v9, v18, v19, v20, v21, v22, pn, Q⟩ :=
    envDefinePrologueExit g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O c h
  have F := h.facts
  have Sf := Q.facts
  have P := Q.post
  have hAlo := O.arena_ram.1
  have hAhi := O.arena_ram.2
  have hAhtif := O.arena_htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have henvLt : env < st.store.frames.size := Sf.env_lt
  obtain ⟨henvArena, henvAlign⟩ := F.store.frames_arena env henvLt
  unfold Arena.contains at henvArena
  have henvNat : aEnv.toNat = φf env := Sf.env_addr
  have hlen : st.store.frames[env].vars.length < 2^31 := Sf.count_signed
  have hpn0 := Sf.pn_read
  have hpnLt : pn < 2^64 := read64_lt_eg4 _ _ _ hpn0
  have hfr0 : FrameRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φf φc
      aEnv.toNat st.store.frames[env] := by
    rw [henvNat]; exact Sf.store0.frames env henvLt
  have hcode1 : Env_defineLoaded c1.σ.mem := by rw [P.mem]; exact Sf.code0
  have hstrcmp1 : StrcmpLoaded c1.σ.mem := by
    rw [P.mem]; exact Vsa.Sim.Code.FixedTextLoaded.StrcmpLoaded Sf.text0
  let gm0 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  have hsp1 := F.stack.1
  have hsp2 := F.stack.2.1
  have hsp3 := F.stack.2.2
  have hhr := O.headroom_le
  have hsp64 : (esp - 64#64).toNat = esp.toNat - 64 := sp_sub64_toNat esp (by omega)
  have hstack : StackOK SL (esp - 64#64) headroom := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [hsp64] <;> omega
  have hentryFrame : EnvDefineScanEntryFrame M exts out (esp - 64#64) gm0 c1 :=
    ⟨hstack, Q.gp, fun R _ => rfl, Q.ainv, P.out⟩
  have hgeom : EnvDefineScanInitGeom aEnv (BitVec.ofNat 64 pn)
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    { read := by
        rw [henvNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hpn0
      lo := by omega
      hi := by omega
      htif := by right; omega
      align := by omega }
  have hlenNat : (BitVec.ofNat 64 st.store.frames[env].vars.length).toNat =
      st.store.frames[env].vars.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → M.AInv σa exts → M.AInv σb exts :=
    fun σa σb h1 h2 => O.ainv_stable σa σb h1 (fun a _ => h2 a)
  obtain ⟨c2, hs2, hres⟩ := envDefineScanDispatchFramed M exts out (envDefineSaved g r) gm0 aEnv
    aName
    pv (BitVec.ofNat 64 st.store.frames[env].vars.length) (BitVec.ofNat 64 pn) (esp - 64#64)
    st.store.frames[env] x N φf φc _ hfr0
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Sf.names0)
    hlenNat (hpos henvLt) hlen hgeom hAInvStable c1
    ⟨P.good, hcode1, hstrcmp1, P.mem, P.pc, P.a0, P.s4, P.s2, P.s5, P.s3, P.sp, P.tick, Q.saved,
      hentryFrame⟩
  exact ⟨c2, hs1.trans hs2, v8, v9, v18, v19, v20, v21, v22, pn,
    envDefineScanBaseGhost gm0 (BitVec.ofNat 64 pn), ⟨Sf, hres⟩⟩

#print axioms envDefineScanned

/-! ## 6. The update lane (hit) -/

private theorem updateIdx3 (idx : Nat) :
    (BitVec.ofNat 64 idx <<< 1) + BitVec.ofNat 64 idx = BitVec.ofNat 64 (3 * idx) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

private theorem updateIdx24 (idx : Nat) :
    BitVec.ofNat 64 (3 * idx) <<< 3 = BitVec.ofNat 64 (24 * idx) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

private theorem updateStride (idx : Nat) (h : 24 * idx < 2^64) :
    shift_bits_left
        (shift_bits_left (BitVec.ofNat 64 idx)
          (Sail.BitVec.extractLsb (1#6) 5 0) + BitVec.ofNat 64 idx)
        (Sail.BitVec.extractLsb (3#6) 5 0) =
      BitVec.ofNat 64 (24 * idx) := by
  apply BitVec.eq_of_toNat_eq
  rw [update_a4_stride (BitVec.ofNat 64 idx) idx (by rw [BitVec.toNat_ofNat]; omega) h]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The update lane, with the return residuals.**  When `x` is already bound in
the frame at `env`, the helper runs from the contract entry to the return core:
prologue seg ≫ landed scan (first hit, output-carrying frame) ≫ keep-set-framed
exact update (`envDefineUpdateFromHitKeep_of_heap_owned`) ≫ keep-set-framed
epilogue (`EnvDefineUpdatePost.restoreKeep`), with the semantic advance
(`StoreDefineAdvance`) rebuilt at the epilogue's unchanged memory.  The three
`EnvDefineReturnResiduals` come off the scan frame (`out`, the `x3`/`x4`/`x23`–`x27`
ghost) and the hit's `a0`, transported by `KeepGhost`. -/
theorem envDefineUpdateLaneKeep
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hhit : ∀ (_h : env < st.store.frames.size), x ∈ st.store.frames[env].vars.map Prod.fst) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (fun c => EnvDefineReturnCore g N A SL φf φc st env x v esp r m c ∧
        EnvDefineReturnResiduals g out c) := by
  intro c h
  have hhit' : ∀ (h : env < st.store.frames.size), ∃ j, ∃ hj : j < st.store.frames[env].vars.length,
      (st.store.frames[env].vars[j]'hj).1 = x := by
    intro hl
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp (hhit hl)
    obtain ⟨j, hj, hjp⟩ := List.mem_iff_getElem.mp hp
    exact ⟨j, hj, by rw [hjp]; exact hpx⟩
  have hpos : ∀ (h : env < st.store.frames.size), 0 < st.store.frames[env].vars.length := by
    intro hl
    obtain ⟨j, hj, _⟩ := hhit' hl
    omega
  obtain ⟨c2, hs2, v8, v9, v18, v19, v20, v21, v22, pn, gm, S⟩ :=
    envDefineScanned g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O hpos c h
  have F := h.facts
  have Sf := S.facts
  have henvLt := Sf.env_lt
  rcases S.result with ⟨i, hi, _, hmatch, cmp, hlive, hsaved, hframe⟩ | ⟨hall, _⟩
  case inr =>
    exfalso
    obtain ⟨j, hj, hjx⟩ := hhit' henvLt
    exact hall j hj hjx
  have hsp1 := F.stack.1
  have hsp2 := F.stack.2.1
  have hsp3 := F.stack.2.2
  have hramLo := F.stack_ram.1
  have hramHi := F.stack_ram.2
  have hwin := F.stack_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have h64 : 64 ≤ esp.toNat := by omega
  have hsp64 : (esp - 64#64).toNat = esp.toNat - 64 := sp_sub64_toNat esp h64
  have hAlo := O.arena_ram.1
  have hAhi := O.arena_ram.2
  have hAhtif := O.arena_htif
  have hAstack := F.arena_stack
  have hpvNat := F.pv_frame
  have hslotStack := O.slot_in_stack
  have henvNat := Sf.env_addr
  obtain ⟨henvArena, henvAlign⟩ := F.store.frames_arena env henvLt
  unfold Arena.contains at henvArena
  have hget : st.store.frames[env]? = some st.store.frames[env] :=
    Array.getElem?_eq_some_iff.mpr ⟨henvLt, rfl⟩
  have hAg : AgreeP (fun a => a < esp.toNat - 64 ∨ esp.toNat ≤ a) m
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    fun a ha => (Sf.mem_agree a ha).symm
  have harenaOut : ∀ k, A.lo ≤ k → k < A.hi → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk1 hk2
    rcases hAstack with hA | hA
    · left; omega
    · right; omega
  -- the target frame's values array
  obtain ⟨_, ⟨cap, hcap, hcaple⟩, ⟨pn', vals, hpn', hvals, _⟩, _⟩ := Sf.store0.frames env henvLt
  obtain ⟨alloc, shared, readable, writes, hheap, hstackW, hvalO, hnameO⟩ := Sf.owned0
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  have hvalsEq : arr.values = vals := Option.some.inj (harr.valuesRead.symm.trans hvals)
  have hcapEq : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans hcap)
  have hvalsMem : (vals, 24 * cap) ∈ exts := by
    have := hheap.ledger.live _ _ _ (harr.values.nonempty (by omega))
    rwa [hvalsEq, hcapEq] at this
  obtain ⟨_, hvalsLo, hvalsHi⟩ := hheap.ledger.arena.1 _ hvalsMem
  simp only at hvalsLo hvalsHi
  have hvalsM : read64 m (φf env + 16) = some vals :=
    (read64_agreeP hAg (fun k hk => harenaOut _ (by omega) (by omega))).trans hvals
  have hvalsAlign : vals % 8 = 0 := O.arrays_aligned vals hvalsM
  have h24 : 24 * i < 2^64 := by omega
  have hvalsNat : (BitVec.ofNat 64 vals).toNat = vals := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdstNat : (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat = vals + 24 * i := by
    rw [BitVec.toNat_add, hvalsNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h24,
      Nat.mod_eq_of_lt (by omega)]
  have hdstBV : (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat =
      (BitVec.ofNat 64 vals).toNat + 24 * i := by
    rw [hvalsNat]; exact hdstNat
  have hgeomU : EnvDefineUpdateGeom aEnv pv (BitVec.ofNat 64 vals)
      (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)) i
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    { valsRead := by rw [henvNat, hvalsNat]; exact hvals
      envLo := by omega
      envHi := by omega
      envHtif := by right; omega
      envAlign := by omega
      srcLo := by omega
      srcHi := by omega
      srcHtif := by right; omega
      srcAlign := by omega
      dstEq := hdstBV
      idx3 := updateIdx3 i
      idx24 := updateIdx24 i
      strideCalc := updateStride i h24
      addrCalc := rfl
      dstLo := by rw [hdstNat]; omega
      dstHi := by rw [hdstNat]; omega
      dstHtif := by rw [hdstNat]; omega
      dstAlign := by rw [hdstNat]; omega }
  -- the hit's result register
  have hlive' := hlive
  obtain ⟨_, _, _, hregs2, _⟩ := hlive'
  have ha0_2 : gprGet c2.σ 10 = some cmp := gholds_lookup _ hregs2 (by rfl)
  -- the keep-set-framed exact update
  have hpayload : ValuePayloadCovered
      (fun a => a < (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat ∨
        (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat + 24 ≤ a)
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) pv.toNat v := by
    have hp := hfo.payloadOutsideSet hheap.immutable hi hvals hvalO
    simpa +unfoldPartialApp [SetOutside, hdstNat] using hp
  obtain ⟨c3, hs3, hp, hk3⟩ := envDefineUpdateFromHitKeep (envDefineSaved g r) aEnv
    aName pv (BitVec.ofNat 64 st.store.frames[env].vars.length)
    (BitVec.ofNat 64 pn + BitVec.ofNat 64 (8 * i)) (esp - 64#64)
    (BitVec.ofNat 64 vals) (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)) i _ N φc v A
    (fun R => c2.σ.regs.get? R) out Sf.code0 Sf.word0 hgeomU hpayload
    ⟨by rw [hdstNat]; omega, by rw [hdstNat]; omega⟩
    (by rcases hAstack with hA | hA
        · left; omega
        · right; omega)
    O.arena_code c2 ⟨⟨cmp, hlive, hsaved⟩, ⟨fun R _ => rfl, hframe.out⟩⟩
  -- the semantic advance at the epilogue's (unchanged) memory
  have hshell := StoreSetFootprint.target_of_runtime_owned (N := N) henvLt hi hvals hdstNat hheap
  have hframeFoot : EnvDefineUpdateFrameFootprint
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φf φc aEnv.toNat
      (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat st.store.frames[env] i := by
    rw [henvNat]
    exact ⟨hshell.header, hshell.nameSlots, hshell.names, hshell.otherValueHeaders,
      hshell.otherValueStrings⟩
  have hslot : ∀ pv', read64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
      (aEnv.toNat + 16) = some pv' →
      (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)).toNat = pv' + 24 * i := by
    intro pv' hpv'
    rw [henvNat] at hpv'
    rw [Option.some.inj (hpv'.symm.trans hvals)]
    exact hdstNat
  have hfrA : FrameRepr (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) N φf φc
      aEnv.toNat st.store.frames[env] := by
    rw [henvNat]; exact Sf.store0.frames env henvLt
  have hnew := envDefineUpdateFrameRepr (envDefineSaved g r) aEnv pv
    (BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * i)) (esp - 64#64) i _ N φf φc
    st.store.frames[env] x v c3 hp hfrA hi hmatch (O.unique henvLt) hslot hframeFoot
  rw [henvNat] at hnew
  have hwhole := StoreSetFootprint.of_runtime_owned (N := N) henvLt hi hvals hdstNat hheap
    hp.agree_outside
  have hadv : StoreDefineAdvance N A φf φc st.store env x v c3.σ.mem :=
    storeDefineAdvance_of_update Sf.store0 hget hnew hwhole
  -- the keep-set-framed epilogue
  obtain ⟨c4, hs4, hepi, hk4⟩ := hp.restoreKeep hk3
  obtain ⟨lds, _, _, _, _, hmemT⟩ := hp
  have hmem4 : c4.σ.mem = c3.σ.mem := hepi.mem
  have hmf : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
      c4.σ.mem[k]? = m[k]? := by
    intro k hkA hkS
    rw [hmem4, hmemT, updateValueTowerOutside _ _ _ _ _ _ (by rw [hdstNat]; omega)]
    exact Sf.mem_agree k (by omega)
  have hext4 : MemExtends m c4.σ.mem := by
    rw [hmem4, hmemT]
    unfold UpdateValueTower
    exact Sf.mem_extends.trans ((memExtends_writeMap8 _ _ _).trans
      ((memExtends_writeMap8 _ _ _).trans (memExtends_writeMap8 _ _ _)))
  have hstore4 : StoreRepr c4.σ.mem N A φf φc (st.store.define env x v) := by
    rw [hmem4]; exact hadv.toStoreRepr
  have hra_align := h.ra_align
  refine ⟨c4, hs2.trans (hs3.trans hs4), ?_, ?_⟩
  · exact
    { good := hepi.good
      tick := hepi.tick
      pc := by rw [hepi.pc, envDefineSaved_x1, Option.getD_some, bitvec_update_self r hra_align]
      ra := by rw [hepi.ra, envDefineSaved_x1]; rfl
      sp := by rw [hepi.spReg, BitVec.sub_add_cancel]
      minstret := hepi.good.minstret
      restored := by
        intro R hR
        simp only [EnvDefineRestored, Bool.or_eq_true, beq_iff_eq] at hR
        rcases hR with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
        · rw [hepi.s0, envDefineSaved_ne g r (by decide), Sf.s0]; rfl
        · rw [hepi.s1, envDefineSaved_ne g r (by decide), Sf.s1]; rfl
        · rw [hepi.s2, envDefineSaved_ne g r (by decide), Sf.s2]; rfl
        · rw [hepi.s3, envDefineSaved_ne g r (by decide), Sf.s3]; rfl
        · rw [hepi.s4, envDefineSaved_ne g r (by decide), Sf.s4]; rfl
        · rw [hepi.s5, envDefineSaved_ne g r (by decide), Sf.s5]; rfl
        · rw [hepi.s6, envDefineSaved_ne g r (by decide), Sf.s6]; rfl
      store := hstore4
      store_survives := fun m' hm' => O.define_survives c4.σ.mem hmf hstore4 m' hm'
      mem_frame := hmf
      mem_extends := hext4 }
  · exact
    { out := hk4.out
      rest := by
        intro R hR hRes h2
        obtain ⟨hkeep, hpk, h8, h9, h22⟩ := envDefineRest_facts R hR hRes h2
        refine (hk4.keep R hkeep).trans ?_
        show c2.σ.regs.get? R = g R
        rw [hframe.abi R hR, envDefineScanGhost_ne _ _ _ h8 h9]
        exact Sf.gm_keep R hpk h22
      a0 := ⟨cmp, by
        refine (hk4.keep Register.x10 (by decide)).trans ?_
        show c2.σ.regs.get? Register.x10 = some cmp
        simpa [gprGet] using ha0_2⟩ }

#print axioms envDefineUpdateLaneKeep

/-- **The update lane** (the return core alone; `envDefineUpdateLaneKeep` projected). -/
theorem envDefineUpdateLane
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hhit : ∀ (_h : env < st.store.frames.size), x ∈ st.store.frames[env].vars.map Prod.fst) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (EnvDefineReturnCore g N A SL φf φc st env x v esp r m) := by
  intro c h
  obtain ⟨c', hs, hcore, _⟩ :=
    envDefineUpdateLaneKeep g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O hhit c h
  exact ⟨c', hs, hcore⟩

#print axioms envDefineUpdateLane

/-! ## 7. The miss lane (exhaustive miss on a non-empty frame) -/

/-- The state at the append/grow cap dispatch after an exhaustive miss, with the
scanned-memory facts.  The append and grow lanes continue from `cap`
(`envDefineAppendEntry_of_cap`, `envDefineCapGrowRowFramed`). -/
structure EnvDefineMissReady (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
    (gm : (R : Register) → Option (RegisterType R)) (c : Config) : Prop where
  facts : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
    v8 v9 v18 v19 v20 v21 v22 pn gm
  miss : ∀ j (hj : j < (st.store.frames[env]'facts.env_lt).vars.length),
    ((st.store.frames[env]'facts.env_lt).vars[j]'hj).1 ≠ x
  cap : EnvDefineMissCapResult M exts out (envDefineSaved g r) gm aEnv
    (BitVec.ofNat 64 (st.store.frames[env]'facts.env_lt).vars.length) (BitVec.ofNat 64 pn)
    (esp - 64#64) (st.store.frames[env]'facts.env_lt)
    (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) c

/-- **The miss lane.**  When `x` is bound nowhere in the (non-empty) frame at
`env`, the helper runs from the contract entry to the cap dispatch
(`envDefineMissCapDispatch`): the append arm at `0x80002b1c` or the grow arm at
`0x80002b90`.  The empty-frame path (`blez` taken at `0x80002a90` to `0x80002bf4`)
is not a landed lane and is excluded by `hpos`. -/
theorem envDefineMissLane
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hmiss : ∀ (_h : env < st.store.frames.size), x ∉ st.store.frames[env].vars.map Prod.fst)
    (hpos : ∀ (h : env < st.store.frames.size), 0 < st.store.frames[env].vars.length) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (fun c => ∃ (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
        (gm : (R : Register) → Option (RegisterType R)),
        EnvDefineMissReady g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          v8 v9 v18 v19 v20 v21 v22 pn gm c) := by
  intro c h
  obtain ⟨c2, hs2, v8, v9, v18, v19, v20, v21, v22, pn, gm, S⟩ :=
    envDefineScanned g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O hpos c h
  have F := h.facts
  have Sf := S.facts
  have henvLt := Sf.env_lt
  have hmiss' : ∀ j (hj : j < st.store.frames[env].vars.length),
      (st.store.frames[env].vars[j]'hj).1 ≠ x := fun j hj hjx =>
    hmiss henvLt (List.mem_map.mpr ⟨_, List.getElem_mem hj, hjx⟩)
  rcases S.result with ⟨i, hi, _, hmatch, _⟩ | ⟨hall, i, hi1, cmp, hdone, hsaved, hframe⟩
  · exfalso
    exact hmiss' i hi hmatch
  have hAlo := O.arena_ram.1
  have hAhi := O.arena_ram.2
  have hAhtif := O.arena_htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨henvArena, henvAlign⟩ := F.store.frames_arena env henvLt
  have hlenNat : (BitVec.ofNat 64 st.store.frames[env].vars.length).toNat =
      st.store.frames[env].vars.length := by
    have := Sf.count_signed
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → M.AInv σa exts → M.AInv σb exts :=
    fun σa σb h1 h2 => O.ainv_stable σa σb h1 (fun a _ => h2 a)
  obtain ⟨_, ⟨cap, hcapR, hcaple⟩, _, _⟩ := Sf.store0.frames env henvLt
  obtain ⟨alloc, shared, readable, writes, hheap, _, _, _⟩ := Sf.owned0
  have hcapSigned : cap < 2^31 :=
    (hheap.store.frames env henvLt).capSigned hheap.ledger hcapR (by omega)
  obtain ⟨c3, hs3, hcap⟩ := envDefineMissCapDispatch M exts out (envDefineSaved g r) gm aEnv aName
    pv
    (BitVec.ofNat 64 st.store.frames[env].vars.length) (BitVec.ofNat 64 pn) (esp - 64#64)
    st.store.frames[env] x _ cap (by rw [Sf.env_addr]; exact hcapR) hcapSigned hcaple
    ⟨hAlo, hAhi, Or.inr (by omega)⟩ (by rw [Sf.env_addr]; exact henvArena)
    (by rw [Sf.env_addr]; exact henvAlign) hlenNat hAInvStable c2
    ⟨hall, i, hi1, cmp, hdone, hsaved, hframe⟩
  exact ⟨c3, hs2.trans hs3, v8, v9, v18, v19, v20, v21, v22, pn, gm, ⟨Sf, hmiss', hcap⟩⟩

#print axioms envDefineMissLane

/-- The contract's return state is the core plus the named residuals (a consumer
holding `EnvDefineReturnResiduals` at the reached config closes
`EnvDefineContract`'s post for this lane). -/
theorem envDefineUpdateLane_return
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hhit : ∀ (_h : env < st.store.frames.size), x ∈ st.store.frames[env].vars.map Prod.fst) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (fun c => EnvDefineReturnCore g N A SL φf φc st env x v esp r m c ∧
        (EnvDefineReturnResiduals g out c →
          EnvDefineReturnState g N A SL φf φc st env x v esp r m out c)) := by
  intro c h
  obtain ⟨c', hs, hcore⟩ :=
    envDefineUpdateLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O hhit c h
  exact ⟨c', hs, hcore, fun hres => hcore.toReturn ((h.frame _ (by decide)).symm.trans h.sp) hres⟩

/-- **The update lane closes the contract's return state** with no residual
hypothesis: the output, the untouched ABI frame and the `a0` presence are
discharged by `envDefineUpdateLaneKeep`. -/
theorem envDefineUpdateLane_full
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (O : EnvDefineUpdateOracles g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hhit : ∀ (_h : env < st.store.frames.size), x ∈ st.store.frames[env].vars.map Prod.fst) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c h
  obtain ⟨c', hs, hcore, hres⟩ :=
    envDefineUpdateLaneKeep g N A SL φf φc st env x v esp aEnv aName pv r m out M exts O hhit c h
  exact ⟨c', hs, hcore.toReturn ((h.frame _ (by decide)).symm.trans h.sp) hres⟩

/-- **The update lane from the entry facts and the ledger** (the oracles derived by
`EnvDefineUpdateOracles.of_entry`). -/
theorem envDefineUpdateLane_ledger
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hhit : ∀ (_h : env < st.store.frames.size), x ∈ st.store.frames[env].vars.map Prod.fst) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c h
  exact envDefineUpdateLane_full g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
    (EnvDefineUpdateOracles.of_entry h.facts L) hhit c h

#print axioms envDefinePrologueLog
#print axioms envDefinePrologueMem
#print axioms envDefineEpilogueTermFacts
#print axioms bitvec_update_self
#print axioms lpins4_of_agree
#print axioms PrologueKeep.abi
#print axioms valueHeapOwned_agreeP
#print axioms valuePayloadCovered_of_heapOwned
#print axioms envDefineSaved_x1
#print axioms envDefineSaved_ne
#print axioms envDefineUpdateLane_return
#print axioms envDefineUpdateLane_full
#print axioms envDefineUpdateLane_ledger
#print axioms envDefineRest_facts

end Vsa.Sim
