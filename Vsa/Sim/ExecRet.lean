import Vsa.Sim.ExecRecCommon
import Vsa.Sim.EnvGetSpec6

/-!
# Layer 4 — M4 statement `ExecS.ret` (value-present path)

The `ret` statement arm (kind 6, `0x80004120 → 0x8000416c`, value present). It
evaluates the return expression `e` to `v` (store may change to `st'`), copies
`v`'s 24-byte `Value` struct into the caller-provided `retslot` (`s2 = aRet`,
ABI arg 3), and completes with status `.ret v` — exercising `ExecExit.retval`,
the `retslot` disjunct.

```
80004120:  ld   a2,8(s0)      -- a2 := stmt->expr (the operand node; retSome ⇒ p ≠ 0)
80004124:  beqz a2,…          -- (NOT taken: value present, p ≠ 0)
80004128:  mv   a3,s3         -- a3 := env
8000412c:  mv   a1,s1         -- a1 := interp*
80004130:  addi a0,sp,16      -- a0 := sp'+16 (the local sub-sret buffer)
80004134:  jal  eval_expr     -- the sub-derivation (EvalIH), link 0x80004138
80004138:  ld   a3,16(sp)     -- reload v.word0 from the sub-sret buffer
8000413c:  ld   a4,24(sp)     -- reload v.word1
80004140:  ld   a5,32(sp)     -- reload v.word2
80004144:  sd   a3,0(s2)      -- *retslot[0]  := v.word0   (s2 = aRet)
80004148:  sd   a4,8(s2)      -- *retslot[8]  := v.word1
8000414c:  sd   a5,16(s2)     -- *retslot[16] := v.word2
80004150:  ld   ra,168(sp)    -- epilogue restores (interleaved with li a0,3)
80004154:  ld   s0,160(sp)
80004158:  ld   s1,152(sp)
8000415c:  ld   s2,144(sp)
80004160:  ld   s3,136(sp)
80004164:  li   a0,3          -- x10 := 3 = StatusCode (.ret v)
80004168:  addi sp,sp,176
8000416c:  ret
```

## Structure

`execRetSim` mirrors `execExprSim` (`ExecExprRet.lean`): the `execBlockA` head
(prologue+dispatch to `0x80004120`) and the copy+epilogue TAIL are threaded
UNCONDITIONALLY around the recursion glue `hGlue`, which consumes the `EvalIH`
for the return expression. The glue postcondition is `SubExecReturnR` —
`SubExecReturn` (`ExecExprRet.lean`) PLUS the three `read64` facts on the
sub-sret buffer (the honest "`eval_expr` fills the whole 24-byte result buffer"
residual, needed for the reload `ld`s; the abstract `ValueRepr` alone only pins
the kind tag). `execRetGlue` discharges `hGlue` via the `ret`-arm setup
(`ld a2,8(s0)`, `beqz` not-taken, `mv a3,s3`, `mv a1,s1`, `addi a0,sp,16`) +
`armTail_rec_es`, and `execRetSimC` is the full case conditional only on named
residuals (the `execBlockA` geometry + the concrete sub-expr/code/headroom facts
+ the sub-sret readability), exactly the residual style of `execExprSimC`.

The `retNull` constructor (`return;`, `.ret none`) is a SEPARATE `ExecS`
constructor (`ExecS.retNull`) and is left as a follow-up (it takes the `beqz`
TAKEN path through `value_null`, not covered here).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## `SubExecReturnR` — `SubExecReturn` + the sub-sret buffer readability

`SubExecReturn` re-represents `st'.store` and pins `ValueRepr … subsret vsub`,
but the three reload `ld`s at `0x80004138`/`0x8000413c`/`0x80004140` need the
buffer's three 8-byte words readable at the machine level. `ValueRepr` only pins
the 4-byte kind tag (and, per kind, the payload), not the full 24-byte struct;
so we carry the three `read64`s explicitly. (The concrete machine — `eval_expr`'s
sret write — does fill all 24 bytes; this is the abstraction's residual.) -/
def SubExecReturnR
    (garm : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (vsub : Value)
    (sp r aRet subsret retPC : BitVec 64) (v1 v8 v9 v18 v19 : BitVec 64)
    (m0 mcall : Mem)
    (c : Config) : Prop :=
  SubExecReturn garm N A SL φf φc st' vsub sp r aRet subsret retPC v1 v8 v9 v18 v19 m0 mcall c ∧
  -- the sub-sret buffer sits at the in-frame slot `sp' + 16 = sp - 160`
  -- (`armTail_rec_es` was invoked with `subsret := (sp-176)+16`):
  subsret.toNat = sp.toNat - 160 ∧
  (∃ w0 w1 w2 : Nat,
    read64 c.σ.mem subsret.toNat = some w0 ∧
    read64 c.σ.mem (subsret.toNat + 8) = some w1 ∧
    read64 c.σ.mem (subsret.toNat + 16) = some w2) ∧
  -- store re-representation tolerant of the retslot copy: the three `sd`s write
  -- only `[aRet, aRet+24)`; the represented `st'.store` lives in the arena
  -- (`aRet` disjoint from it), so it survives. (The analog of `EvalExitD`'s
  -- survival clause, restricted to the retslot window — SubExecReturn only carries
  -- the plain exit StoreRepr, which cannot be transported without arena facts.)
  (∃ φf' φc' : Addr → Nat,
    PhiExtends φf φf' st'.store.frames.size ∧
    PhiExtends φc φc' st'.store.closures.size ∧
    ∀ m' : Mem, (∀ k, (k < aRet.toNat ∨ aRet.toNat + 24 ≤ k) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store) ∧
  -- the returned value's string payload (if any) is disjoint from the retslot
  -- window, so the copied `ValueRepr` survives (`valueRepr_copy_of_writeWindow`).
  (∀ (p : Nat) (s : String), read64 c.σ.mem (subsret.toNat + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < aRet.toNat ∨ aRet.toNat + 24 ≤ p + k))

/-! ## `ExecRetSimGoal` — the `ExecS.ret` simulation Triple (packaged) -/
def ExecRetSimGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env (.ret (some e)) sp r aInterp aStmt aEnv aRet m0 c
      ∧ c.σ.sailOutput = out0)
    (ExecExit g N A SL φf φc st' (.ret v) sp r aRet m0)

/-! ## `execRetSim` — `ExecS.ret`: `execBlockA ≫ (jal eval_expr ≫ IH) ≫ copy ≫ epilogue`

The head (`execBlockA`, prologue+dispatch to `0x80004120`) and the 24-byte copy +
inline `li a0,3` epilogue TAIL are threaded UNCONDITIONALLY around the recursion
glue `hGlue` (which consumes the `EvalIH`). The `retval` disjunct is discharged
by `valueRepr_copy_of_writeWindow`: the three `sd`s write exactly
`[aRet, aRet+24)`, byte-for-byte copying the sub-result buffer where the
`ValueRepr vsub` lives. -/
theorem execRetSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env (.ret (some e)) st' (.ret v))
    (hIH : EvalIH st d env e st' v)
    (hslot : StmtSlotPinned 6 execArmRet m0)
    (htableStk : stmtJumpTableBase + 4 * 6 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 6)
    -- the retslot geometry (`s2 = aRet`, an 8-aligned 24-byte `Value` slot in RAM
    -- above HTIF, disjoint from the stack window — the `sd` store-region checks):
    (hRetAl : aRet.toNat % 8 = 0)
    (hRetLo : 0x80000000 ≤ aRet.toNat) (hRetHi : aRet.toNat + 24 ≤ 0x100000000)
    (hRetWin : tohostAddr + 16 ≤ aRet.toNat)
    (hRetStk : aRet.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRet.toNat)
    (_hRetArena : aRet.toNat + 24 ≤ A.lo ∨ A.hi ≤ aRet.toNat)
    -- the retslot is disjoint from the `exec_stmt` code region (for the `sd`s to
    -- leave `Exec_stmtLoaded` intact):
    (hRetCode : aRet.toNat + 24 ≤ execStmtEntry ∨ execStmtEnd ≤ aRet.toNat)
    -- the recursion glue: from the arm-entry state at `0x80004120` the setup +
    -- `jal eval_expr` + the sub-call (the `EvalIH`) reach `0x80004138` in a
    -- `SubExecReturnR` state (with `s2 = aRet` surviving and the 24-byte buffer
    -- readable). RESIDUAL, discharged by `execRetGlue`.
    (hGlue : EvalIH st d env e st' v →
      Triple
        (fun c => ∃ ment v8 v9 v18 v19,
          ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
            v8 v9 v18 v19 out0 m0 ment c)
        (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
          SubExecReturnR g N A SL φf φc st' v
            sp r aRet subsret (0x80004138#64) v1 v8 v9 v18 v19 m0 mcall c)) :
    ExecRetSimGoal g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0 out0 := by
  intro c hpre
  obtain ⟨he, hout0⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- kind read `read32 m0 aStmt = 6` from the `.ret (some e)` StmtRepr
  have hkind : read32 m0 aStmt.toNat = some 6 := by
    have := he.stmt; rw [he.mem] at this; cases this with
    | retSome h6 _ _ _ => exact h6
  -- ===== head: execBlockA (prologue + dispatch → arm entry 0x80004120) =====
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env (.ret (some e))
      sp r aInterp aStmt aEnv aRet execArmRet m0 out0 :=
    execBlockA g N A SL φf φc st d env (.ret (some e)) 6 execArmRet
      sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, hArmExists⟩ := hBlockA c ⟨he, hout0⟩
  -- ===== glue: arm setup + jal eval_expr + sub-call (the IH) → SubExecReturnR =====
  obtain ⟨cG, hstepsG, hGlueOut⟩ := hGlue hIH cA hArmExists
  obtain ⟨subsret, v1, v8, v9, v18, v19, mcall, hSubR⟩ := hGlueOut
  obtain ⟨hSub, hsubEq, ⟨w0, w1, w2, hrw0, hrw1, hrw2⟩,
    ⟨φfS, φcS, hpfS, hpcS, hstoreSurv⟩, hpayDisj⟩ := hSubR
  obtain ⟨hGG, htickG, hpcG, hraG, hspG, hs2G, ⟨vmiG, hmiG⟩, houtG, hframeG,
    hgx8, hgx9, hgx18, hgx19, hgx2, hvalG, hstoreG, hcodeG,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hsubWin, hmemframeG, hmemExtG, hmemPreG⟩ := hSub
  -- subsret geometry facts (from SubExecReturn: subsret ⊂ [SL.lo, sp))
  obtain ⟨hsubLo, hsubHi⟩ := hsubWin
  -- entry-frame geometry (from ExecEntry), reused for the epilogue restores.
  have hstackOK := he.stackOK
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp176 : 176 ≤ sp.toNat := by
    have := he.stack_win; have := he.stack_ram.1; omega
  have hraAl := he.ra_align
  -- `sp' = sp - 176`, so `sp' + {16,24,32}` are the three reload addresses and
  -- `sp' - {8,16,24,32,40}` the five restore slots; all in-frame RAM.
  have hspsub : (sp - 176#64).toNat = sp.toNat - 176 := by
    rw [BitVec.toNat_sub]
    have h176 : (176#64 : BitVec 64).toNat = 176 := by decide
    rw [h176]; have := sp.isLt; omega
  -- the reload addresses `sp' + {16,24,32}`:
  have hr16 : ((sp - 176#64) + sign_extend (m := 64) (0x010#12)).toNat = sp.toNat - 160 := by
    rw [BitVec.toNat_add, hspsub]
    have hv : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
    rw [hv]; have := sp.isLt; omega
  have hr24 : ((sp - 176#64) + sign_extend (m := 64) (0x018#12)).toNat = sp.toNat - 152 := by
    rw [BitVec.toNat_add, hspsub]
    have hv : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
    rw [hv]; have := sp.isLt; omega
  have hr32 : ((sp - 176#64) + sign_extend (m := 64) (0x020#12)).toNat = sp.toNat - 144 := by
    rw [BitVec.toNat_add, hspsub]
    have hv : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide
    rw [hv]; have := sp.isLt; omega
  -- the source words at subsret = sp-160, sp-152, sp-144 (via `hsubEq`):
  have hsw0 : read64 cG.σ.mem (sp.toNat - 160) = some w0 := by rw [← hsubEq]; exact hrw0
  have hsw1 : read64 cG.σ.mem (sp.toNat - 152) = some w1 := by
    rw [hsubEq] at hrw1; rw [show sp.toNat - 160 + 8 = sp.toNat - 152 by omega] at hrw1; exact hrw1
  have hsw2 : read64 cG.σ.mem (sp.toNat - 144) = some w2 := by
    rw [hsubEq] at hrw2; rw [show sp.toNat - 160 + 16 = sp.toNat - 144 by omega] at hrw2; exact hrw2
  -- reload-region facts: `sp-160` (= subsret) is in the stack window `[SL.lo, sp)`,
  -- 8-aligned (`sp % 16 = 0`), in RAM above HTIF; likewise `sp-152`, `sp-144`.
  have hSLsub : SL.lo ≤ sp.toNat - 160 := by rw [← hsubEq]; exact hsubLo
  have hSLhiRam : SL.hi ≤ 0x100000000 := he.stack_ram.2
  have hstackWin : (0x8001ad00 : Nat) + 16 ≤ SL.lo := by have := he.stack_win; rw [htoh] at this; exact this
  have hsub_al : (sp.toNat - 160) % 8 = 0 := by omega
  have hsub_al8 : (sp.toNat - 152) % 8 = 0 := by omega
  have hsub_al16 : (sp.toNat - 144) % 8 = 0 := by omega
  obtain ⟨a30,a31,a32,a33,a34,a35,a36,a37, ha30,ha31,ha32,ha33,ha34,ha35,ha36,ha37⟩ :=
    ld64_bytes cG.σ.mem (sp.toNat - 160) w0 hsw0
  obtain ⟨a40,a41,a42,a43,a44,a45,a46,a47, ha40,ha41,ha42,ha43,ha44,ha45,ha46,ha47⟩ :=
    ld64_bytes cG.σ.mem (sp.toNat - 152) w1 hsw1
  obtain ⟨a50,a51,a52,a53,a54,a55,a56,a57, ha50,ha51,ha52,ha53,ha54,ha55,ha56,ha57⟩ :=
    ld64_bytes cG.σ.mem (sp.toNat - 144) w2 hsw2
  -- x18 = s2 = aRet (the retslot), survives to here (from SubExecReturn.hs2G):
  have hpcG' : cG.σ.regs.get? Register.PC = some (0x80004138#64) := hpcG
  -- ============ 0x80004138: ld a3,16(sp) → x13 := w0 ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80004138_es cG.σ cG.tick cG.steps (0x80004138#64) vmiG (sp - 176#64)
      a30 a31 a32 a33 a34 a35 a36 a37 hGG hpcG' hmiG hspG hcodeG rfl
      (by rw [hr16]; omega) (by rw [hr16]; omega)
      (by rw [hr16, htoh]; right; omega) (by rw [hr16]; exact hsub_al)
      (by rw [hr16]; exact ha30) (by rw [hr16]; exact ha31) (by rw [hr16]; exact ha32)
      (by rw [hr16]; exact ha33) (by rw [hr16]; exact ha34) (by rw [hr16]; exact ha35)
      (by rw [hr16]; exact ha36) (by rw [hr16]; exact ha37) htickG
  have hstep1 : Step cG ⟨σ1, i1, cG.steps + 1⟩ := by cases cG; exact hstep1'
  have hmem1e : σ1.mem = cG.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000413c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80004138#64) 4 = (0x8000413c#64 : BitVec 64) from by decide] at this
  have hw0val : (sign_extend (m := 64) ((((((((a37.append a36).append a35).append a34).append a33).append a32).append a31).append a30) : BitVec (8 * 8)) : BitVec 64) =
      BitVec.ofNat 64 w0 :=
    ld_value_eq_read64 cG.σ.mem (sp.toNat - 160) w0 a30 a31 a32 a33 a34 a35 a36 a37 hsw0 ha30 ha31 ha32 ha33 ha34 ha35 ha36 ha37
  have hx13_1 : σ1.regs.get? Register.x13 = some (BitVec.ofNat 64 w0) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hw0val] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspG
  have hs2_1 : σ1.regs.get? Register.x18 = some aRet := obs_alu_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2G
  have hra_1 : σ1.regs.get? Register.x1 = some (0x80004138#64) := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hraG
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcodeG
  have hsw1_1 : read64 σ1.mem (sp.toNat - 152) = some w1 := by rw [hmem1e]; exact hsw1
  have hsw2_1 : read64 σ1.mem (sp.toNat - 144) = some w2 := by rw [hmem1e]; exact hsw2
  -- ============ 0x8000413c: ld a4,24(sp) → x14 := w1 ============
  obtain ⟨a40',a41',a42',a43',a44',a45',a46',a47', hb40,hb41,hb42,hb43,hb44,hb45,hb46,hb47⟩ :=
    ld64_bytes σ1.mem (sp.toNat - 152) w1 hsw1_1
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_8000413c_es σ1 i1 (cG.steps + 1) (0x8000413c#64) vmi1 (sp - 176#64)
      a40' a41' a42' a43' a44' a45' a46' a47' hG1 hpc1 hmi1 hsp_1 hcode1 rfl
      (by rw [hr24]; omega) (by rw [hr24]; omega)
      (by rw [hr24, htoh]; right; omega) (by rw [hr24]; exact hsub_al8)
      (by rw [hr24]; exact hb40) (by rw [hr24]; exact hb41) (by rw [hr24]; exact hb42)
      (by rw [hr24]; exact hb43) (by rw [hr24]; exact hb44) (by rw [hr24]; exact hb45)
      (by rw [hr24]; exact hb46) (by rw [hr24]; exact hb47) hi1
  have hstep2 : Step ⟨σ1, i1, cG.steps + 1⟩ ⟨σ2, i2, cG.steps + 1 + 1⟩ := hstep2'
  have hmem2e : σ2.mem = cG.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80004140#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000413c#64) 4 = (0x80004140#64 : BitVec 64) from by decide] at this
  have hw1val : (sign_extend (m := 64) ((((((((a47'.append a46').append a45').append a44').append a43').append a42').append a41').append a40') : BitVec (8 * 8)) : BitVec 64) =
      BitVec.ofNat 64 w1 :=
    ld_value_eq_read64 σ1.mem (sp.toNat - 152) w1 a40' a41' a42' a43' a44' a45' a46' a47' hsw1_1 hb40 hb41 hb42 hb43 hb44 hb45 hb46 hb47
  have hx14_2 : σ2.regs.get? Register.x14 = some (BitVec.ofNat 64 w1) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hw1val] at this
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hs2_2 : σ2.regs.get? Register.x18 = some aRet := obs_alu_other hobs2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2_1
  have hx13_2 : σ2.regs.get? Register.x13 = some (BitVec.ofNat 64 w0) := obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
  have hra_2 : σ2.regs.get? Register.x1 = some (0x80004138#64) := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcodeG
  have hsw2_2 : read64 σ2.mem (sp.toNat - 144) = some w2 := by rw [hmem2e]; exact hsw2
  -- ============ 0x80004140: ld a5,32(sp) → x15 := w2 ============
  obtain ⟨a50',a51',a52',a53',a54',a55',a56',a57', hc50,hc51,hc52,hc53,hc54,hc55,hc56,hc57⟩ :=
    ld64_bytes σ2.mem (sp.toNat - 144) w2 hsw2_2
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80004140_es σ2 i2 (cG.steps + 1 + 1) (0x80004140#64) vmi2 (sp - 176#64)
      a50' a51' a52' a53' a54' a55' a56' a57' hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [hr32]; omega) (by rw [hr32]; omega)
      (by rw [hr32, htoh]; right; omega) (by rw [hr32]; exact hsub_al16)
      (by rw [hr32]; exact hc50) (by rw [hr32]; exact hc51) (by rw [hr32]; exact hc52)
      (by rw [hr32]; exact hc53) (by rw [hr32]; exact hc54) (by rw [hr32]; exact hc55)
      (by rw [hr32]; exact hc56) (by rw [hr32]; exact hc57) hi2
  have hstep3 : Step ⟨σ2, i2, cG.steps + 1 + 1⟩ ⟨σ3, i3, cG.steps + 1 + 1 + 1⟩ := hstep3'
  have hmem3e : σ3.mem = cG.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80004144#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80004140#64) 4 = (0x80004144#64 : BitVec 64) from by decide] at this
  have hw2val : (sign_extend (m := 64) ((((((((a57'.append a56').append a55').append a54').append a53').append a52').append a51').append a50') : BitVec (8 * 8)) : BitVec 64) =
      BitVec.ofNat 64 w2 :=
    ld_value_eq_read64 σ2.mem (sp.toNat - 144) w2 a50' a51' a52' a53' a54' a55' a56' a57' hsw2_2 hc50 hc51 hc52 hc53 hc54 hc55 hc56 hc57
  have hx15_3 : σ3.regs.get? Register.x15 = some (BitVec.ofNat 64 w2) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hw2val] at this
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have hs2_3 : σ3.regs.get? Register.x18 = some aRet := obs_alu_other hobs3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2_2
  have hx13_3 : σ3.regs.get? Register.x13 = some (BitVec.ofNat 64 w0) := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
  have hx14_3 : σ3.regs.get? Register.x14 = some (BitVec.ofNat 64 w1) := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hra_3 : σ3.regs.get? Register.x1 = some (0x80004138#64) := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcodeG
  -- store-address helpers: aRet + {0,8,16}
  have hst0 : (aRet + sign_extend (m := 64) (0x000#12)).toNat = aRet.toNat := by
    rw [BitVec.toNat_add]
    have hv : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
    rw [hv]; have := aRet.isLt; omega
  have hst8 : (aRet + sign_extend (m := 64) (0x008#12)).toNat = aRet.toNat + 8 := by
    rw [BitVec.toNat_add]
    have hv : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aRet.isLt; omega
  have hst16 : (aRet + sign_extend (m := 64) (0x010#12)).toNat = aRet.toNat + 16 := by
    rw [BitVec.toNat_add]
    have hv : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
    rw [hv]; have := aRet.isLt; omega
  -- ============ 0x80004144: sd a3,0(s2) → *aRet[0..8) := w0 ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80004144_es σ3 i3 (cG.steps + 1 + 1 + 1) (0x80004144#64) vmi3 aRet (BitVec.ofNat 64 w0)
      hG3 hpc3 hmi3 hs2_3 hx13_3 hcode3 rfl
      (by rw [hst0]; omega) (by rw [hst0]; omega) (by rw [hst0]; omega) (by rw [hst0]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, cG.steps + 1 + 1 + 1⟩ ⟨σ4, i4, cG.steps + 1 + 1 + 1 + 1⟩ := hstep4'
  have hm4def : σ4.mem = writeMap8 cG.σ.mem aRet.toNat (sdData_val (BitVec.ofNat 64 w0)) := by
    rw [hmem4, mem_afterNextPC, mem_afterPrelude, hmem3e, hst0]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004148#64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80004144#64) 4 = (0x80004148#64 : BitVec 64) from by decide] at this
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 176#64) := obs_store_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have hs2_4 : σ4.regs.get? Register.x18 = some aRet := obs_store_other hobs4 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2_3
  have hx14_4 : σ4.regs.get? Register.x14 = some (BitVec.ofNat 64 w1) := obs_store_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hx15_4 : σ4.regs.get? Register.x15 = some (BitVec.ofNat 64 w2) := obs_store_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_3
  have hra_4 : σ4.regs.get? Register.x1 = some (0x80004138#64) := obs_store_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hcode4 : Exec_stmtLoaded σ4.mem := by
    rw [hm4def]
    exact loaded_exec_stmt_writeMap8 cG.σ.mem aRet.toNat _
      (by rcases hRetCode with h | h <;> simp only [execStmtEntry, execStmtEnd] at h ⊢ <;> omega) hcodeG
  -- ============ 0x80004148: sd a4,8(s2) → *aRet[8..16) := w1 ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_80004148_es σ4 i4 (cG.steps + 1 + 1 + 1 + 1) (0x80004148#64) vmi4 aRet (BitVec.ofNat 64 w1)
      hG4 hpc4 hmi4 hs2_4 hx14_4 hcode4 rfl
      (by rw [hst8]; omega) (by rw [hst8]; omega) (by rw [hst8, htoh]; omega) (by rw [hst8]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, cG.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, cG.steps + 1 + 1 + 1 + 1 + 1⟩ := hstep5'
  have hm5def : σ5.mem = writeMap8 σ4.mem (aRet.toNat + 8) (sdData_val (BitVec.ofNat 64 w1)) := by
    rw [hmem5, mem_afterNextPC, mem_afterPrelude, hst8]
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000414c#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80004148#64) 4 = (0x8000414c#64 : BitVec 64) from by decide] at this
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 176#64) := obs_store_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have hs2_5 : σ5.regs.get? Register.x18 = some aRet := obs_store_other hobs5 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2_4
  have hx15_5 : σ5.regs.get? Register.x15 = some (BitVec.ofNat 64 w2) := obs_store_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_4
  have hra_5 : σ5.regs.get? Register.x1 = some (0x80004138#64) := obs_store_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hcode5 : Exec_stmtLoaded σ5.mem := by
    rw [hm5def]
    exact loaded_exec_stmt_writeMap8 σ4.mem (aRet.toNat + 8) _
      (by rcases hRetCode with h | h <;> simp only [execStmtEntry, execStmtEnd] at h ⊢ <;> omega) hcode4
  -- ============ 0x8000414c: sd a5,16(s2) → *aRet[16..24) := w2 ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_8000414c_es σ5 i5 (cG.steps + 1 + 1 + 1 + 1 + 1) (0x8000414c#64) vmi5 aRet (BitVec.ofNat 64 w2)
      hG5 hpc5 hmi5 hs2_5 hx15_5 hcode5 rfl
      (by rw [hst16]; omega) (by rw [hst16]; omega) (by rw [hst16, htoh]; omega) (by rw [hst16]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, cG.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, cG.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep6'
  have hm6def : σ6.mem = writeMap8 σ5.mem (aRet.toNat + 16) (sdData_val (BitVec.ofNat 64 w2)) := by
    rw [hmem6, mem_afterNextPC, mem_afterPrelude, hst16]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80004150#64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x8000414c#64) 4 = (0x80004150#64 : BitVec 64) from by decide] at this
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 176#64) := obs_store_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_5
  have hra_6 : σ6.regs.get? Register.x1 = some (0x80004138#64) := obs_store_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hcode6 : Exec_stmtLoaded σ6.mem := by
    rw [hm6def]
    exact loaded_exec_stmt_writeMap8 σ5.mem (aRet.toNat + 16) _
      (by rcases hRetCode with h | h <;> simp only [execStmtEntry, execStmtEnd] at h ⊢ <;> omega) hcode5
  -- final memory after the three copy stores
  have hm6full : σ6.mem = writeMap8 (writeMap8 (writeMap8 cG.σ.mem aRet.toNat (sdData_val (BitVec.ofNat 64 w0)))
      (aRet.toNat + 8) (sdData_val (BitVec.ofNat 64 w1))) (aRet.toNat + 16) (sdData_val (BitVec.ofNat 64 w2)) := by
    rw [hm6def, hm5def, hm4def]
  -- any 8-byte read disjoint from `[aRet, aRet+24)` passes σ6.mem → cG.σ.mem
  have read64_final_disjoint : ∀ a : Nat, a + 8 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ a →
      read64 σ6.mem a = read64 cG.σ.mem a := by
    intro a ha
    rw [hm6full,
        read64_writeMap8_disjoint_ee _ _ _ _ (by rcases ha with h | h <;> omega),
        read64_writeMap8_disjoint_ee _ _ _ _ (by rcases ha with h | h <;> omega),
        read64_writeMap8_disjoint_ee _ _ _ _ (by rcases ha with h | h <;> omega)]
  -- byte-level agreement outside `[aRet, aRet+24)` (for the exit memFrame + ValueRepr)
  have houtside6 : ∀ a : Nat, a < aRet.toNat ∨ aRet.toNat + 24 ≤ a → σ6.mem[a]? = cG.σ.mem[a]? := by
    intro a ha
    rw [hm6full,
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega),
        getElem_writeMap8_disjoint _ _ _ _ (by rcases ha with h | h <;> omega)]
  -- the five spill slots survive into σ6.mem (each disjoint from [aRet, aRet+24)):
  -- spills live at sp-{8,16,24,32,40} ⊂ [SL.lo, sp); aRet is stack-disjoint (hRetStk).
  have hslotDisj : ∀ k : Nat, sp.toNat - 40 ≤ k → k + 8 ≤ sp.toNat →
      k + 8 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ k := by
    intro k h1 h2
    rcases hRetStk with h | h
    · right; omega
    · left; omega
  have hslotRa6 : read64 σ6.mem (sp.toNat - 8) = some r.toNat := by
    rw [read64_final_disjoint _ (hslotDisj (sp.toNat - 8) (by omega) (by omega))]; exact hslotRa
  have hslotS06 : read64 σ6.mem (sp.toNat - 16) = some v8.toNat := by
    rw [read64_final_disjoint _ (hslotDisj (sp.toNat - 16) (by omega) (by omega))]; exact hslotS0
  have hslotS16 : read64 σ6.mem (sp.toNat - 24) = some v9.toNat := by
    rw [read64_final_disjoint _ (hslotDisj (sp.toNat - 24) (by omega) (by omega))]; exact hslotS1
  have hslotS26 : read64 σ6.mem (sp.toNat - 32) = some v18.toNat := by
    rw [read64_final_disjoint _ (hslotDisj (sp.toNat - 32) (by omega) (by omega))]; exact hslotS2
  have hslotS36 : read64 σ6.mem (sp.toNat - 40) = some v19.toNat := by
    rw [read64_final_disjoint _ (hslotDisj (sp.toNat - 40) (by omega) (by omega))]; exact hslotS3
  -- restore-slot addresses `sp' + {168,160,152,144,136} = sp - {8,16,24,32,40}`
  have haRa : ((sp - 176#64) + sign_extend (m := 64) (0x0a8#12)).toNat = sp.toNat - 8 := es_off168 sp hsp176
  have haS0 : ((sp - 176#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 16 := es_off160 sp hsp176
  have haS1 : ((sp - 176#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 24 := es_off152 sp hsp176
  have haS2 : ((sp - 176#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 32 := es_off144 sp hsp176
  have haS3 : ((sp - 176#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 40 := es_off136 sp hsp176
  obtain ⟨ra0,ra1,ra2,ra3,ra4,ra5,ra6,ra7, hra0,hra1,hra2,hra3,hra4,hra5,hra6,hra7⟩ :=
    ld64_bytes σ6.mem (sp.toNat - 8) r.toNat hslotRa6
  obtain ⟨t00,t01,t02,t03,t04,t05,t06,t07, ht00,ht01,ht02,ht03,ht04,ht05,ht06,ht07⟩ :=
    ld64_bytes σ6.mem (sp.toNat - 16) v8.toNat hslotS06
  obtain ⟨t10,t11,t12,t13,t14,t15,t16,t17, ht10,ht11,ht12,ht13,ht14,ht15,ht16,ht17⟩ :=
    ld64_bytes σ6.mem (sp.toNat - 24) v9.toNat hslotS16
  obtain ⟨t20,t21,t22,t23,t24,t25,t26,t27, ht20,ht21,ht22,ht23,ht24,ht25,ht26,ht27⟩ :=
    ld64_bytes σ6.mem (sp.toNat - 32) v18.toNat hslotS26
  obtain ⟨t30,t31,t32,t33,t34,t35,t36,t37, ht30,ht31,ht32,ht33,ht34,ht35,ht36,ht37⟩ :=
    ld64_bytes σ6.mem (sp.toNat - 40) v19.toNat hslotS36
  -- ld value round-trips (the loaded sign_extend byte-octet equals the toNat word)
  have hraVal : (sign_extend (m := 64) ((((((((ra7.append ra6).append ra5).append ra4).append ra3).append ra2).append ra1).append ra0) : BitVec (8 * 8)) : BitVec 64) = r := by
    have := ld_value_eq_read64 σ6.mem (sp.toNat - 8) r.toNat ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 hslotRa6 hra0 hra1 hra2 hra3 hra4 hra5 hra6 hra7
    rw [this]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := r.isLt; omega
  have hs0Val : (sign_extend (m := 64) ((((((((t07.append t06).append t05).append t04).append t03).append t02).append t01).append t00) : BitVec (8 * 8)) : BitVec 64) = v8 := by
    have := ld_value_eq_read64 σ6.mem (sp.toNat - 16) v8.toNat t00 t01 t02 t03 t04 t05 t06 t07 hslotS06 ht00 ht01 ht02 ht03 ht04 ht05 ht06 ht07
    rw [this]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := v8.isLt; omega
  have hs1Val : (sign_extend (m := 64) ((((((((t17.append t16).append t15).append t14).append t13).append t12).append t11).append t10) : BitVec (8 * 8)) : BitVec 64) = v9 := by
    have := ld_value_eq_read64 σ6.mem (sp.toNat - 24) v9.toNat t10 t11 t12 t13 t14 t15 t16 t17 hslotS16 ht10 ht11 ht12 ht13 ht14 ht15 ht16 ht17
    rw [this]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := v9.isLt; omega
  have hs2Val : (sign_extend (m := 64) ((((((((t27.append t26).append t25).append t24).append t23).append t22).append t21).append t20) : BitVec (8 * 8)) : BitVec 64) = v18 := by
    have := ld_value_eq_read64 σ6.mem (sp.toNat - 32) v18.toNat t20 t21 t22 t23 t24 t25 t26 t27 hslotS26 ht20 ht21 ht22 ht23 ht24 ht25 ht26 ht27
    rw [this]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := v18.isLt; omega
  have hs3Val : (sign_extend (m := 64) ((((((((t37.append t36).append t35).append t34).append t33).append t32).append t31).append t30) : BitVec (8 * 8)) : BitVec 64) = v19 := by
    have := ld_value_eq_read64 σ6.mem (sp.toNat - 40) v19.toNat t30 t31 t32 t33 t34 t35 t36 t37 hslotS36 ht30 ht31 ht32 ht33 ht34 ht35 ht36 ht37
    rw [this]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := v19.isLt; omega
  -- ============ 0x80004150: ld ra,168(sp) → x1 := r ============
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80004150_es σ6 i6 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80004150#64) vmi6 (sp - 176#64)
      ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 hG6 hpc6 hmi6 hsp_6 hcode6 rfl
      (by rw [haRa]; omega) (by rw [haRa]; omega) (by rw [haRa, htoh]; right; omega) (by rw [haRa]; omega)
      (by rw [haRa]; exact hra0) (by rw [haRa]; exact hra1) (by rw [haRa]; exact hra2)
      (by rw [haRa]; exact hra3) (by rw [haRa]; exact hra4) (by rw [haRa]; exact hra5)
      (by rw [haRa]; exact hra6) (by rw [haRa]; exact hra7) hi6
  have hstep7 : Step ⟨σ6, i6, cG.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep7'
  have hmem7e : σ7.mem = σ6.mem := hmem7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80004154#64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80004150#64) 4 = (0x80004154#64:BitVec 64) from by decide] at this
  have hra_7 : σ7.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hraVal] at this
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hcode7 : Exec_stmtLoaded σ7.mem := by rw [hmem7e]; exact hcode6
  -- ============ 0x80004154: ld s0,160(sp) → x8 := v8 ============
  obtain ⟨σ8, i8, hstep8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80004154_es σ7 i7 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80004154#64) vmi7 (sp - 176#64)
      t00 t01 t02 t03 t04 t05 t06 t07 hG7 hpc7 hmi7 hsp_7 hcode7 rfl
      (by rw [haS0]; omega) (by rw [haS0]; omega) (by rw [haS0, htoh]; right; omega) (by rw [haS0]; omega)
      (by rw [haS0, hmem7e]; exact ht00) (by rw [haS0, hmem7e]; exact ht01) (by rw [haS0, hmem7e]; exact ht02)
      (by rw [haS0, hmem7e]; exact ht03) (by rw [haS0, hmem7e]; exact ht04) (by rw [haS0, hmem7e]; exact ht05)
      (by rw [haS0, hmem7e]; exact ht06) (by rw [haS0, hmem7e]; exact ht07) hi7
  have hstep8 : Step ⟨σ7, i7, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep8'
  have hmem8e : σ8.mem = σ6.mem := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (0x80004158#64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80004154#64) 4 = (0x80004158#64:BitVec 64) from by decide] at this
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs0Val] at this
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hcode8 : Exec_stmtLoaded σ8.mem := by rw [hmem8e]; exact hcode6
  -- ============ 0x80004158: ld s1,152(sp) → x9 := v9 ============
  obtain ⟨σ9, i9, hstep9', hi9, hG9, hmem9, hobs9⟩ :=
    site_80004158_es σ8 i8 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80004158#64) vmi8 (sp - 176#64)
      t10 t11 t12 t13 t14 t15 t16 t17 hG8 hpc8 hmi8 hsp_8 hcode8 rfl
      (by rw [haS1]; omega) (by rw [haS1]; omega) (by rw [haS1, htoh]; right; omega) (by rw [haS1]; omega)
      (by rw [haS1, hmem8e]; exact ht10) (by rw [haS1, hmem8e]; exact ht11) (by rw [haS1, hmem8e]; exact ht12)
      (by rw [haS1, hmem8e]; exact ht13) (by rw [haS1, hmem8e]; exact ht14) (by rw [haS1, hmem8e]; exact ht15)
      (by rw [haS1, hmem8e]; exact ht16) (by rw [haS1, hmem8e]; exact ht17) hi8
  have hstep9 : Step ⟨σ8, i8, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep9'
  have hmem9e : σ9.mem = σ6.mem := by rw [hmem9]; exact hmem8e
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000415c#64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80004158#64) 4 = (0x8000415c#64:BitVec 64) from by decide] at this
  have hx9_9 : σ9.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs1Val] at this
  have hra_9 : σ9.regs.get? Register.x1 = some r := obs_alu_other hobs9 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_8
  have hx8_9 : σ9.regs.get? Register.x8 = some v8 := obs_alu_other hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hcode9 : Exec_stmtLoaded σ9.mem := by rw [hmem9e]; exact hcode6
  -- ============ 0x8000415c: ld s2,144(sp) → x18 := v18 ============
  obtain ⟨σ10, i10, hstep10', hi10, hG10, hmem10, hobs10⟩ :=
    site_8000415c_es σ9 i9 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000415c#64) vmi9 (sp - 176#64)
      t20 t21 t22 t23 t24 t25 t26 t27 hG9 hpc9 hmi9 hsp_9 hcode9 rfl
      (by rw [haS2]; omega) (by rw [haS2]; omega) (by rw [haS2, htoh]; right; omega) (by rw [haS2]; omega)
      (by rw [haS2, hmem9e]; exact ht20) (by rw [haS2, hmem9e]; exact ht21) (by rw [haS2, hmem9e]; exact ht22)
      (by rw [haS2, hmem9e]; exact ht23) (by rw [haS2, hmem9e]; exact ht24) (by rw [haS2, hmem9e]; exact ht25)
      (by rw [haS2, hmem9e]; exact ht26) (by rw [haS2, hmem9e]; exact ht27) hi9
  have hstep10 : Step ⟨σ9, i9, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep10'
  have hmem10e : σ10.mem = σ6.mem := by rw [hmem10]; exact hmem9e
  have hpc10 : σ10.regs.get? Register.PC = some (0x80004160#64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x8000415c#64) 4 = (0x80004160#64:BitVec 64) from by decide] at this
  have hx18_10 : σ10.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs2Val] at this
  have hra_10 : σ10.regs.get? Register.x1 = some r := obs_alu_other hobs10 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_9
  have hx8_10 : σ10.regs.get? Register.x8 = some v8 := obs_alu_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_9
  have hx9_10 : σ10.regs.get? Register.x9 = some v9 := obs_alu_other hobs10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hcode10 : Exec_stmtLoaded σ10.mem := by rw [hmem10e]; exact hcode6
  -- ============ 0x80004160: ld s3,136(sp) → x19 := v19 ============
  obtain ⟨σ11, i11, hstep11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80004160_es σ10 i10 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80004160#64) vmi10 (sp - 176#64)
      t30 t31 t32 t33 t34 t35 t36 t37 hG10 hpc10 hmi10 hsp_10 hcode10 rfl
      (by rw [haS3]; omega) (by rw [haS3]; omega) (by rw [haS3, htoh]; right; omega) (by rw [haS3]; omega)
      (by rw [haS3, hmem10e]; exact ht30) (by rw [haS3, hmem10e]; exact ht31) (by rw [haS3, hmem10e]; exact ht32)
      (by rw [haS3, hmem10e]; exact ht33) (by rw [haS3, hmem10e]; exact ht34) (by rw [haS3, hmem10e]; exact ht35)
      (by rw [haS3, hmem10e]; exact ht36) (by rw [haS3, hmem10e]; exact ht37) hi10
  have hstep11 : Step ⟨σ10, i10, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ11, i11, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep11'
  have hmem11e : σ11.mem = σ6.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80004164#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80004160#64) 4 = (0x80004164#64:BitVec 64) from by decide] at this
  have hx19_11 : σ11.regs.get? Register.x19 = some v19 := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs3Val] at this
  have hra_11 : σ11.regs.get? Register.x1 = some r := obs_alu_other hobs11 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_10
  have hx8_11 : σ11.regs.get? Register.x8 = some v8 := obs_alu_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_10
  have hx9_11 : σ11.regs.get? Register.x9 = some v9 := obs_alu_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_10
  have hx18_11 : σ11.regs.get? Register.x18 = some v18 := obs_alu_other hobs11 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hcode11 : Exec_stmtLoaded σ11.mem := by rw [hmem11e]; exact hcode6
  -- ============ 0x80004164: li a0,3 → x10 := 3 = StatusCode (.ret v) ============
  obtain ⟨σ12, i12, hstep12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80004164_es σ11 i11 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80004164#64) vmi11 hG11 hpc11 hmi11 hcode11 rfl hi11
  have hstep12 : Step ⟨σ11, i11, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ12, i12, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep12'
  have hmem12e : σ12.mem = σ6.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x80004168#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80004164#64) 4 = (0x80004168#64:BitVec 64) from by decide] at this
  have ha0_12 : σ12.regs.get? Register.x10 = some (StatusCode (.ret v)) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [statusCode_ret]
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = (3#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hra_12 : σ12.regs.get? Register.x1 = some r := obs_alu_other hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_11
  have hx8_12 : σ12.regs.get? Register.x8 = some v8 := obs_alu_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_11
  have hx9_12 : σ12.regs.get? Register.x9 = some v9 := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_11
  have hx18_12 : σ12.regs.get? Register.x18 = some v18 := obs_alu_other hobs12 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_11
  have hx19_12 : σ12.regs.get? Register.x19 = some v19 := obs_alu_other hobs12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hcode12 : Exec_stmtLoaded σ12.mem := by rw [hmem12e]; exact hcode6
  -- ============ 0x80004168: addi sp,sp,176 → x2 := sp ============
  obtain ⟨σ13, i13, hstep13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80004168_es σ12 i12 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80004168#64) vmi12 (sp - 176#64) hG12 hpc12 hmi12 hsp_12 hcode12 rfl hi12
  have hstep13 : Step ⟨σ12, i12, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ13, i13, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep13'
  have hmem13e : σ13.mem = σ6.mem := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000416c#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80004168#64) 4 = (0x8000416c#64:BitVec 64) from by decide] at this
  have hsp_13 : σ13.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [sp_add176] at this
  have hra_13 : σ13.regs.get? Register.x1 = some r := obs_alu_other hobs13 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_12
  have ha0_13 : σ13.regs.get? Register.x10 = some (StatusCode (.ret v)) := obs_alu_other hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_12
  have hx8_13 : σ13.regs.get? Register.x8 = some v8 := obs_alu_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_12
  have hx9_13 : σ13.regs.get? Register.x9 = some v9 := obs_alu_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_12
  have hx18_13 : σ13.regs.get? Register.x18 = some v18 := obs_alu_other hobs13 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_12
  have hx19_13 : σ13.regs.get? Register.x19 = some v19 := obs_alu_other hobs13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hcode13 : Exec_stmtLoaded σ13.mem := by rw [hmem13e]; exact hcode6
  -- ============ 0x8000416c: ret → PC := r ============
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r hraAl]; exact hraAl
  obtain ⟨σ14, i14, hstep14', hi14, hG14, hmem14, hobs14⟩ :=
    site_8000416c_es σ13 i13 (cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000416c#64) vmi13 r hG13 hpc13 hmi13 hra_13 hcode13 rfl hrettgt hi13
  have hstep14 : Step ⟨σ13, i13, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ14, i14, cG.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hstep14'
  have hmem14e : σ14.mem = σ6.mem := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs14
  have ha0_14 : σ14.regs.get? Register.x10 = some (StatusCode (.ret v)) := obs_jr_other hobs14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_13
  have hra_14 : σ14.regs.get? Register.x1 = some r := obs_jr_other hobs14 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_13
  have hsp_14 : σ14.regs.get? Register.x2 = some sp := obs_jr_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_13
  have hx8_14 : σ14.regs.get? Register.x8 = some v8 := obs_jr_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_13
  have hx9_14 : σ14.regs.get? Register.x9 = some v9 := obs_jr_other hobs14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_13
  have hx18_14 : σ14.regs.get? Register.x18 = some v18 := obs_jr_other hobs14 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_13
  have hx19_14 : σ14.regs.get? Register.x19 = some v19 := obs_jr_other hobs14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_13
  obtain ⟨vmi14, hmi14⟩ := obs_jr_minstret hobs14
  -- output invariance across the entire tail (6 copy + 8 epilogue steps, all
  -- non-output — the `sailOutput` array is untouched by ld/sd/alu/jr):
  have hout14 : String.join σ14.sailOutput.toList = st'.out := by
    have hbase : String.join cG.σ.sailOutput.toList = st'.out := houtG
    rw [hobs14.out, sailOutput_sigmaPost_jump_x0, hobs13.out, sailOutput_sigmaPost_alu,
      hobs12.out, sailOutput_sigmaPost_alu, hobs11.out, sailOutput_sigmaPost_alu,
      hobs10.out, sailOutput_sigmaPost_alu, hobs9.out, sailOutput_sigmaPost_alu,
      hobs8.out, sailOutput_sigmaPost_alu, hobs7.out, sailOutput_sigmaPost_alu,
      hobs6.out, sailOutput_sigmaPost_store, hobs5.out, sailOutput_sigmaPost_store,
      hobs4.out, sailOutput_sigmaPost_store, hobs3.out, sailOutput_sigmaPost_alu,
      hobs2.out, sailOutput_sigmaPost_alu, hobs1.out, sailOutput_sigmaPost_alu]
    exact hbase
  -- abi-disequality helper
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- the callee-saved frame at σ14 (excl x8/x9/x18/x19/x2/x1/x10): the whole tail
  -- writes only x13/x14/x15 (copy) + x1/x8/x9/x18/x19/x10/x2 (epilogue), all of
  -- which are either restored or caller-saved; the ghost frame reads back to `g`.
  have hframe14 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false → (Register.x2 == R) = false →
      (Register.x1 == R) = false → (Register.x10 == R) = false →
      σ14.regs.get? R = cG.σ.regs.get? R := by
    intro R hR he8 he9 he18 he19 he2 he1 he10
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have h13 : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h14 : (Register.x14 == R) = false := abi_ne' (by decide) hab
    have h15 : (Register.x15 == R) = false := abi_ne' (by decide) hab
    have a : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {vv : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd vv) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
    have st : ∀ {σa σb : MState} {pc vm : BitVec 64} {mm : Mem},
        ReadsLikePost σb (sigmaPost_store σa pc vm mm) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
    have jr : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
        ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    exact (jr hobs14).trans ((a hobs13 he2).trans ((a hobs12 he10).trans ((a hobs11 he19).trans
      ((a hobs10 he18).trans ((a hobs9 he9).trans ((a hobs8 he8).trans ((a hobs7 he1).trans
      ((st hobs6).trans ((st hobs5).trans ((st hobs4).trans ((a hobs3 h15).trans
      ((a hobs2 h14).trans (a hobs1 h13)))))))))))))
  -- ===== assemble the full Steps chain and the ExecExit .ret v =====
  refine ⟨⟨σ14, i14, _⟩,
    (hstepsA.trans (hstepsG.trans
      ((Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans (Steps.single hstep14)))))))))))))))), ?_⟩
  refine
    { good := hG14
      tick := hi14
      pc := hpc14
      a0 := ha0_14
      ra := hra_14
      spReg := hsp_14
      minstret := ⟨_, hmi14⟩
      store := ?_
      out := ?_
      retval := ?_
      frame := ?_
      memFrame := ?_ }
  · -- store: re-represent st'.store in σ14.mem = σ6.mem (extended maps φfS/φcS).
    -- The three copy stores only touched `[aRet, aRet+24)`; transport via the
    -- retslot-tolerant survival clause carried by `SubExecReturnR`.
    refine ⟨φfS, φcS, hpfS, hpcS, ?_⟩
    rw [hmem14e]
    exact hstoreSurv σ6.mem (fun k hk => (houtside6 k hk).symm)
  · show Vsa.Machine.output σ14 = st'.out
    simp only [Vsa.Machine.output]; exact hout14
  · -- retval: the retslot holds ValueRepr v (extended φcv) via copy-of-write-window.
    intro v' hv'
    have hveq : v' = v := by cases hv'; rfl
    subst hveq
    obtain ⟨φcv, hpcv, hvr⟩ := hvalG
    refine ⟨φcv, hpcv, ?_⟩
    -- source word bounds (each `read64` result is `< 2^64`)
    have hwbnd : ∀ (mm : Mem) (a w : Nat), read64 mm a = some w → w < 2^64 :=
      fun mm a w hw => read64_lt_eg4 mm a w hw
    -- destination words in σ6.mem (each write reads back, later disjoint writes pass through)
    have hd0 : read64 σ6.mem aRet.toNat = some w0 := by
      rw [hm6full,
        read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat]
      have := hwbnd _ _ _ (hsubEq ▸ hrw0); congr 1; omega
    have hd1 : read64 σ6.mem (aRet.toNat + 8) = some w1 := by
      rw [hm6full,
        read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat]
      have := hwbnd _ _ _ hrw1; congr 1; omega
    have hd2 : read64 σ6.mem (aRet.toNat + 16) = some w2 := by
      rw [hm6full, read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat]
      have := hwbnd _ _ _ hrw2; congr 1; omega
    -- byte-copy: each destination octet equals the source octet (both reconstruct wk)
    have hcopy8 : ∀ (dst src w : Nat), read64 σ6.mem dst = some w → read64 cG.σ.mem src = some w →
        ∀ j, j < 8 → σ6.mem[dst + j]? = cG.σ.mem[src + j]? := by
      intro dst src w hd hs j hj
      obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7, hd0',hd1',hd2',hd3',hd4',hd5',hd6',hd7', _⟩ := read64_bytes_eg4 σ6.mem dst w hd
      obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7, he0,he1,he2,he3,he4,he5,he6,he7, _⟩ := read64_bytes_eg4 cG.σ.mem src w hs
      have b0 := d0.isLt; have b1 := d1.isLt; have b2 := d2.isLt; have b3 := d3.isLt
      have b4 := d4.isLt; have b5 := d5.isLt; have b6 := d6.isLt; have b7 := d7.isLt
      have c0 := e0.isLt; have c1 := e1.isLt; have c2 := e2.isLt; have c3 := e3.isLt
      have c4 := e4.isLt; have c5 := e5.isLt; have c6 := e6.isLt; have c7 := e7.isLt
      have hq0 : d0 = e0 := by apply BitVec.eq_of_toNat_eq; omega
      have hq1 : d1 = e1 := by apply BitVec.eq_of_toNat_eq; omega
      have hq2 : d2 = e2 := by apply BitVec.eq_of_toNat_eq; omega
      have hq3 : d3 = e3 := by apply BitVec.eq_of_toNat_eq; omega
      have hq4 : d4 = e4 := by apply BitVec.eq_of_toNat_eq; omega
      have hq5 : d5 = e5 := by apply BitVec.eq_of_toNat_eq; omega
      have hq6 : d6 = e6 := by apply BitVec.eq_of_toNat_eq; omega
      have hq7 : d7 = e7 := by apply BitVec.eq_of_toNat_eq; omega
      match j, hj with
      | 0, _ => rw [Nat.add_zero, Nat.add_zero, hd0', he0, hq0]
      | 1, _ => rw [hd1', he1, hq1]
      | 2, _ => rw [hd2', he2, hq2]
      | 3, _ => rw [hd3', he3, hq3]
      | 4, _ => rw [hd4', he4, hq4]
      | 5, _ => rw [hd5', he5, hq5]
      | 6, _ => rw [hd6', he6, hq6]
      | 7, _ => rw [hd7', he7, hq7]
    have hcopy : ∀ j, j < 24 → σ6.mem[aRet.toNat + j]? = cG.σ.mem[subsret.toNat + j]? := by
      intro j hj
      rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ 16 ≤ j) with h | ⟨h1, h2⟩ | h
      · exact hcopy8 aRet.toNat subsret.toNat w0 hd0 hrw0 j h
      · have := hcopy8 (aRet.toNat + 8) (subsret.toNat + 8) w1 hd1 hrw1 (j - 8) (by omega)
        rw [show aRet.toNat + 8 + (j - 8) = aRet.toNat + j by omega,
            show subsret.toNat + 8 + (j - 8) = subsret.toNat + j by omega] at this
        exact this
      · have := hcopy8 (aRet.toNat + 16) (subsret.toNat + 16) w2 hd2 hrw2 (j - 16) (by omega)
        rw [show aRet.toNat + 16 + (j - 16) = aRet.toNat + j by omega,
            show subsret.toNat + 16 + (j - 16) = subsret.toNat + j by omega] at this
        exact this
    -- assemble ValueRepr σ14.mem N φcv aRet v (= σ6.mem)
    rw [hmem14e]
    refine valueRepr_copy_of_writeWindow (m := cG.σ.mem) (m' := σ6.mem)
      (srcAddr := subsret.toNat) (dstAddr := aRet.toNat) hcopy ?_ ?_ hvr
    · intro a ha; exact houtside6 a ha
    · intro p s hp k hk
      exact hpayDisj p s hp k hk
  · -- frame: every callee-preserved register restored to `g R`.
    intro R hR
    by_cases h8 : (Register.x8 == R) = true
    · have : R = Register.x8 := by rw [beq_iff_eq] at h8; exact h8.symm
      subst this; rw [hx8_14]; exact hgx8.symm
    by_cases h9 : (Register.x9 == R) = true
    · have : R = Register.x9 := by rw [beq_iff_eq] at h9; exact h9.symm
      subst this; rw [hx9_14]; exact hgx9.symm
    by_cases h18 : (Register.x18 == R) = true
    · have : R = Register.x18 := by rw [beq_iff_eq] at h18; exact h18.symm
      subst this; rw [hx18_14]; exact hgx18.symm
    by_cases h19 : (Register.x19 == R) = true
    · have : R = Register.x19 := by rw [beq_iff_eq] at h19; exact h19.symm
      subst this; rw [hx19_14]; exact hgx19.symm
    by_cases h2 : (Register.x2 == R) = true
    · have : R = Register.x2 := by rw [beq_iff_eq] at h2; exact h2.symm
      subst this; rw [hsp_14]; exact hgx2.symm
    · have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hR.1
      have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hR.1
      rw [hframe14 R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
        (by simpa using h19) (by simpa using h2) h1 h10]
      exact hframeG R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
        (by simpa using h19) (by simpa using h2)
  · -- memFrame: outside stack ∪ arena, σ14.mem = m0 (with the retslot window disjunct).
    intro a hstk harena
    rw [hmem14e]
    -- σ6.mem[a]? relates to cG.σ.mem[a]? outside [aRet,aRet+24); cG relates to m0
    -- outside stack ∪ arena ∪ subsret (subsret ⊂ stack window).
    by_cases hin : aRet.toNat ≤ a ∧ a < aRet.toNat + 24
    · exact Or.inl hin
    · right
      have hout6 : σ6.mem[a]? = cG.σ.mem[a]? := by
        refine houtside6 a ?_
        rcases Nat.lt_or_ge a aRet.toNat with h | h
        · exact Or.inl h
        · right; rcases Nat.lt_or_ge a (aRet.toNat + 24) with h2 | h2
          · exact absurd ⟨h, h2⟩ hin
          · exact h2
      rw [hout6]
      rcases hmemframeG a hstk harena with hsub | heqC
      · exact absurd (⟨by omega, by omega⟩ : SL.lo ≤ a ∧ a < sp.toNat) hstk
      · rw [heqC, hmemPreG a hstk]

end Vsa.Sim
