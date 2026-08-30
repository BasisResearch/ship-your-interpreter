import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNotSim
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.LogicalSites
import Vsa.Sim.LogicalSites2
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.EvalAndSim
import Vsa.Sim.EvalOrSim
import Vsa.Sim.EvalBinSim
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 recursive cases: the logical two-eval TRUTHY-CONTINUE constructors

The two constructors that evaluate BOTH operands (they do NOT short-circuit):

* **and-true** — `EvalE (.logical .and l r) st'' (.bool vr.truthy)` when
  `vl.truthy = true`: evaluate `l` (truthy), then evaluate `r`, produce
  `.bool vr.truthy`.
* **or-false** — `EvalE (.logical .or l r) st'' (.bool vr.truthy)` when
  `vl.truthy = false`: evaluate `l` (falsy), then evaluate `r`, produce
  `.bool vr.truthy`.

Both reach a SHARED tail at `0x800035bc` (`blockC_logTail`): copy the RIGHT
value `rv` into the `value_truthy` arg buffer `sp-1024`, `value_truthy(rv)`,
`value_bool` → `.bool rv.truthy`, `j 0x800033ec`.

Decoded machine paths (`riscv64-elf-objdump -d`; op tokens `.and = 24`,
`.or = 25`):

```
-- and-true continue (beqz@0x8000359c NOT taken; op != 25 → AND arm) --
800035a0: ld   a2,24(s0)      -- RIGHT operand ptr (node offset 24)
800035a4: mv   a1,s2          -- a1 := interp*
800035a8: addi a0,sp,240      -- sret_R = (sp-1088)+240 = sp-848
800035ac: jal  eval_expr      -- RIGHT call; ra := 0x800035b0
800035b0: ld   a3,240(sp)     -- rv kind  @ sp-848
800035b4: ld   a4,248(sp)     -- rv pay   @ sp-840
800035b8: ld   a5,256(sp)     -- rv[16..) @ sp-832
-- SHARED tail @0x800035bc --
800035bc: addi a0,sp,64       -- buf = sp-1024
800035c0: sd   a3,64(sp)      -- copy rv kind
800035c4: sd   a4,72(sp)      -- copy rv pay
800035c8: sd   a5,80(sp)      -- copy rv[16..)
800035cc: jal  value_truthy   -- a0 := rv.truthy ; ra = 0x800035d0
800035d0: mv   a1,a0          -- a1 := rv.truthy
800035d4: mv   a0,s1          -- a0 := outer sret
800035d8: jal  value_bool     -- value_bool(sret, rv.truthy) ; ra = 0x800035dc
800035dc: j    800033ec       -- shared epilogue → blockD_v_rec

-- or-false continue (beqz@0x80003998 TAKEN → 0x80003a00; op == 25 → OR arm) --
80003a00: ld   a2,24(s0)      -- RIGHT operand ptr
80003a04: mv   a1,s2          -- a1 := interp*
80003a08: addi a0,sp,144      -- sret_R = (sp-1088)+144 = sp-944
80003a0c: jal  eval_expr      -- RIGHT call; ra := 0x80003a10
80003a10: ld   a3,144(sp)     -- rv kind  @ sp-944
80003a14: ld   a4,152(sp)     -- rv pay   @ sp-936
80003a18: ld   a5,160(sp)     -- rv[16..) @ sp-928
80003a1c: j    800035bc       -- JOIN the shared tail
```

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

/-! ## `LogTailPre` — the shared-tail precondition at `0x800035bc`

The state at `0x800035bc` (reached by and-true fall-through and or-false via
`j 0x800035bc`): control at the tail PC, `sp` lowered, `s1 = sret`, `s0 = aExpr`,
the three RIGHT-value words in `a3/a4/a5` (kind/payload/[16,24) at the RIGHT sret
buffer `sretR`), `rv` represented at `sretR`, `value_truthy`/`value_bool` loaded,
the store re-represented for the post state `st''`, spill slots intact,
presence-extended over `m0`. -/
structure LogTailPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st'' : Vsa.While.St) (rv : Value)
    (sp r sret sretR : BitVec 64)
    (kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 : BitVec 8)
    (qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 : BitVec 8)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x800035bc#64)
  s1 : c.σ.regs.get? Register.x9 = some sret
  sp2 : c.σ.regs.get? Register.x2 = some (sp - 1088#64)
  a3 : c.σ.regs.get? Register.x13 = some (sign_extend (m := 64)
    ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8)))
  a4 : c.σ.regs.get? Register.x14 = some (sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8)))
  a5 : c.σ.regs.get? Register.x15 = some (sign_extend (m := 64)
    ((((((((qb7.append qb6).append qb5).append qb4).append qb3).append qb2).append qb1).append qb0) : BitVec (8*8)))
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  out : c.σ.sailOutput = out0
  outStr : String.join out0.toList = st''.out
  code : Eval_exprLoaded c.σ.mem
  truthyLoaded : Value_truthyLoaded c.σ.mem
  boolLoaded : Value_boolLoaded c.σ.mem
  -- the RIGHT value is represented at `sretR` (extended `φc`)
  vrepr : ValueRepr c.σ.mem N φc sretR.toNat rv
  -- the 24 source bytes at the RIGHT buffer `sretR` (which the `a3/a4/a5` words
  -- sign-extend), pinned so `sd a3/a4/a5,64/72/80(sp)` byte-copies `rv` to sp-1024.
  bK0 : c.σ.mem[sretR.toNat]? = some kb0
  bK1 : c.σ.mem[sretR.toNat + 1]? = some kb1
  bK2 : c.σ.mem[sretR.toNat + 2]? = some kb2
  bK3 : c.σ.mem[sretR.toNat + 3]? = some kb3
  bK4 : c.σ.mem[sretR.toNat + 4]? = some kb4
  bK5 : c.σ.mem[sretR.toNat + 5]? = some kb5
  bK6 : c.σ.mem[sretR.toNat + 6]? = some kb6
  bK7 : c.σ.mem[sretR.toNat + 7]? = some kb7
  bP0 : c.σ.mem[sretR.toNat + 8]? = some pb0
  bP1 : c.σ.mem[sretR.toNat + 8 + 1]? = some pb1
  bP2 : c.σ.mem[sretR.toNat + 8 + 2]? = some pb2
  bP3 : c.σ.mem[sretR.toNat + 8 + 3]? = some pb3
  bP4 : c.σ.mem[sretR.toNat + 8 + 4]? = some pb4
  bP5 : c.σ.mem[sretR.toNat + 8 + 5]? = some pb5
  bP6 : c.σ.mem[sretR.toNat + 8 + 6]? = some pb6
  bP7 : c.σ.mem[sretR.toNat + 8 + 7]? = some pb7
  bQ0 : c.σ.mem[sretR.toNat + 16]? = some qb0
  bQ1 : c.σ.mem[sretR.toNat + 16 + 1]? = some qb1
  bQ2 : c.σ.mem[sretR.toNat + 16 + 2]? = some qb2
  bQ3 : c.σ.mem[sretR.toNat + 16 + 3]? = some qb3
  bQ4 : c.σ.mem[sretR.toNat + 16 + 4]? = some qb4
  bQ5 : c.σ.mem[sretR.toNat + 16 + 5]? = some qb5
  bQ6 : c.σ.mem[sretR.toNat + 16 + 6]? = some qb6
  bQ7 : c.σ.mem[sretR.toNat + 16 + 7]? = some qb7
  -- the payload-disjointness for the copy (mirrors LogicalBufExtras.pay_disj)
  payDisj : ∀ (p : Nat) (s : String),
    read64 c.σ.mem (sretR.toNat + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)
  -- store re-represented + survival on [SL.lo, SL.hi)
  store : StoreRepr c.σ.mem N A φf φc st''.store
  storeSurv : ∀ m' : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st''.store
  -- spill slots
  slotRa : read64 c.σ.mem (sp.toNat - 8) = some r.toNat
  slotS0 : read64 c.σ.mem (sp.toNat - 16) = some v8.toNat
  slotS1 : read64 c.σ.mem (sp.toNat - 24) = some v9.toNat
  slotS2 : read64 c.σ.mem (sp.toNat - 32) = some v18.toNat
  -- ghost frame + spill witnesses (the same shape blockD needs)
  gv8 : g Register.x8 = some v8
  gv9 : g Register.x9 = some v9
  gv18 : g Register.x18 = some v18
  gv2 : g Register.x2 = some sp
  frame : ∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false →
    c.σ.regs.get? R = g R
  -- memory frame m0
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ c.σ.mem[a]? = m0[a]?
  memExt : MemExtends m0 c.σ.mem
  -- geometry
  bufLo : 0x80000000 + 1024 ≤ sp.toNat
  bufWin : tohostAddr + 16 + 1024 ≤ sp.toNat
  sretAl : sret.toNat % 8 = 0
  sretLo : 0x80000000 ≤ sret.toNat
  sretHi : sret.toNat + 24 ≤ 0x100000000
  sretWin : tohostAddr + 16 ≤ sret.toNat
  sretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sretBoolCode : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  raAl : r.toNat % 4 = 0
  spSLhi : sp.toNat ≤ SL.hi
  spRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  spLo : 1088 ≤ sp.toNat
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  -- buffer sp-1024 disjunctions vs value_truthy/value_bool code + arena
  truthyStk : sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo
  boolStk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo

/-! ## `blockC_logTail` — the shared value_truthy/value_bool tail

From `LogTailPre` at `0x800035bc`: copy `rv` (words `kv/pv/qv` in a3/a4/a5) into
the `value_truthy` arg buffer `sp-1024`, compute `value_truthy(rv)`, then
`value_bool(sret, rv.truthy)` producing `.bool rv.truthy`, and `j 0x800033ec`.
Output: `PreEpilogueVD … (.bool rv.truthy) 0x800033ec`, ready for `blockD_v_rec`. -/
theorem blockC_logTail
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st'' : Vsa.While.St) (rv : Value)
    (sp r sret sretR : BitVec 64)
    (kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 : BitVec 8)
    (pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 : BitVec 8)
    (qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 : BitVec 8)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem) :
    Triple
      (fun c => LogTailPre g N A SL φf φc st'' rv sp r sret sretR
        kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
        qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 v8 v9 v18 out0 m0 c)
      (fun c => ∃ mpre,
        PreEpilogueVD g N A SL φf φc st'' (.bool rv.truthy) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hG, htick, hpc, hs1, hsp, ha3, ha4, ha5, ⟨vmi, hmi⟩, hout, houtStr, hcode,
    hVtruthyC, hVboolC, hvrepr,
    hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7,
    hpb0, hpb1, hpb2, hpb3, hpb4, hpb5, hpb6, hpb7,
    hqb0, hqb1, hqb2, hqb3, hqb4, hqb5, hqb6, hqb7, hpayDisj,
    hstore, hstoreSurv, hslotRa, hslotS0, hslotS1, hslotS2,
    hgv8, hgv9, hgv18, hgv2, hframe, hmemFrame, hMemExt,
    hbufLo, hbufWin, hsretAl, hsretLo, hsretHi, hsretWin, hsretStk, hsretBoolCode,
    hsretInSL, hsretEvalCode, hraAl, hspSLhi, hspRam, hsp8, hSLhiRam, hSLlo, hSLwin,
    hspLo, hSLloSp, hTruthyStk, hBoolStk, hcodeStk⟩ := hpre
  -- name the three copy words (a3/a4/a5) as the byte reconstructions
  let kv : BitVec 64 := sign_extend (m := 64)
    ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  let pv : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  let qv : BitVec 64 := sign_extend (m := 64)
    ((((((((qb7.append qb6).append qb5).append qb4).append qb3).append qb2).append qb1).append qb0) : BitVec (8*8))
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := hspLo
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have haddr64 : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 :=
    spill_addr sp (0x040#12) 1024 (by decide) (by omega) hsp1088
  have haddr72 : ((sp - 1088#64) + sign_extend (m := 64) (0x048#12)).toNat = sp.toNat - 1016 :=
    spill_addr sp (0x048#12) 1016 (by decide) (by omega) hsp1088
  have haddr80 : ((sp - 1088#64) + sign_extend (m := 64) (0x050#12)).toNat = sp.toNat - 1008 :=
    spill_addr sp (0x050#12) 1008 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- 0x800035bc: addi a0,sp,64 → x10 := (sp-1088)+64 = sp-1024 (buf)
  ------------------------------------------------------------------------
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800035bc_lg c.σ c.tick c.steps (0x800035bc#64) vmi (sp - 1088#64)
      hG hpc hmi hsp hcode rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800035c0#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800035bc#64) 4 = (0x800035c0#64 : BitVec 64) from by decide] at this
  have hx10_1 : σ1.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha3_1 : σ1.regs.get? Register.x13 = some kv := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 : σ1.regs.get? Register.x14 = some pv := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have ha5_1 : σ1.regs.get? Register.x15 = some qv := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  ------------------------------------------------------------------------
  -- 0x800035c0 / c4 / c8: the three copy stores. Memory tower m1/m2/m3.
  ------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val kv)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 1016) (sdData_val pv)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 1008) (sdData_val qv)
  -- 0x800035c0: sd a3,64(sp) → m1
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800035c0_lg σ1 i1 (c.steps + 1) (0x800035c0#64) vmi1 (sp - 1088#64) kv
      hG1 hpc1 hmi1 hsp_1 ha3_1 hcode1 rfl
      (by rw [haddr64]; omega) (by rw [haddr64]; omega) (by rw [haddr64, htoh]; omega) (by rw [haddr64]; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = m1 := by rw [hmem2, mem_afterNextPC, haddr64, hmem1e]
  have hpc2 : σ2.regs.get? Register.PC = some (0x800035c4#64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x800035c0#64) 4 = (0x800035c4#64 : BitVec 64) from by decide] at this
  have hx10_2 := obs_store_other_val' hobs2 Register.x10 (by decide) hx10_1
  have ha4_2 := obs_store_other_val' hobs2 Register.x14 (by decide) ha4_1
  have ha5_2 := obs_store_other_val' hobs2 Register.x15 (by decide) ha5_1
  have hs1_2 := obs_store_other_val' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 := obs_store_other_val' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_store]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by
    rw [hmem2e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val kv)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  -- 0x800035c4: sd a4,72(sp) → m2
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800035c4_lg σ2 i2 (c.steps + 1 + 1) (0x800035c4#64) vmi2 (sp - 1088#64) pv
      hG2 hpc2 hmi2 hsp_2 ha4_2 hcode2 rfl
      (by rw [haddr72]; omega) (by rw [haddr72]; omega) (by rw [haddr72, htoh]; omega) (by rw [haddr72]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = m2 := by rw [hmem3, mem_afterNextPC, haddr72, hmem2e]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800035c8#64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x800035c4#64) 4 = (0x800035c8#64 : BitVec 64) from by decide] at this
  have hx10_3 := obs_store_other_val' hobs3 Register.x10 (by decide) hx10_2
  have ha5_3 := obs_store_other_val' hobs3 Register.x15 (by decide) ha5_2
  have hs1_3 := obs_store_other_val' hobs3 Register.x9 (by decide) hs1_2
  have hsp_3 := obs_store_other_val' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by
    rw [hmem3e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val pv)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem2e ▸ hcode2)
  -- 0x800035c8: sd a5,80(sp) → m3
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800035c8_lg σ3 i3 (c.steps + 1 + 1 + 1) (0x800035c8#64) vmi3 (sp - 1088#64) qv
      hG3 hpc3 hmi3 hsp_3 ha5_3 hcode3 rfl
      (by rw [haddr80]; omega) (by rw [haddr80]; omega) (by rw [haddr80, htoh]; omega) (by rw [haddr80]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = m3 := by rw [hmem4, mem_afterNextPC, haddr80, hmem3e]
  have hpc4 : σ4.regs.get? Register.PC = some (0x800035cc#64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x800035c8#64) 4 = (0x800035cc#64 : BitVec 64) from by decide] at this
  have hx10_4 := obs_store_other_val' hobs4 Register.x10 (by decide) hx10_3
  have hs1_4 := obs_store_other_val' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 := obs_store_other_val' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_store]; exact hout3
  have hcode_m3 : Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val qv)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem3e ▸ hcode3)
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode_m3
  have hx10_4' : σ4.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) := hx10_4
  ------------------------------------------------------------------------
  -- the copied 24-byte buffer represents `rv`: ValueRepr m3 (sp-1024) rv.
  ------------------------------------------------------------------------
  have hm3_out : ∀ a, (a < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ a) → m3[a]? = c.σ.mem[a]? := by
    intro a ha
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val qv) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val pv) (by omega)]
    show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val kv))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val kv) (by omega)]
  -- the m3 window byte-copies the sretR buffer (mirrors orTrue's hm3_copy)
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := sdData_sext_bytes kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := sdData_sext_bytes pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := sdData_sext_bytes qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7
  have hK : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1024 + o]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val kv))[sp.toNat - 1024 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val qv) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[_]? = _
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) _ (sdData_val pv) (by omega)]
  have hP : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1016 + o]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[sp.toNat - 1016 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val qv) (by omega)]
  have hm3_copy : ∀ j, j < 24 → m3[(sp.toNat - 1024) + j]? = c.σ.mem[sretR.toNat + j]? := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK 0 (by omega), show sp.toNat-1024+0 = sp.toNat-1024 from by omega,
        getElem_writeMap8_0, eK0, show sretR.toNat+0 = sretR.toNat from by omega]; exact hkb0.symm
    · rw [hK 1 (by omega), getElem_writeMap8_1, eK1]; exact hkb1.symm
    · rw [hK 2 (by omega), getElem_writeMap8_2, eK2]; exact hkb2.symm
    · rw [hK 3 (by omega), getElem_writeMap8_3, eK3]; exact hkb3.symm
    · rw [hK 4 (by omega), getElem_writeMap8_4, eK4]; exact hkb4.symm
    · rw [hK 5 (by omega), getElem_writeMap8_5, eK5]; exact hkb5.symm
    · rw [hK 6 (by omega), getElem_writeMap8_6, eK6]; exact hkb6.symm
    · rw [hK 7 (by omega), getElem_writeMap8_7, eK7]; exact hkb7.symm
    · rw [show sp.toNat-1024+8 = sp.toNat-1016+0 from by omega, hP 0 (by omega),
        show sp.toNat-1016+0 = sp.toNat-1016 from by omega, getElem_writeMap8_0, eP0,
        show sretR.toNat+8 = sretR.toNat+8 from by omega]; exact hpb0.symm
    · rw [show sp.toNat-1024+9 = sp.toNat-1016+1 from by omega, hP 1 (by omega), getElem_writeMap8_1, eP1,
        show sretR.toNat+9 = sretR.toNat+8+1 from by omega]; exact hpb1.symm
    · rw [show sp.toNat-1024+10 = sp.toNat-1016+2 from by omega, hP 2 (by omega), getElem_writeMap8_2, eP2,
        show sretR.toNat+10 = sretR.toNat+8+2 from by omega]; exact hpb2.symm
    · rw [show sp.toNat-1024+11 = sp.toNat-1016+3 from by omega, hP 3 (by omega), getElem_writeMap8_3, eP3,
        show sretR.toNat+11 = sretR.toNat+8+3 from by omega]; exact hpb3.symm
    · rw [show sp.toNat-1024+12 = sp.toNat-1016+4 from by omega, hP 4 (by omega), getElem_writeMap8_4, eP4,
        show sretR.toNat+12 = sretR.toNat+8+4 from by omega]; exact hpb4.symm
    · rw [show sp.toNat-1024+13 = sp.toNat-1016+5 from by omega, hP 5 (by omega), getElem_writeMap8_5, eP5,
        show sretR.toNat+13 = sretR.toNat+8+5 from by omega]; exact hpb5.symm
    · rw [show sp.toNat-1024+14 = sp.toNat-1016+6 from by omega, hP 6 (by omega), getElem_writeMap8_6, eP6,
        show sretR.toNat+14 = sretR.toNat+8+6 from by omega]; exact hpb6.symm
    · rw [show sp.toNat-1024+15 = sp.toNat-1016+7 from by omega, hP 7 (by omega), getElem_writeMap8_7, eP7,
        show sretR.toNat+15 = sretR.toNat+8+7 from by omega]; exact hpb7.symm
    · rw [show sp.toNat-1024+16 = sp.toNat-1008 from by omega, getElem_writeMap8_0, eQ0,
        show sretR.toNat+16 = sretR.toNat+16 from by omega]; exact hqb0.symm
    · rw [show sp.toNat-1024+17 = sp.toNat-1008+1 from by omega, getElem_writeMap8_1, eQ1,
        show sretR.toNat+17 = sretR.toNat+16+1 from by omega]; exact hqb1.symm
    · rw [show sp.toNat-1024+18 = sp.toNat-1008+2 from by omega, getElem_writeMap8_2, eQ2,
        show sretR.toNat+18 = sretR.toNat+16+2 from by omega]; exact hqb2.symm
    · rw [show sp.toNat-1024+19 = sp.toNat-1008+3 from by omega, getElem_writeMap8_3, eQ3,
        show sretR.toNat+19 = sretR.toNat+16+3 from by omega]; exact hqb3.symm
    · rw [show sp.toNat-1024+20 = sp.toNat-1008+4 from by omega, getElem_writeMap8_4, eQ4,
        show sretR.toNat+20 = sretR.toNat+16+4 from by omega]; exact hqb4.symm
    · rw [show sp.toNat-1024+21 = sp.toNat-1008+5 from by omega, getElem_writeMap8_5, eQ5,
        show sretR.toNat+21 = sretR.toNat+16+5 from by omega]; exact hqb5.symm
    · rw [show sp.toNat-1024+22 = sp.toNat-1008+6 from by omega, getElem_writeMap8_6, eQ6,
        show sretR.toNat+22 = sretR.toNat+16+6 from by omega]; exact hqb6.symm
    · rw [show sp.toNat-1024+23 = sp.toNat-1008+7 from by omega, getElem_writeMap8_7, eQ7,
        show sretR.toNat+23 = sretR.toNat+16+7 from by omega]; exact hqb7.symm
  -- ValueRepr m3 (sp-1024) rv
  have hbufRepr : ValueRepr m3 N φc (sp.toNat - 1024) rv :=
    valueRepr_copy_of_writeWindow (srcAddr := sretR.toNat) (dstAddr := sp.toNat - 1024)
      hm3_copy hm3_out
      (fun p s hp k hk => hpayDisj p s hp k hk) hvrepr
  -- value_truthy / value_bool code loaded at m3
  have hVtruthy_m3 : Value_truthyLoaded m3 :=
    loaded_truthy_writeMap8 m2 (sp.toNat - 1008) (sdData_val qv) (by rcases hTruthyStk with h | h <;> omega)
      (loaded_truthy_writeMap8 m1 (sp.toNat - 1016) (sdData_val pv) (by rcases hTruthyStk with h | h <;> omega)
        (loaded_truthy_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val kv) (by rcases hTruthyStk with h | h <;> omega) hVtruthyC))
  have hVbool_m3 : Value_boolLoaded m3 :=
    loaded_bool_writeMap8 m2 (sp.toNat - 1008) (sdData_val qv) (by rcases hBoolStk with h | h <;> omega)
      (loaded_bool_writeMap8 m1 (sp.toNat - 1016) (sdData_val pv) (by rcases hBoolStk with h | h <;> omega)
        (loaded_bool_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val kv) (by rcases hBoolStk with h | h <;> omega) hVboolC))
  have hbuftag : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) = (sp - 1024#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    have : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 := haddr64
    rw [this, h1024]; have := sp.isLt; omega
  have hbufNat : (sp - 1024#64 : BitVec 64).toNat = sp.toNat - 1024 := by
    rw [BitVec.toNat_sub]; have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    rw [h1024]; have := sp.isLt; omega
  have hTruthyReg : TruthyRegion (sp - 1024#64) :=
    ⟨by rw [hbufNat]; omega, by rw [hbufNat]; omega,
     by rw [hbufNat]; omega, by rw [hbufNat, htoh]; omega⟩
  have hrettgt_t : (BitVec.update ((0x800035d0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  have hbufRepr' : ValueRepr m3 N φc (sp - 1024#64).toNat rv := by rw [hbufNat]; exact hbufRepr
  have hx10_4'' : σ4.regs.get? Register.x10 = some (sp - 1024#64) := by rw [hx10_4', hbuftag]
  ------------------------------------------------------------------------
  -- 0x800035cc: jal value_truthy → PC := value_truthy entry, ra := 0x800035d0
  ------------------------------------------------------------------------
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800035cc_lg σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800035cc#64) vmi4
      hG4 hpc4 hmi4 hcode4 rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = m3 := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000282c#64) := by
    have := obs_jal_pc hobs5
    rwa [show ((0x800035cc#64 : BitVec 64) + sign_extend (m := 64) (0x1ff260#21)) = 0x8000282c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink5 : σ5.regs.get? Register.x1 = some (0x800035d0#64) := by
    have := obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800035cc#64 : BitVec 64) 4 = (0x800035d0#64:BitVec 64) from by decide] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some (sp - 1024#64) :=
    obs_jal_other' hobs5 Register.x10 (by decide) hx10_4''
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_jal_other' hobs5 Register.x9 (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_jal_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_jal]; exact hout4
  have hVbool_5 : Value_boolLoaded σ5.mem := by rw [hmem5e]; exact hVbool_m3
  ------------------------------------------------------------------------
  -- value_truthy(rv) via value_truthy_spec, buf = sp-1024, ra = 0x800035d0
  ------------------------------------------------------------------------
  obtain ⟨cT, hsT, hpostT⟩ :=
    value_truthy_spec (fun R => σ5.regs.get? R) (sp - 1024#64) (0x800035d0#64) N φc rv m3 out0
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG5, hmem5e ▸ hVtruthy_m3, hmem5e, hpc5, hx10_5, hlink5, ⟨vmi5, hmi5⟩, hi5,
        hbufRepr', hTruthyReg, hrettgt_t, hout5, fun R _ => rfl⟩
  obtain ⟨hGT, hpcT, ha0T, hraT, ⟨vmiT, hmiT⟩, htickT, hmemT, houtT, hframeT⟩ := hpostT
  have hmemT' : cT.σ.mem = m3 := hmemT
  have hpcT' : cT.σ.regs.get? Register.PC = some (0x800035d0#64) := by
    rw [hpcT, show (BitVec.update ((0x800035d0#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x800035d0#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have ha0T' : cT.σ.regs.get? Register.x10 = some (cond rv.truthy (1#64) (0#64)) := ha0T
  have hs1_T : cT.σ.regs.get? Register.x9 = some sret := by
    rw [hframeT Register.x9 (by decide)]; exact hs1_5
  have hVbool_T : Value_boolLoaded cT.σ.mem := by rw [hmemT']; exact hVbool_m3
  have hcode_T : Eval_exprLoaded cT.σ.mem := by rw [hmemT']; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x800035d0: mv a1,a0 → x11 := truthy(rv)
  ------------------------------------------------------------------------
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_800035d0_lg cT.σ cT.tick cT.steps (0x800035d0#64) vmiT (cond rv.truthy (1#64) (0#64))
      hGT hpcT' hmiT ha0T' (hmemT' ▸ hcode_m3) rfl htickT
  have hstep6 : Step cT ⟨σ6, i6, cT.steps + 1⟩ := by cases cT; exact hs6'
  have hmem6e : σ6.mem = m3 := by rw [hmem6]; exact hmemT'
  have hpc6 : σ6.regs.get? Register.PC = some (0x800035d4#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800035d0#64) 4 = (0x800035d4#64 : BitVec 64) from by decide] at this
  have ha1_6 : σ6.regs.get? Register.x11 = some ((cond rv.truthy (1#64) (0#64)) + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other' hobs6 Register.x9 (by decide) hs1_T
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact houtT
  have hVbool_6 : Value_boolLoaded σ6.mem := by rw [hmem6e]; exact hVbool_m3
  have hcode_6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x800035d4: mv a0,s1 → x10 := sret
  ------------------------------------------------------------------------
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_800035d4_lg σ6 i6 (cT.steps + 1) (0x800035d4#64) vmi6 sret hG6 hpc6 hmi6 hs1_6 hcode_6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, cT.steps + 1⟩ ⟨σ7, i7, cT.steps + 1 + 1⟩ := hs7'
  have hmem7e : σ7.mem = m3 := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x800035d8#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800035d4#64) 4 = (0x800035d8#64 : BitVec 64) from by decide] at this
  have hx10_7 : σ7.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide]; rw [BitVec.add_zero]] at this
  have ha1_7 : σ7.regs.get? Register.x11 = some ((cond rv.truthy (1#64) (0#64)) + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_alu_other' hobs7 Register.x9 (by decide) hs1_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_alu]; exact hout6
  have hVbool_7 : Value_boolLoaded σ7.mem := by rw [hmem7e]; exact hVbool_m3
  have hcode_7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode_m3
  have hBoolReg : BoolRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretBoolCode⟩
  have hrettgt_b : (BitVec.update ((0x800035dc#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  ------------------------------------------------------------------------
  -- 0x800035d8: jal value_bool → PC := value_bool entry, ra := 0x800035dc
  ------------------------------------------------------------------------
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_800035d8_lg σ7 i7 (cT.steps + 1 + 1) (0x800035d8#64) vmi7 hG7 hpc7 hmi7 hcode_7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, cT.steps + 1 + 1⟩ ⟨σ8, i8, cT.steps + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = m3 := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hobs8
    rwa [show ((0x800035d8#64 : BitVec 64) + sign_extend (m := 64) (0x1ff220#21)) = 0x800027f8#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink8 : σ8.regs.get? Register.x1 = some (0x800035dc#64) := by
    have := obs_jal_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800035d8#64 : BitVec 64) 4 = (0x800035dc#64:BitVec 64) from by decide] at this
  have hx10_8 : σ8.regs.get? Register.x10 = some sret := obs_jal_other' hobs8 Register.x10 (by decide) hx10_7
  have ha1_8 : σ8.regs.get? Register.x11 = some ((cond rv.truthy (1#64) (0#64)) + sign_extend (m := 64) (0x000#12)) :=
    obs_jal_other' hobs8 Register.x11 (by decide) ha1_7
  have hs1_8 : σ8.regs.get? Register.x9 = some sret := obs_jal_other' hobs8 Register.x9 (by decide) hs1_7
  obtain ⟨vmi8, hmi8⟩ := obs_jal_minstret hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_jal]; exact hout7
  have hVbool_8 : Value_boolLoaded σ8.mem := by rw [hmem8e]; exact hVbool_m3
  -- the value_bool arg register value = cond rv.truthy 1 0 (+0)
  have ha1_8' : σ8.regs.get? Register.x11 = some (cond rv.truthy (1#64) (0#64)) := by
    rw [ha1_8, show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]
  ------------------------------------------------------------------------
  -- value_bool(sret, truthy(rv)) via value_bool_spec_full → .bool (truthy != 0) = .bool rv.truthy
  ------------------------------------------------------------------------
  obtain ⟨cB, hsB, hGB, hpcB, ha0B, hraB, ⟨vmiB, hmiB⟩, htickB, hvalB, houtB, hmemframeB, hMemExtB, hframeB⟩ :=
    value_bool_spec_full (fun R => σ8.regs.get? R) sret (cond rv.truthy (1#64) (0#64)) (0x800035dc#64) N φc m3 out0
      ⟨σ8, i8, cT.steps + 1 + 1 + 1⟩
      ⟨hG8, hVbool_8, hmem8e, hpc8, hx10_8, ha1_8', hlink8, ⟨vmi8, hmi8⟩, hi8,
        hBoolReg, hrettgt_b, hout8, fun R _ => rfl⟩
  have hcondEq : ((cond rv.truthy (1#64) (0#64)) != 0#64) = rv.truthy := by
    cases rv.truthy <;> rfl
  have hvaltrue : ValueRepr cB.σ.mem N φc sret.toNat (.bool rv.truthy) := by
    rw [show ((.bool rv.truthy) : Value) = .bool ((cond rv.truthy (1#64) (0#64)) != 0#64) from by
      rw [hcondEq]]; exact hvalB
  have hpcB' : cB.σ.regs.get? Register.PC = some (0x800035dc#64) := by
    rw [hpcB, show (BitVec.update ((0x800035dc#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x800035dc#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hs1_B : cB.σ.regs.get? Register.x9 = some sret := by
    rw [hframeB Register.x9 (by decide)]; exact hs1_8
  have hcode_B : Eval_exprLoaded cB.σ.mem :=
    loaded_eval_expr_agreeP m3 cB.σ.mem
      (fun k hk => hmemframeB k (by rcases hsretEvalCode with h | h <;> omega)) hcode_m3
  ------------------------------------------------------------------------
  -- 0x800035dc: j 0x800033ec → shared epilogue entry
  ------------------------------------------------------------------------
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_800035dc_lg cB.σ cB.tick cB.steps (0x800035dc#64) vmiB hGB hpcB' hmiB hcode_B rfl
      (by rw [show ((0x800035dc#64:BitVec 64) + sign_extend (m := 64) (0x1ffe10#21)) = 0x800033ec#64 from by
            apply BitVec.eq_of_toNat_eq; decide]; decide) htickB
  have hstep10 : Step cB ⟨σ10, i10, cB.steps + 1⟩ := by cases cB; exact hs10'
  have hmem10e : σ10.mem = cB.σ.mem := hmem10
  have hpc_fin : σ10.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs10
    rwa [show ((0x800035dc#64:BitVec 64) + sign_extend (m := 64) (0x1ffe10#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : σ10.regs.get? Register.x9 = some sret := obs_jr_other' hobs10 Register.x9 (by decide) hs1_B
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hobs10
  have hout_fin : σ10.sailOutput = out0 := by
    rw [hobs10.out, sailOutput_sigmaPost_jump_x0]; exact houtB
  -- sp survives value_truthy/value_bool (both NotWrittenT/NotWrittenV frame x2)
  have hsp_T : cT.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeT Register.x2 (by decide)]; exact hsp_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs6 Register.x2 (by decide) hsp_T
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs8 Register.x2 (by decide) hsp_7
  have hsp_B : cB.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeB Register.x2 (by decide)]; exact hsp_8
  have hsp_fin : σ10.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other' hobs10 Register.x2 (by decide) hsp_B
  ------------------------------------------------------------------------
  -- spill slots survive; StoreRepr survives; MemExtends; frame.
  ------------------------------------------------------------------------
  have hslotAgree : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem σ10.mem := by
    intro k hk
    rw [hmem10e, ← hmemframeB k (by rcases hsretStk with h | h <;> omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val qv) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val pv) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val kv))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val kv) (by omega)]
  have hslotRa_f : read64 σ10.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 σ10.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 σ10.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 σ10.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  have hSL10 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = σ10.mem[k]? := by
    intro k hk
    rw [hmem10e, ← hmemframeB k (by rcases hsretInSL with ⟨hl, hr⟩; omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val qv) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val pv) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val kv))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val kv) (by omega)]
  have hstore_fin : StoreRepr σ10.mem N A φf φc st''.store :=
    hstoreSurv σ10.mem (fun k hk => hSL10 k hk)
  have hMemExt_c_8 : MemExtends c.σ.mem σ8.mem := by
    rw [hmem8e]
    exact ((MemExtends.refl c.σ.mem).trans
      (memExtends_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val kv))).trans
      ((memExtends_writeMap8 m1 (sp.toNat - 1016) (sdData_val pv)).trans
        (memExtends_writeMap8 m2 (sp.toNat - 1008) (sdData_val qv)))
  have hMemExt_8_10 : MemExtends σ8.mem σ10.mem := by
    rw [hmem10e, hmem8e]; exact hMemExtB
  have hMemExt_fin : MemExtends m0 σ10.mem :=
    (hMemExt.trans hMemExt_c_8).trans hMemExt_8_10
  -- callee-saved (noise) frame across the tail, then the prologue bridge.
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ10.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx10R : (Register.x10 == R) = false := abi_ne' (by decide)
    have hx11R : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx13R : (Register.x13 == R) = false := abi_ne' (by decide)
    have hx14R : (Register.x14 == R) = false := abi_ne' (by decide)
    have hx15R : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide)
    -- NotWrittenT: value_truthy preserves R (need R ≠ x10/x14/x15)
    have hNWT : NotWrittenT R := ⟨hx10R, hx14R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have hNWV : NotWrittenV R := ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ1: addi a0 (x10)
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ2..σ4: sd/sd/sd
    have f2 : σ2.regs.get? R = σ1.regs.get? R := frame_store_v hobs2 R hNWV
    have f3 : σ3.regs.get? R = σ2.regs.get? R := frame_store_v hobs3 R hNWV
    have f4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_v hobs4 R hNWV
    -- σ5: jal value_truthy (x1)
    have f5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    have fT : cT.σ.regs.get? R = σ5.regs.get? R := hframeT R hNWT
    -- σ6: mv a1,a0 (x11)
    have f6 : σ6.regs.get? R = cT.σ.regs.get? R :=
      (hobs6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11R hnpc' hmii')
    -- σ7: mv a0,s1 (x10)
    have f7 : σ7.regs.get? R = σ6.regs.get? R :=
      (hobs7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ8: jal value_bool (x1)
    have f8 : σ8.regs.get? R = σ7.regs.get? R :=
      (hobs8.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    have fB : cB.σ.regs.get? R = σ8.regs.get? R := hframeB R hNWV
    -- σ10: j (PC)
    have f10 : σ10.regs.get? R = cB.σ.regs.get? R :=
      (hobs10.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f10, fB, f8, f7, f6, fT, f5, f4, f3, f2, f1]
    exact hframe R hR' he8 he9 he18 he2
  ------------------------------------------------------------------------
  -- assemble PreEpilogueVD
  ------------------------------------------------------------------------
  have hSteps : Steps c ⟨σ10, i10, cB.steps + 1⟩ := by
    refine (Steps.single hstep1).trans (?_)
    refine (Steps.single hstep2).trans (?_)
    refine (Steps.single hstep3).trans (?_)
    refine (Steps.single hstep4).trans (?_)
    refine (Steps.single hstep5).trans (?_)
    refine hsT.trans (?_)
    refine (Steps.single hstep6).trans (?_)
    refine (Steps.single hstep7).trans (?_)
    refine (Steps.single hstep8).trans (?_)
    refine hsB.trans (?_)
    exact Steps.single hstep10
  refine ⟨⟨σ10, i10, cB.steps + 1⟩, hSteps, σ10.mem, ?_, hMemExt_fin, ?_⟩
  · refine ⟨hG10, hi10, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
      hout_fin, houtStr, rfl, (by rw [hmem10e]; exact hcode_B),
      (by rw [hmem10e]; exact hvaltrue), hstore_fin, hframeG,
      hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, ?_,
      hspLo, hspRam, (by omega), (by rw [htoh] at hbufWin ⊢; omega), hsp8, hraAl⟩
    · intro a ha hA
      by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
      · exact Or.inl hsr
      · refine Or.inr ?_
        rw [hmem10e, ← hmemframeB a hsr]
        show (writeMap8 m2 (sp.toNat-1008) (sdData_val qv))[a]? = m0[a]?
        rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val qv) (by omega)]
        show (writeMap8 m1 (sp.toNat-1016) (sdData_val pv))[a]? = m0[a]?
        rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val pv) (by omega)]
        show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val kv))[a]? = m0[a]?
        rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val kv) (by omega)]
        rcases hmemFrame a ha hA with hin | heq
        · exact absurd hin hsr
        · exact heq
  · intro m' hm'
    exact hstoreSurv m' (fun k hk => (hSL10 k hk).trans (hm' k hk))

end Vsa.Sim
