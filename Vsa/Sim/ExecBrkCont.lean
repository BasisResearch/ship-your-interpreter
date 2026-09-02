import Vsa.Sim.ExecSimCommon
import Vsa.Sim.Exec_stmtSites
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.GeomFacts
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 statement family: `execBlockA`/`execBlockD` + `ExecS.brk`/`ExecS.cont`

The register-only statement cases (`brk`/`cont`) — the statement-side analog of the
expression-side leaf `int`/`null` cases (`EvalIntSim`/`EvalNullSim`). They validate
the `exec_stmt` prologue/dispatch/epilogue infrastructure end-to-end: nothing
recurses, the store and output are UNCHANGED (`st` in = `st` out), and only the
status register `a0` is set (`1` for `brk`, `2` for `cont`).

This file provides two reusable multipliers, mirroring the expression-side
`blockA_k`/`blockD_v` (`EvalSimCommon.lean`):

* **`ExecArmEntryK`** + **`execBlockA`** — the shared prologue (`addi sp,-176`, five
  spills of `s0/s1/s2/s3/ra`, the `mv` moves, `li a6,8`) + jump-table dispatch
  (`auipc`/`lw`/`bltu`/`lwu`/`slli`/`add`/`lw`/`add`/`jr`), landing at a per-kind arm
  PC. Parameterized over the dispatched kind `k`, arm PC `armPC`, and the
  `StmtSlotPinned k armPC` coupling.
* **`execBlockD`** — the shared epilogue (`ld ra/s0/s1/s2/s3`, `addi sp,176`, `ret`),
  from a state with `x10 = StatusCode status` already set, producing `ExecExit`.
  Reused by `brk` directly; `cont` threads the equivalent restore-copy at its own
  PCs (`li a0,2` interleaved, but the loads never touch `x10`).

`execBrkSim`/`execContSim` compose `execBlockA ≫ (li a0,N) ≫ execBlockD` into
`Triple (ExecEntry …) (ExecExit … st .brk/.cont …)`.

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

/-! ## Address arithmetic for the 176-byte `exec_stmt` frame + spill windows -/

/-- `addi sp,sp,-176`: `sp + sext 0xf50 = sp - 176`. -/
theorem sp_sub176 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xf50#12)) = sp - 176#64 := by
  have hs : (sign_extend (m := 64) (0xf50#12) : BitVec 64) = -(176#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(176#64) : BitVec 64).toNat = 2^64 - 176 := by decide
  have h : (176#64 : BitVec 64).toNat = 176 := by decide
  rw [hn, h]; have := sp.isLt; omega

/-- `addi sp,sp,176`: `(sp - 176) + sext 0x0b0 = sp`. -/
theorem sp_add176 (sp : BitVec 64) :
    (sp - 176#64) + sign_extend (m := 64) (0x0b0#12) = sp := by
  have hs : (sign_extend (m := 64) (0x0b0#12) : BitVec 64) = 176#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have h : (176#64 : BitVec 64).toNat = 176 := by decide
  rw [h]; have := sp.isLt; omega

/-- A spill store/load `off(sp')` where `sp' = sp - 176`, `off ∈ {136,144,152,160,168}`
targets `sp - (176 - off)`. -/
theorem spill_addr176 (sp : BitVec 64) (off : BitVec 12) (k : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = 176 - k)
    (hk : k ≤ 176) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) off).toNat = sp.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_sub, hoff]
  have h : (176#64 : BitVec 64).toNat = 176 := by decide
  rw [h]; have := sp.isLt; omega

/-- ra@168 → sp-8. -/
theorem es_off168 (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) (0x0a8#12)).toNat = sp.toNat - 8 :=
  spill_addr176 sp (0x0a8#12) 8 (by decide) (by omega) hsp
/-- s0@160 → sp-16. -/
theorem es_off160 (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 16 :=
  spill_addr176 sp (0x0a0#12) 16 (by decide) (by omega) hsp
/-- s1@152 → sp-24. -/
theorem es_off152 (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 24 :=
  spill_addr176 sp (0x098#12) 24 (by decide) (by omega) hsp
/-- s2@144 → sp-32. -/
theorem es_off144 (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 32 :=
  spill_addr176 sp (0x090#12) 32 (by decide) (by omega) hsp
/-- s3@136 → sp-40. -/
theorem es_off136 (sp : BitVec 64) (hsp : 176 ≤ sp.toNat) :
    ((sp - 176#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 40 :=
  spill_addr176 sp (0x088#12) 40 (by decide) (by omega) hsp

/-! ## `Exec_stmtLoaded` survives a stack-window `sd` spill

The code region is `[0x80003fe0, 0x80004308)` (chunks 0..12). A prologue `sd`
writes an 8-byte window disjoint from that region. -/
theorem loaded_exec_stmt_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a8 + 8 ≤ 0x80003fe0 ∨ 0x80004308 ≤ a8)
    (h : Exec_stmtLoaded mem) : Exec_stmtLoaded (writeMap8 mem a8 d) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [exec_stmtChunk0] at c0 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk1] at c1 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk2] at c2 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk3] at c3 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk4] at c4 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk5] at c5 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk6] at c6 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk7] at c7 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk8] at c8 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk9] at c9 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk10] at c10 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk11] at c11 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [exec_stmtChunk12] at c12 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## `ExecArmEntryK` — machine state at a per-kind arm entry (dispatch target)

The case-INDEPENDENT half of the `exec_stmt` prologue + jump-table dispatch. It
lands at the per-kind arm PC `armPC` (from `StmtSlotPinned k armPC`), with the four
callee-saved slots spilled, `sp` lowered by 176, the ABI args moved into
`s0/s1/s2/s3`, and every store/frame/geometry fact carried. `brk`/`cont` instantiate
`k := 7/8`, `armPC := 0x80004098/0x800040b8`.

`v8/v9/v18/v19` are the ENTRY callee-saved `s0/s1/s2/s3` (spilled before the `mv`
moves clobber them), i.e. the ghost-frame values `g x8/x9/x18/x19`. `ment` is the
post-memory (`m0` + five spills). -/
def ExecArmEntryK
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (armPC : BitVec 64)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some armPC ∧
  c.σ.regs.get? Register.x8 = some aStmt ∧            -- s0 = Stmt*  (mv s0,a1)
  c.σ.regs.get? Register.x9 = some aInterp ∧          -- s1 = interp* (mv s1,a0)
  c.σ.regs.get? Register.x19 = some aEnv ∧            -- s3 = env     (mv s3,a2)
  c.σ.regs.get? Register.x18 = some aRet ∧            -- s2 = retslot (mv s2,a3)
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧    -- sp lowered
  c.σ.regs.get? Register.x1 = some r ∧               -- ra still = r (also spilled)
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
  c.σ.mem = ment ∧ Exec_stmtLoaded ment ∧
  StoreRepr ment N A φf φc st.store ∧
  -- the five spill slots hold the entry ra/s0/s1/s2/s3
  read64 ment (sp.toNat - 8) = some r.toNat ∧
  read64 ment (sp.toNat - 16) = some v8.toNat ∧
  read64 ment (sp.toNat - 24) = some v9.toNat ∧
  read64 ment (sp.toNat - 32) = some v18.toNat ∧
  read64 ment (sp.toNat - 40) = some v19.toNat ∧
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
  g Register.x18 = some v18 ∧ g Register.x19 = some v19 ∧
  g Register.x2 = some sp ∧
  -- callee-saved regs not clobbered by the prologue still read `g R`
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = g R) ∧
  -- memory frame: `ment` differs from `m0` only inside the stack window `[SL.lo, sp)`
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) ∧
  -- geometry the epilogue restores need
  176 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 176 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧ r.toNat % 4 = 0

/-! ## `execBlockD` — the shared `exec_stmt` epilogue (restore + `addi sp,176` + `ret`)

The seven-instruction restore/return run at `0x8000409c`: `ld ra/s0/s1/s2/s3` from
`sp+{168,160,152,144,136}` (i.e. `sp-{8,16,24,32,40}` of the ENTRY sp), `addi
sp,sp,176`, `ret`. It never inspects any payload; it only threads the produced
`status` (via `x10 = StatusCode status`, set by the arm's `li a0,N` BEFORE entry)
into `ExecExit.a0`, and re-establishes the callee-saved frame from the spill slots.

`PreExecEpilogue` is the machine state at `0x8000409c`. `st'` is the (unchanged)
post-state; `status` the produced status; `mpre` the current memory (entry `m0`
plus the five prologue spills, unchanged in the region the epilogue reads). -/
def PreExecEpilogue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (status : Status)
    (sp r aRet : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 mpre : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x8000409c#64) ∧
  c.σ.regs.get? Register.x10 = some (StatusCode status) ∧   -- a0 = status (li a0,N ran)
  c.σ.regs.get? Register.x2 = some (sp - 176#64) ∧          -- sp lowered
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  c.σ.sailOutput = out0 ∧ String.join out0.toList = st'.out ∧
  c.σ.mem = mpre ∧ Exec_stmtLoaded mpre ∧
  StoreRepr mpre N A φf φc st'.store ∧
  -- callee-saved regs not clobbered by the prologue (not s0/s1/s2/s3/sp) still read `g R`
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x19 == R) = false →
    (Register.x2 == R) = false → c.σ.regs.get? R = g R) ∧
  -- the five callee-saved spill slots still hold the entry ra/s0/s1/s2/s3
  read64 mpre (sp.toNat - 8) = some r.toNat ∧
  read64 mpre (sp.toNat - 16) = some v8.toNat ∧
  read64 mpre (sp.toNat - 24) = some v9.toNat ∧
  read64 mpre (sp.toNat - 32) = some v18.toNat ∧
  read64 mpre (sp.toNat - 40) = some v19.toNat ∧
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
  g Register.x18 = some v18 ∧ g Register.x19 = some v19 ∧
  g Register.x2 = some sp ∧
  -- memory frame: `mpre` differs from entry `m0` only inside the stack window
  -- `[SL.lo, sp)` (the prologue spills). No arena / retslot write on the brk/cont path.
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mpre[a]? = m0[a]?) ∧
  -- geometry the restores need
  176 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 176 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
  r.toNat % 4 = 0

/-- The `ExecExit` produced by the epilogue, packaged as a `Triple`. The store /
output are re-represented with IDENTITY φ-maps (`st'.store` unchanged on the
brk/cont path). `retval` is vacuous (brk/cont are not `.ret`). -/
theorem execBlockD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (status : Status)
    (sp r aRet : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (hnotret : ∀ v, status ≠ .ret v) :
    Triple
      (fun c => ∃ mpre, PreExecEpilogue g N A SL φf φc st' status sp r aRet v8 v9 v18 v19 out0 m0 mpre c)
      (ExecExit g N A SL φf φc nf nc st' status sp r aRet m0) := by
  intro c hpre
  obtain ⟨mpre, hG, htick, hpc, ha0, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmem, hcode, hstore, hframe,
    hslotRa, hslotS0, hslotS1, hslotS2, hslotS3, hgx8, hgx9, hgx18, hgx19, hgx2, hmemframe,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- restore addresses
  have haRa : ((sp - 176#64) + sign_extend (m := 64) (0x0a8#12)).toNat = sp.toNat - 8 := es_off168 sp hsp176
  have haS0 : ((sp - 176#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 16 := es_off160 sp hsp176
  have haS1 : ((sp - 176#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 24 := es_off152 sp hsp176
  have haS2 : ((sp - 176#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 32 := es_off144 sp hsp176
  have haS3 : ((sp - 176#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 40 := es_off136 sp hsp176
  -- spill_roundtrip byte facts for each slot (reuse the value-independent bridge)
  obtain ⟨ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, hra0, hra1, hra2, hra3, hra4, hra5, hra6, hra7, hraSext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 8) r hslotRa
  obtain ⟨s00, s01, s02, s03, s04, s05, s06, s07, hs00, hs01, hs02, hs03, hs04, hs05, hs06, hs07, hs0Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 16) v8 hslotS0
  obtain ⟨s10, s11, s12, s13, s14, s15, s16, s17, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs1Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 24) v9 hslotS1
  obtain ⟨s20, s21, s22, s23, s24, s25, s26, s27, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs2Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 32) v18 hslotS2
  obtain ⟨s30, s31, s32, s33, s34, s35, s36, s37, hs30, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs3Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 40) v19 hslotS3
  -- ============ 0x8000409c: ld ra,168(sp) → x1 := r ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000409c_es c.σ c.tick c.steps (0x8000409c#64) vmi (sp-176#64) ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
      hG hpc hmi hsp (hmem ▸ hcode) rfl
      (by rw [haRa]; omega) (by rw [haRa]; omega) (by rw [haRa, htoh]; right; omega) (by rw [haRa]; omega)
      (by rw [haRa, hmem]; exact hra0) (by rw [haRa, hmem]; exact hra1) (by rw [haRa, hmem]; exact hra2)
      (by rw [haRa, hmem]; exact hra3) (by rw [haRa, hmem]; exact hra4) (by rw [haRa, hmem]; exact hra5)
      (by rw [haRa, hmem]; exact hra6) (by rw [haRa, hmem]; exact hra7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = mpre := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800040a0#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x8000409c#64) 4 = (0x800040a0#64:BitVec 64) from by decide] at this
  have hra_1 : σ1.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hraSext] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800040a0: ld s0,160(sp) → x8 := v8 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800040a0_es σ1 i1 (c.steps + 1) (0x800040a0#64) vmi1 (sp-176#64) s00 s01 s02 s03 s04 s05 s06 s07
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl
      (by rw [haS0]; omega) (by rw [haS0]; omega) (by rw [haS0, htoh]; right; omega) (by rw [haS0]; omega)
      (by rw [haS0, hmem1e]; exact hs00) (by rw [haS0, hmem1e]; exact hs01) (by rw [haS0, hmem1e]; exact hs02)
      (by rw [haS0, hmem1e]; exact hs03) (by rw [haS0, hmem1e]; exact hs04) (by rw [haS0, hmem1e]; exact hs05)
      (by rw [haS0, hmem1e]; exact hs06) (by rw [haS0, hmem1e]; exact hs07) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = mpre := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800040a4#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x800040a0#64) 4 = (0x800040a4#64:BitVec 64) from by decide] at this
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs0Sext] at this
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x800040a4: ld s1,152(sp) → x9 := v9 ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800040a4_es σ2 i2 (c.steps + 1 + 1) (0x800040a4#64) vmi2 (sp-176#64) s10 s11 s12 s13 s14 s15 s16 s17
      hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haS1]; omega) (by rw [haS1]; omega) (by rw [haS1, htoh]; right; omega) (by rw [haS1]; omega)
      (by rw [haS1, hmem2e]; exact hs10) (by rw [haS1, hmem2e]; exact hs11) (by rw [haS1, hmem2e]; exact hs12)
      (by rw [haS1, hmem2e]; exact hs13) (by rw [haS1, hmem2e]; exact hs14) (by rw [haS1, hmem2e]; exact hs15)
      (by rw [haS1, hmem2e]; exact hs16) (by rw [haS1, hmem2e]; exact hs17) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = mpre := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x800040a8#64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x800040a4#64) 4 = (0x800040a8#64:BitVec 64) from by decide] at this
  have hx9_3 : σ3.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs1Sext] at this
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  have ha0_3 : σ3.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 := obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x800040a8: ld s2,144(sp) → x18 := v18 ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800040a8_es σ3 i3 (c.steps + 1 + 1 + 1) (0x800040a8#64) vmi3 (sp-176#64) s20 s21 s22 s23 s24 s25 s26 s27
      hG3 hpc3 hmi3 hsp_3 hcode3 rfl
      (by rw [haS2]; omega) (by rw [haS2]; omega) (by rw [haS2, htoh]; right; omega) (by rw [haS2]; omega)
      (by rw [haS2, hmem3e]; exact hs20) (by rw [haS2, hmem3e]; exact hs21) (by rw [haS2, hmem3e]; exact hs22)
      (by rw [haS2, hmem3e]; exact hs23) (by rw [haS2, hmem3e]; exact hs24) (by rw [haS2, hmem3e]; exact hs25)
      (by rw [haS2, hmem3e]; exact hs26) (by rw [haS2, hmem3e]; exact hs27) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = mpre := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x800040ac#64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x800040a8#64) 4 = (0x800040ac#64:BitVec 64) from by decide] at this
  have hx18_4 : σ4.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs2Sext] at this
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  have ha0_4 : σ4.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 := obs_alu_other' hobs4 Register.x8 (by decide) hx8_3
  have hx9_4 : σ4.regs.get? Register.x9 = some v9 := obs_alu_other' hobs4 Register.x9 (by decide) hx9_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hcode4 : Exec_stmtLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- ============ 0x800040ac: ld s3,136(sp) → x19 := v19 ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800040ac_es σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800040ac#64) vmi4 (sp-176#64) s30 s31 s32 s33 s34 s35 s36 s37
      hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haS3]; omega) (by rw [haS3]; omega) (by rw [haS3, htoh]; right; omega) (by rw [haS3]; omega)
      (by rw [haS3, hmem4e]; exact hs30) (by rw [haS3, hmem4e]; exact hs31) (by rw [haS3, hmem4e]; exact hs32)
      (by rw [haS3, hmem4e]; exact hs33) (by rw [haS3, hmem4e]; exact hs34) (by rw [haS3, hmem4e]; exact hs35)
      (by rw [haS3, hmem4e]; exact hs36) (by rw [haS3, hmem4e]; exact hs37) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps+1+1+1+1⟩ ⟨σ5, i5, c.steps+1+1+1+1+1⟩ := hstep5'
  have hmem5e : σ5.mem = mpre := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x800040b0#64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x800040ac#64) 4 = (0x800040b0#64:BitVec 64) from by decide] at this
  have hx19_5 : σ5.regs.get? Register.x19 = some v19 := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs3Sext] at this
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  have ha0_5 : σ5.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 := obs_alu_other' hobs5 Register.x8 (by decide) hx8_4
  have hx9_5 : σ5.regs.get? Register.x9 = some v9 := obs_alu_other' hobs5 Register.x9 (by decide) hx9_4
  have hx18_5 : σ5.regs.get? Register.x18 = some v18 := obs_alu_other' hobs5 Register.x18 (by decide) hx18_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hcode5 : Exec_stmtLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- ============ 0x800040b0: addi sp,sp,176 → x2 := sp ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_800040b0_es σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x800040b0#64) vmi5 (sp-176#64) hG5 hpc5 hmi5 hsp_5 hcode5 rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps+1+1+1+1+1⟩ ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ := hstep6'
  have hmem6e : σ6.mem = mpre := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x800040b4#64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x800040b0#64) 4 = (0x800040b4#64:BitVec 64) from by decide] at this
  have hsp_6 : σ6.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [sp_add176] at this
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha0_6 : σ6.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := obs_alu_other' hobs6 Register.x8 (by decide) hx8_5
  have hx9_6 : σ6.regs.get? Register.x9 = some v9 := obs_alu_other' hobs6 Register.x9 (by decide) hx9_5
  have hx18_6 : σ6.regs.get? Register.x18 = some v18 := obs_alu_other' hobs6 Register.x18 (by decide) hx18_5
  have hx19_6 : σ6.regs.get? Register.x19 = some v19 := obs_alu_other' hobs6 Register.x19 (by decide) hx19_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hcode6 : Exec_stmtLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- ============ 0x800040b4: ret → PC := r ============
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r hraAl]; exact hraAl
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_800040b4_es σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800040b4#64) vmi6 r hG6 hpc6 hmi6 hra_6 hcode6 rfl hrettgt hi6
  have hstep7 : Step ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ := hstep7'
  have hmem7e : σ7.mem = mpre := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs7
  have ha0_7 : σ7.regs.get? Register.x10 = some (StatusCode status) := obs_jr_other' hobs7 Register.x10 (by decide) ha0_6
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_jr_other' hobs7 Register.x1 (by decide) hra_6
  have hsp_7 : σ7.regs.get? Register.x2 = some sp := obs_jr_other' hobs7 Register.x2 (by decide) hsp_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_jr_other' hobs7 Register.x8 (by decide) hx8_6
  have hx9_7 : σ7.regs.get? Register.x9 = some v9 := obs_jr_other' hobs7 Register.x9 (by decide) hx9_6
  have hx18_7 : σ7.regs.get? Register.x18 = some v18 := obs_jr_other' hobs7 Register.x18 (by decide) hx18_6
  have hx19_7 : σ7.regs.get? Register.x19 = some v19 := obs_jr_other' hobs7 Register.x19 (by decide) hx19_6
  obtain ⟨vmi7, hmi7⟩ := obs_jr_minstret hobs7
  -- output invariance through the 7 epilogue steps
  have hout7 : σ7.sailOutput = out0 := by
    rw [hobs7.out, sailOutput_sigmaPost_jump_x0, hobs6.out, sailOutput_sigmaPost_alu,
      hobs5.out, sailOutput_sigmaPost_alu, hobs4.out, sailOutput_sigmaPost_alu,
      hobs3.out, sailOutput_sigmaPost_alu, hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  -- the abi-disequality helper (an AbiPreserved X = false register differs from any
  -- AbiPreserved R = true register)
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- epilogue register frame: callee-saved (excl x8/x9/x18/x19/x2/x1/x10) unchanged.
  have hframe7 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false → (Register.x2 == R) = false →
      (Register.x1 == R) = false → (Register.x10 == R) = false →
      σ7.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8 he9 he18 he19 he2 he1 he10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have a : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd v) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
    have jr : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
        ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    exact (jr hobs7).trans ((a hobs6 he2).trans ((a hobs5 he19).trans ((a hobs4 he18).trans
      ((a hobs3 he9).trans ((a hobs2 he8).trans (a hobs1 he1))))))
  -- assemble ExecExit
  refine ⟨⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩, ?_, ?_⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      (Steps.single hstep7))))))
  · refine
      { good := hG7
        tick := hi7
        pc := hpc7
        a0 := ha0_7
        ra := hra_7
        spReg := hsp_7
        minstret := ⟨_, hmi7⟩
        store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, by rw [hmem7e]; exact hstore⟩
        out := ?_
        retval := ?_
        frame := ?_
        memFrame := ?_ }
    · -- OutRepr σ7 st'
      show Vsa.Machine.output σ7 = st'.out
      simp only [Vsa.Machine.output]; rw [hout7]; exact houtStr
    · -- retval: vacuous (status ≠ .ret v)
      intro v hv; exact absurd hv (hnotret v)
    · -- ExecExit.frame: every AbiPreservedNoise R = g R at exit
      intro R hR
      by_cases h8 : (Register.x8 == R) = true
      · have : R = Register.x8 := by rw [beq_iff_eq] at h8; exact h8.symm
        subst this; rw [hx8_7]; exact hgx8.symm
      by_cases h9 : (Register.x9 == R) = true
      · have : R = Register.x9 := by rw [beq_iff_eq] at h9; exact h9.symm
        subst this; rw [hx9_7]; exact hgx9.symm
      by_cases h18 : (Register.x18 == R) = true
      · have : R = Register.x18 := by rw [beq_iff_eq] at h18; exact h18.symm
        subst this; rw [hx18_7]; exact hgx18.symm
      by_cases h19 : (Register.x19 == R) = true
      · have : R = Register.x19 := by rw [beq_iff_eq] at h19; exact h19.symm
        subst this; rw [hx19_7]; exact hgx19.symm
      by_cases h2 : (Register.x2 == R) = true
      · have : R = Register.x2 := by rw [beq_iff_eq] at h2; exact h2.symm
        subst this; rw [hsp_7]; exact hgx2.symm
      · -- x1/x10 are NOT AbiPreserved, so both differ from AbiPreservedNoise R.
        have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hR.1
        have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hR.1
        rw [hframe7 R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
          (by simpa using h19) (by simpa using h2) h1 h10]
        exact hframe R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
          (by simpa using h19) (by simpa using h2)
    · -- memFrame: memory unchanged (σ7.mem = mpre), differs from m0 only in stack window
      intro a hstk _harena
      right; rw [hmem7e]; exact hmemframe a hstk

/-! ## `execBlockA` — the prologue + jump-table dispatch (residual)

The shared prologue (`addi sp,-176`; five spills of `s0/s1/s2/s3/ra`; the `mv`
moves; `li a6,8`) + jump-table dispatch (`auipc`/`lw`/`bltu`/`lwu`/`slli`/`add`/`lw`/
`add`/`jr`), landing at the per-kind arm PC. It is the statement-side analog of
`blockA_k` (`EvalIntSim2.lean`) and is stated here as `ExecBlockAGoal` — a named
residual (documented, like `env_get_found_spec`'s `hreach`). Its ~21-step per-site
proof (mirroring the fully-proven expression-side `blockA_k`) is the last open piece
of the brk/cont path; every OTHER part of the path (`execBlockD`, the arm `li a0`,
the whole compositional glue below) is proven unconditionally.

`ExecBlockAGoal g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet k armPC m0 out0`
is the Triple `ExecEntry(kind s)  →  ∃ ment v8 v9 v18 v19, ExecArmEntryK … armPC …`. -/
def ExecBlockAGoal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (armPC : BitVec 64)
    (m0 : Mem) (out0 : Array String) : Prop :=
  Triple
    (fun c => ExecEntry g N A SL φf φc st d env s sp r aInterp aStmt aEnv aRet m0 c
      ∧ c.σ.sailOutput = out0)
    (fun c => ∃ ment v8 v9 v18 v19,
      ExecArmEntryK g N A SL φf φc st armPC sp r aInterp aStmt aEnv aRet
        v8 v9 v18 v19 out0 m0 ment c)

/-! ## `StmtSlotPinned` survives a `writeMap8` disjoint from its four slot bytes. -/
theorem stmtslot_wm8 (k : Nat) (armPC : BitVec 64) (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ stmtJumpTableBase + 4 * k ∨ stmtJumpTableBase + 4 * k + 4 ≤ a8)
    (hh : StmtSlotPinned k armPC mem) : StmtSlotPinned k armPC (writeMap8 mem a8 dd) := by
  obtain ⟨t0, t1, t2, t3, p0, p1, p2, p3, ptgt⟩ := hh.b0
  exact ⟨t0, t1, t2, t3,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p0,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p1,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p2,
    by rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p3, ptgt⟩

/-! ## `execBlockA` — the `exec_stmt` prologue + jump-table dispatch (case-independent)

The statement-side analog of the fully-proven expression-side `blockA_k`
(`EvalIntSim2.lean`). It runs the 21-instruction prologue (`addi sp,-176`; five
spills of `s0/s1/s2/s3/ra`; the four `mv` moves `s0:=a1`, `s1:=a0`, `s3:=a2`,
`s2:=a3`; `li a6,8`) + jump-table dispatch (`auipc/addi a4`, `lw`/`bltu`/`lwu`/
`slli`/`add`/`lw`/`add`/`jr`), landing at the per-kind arm PC `armPC`.

Parameterized over the dispatched kind `k`, arm PC `armPC`, and the
`StmtSlotPinned k armPC m0` coupling — so `brk` (`k=7`, `0x80004098`), `cont`
(`k=8`, `0x800040b8`), and every future statement kind instantiate it. Unlike
`blockA_k` there is NO sub-callee (`exec_stmt` calls nothing in the prologue) so
only `Exec_stmtLoaded` is threaded (via `loaded_exec_stmt_writeMap8`), and
`ExecArmEntryK` carries no `StmtRepr`/callee-loaded facts — a strict
simplification. Proven UNCONDITIONALLY. -/
theorem execBlockA
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (s : Stmt)
    (k : Nat) (armPC : BitVec 64)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (hkle : k ≤ 8) (hklt : k < 128)
    (hkind : read32 m0 aStmt.toNat = some k)
    (hslot : StmtSlotPinned k armPC m0)
    (harmAl : armPC.toNat % 4 = 0)
    -- GeomFacts retrofit (rule 6): the jump-table slot's stack-disjointness
    -- residual is supplied as ONE projected record `StackDisjoint …` (the D-atom
    -- alone — the table is a below-HTIF rodata object, so not a full `ObjGeom`).
    -- The M6 caller hands this record; `htableStk` below is an O(1) `.disj`
    -- projection off it, stated over `Nat` endpoints so there is NO pair whnf.
    (htableGeom : StackDisjoint (stmtJumpTableBase + 4 * k) 4 SL sp.toNat) :
    ExecBlockAGoal g N A SL φf φc st d env s
      sp r aInterp aStmt aEnv aRet armPC m0 out0 := by
  intro c hpre'
  have htableStk : stmtJumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * k :=
    htableGeom.disj
  obtain ⟨he, hout0⟩ := hpre'
  have hG := he.good; have htick := he.tick; have hpc := he.pc
  have ha0 := he.a0; have ha1 := he.a1; have ha2 := he.a2; have ha3 := he.a3
  have hra := he.ra; have hraAl := he.ra_align; have hspReg := he.spReg
  have hstackOK := he.stackOK
  obtain ⟨vmi, hmi⟩ := he.minstret
  have hmem := he.mem; have hcode := he.code; have hstmt := he.stmt
  have hstore := he.store; have hstoreSurv := he.store_survives_sp; have hout := he.out
  have hframe := he.frame; have hcodeStk := he.code_stack_disjoint
  have hstkRam := he.stack_ram; have hstkWin := he.stack_win
  have hstmtStk := he.stmt_stack_disjoint; have hstmtAl := he.stmt_align
  have hstmtRam := he.stmt_ram; have hstmtWin := he.stmt_win
  obtain ⟨⟨v8, h8_0⟩, ⟨v9, h9_0⟩, ⟨v18, h18_0⟩, ⟨v19, h19_0⟩⟩ := he.spill_defined
  have hload0 : Exec_stmtLoaded c.σ.mem := hcode
  have hslot0 : StmtSlotPinned k armPC c.σ.mem := hmem ▸ hslot
  have haddr0 : (aStmt + sign_extend (m := 64) (0x000#12)).toNat = aStmt.toNat := by
    rw [sext_zero, BitVec.add_zero]
  obtain ⟨hkb0v, hkb1v, hkb2v, hkb3v, hkb0, hkb1, hkb2, hkb3, hkrec⟩ :=
    kind_bytes (hmem ▸ hkind)
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp176 : 176 ≤ sp.toNat := by omega
  have hpce : c.σ.regs.get? Register.PC = some (0x80003fe0#64 : BitVec 64) := by rw [hpc]; rfl
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- stmt kind read-bytes in m0 survive the four disjoint spills (used at 80004014/8000401c)
  -- (established after the spills as σ6-side reads; done inline below)
  -- ============ 0x80003fe0: addi sp,sp,-176 → x2 := sp - 176 ============
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80003fe0_es c.σ c.tick c.steps (0x80003fe0#64) vmi sp hG hpce hmi hspReg hload0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003fe4#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80003fe0#64) 4 = (0x80003fe4#64:BitVec 64) from by decide] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 176#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub176] at this
  have h8_1 : σ1.regs.get? Register.x8 = some v8 := obs_alu_other' hobs1 Register.x8 (by decide) h8_0
  have h9_1 : σ1.regs.get? Register.x9 = some v9 := obs_alu_other' hobs1 Register.x9 (by decide) h9_0
  have h18_1 : σ1.regs.get? Register.x18 = some v18 := obs_alu_other' hobs1 Register.x18 (by decide) h18_0
  have h19_1 : σ1.regs.get? Register.x19 = some v19 := obs_alu_other' hobs1 Register.x19 (by decide) h19_0
  have ha0_1 : σ1.regs.get? Register.x10 = some aInterp := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 : σ1.regs.get? Register.x11 = some aStmt := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha2_1 : σ1.regs.get? Register.x12 = some aEnv := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have ha3_1 : σ1.regs.get? Register.x13 = some aRet := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hra_1 : σ1.regs.get? Register.x1 = some r := obs_alu_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- spill address helpers (sp-176 window)
  have haS0 : ((sp - 176#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 16 := es_off160 sp hsp176
  have haS1 : ((sp - 176#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 24 := es_off152 sp hsp176
  have haS2 : ((sp - 176#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 32 := es_off144 sp hsp176
  have haS3 : ((sp - 176#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 40 := es_off136 sp hsp176
  have haRa : ((sp - 176#64) + sign_extend (m := 64) (0x0a8#12)).toNat = sp.toNat - 8 := es_off168 sp hsp176
  -- ============ 0x80003fe4: sd s0,160(sp') → mem[sp-16] := v8 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80003fe4_es σ1 i1 (c.steps+1) (0x80003fe4#64) vmi1 (sp-176#64) v8 hG1 hpc1 hmi1 hsp_1 h8_1 (hmem1e ▸ hload0) rfl
      (by rw [haS0]; have := hstkRam.1; omega) (by rw [haS0]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haS0]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haS0]; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hs2
  have hmem2e : σ2.mem = writeMap8 c.σ.mem (sp.toNat - 16) (sdData_val v8) := by
    rw [hmem2, mem_afterNextPC, hmem1e, haS0]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003fe8#64) := by
    have := obs_store_pc_val hobs2; rwa [show BitVec.addInt (0x80003fe4#64) 4 = (0x80003fe8#64:BitVec 64) from by decide] at this
  have hload2 : Exec_stmtLoaded σ2.mem := by
    rw [hmem2e]; exact loaded_exec_stmt_writeMap8 c.σ.mem (sp.toNat-16) (sdData_val v8) (by have := hcodeStk; omega) hload0
  have hslot2 : StmtSlotPinned k armPC σ2.mem := by
    rw [hmem2e]; exact stmtslot_wm8 k armPC c.σ.mem (sp.toNat-16) (sdData_val v8) (by have := htableStk; omega) hslot0
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-176#64) := obs_store_other_val' hobs2 Register.x2 (by decide) hsp_1
  have h9_2 : σ2.regs.get? Register.x9 = some v9 := obs_store_other_val' hobs2 Register.x9 (by decide) h9_1
  have h18_2 : σ2.regs.get? Register.x18 = some v18 := obs_store_other_val' hobs2 Register.x18 (by decide) h18_1
  have h19_2 : σ2.regs.get? Register.x19 = some v19 := obs_store_other_val' hobs2 Register.x19 (by decide) h19_1
  have ha0_2 : σ2.regs.get? Register.x10 = some aInterp := obs_store_other_val' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 : σ2.regs.get? Register.x11 = some aStmt := obs_store_other_val' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 : σ2.regs.get? Register.x12 = some aEnv := obs_store_other_val' hobs2 Register.x12 (by decide) ha2_1
  have ha3_2 : σ2.regs.get? Register.x13 = some aRet := obs_store_other_val' hobs2 Register.x13 (by decide) ha3_1
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_store_other_val' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  -- ============ 0x80003fe8: sd s1,152(sp') → mem[sp-24] := v9 ============
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80003fe8_es σ2 i2 (c.steps+1+1) (0x80003fe8#64) vmi2 (sp-176#64) v9 hG2 hpc2 hmi2 hsp_2 h9_2 hload2 rfl
      (by rw [haS1]; have := hstkRam.1; omega) (by rw [haS1]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haS1]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haS1]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hs3
  have hmem3e : σ3.mem = writeMap8 σ2.mem (sp.toNat - 24) (sdData_val v9) := by
    rw [hmem3, mem_afterNextPC, haS1]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003fec#64) := by
    have := obs_store_pc_val hobs3; rwa [show BitVec.addInt (0x80003fe8#64) 4 = (0x80003fec#64:BitVec 64) from by decide] at this
  have hload3 : Exec_stmtLoaded σ3.mem := by
    rw [hmem3e]; exact loaded_exec_stmt_writeMap8 σ2.mem (sp.toNat-24) (sdData_val v9) (by have := hcodeStk; omega) hload2
  have hslot3 : StmtSlotPinned k armPC σ3.mem := by
    rw [hmem3e]; exact stmtslot_wm8 k armPC σ2.mem (sp.toNat-24) (sdData_val v9) (by have := htableStk; omega) hslot2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-176#64) := obs_store_other_val' hobs3 Register.x2 (by decide) hsp_2
  have h18_3 : σ3.regs.get? Register.x18 = some v18 := obs_store_other_val' hobs3 Register.x18 (by decide) h18_2
  have h19_3 : σ3.regs.get? Register.x19 = some v19 := obs_store_other_val' hobs3 Register.x19 (by decide) h19_2
  have ha0_3 : σ3.regs.get? Register.x10 = some aInterp := obs_store_other_val' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 : σ3.regs.get? Register.x11 = some aStmt := obs_store_other_val' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 : σ3.regs.get? Register.x12 = some aEnv := obs_store_other_val' hobs3 Register.x12 (by decide) ha2_2
  have ha3_3 : σ3.regs.get? Register.x13 = some aRet := obs_store_other_val' hobs3 Register.x13 (by decide) ha3_2
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_store_other_val' hobs3 Register.x1 (by decide) hra_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  -- ============ 0x80003fec: sd s2,144(sp') → mem[sp-32] := v18 ============
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80003fec_es σ3 i3 (c.steps+1+1+1) (0x80003fec#64) vmi3 (sp-176#64) v18 hG3 hpc3 hmi3 hsp_3 h18_3 hload3 rfl
      (by rw [haS2]; have := hstkRam.1; omega) (by rw [haS2]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haS2]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haS2]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hs4
  have hmem4e : σ4.mem = writeMap8 σ3.mem (sp.toNat - 32) (sdData_val v18) := by
    rw [hmem4, mem_afterNextPC, haS2]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80003ff0#64) := by
    have := obs_store_pc_val hobs4; rwa [show BitVec.addInt (0x80003fec#64) 4 = (0x80003ff0#64:BitVec 64) from by decide] at this
  have hload4 : Exec_stmtLoaded σ4.mem := by
    rw [hmem4e]; exact loaded_exec_stmt_writeMap8 σ3.mem (sp.toNat-32) (sdData_val v18) (by have := hcodeStk; omega) hload3
  have hslot4 : StmtSlotPinned k armPC σ4.mem := by
    rw [hmem4e]; exact stmtslot_wm8 k armPC σ3.mem (sp.toNat-32) (sdData_val v18) (by have := htableStk; omega) hslot3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-176#64) := obs_store_other_val' hobs4 Register.x2 (by decide) hsp_3
  have h19_4 : σ4.regs.get? Register.x19 = some v19 := obs_store_other_val' hobs4 Register.x19 (by decide) h19_3
  have ha0_4 : σ4.regs.get? Register.x10 = some aInterp := obs_store_other_val' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 : σ4.regs.get? Register.x11 = some aStmt := obs_store_other_val' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 : σ4.regs.get? Register.x12 = some aEnv := obs_store_other_val' hobs4 Register.x12 (by decide) ha2_3
  have ha3_4 : σ4.regs.get? Register.x13 = some aRet := obs_store_other_val' hobs4 Register.x13 (by decide) ha3_3
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_store_other_val' hobs4 Register.x1 (by decide) hra_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  -- ============ 0x80003ff0: sd s3,136(sp') → mem[sp-40] := v19 ============
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80003ff0_es σ4 i4 (c.steps+1+1+1+1) (0x80003ff0#64) vmi4 (sp-176#64) v19 hG4 hpc4 hmi4 hsp_4 h19_4 hload4 rfl
      (by rw [haS3]; have := hstkRam.1; omega) (by rw [haS3]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haS3]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haS3]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps+1+1+1+1⟩ ⟨σ5, i5, c.steps+1+1+1+1+1⟩ := hs5
  have hmem5e : σ5.mem = writeMap8 σ4.mem (sp.toNat - 40) (sdData_val v19) := by
    rw [hmem5, mem_afterNextPC, haS3]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003ff4#64) := by
    have := obs_store_pc_val hobs5; rwa [show BitVec.addInt (0x80003ff0#64) 4 = (0x80003ff4#64:BitVec 64) from by decide] at this
  have hload5 : Exec_stmtLoaded σ5.mem := by
    rw [hmem5e]; exact loaded_exec_stmt_writeMap8 σ4.mem (sp.toNat-40) (sdData_val v19) (by have := hcodeStk; omega) hload4
  have hslot5 : StmtSlotPinned k armPC σ5.mem := by
    rw [hmem5e]; exact stmtslot_wm8 k armPC σ4.mem (sp.toNat-40) (sdData_val v19) (by have := htableStk; omega) hslot4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-176#64) := obs_store_other_val' hobs5 Register.x2 (by decide) hsp_4
  have ha0_5 : σ5.regs.get? Register.x10 = some aInterp := obs_store_other_val' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 : σ5.regs.get? Register.x11 = some aStmt := obs_store_other_val' hobs5 Register.x11 (by decide) ha1_4
  have ha2_5 : σ5.regs.get? Register.x12 = some aEnv := obs_store_other_val' hobs5 Register.x12 (by decide) ha2_4
  have ha3_5 : σ5.regs.get? Register.x13 = some aRet := obs_store_other_val' hobs5 Register.x13 (by decide) ha3_4
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_store_other_val' hobs5 Register.x1 (by decide) hra_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret_val hobs5
  -- ============ 0x80003ff4: sd ra,168(sp') → mem[sp-8] := r ============
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80003ff4_es σ5 i5 (c.steps+1+1+1+1+1) (0x80003ff4#64) vmi5 (sp-176#64) r hG5 hpc5 hmi5 hsp_5 hra_5 hload5 rfl
      (by rw [haRa]; have := hstkRam.1; omega) (by rw [haRa]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haRa]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haRa]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps+1+1+1+1+1⟩ ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ := hs6
  have hmem6e : σ6.mem = writeMap8 σ5.mem (sp.toNat - 8) (sdData_val r) := by
    rw [hmem6, mem_afterNextPC, haRa]
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003ff8#64) := by
    have := obs_store_pc_val hobs6; rwa [show BitVec.addInt (0x80003ff4#64) 4 = (0x80003ff8#64:BitVec 64) from by decide] at this
  have hload6 : Exec_stmtLoaded σ6.mem := by
    rw [hmem6e]; exact loaded_exec_stmt_writeMap8 σ5.mem (sp.toNat-8) (sdData_val r) (by have := hcodeStk; omega) hload5
  have hslot6 : StmtSlotPinned k armPC σ6.mem := by
    rw [hmem6e]; exact stmtslot_wm8 k armPC σ5.mem (sp.toNat-8) (sdData_val r) (by have := htableStk; omega) hslot5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp-176#64) := obs_store_other_val' hobs6 Register.x2 (by decide) hsp_5
  have ha0_6 : σ6.regs.get? Register.x10 = some aInterp := obs_store_other_val' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 : σ6.regs.get? Register.x11 = some aStmt := obs_store_other_val' hobs6 Register.x11 (by decide) ha1_5
  have ha2_6 : σ6.regs.get? Register.x12 = some aEnv := obs_store_other_val' hobs6 Register.x12 (by decide) ha2_5
  have ha3_6 : σ6.regs.get? Register.x13 = some aRet := obs_store_other_val' hobs6 Register.x13 (by decide) ha3_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret_val hobs6
  -- σ6.mem agrees with m0 (= c.σ.mem) outside `[SL.lo, sp)` (the five spills all inside)
  have hmemframe6 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → σ6.mem[a]? = m0[a]? := by
    intro a ha
    rw [hmem6e, hmem5e, hmem4e, hmem3e, hmem2e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), ← hmem]
  -- the four stmt-kind bytes at aStmt in σ6.mem (survive the five disjoint spills)
  have hkb0' : σ6.mem[aStmt.toNat]? = some hkb0v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e, hmem2e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega)]; exact hkb0
  have hkb1' : σ6.mem[aStmt.toNat + 1]? = some hkb1v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e, hmem2e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega)]; exact hkb1
  have hkb2' : σ6.mem[aStmt.toNat + 2]? = some hkb2v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e, hmem2e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega)]; exact hkb2
  have hkb3' : σ6.mem[aStmt.toNat + 3]? = some hkb3v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e, hmem2e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hstmtStk; omega)]; exact hkb3
  have hhtif_e : (aStmt + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) (0x000#12)).toNat := by
    right; rw [haddr0, htoh]; have := hstmtWin; rw [htoh] at this; omega
  -- ============ 0x80003ff8: mv s0,a1 → x8 := aStmt ============
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80003ff8_es σ6 i6 (c.steps+1+1+1+1+1+1) (0x80003ff8#64) vmi6 aStmt hG6 hpc6 hmi6 ha1_6 (hmem6e ▸ hload6) rfl hi6
  have hstep7 : Step ⟨σ6, i6, _⟩ ⟨σ7, i7, _⟩ := hs7
  have hmem7e : σ7.mem = σ6.mem := hmem7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003ffc#64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80003ff8#64) 4 = (0x80003ffc#64:BitVec 64) from by decide] at this
  have hsext0e : ∀ w : BitVec 64, (w + sign_extend (m := 64) (0x000#12) : BitVec 64) = w := by
    intro w; rw [sext_zero, BitVec.add_zero]
  have hx8_7 : σ7.regs.get? Register.x8 = some aStmt := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hsext0e] at this
  have ha0_7 : σ7.regs.get? Register.x10 = some aInterp := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha2_7 : σ7.regs.get? Register.x12 = some aEnv := obs_alu_other' hobs7 Register.x12 (by decide) ha2_6
  have ha3_7 : σ7.regs.get? Register.x13 = some aRet := obs_alu_other' hobs7 Register.x13 (by decide) ha3_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  -- ============ 0x80003ffc: mv s1,a0 → x9 := aInterp ============
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80003ffc_es σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80003ffc#64) vmi7 aInterp hG7 hpc7 hmi7 ha0_7 (hmem7e ▸ hload6) rfl hi7
  have hstep8 : Step ⟨σ7, i7, _⟩ ⟨σ8, i8, _⟩ := hs8
  have hmem8e : σ8.mem = σ6.mem := by rw [hmem8, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80004000#64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80003ffc#64) 4 = (0x80004000#64:BitVec 64) from by decide] at this
  have hx9_8 : σ8.regs.get? Register.x9 = some aInterp := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hsext0e] at this
  have hx8_8 : σ8.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs8 Register.x8 (by decide) hx8_7
  have ha2_8 : σ8.regs.get? Register.x12 = some aEnv := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
  have ha3_8 : σ8.regs.get? Register.x13 = some aRet := obs_alu_other' hobs8 Register.x13 (by decide) ha3_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  -- ============ 0x80004000: mv s3,a2 → x19 := aEnv ============
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80004000_es σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80004000#64) vmi8 aEnv hG8 hpc8 hmi8 ha2_8 (hmem8e ▸ hload6) rfl hi8
  have hstep9 : Step ⟨σ8, i8, _⟩ ⟨σ9, i9, _⟩ := hs9
  have hmem9e : σ9.mem = σ6.mem := by rw [hmem9, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80004004#64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80004000#64) 4 = (0x80004004#64:BitVec 64) from by decide] at this
  have hx19_9 : σ9.regs.get? Register.x19 = some aEnv := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hsext0e] at this
  have hx8_9 : σ9.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs9 Register.x8 (by decide) hx8_8
  have hx9_9 : σ9.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs9 Register.x9 (by decide) hx9_8
  have ha3_9 : σ9.regs.get? Register.x13 = some aRet := obs_alu_other' hobs9 Register.x13 (by decide) ha3_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  -- ============ 0x80004004: mv s2,a3 → x18 := aRet ============
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80004004_es σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80004004#64) vmi9 aRet hG9 hpc9 hmi9 ha3_9 (hmem9e ▸ hload6) rfl hi9
  have hstep10 : Step ⟨σ9, i9, _⟩ ⟨σ10, i10, _⟩ := hs10
  have hmem10e : σ10.mem = σ6.mem := by rw [hmem10, hmem9e]
  have hpc10 : σ10.regs.get? Register.PC = some (0x80004008#64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x80004004#64) 4 = (0x80004008#64:BitVec 64) from by decide] at this
  have hx18_10 : σ10.regs.get? Register.x18 = some aRet := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hsext0e] at this
  have hx8_10 : σ10.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs10 Register.x8 (by decide) hx8_9
  have hx9_10 : σ10.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs10 Register.x9 (by decide) hx9_9
  have hx19_10 : σ10.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs10 Register.x19 (by decide) hx19_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  -- ============ 0x80004008: li a6,8 → x16 := 8 ============
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80004008_es σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80004008#64) vmi10 hG10 hpc10 hmi10 (hmem10e ▸ hload6) rfl hi10
  have hstep11 : Step ⟨σ10, i10, _⟩ ⟨σ11, i11, _⟩ := hs11
  have hmem11e : σ11.mem = σ6.mem := by rw [hmem11, hmem10e]
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000400c#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80004008#64) 4 = (0x8000400c#64:BitVec 64) from by decide] at this
  have hx16_11 : σ11.regs.get? Register.x16 = some (8#64) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_11 : σ11.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs11 Register.x8 (by decide) hx8_10
  have hx18_11 : σ11.regs.get? Register.x18 = some aRet := obs_alu_other' hobs11 Register.x18 (by decide) hx18_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- ============ 0x8000400c: auipc a4 → x14 := 0x8001a00c ============
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_8000400c_es σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x8000400c#64) vmi11 hG11 hpc11 hmi11 (hmem11e ▸ hload6) rfl hi11
  have hstep12 : Step ⟨σ11, i11, _⟩ ⟨σ12, i12, _⟩ := hs12
  have hmem12e : σ12.mem = σ6.mem := by rw [hmem12, hmem11e]
  have hpc12 : σ12.regs.get? Register.PC = some (0x80004010#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x8000400c#64) 4 = (0x80004010#64:BitVec 64) from by decide] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some (0x8001a00c#64) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x8000400c#64 : BitVec 64) + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12) : BitVec 64) = 0x8001a00c#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_12 : σ12.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs12 Register.x8 (by decide) hx8_11
  have hx16_12 : σ12.regs.get? Register.x16 = some (8#64) := obs_alu_other' hobs12 Register.x16 (by decide) hx16_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs12 Register.x2 (by decide) hsp_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  -- ============ 0x80004010: addi a4,a4,-84 → x14 := 0x80019fb8 (table base) ============
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80004010_es σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004010#64) vmi12 (0x8001a00c#64) hG12 hpc12 hmi12 hx14_12 (hmem12e ▸ hload6) rfl hi12
  have hstep13 : Step ⟨σ12, i12, _⟩ ⟨σ13, i13, _⟩ := hs13
  have hmem13e : σ13.mem = σ6.mem := by rw [hmem13, hmem12e]
  have hpc13 : σ13.regs.get? Register.PC = some (0x80004014#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80004010#64) 4 = (0x80004014#64:BitVec 64) from by decide] at this
  have hx14_13 : σ13.regs.get? Register.x14 = some (0x80019fb8#64) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x8001a00c#64 : BitVec 64) + sign_extend (m := 64) (0xfac#12) : BitVec 64) = 0x80019fb8#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8_13 : σ13.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs13 Register.x8 (by decide) hx8_12
  have hx16_13 : σ13.regs.get? Register.x16 = some (8#64) := obs_alu_other' hobs13 Register.x16 (by decide) hx16_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs13 Register.x2 (by decide) hsp_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  -- ============ 0x80004014: lw a5,0(s0) → x15 := ofNat k (kind) ============
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80004014_es σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004014#64) vmi13 aStmt hkb0v hkb1v hkb2v hkb3v
      hG13 hpc13 hmi13 hx8_13 (hmem13e ▸ hload6) rfl
      (by rw [haddr0]; have := hstmtRam.1; omega) (by rw [haddr0]; have := hstmtRam.2; omega) hhtif_e
      (by rw [haddr0]; omega)
      (by rw [haddr0, hmem13e]; exact hkb0') (by rw [haddr0, hmem13e]; exact hkb1')
      (by rw [haddr0, hmem13e]; exact hkb2') (by rw [haddr0, hmem13e]; exact hkb3') hi13
  have hstep14 : Step ⟨σ13, i13, _⟩ ⟨σ14, i14, _⟩ := hs14
  have hmem14e : σ14.mem = σ6.mem := by rw [hmem14, hmem13e]
  have hpc14 : σ14.regs.get? Register.PC = some (0x80004018#64) := by
    have := obs_alu_pc hobs14; rwa [show BitVec.addInt (0x80004014#64) 4 = (0x80004018#64:BitVec 64) from by decide] at this
  have hx15_14 : σ14.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_kind hkb0v hkb1v hkb2v hkb3v k hklt hkrec] at this
  have hx16_14 : σ14.regs.get? Register.x16 = some (8#64) := obs_alu_other' hobs14 Register.x16 (by decide) hx16_13
  have hx14_14 : σ14.regs.get? Register.x14 = some (0x80019fb8#64) := obs_alu_other' hobs14 Register.x14 (by decide) hx14_13
  have hx8_14 : σ14.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs14 Register.x8 (by decide) hx8_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs14 Register.x2 (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  -- ============ 0x80004018: bltu a6,a5 NOT taken (8 <u k = false, k ≤ 8) ============
  have hbltu : zopz0zI_u (8#64) (BitVec.ofNat 64 k) = false := by
    have hkeq : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 by omega)]
    unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
    apply decide_eq_false
    rw [Int.not_lt, hkeq, show (8#64 : BitVec 64).toNat = 8 from by decide]
    exact Int.ofNat_le.mpr (by omega)
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80004018_nottaken_es σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004018#64) vmi14 (8#64) (BitVec.ofNat 64 k)
      hG14 hpc14 hmi14 hx16_14 hx15_14 (hmem14e ▸ hload6) rfl hbltu hi14
  have hstep15 : Step ⟨σ14, i14, _⟩ ⟨σ15, i15, _⟩ := hs15
  have hmem15e : σ15.mem = σ6.mem := by rw [hmem15, hmem14e]
  have hpc15 : σ15.regs.get? Register.PC = some (0x8000401c#64) := by
    have := obs_branch_nottaken_pc hobs15; rwa [show BitVec.addInt (0x80004018#64) 4 = (0x8000401c#64:BitVec 64) from by decide] at this
  have hx14_15 : σ15.regs.get? Register.x14 = some (0x80019fb8#64) := obs_branch_nottaken_other' hobs15 Register.x14 (by decide) hx14_14
  have hx8_15 : σ15.regs.get? Register.x8 = some aStmt := obs_branch_nottaken_other' hobs15 Register.x8 (by decide) hx8_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp-176#64) := obs_branch_nottaken_other' hobs15 Register.x2 (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_branch_nottaken_minstret hobs15
  -- ============ 0x8000401c: lwu a5,0(s0) → x15 := ofNat k (zero-ext) ============
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_8000401c_es σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000401c#64) vmi15 aStmt hkb0v hkb1v hkb2v hkb3v
      hG15 hpc15 hmi15 hx8_15 (hmem15e ▸ hload6) rfl
      (by rw [haddr0]; have := hstmtRam.1; omega) (by rw [haddr0]; have := hstmtRam.2; omega) hhtif_e
      (by rw [haddr0]; omega)
      (by rw [haddr0, hmem15e]; exact hkb0') (by rw [haddr0, hmem15e]; exact hkb1')
      (by rw [haddr0, hmem15e]; exact hkb2') (by rw [haddr0, hmem15e]; exact hkb3') hi15
  have hstep16 : Step ⟨σ15, i15, _⟩ ⟨σ16, i16, _⟩ := hs16
  have hmem16e : σ16.mem = σ6.mem := by rw [hmem16, hmem15e]
  have hpc16 : σ16.regs.get? Register.PC = some (0x80004020#64) := by
    have := obs_alu_pc hobs16; rwa [show BitVec.addInt (0x8000401c#64) 4 = (0x80004020#64:BitVec 64) from by decide] at this
  have hx15_16 : σ16.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [zext_kind hkb0v hkb1v hkb2v hkb3v k hklt hkrec] at this
  have hx14_16 : σ16.regs.get? Register.x14 = some (0x80019fb8#64) := obs_alu_other' hobs16 Register.x14 (by decide) hx14_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs16 Register.x2 (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  -- ============ 0x80004020: slli a5,a5,2 → x15 := ofNat (4*k) ============
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80004020_es σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004020#64) vmi16 (BitVec.ofNat 64 k) hG16 hpc16 hmi16 hx15_16 (hmem16e ▸ hload6) rfl hi16
  have hstep17 : Step ⟨σ16, i16, _⟩ ⟨σ17, i17, _⟩ := hs17
  have hmem17e : σ17.mem = σ6.mem := by rw [hmem17, hmem16e]
  have hpc17 : σ17.regs.get? Register.PC = some (0x80004024#64) := by
    have := obs_alu_pc hobs17; rwa [show BitVec.addInt (0x80004020#64) 4 = (0x80004024#64:BitVec 64) from by decide] at this
  have hshleq : (shift_bits_left (BitVec.ofNat 64 k) (Sail.BitVec.extractLsb (0x02#6) 5 0) : BitVec 64)
      = BitVec.ofNat 64 (4 * k) := by
    show (BitVec.ofNat 64 k) <<< (Sail.BitVec.extractLsb (0x02#6) 5 0) = _
    rw [show (Sail.BitVec.extractLsb (0x02#6) 5 0 : BitVec 6) = (2#6 : BitVec 6) from by decide]
    show (BitVec.ofNat 64 k) <<< (2 : Nat) = _
    apply BitVec.eq_of_toNat_eq
    have h4 : ((BitVec.ofNat 64 k) <<< (2 : Nat)).toNat = 4 * k := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show k < 2^64 by omega)]
      have : k * 2 ^ 2 = 4 * k := by rw [show (2:Nat)^2 = 4 from rfl]; omega
      rw [this, Nat.mod_eq_of_lt (show 4*k < 2^64 by omega)]
    rw [h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4*k < 2^64 by omega)]
  have hx15_17 : σ17.regs.get? Register.x15 = some (BitVec.ofNat 64 (4 * k)) := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hshleq] at this
  have hx14_17 : σ17.regs.get? Register.x14 = some (0x80019fb8#64) := obs_alu_other' hobs17 Register.x14 (by decide) hx14_16
  have hsp_17 : σ17.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs17 Register.x2 (by decide) hsp_16
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  -- ============ 0x80004024: add a5,a5,a4 → x15 := ofNat (table + 4*k) ============
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80004024_es σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004024#64) vmi17 (BitVec.ofNat 64 (4 * k)) (0x80019fb8#64) hG17 hpc17 hmi17 hx15_17 hx14_17 (hmem17e ▸ hload6) rfl hi17
  have hstep18 : Step ⟨σ17, i17, _⟩ ⟨σ18, i18, _⟩ := hs18
  have hmem18e : σ18.mem = σ6.mem := by rw [hmem18, hmem17e]
  have hpc18 : σ18.regs.get? Register.PC = some (0x80004028#64) := by
    have := obs_alu_pc hobs18; rwa [show BitVec.addInt (0x80004024#64) 4 = (0x80004028#64:BitVec 64) from by decide] at this
  have hx15_18 : σ18.regs.get? Register.x15 = some (BitVec.ofNat 64 (stmtJumpTableBase + 4 * k)) := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((BitVec.ofNat 64 (4 * k)) + (0x80019fb8#64) : BitVec 64) = BitVec.ofNat 64 (stmtJumpTableBase + 4 * k) from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      rw [show (BitVec.ofNat 64 (4 * k)).toNat = 4 * k from by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * k < 2^64 by omega)]]
      rw [show (0x80019fb8#64 : BitVec 64).toNat = 0x80019fb8 from by decide]
      rw [show (BitVec.ofNat 64 (stmtJumpTableBase + 4 * k)).toNat = stmtJumpTableBase + 4 * k from by
            rw [BitVec.toNat_ofNat]; simp only [stmtJumpTableBase]
            rw [Nat.mod_eq_of_lt (show 0x80019fb8 + 4*k < 2^64 by omega)]]
      simp only [stmtJumpTableBase]
      rw [Nat.mod_eq_of_lt (show 4*k + 0x80019fb8 < 2^64 by omega)]; omega] at this
  have hx14_18 : σ18.regs.get? Register.x14 = some (0x80019fb8#64) := obs_alu_other' hobs18 Register.x14 (by decide) hx14_17
  have hsp_18 : σ18.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs18 Register.x2 (by decide) hsp_17
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  -- slot bytes at `table + 4k` in σ6.mem (= σ18.mem)
  have hslot18 : StmtSlotPinned k armPC σ18.mem := by rw [hmem18e]; exact hslot6
  obtain ⟨sb0, sb1, sb2, sb3, hsb0, hsb1, hsb2, hsb3, hsbtgt⟩ := hslot18.b0
  have hslotBaseNat : (BitVec.ofNat 64 (stmtJumpTableBase + 4 * k)).toNat = stmtJumpTableBase + 4 * k := by
    simp only [BitVec.toNat_ofNat, stmtJumpTableBase]; rw [Nat.mod_eq_of_lt (by omega)]
  have haddrT : ((BitVec.ofNat 64 (stmtJumpTableBase + 4 * k) : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = stmtJumpTableBase + 4 * k := by rw [sext_zero, BitVec.add_zero]; exact hslotBaseNat
  -- ============ 0x80004028: lw a5,0(a5) → x15 := sext(slot bytes) ============
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80004028_es σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004028#64) vmi18 (BitVec.ofNat 64 (stmtJumpTableBase + 4 * k))
      sb0 sb1 sb2 sb3 hG18 hpc18 hmi18 hx15_18 (hmem18e ▸ hload6) rfl
      (by rw [haddrT]; simp only [stmtJumpTableBase]; omega) (by rw [haddrT]; simp only [stmtJumpTableBase]; omega)
      (by rw [haddrT]; left; simp only [stmtJumpTableBase]; rw [htoh]; omega) (by rw [haddrT]; simp only [stmtJumpTableBase]; omega)
      (by rw [haddrT]; simpa using hsb0) (by rw [haddrT]; simpa using hsb1)
      (by rw [haddrT]; simpa using hsb2) (by rw [haddrT]; simpa using hsb3) hi18
  have hstep19 : Step ⟨σ18, i18, _⟩ ⟨σ19, i19, _⟩ := hs19
  have hmem19e : σ19.mem = σ6.mem := by rw [hmem19, hmem18e]
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000402c#64) := by
    have := obs_alu_pc hobs19; rwa [show BitVec.addInt (0x80004028#64) 4 = (0x8000402c#64:BitVec 64) from by decide] at this
  have hx15_19 : σ19.regs.get? Register.x15 = some (sign_extend (m := 64) ((((sb3.append sb2).append sb1).append sb0) : BitVec (8*4))) :=
    obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_19 : σ19.regs.get? Register.x14 = some (0x80019fb8#64) := obs_alu_other' hobs19 Register.x14 (by decide) hx14_18
  have hsp_19 : σ19.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs19 Register.x2 (by decide) hsp_18
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  -- ============ 0x8000402c: add a5,a5,a4 → x15 := sext(slot) + table = armPC ============
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_8000402c_es σ19 i19 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000402c#64) vmi19
      (sign_extend (m := 64) ((((sb3.append sb2).append sb1).append sb0) : BitVec (8*4)))
      (0x80019fb8#64) hG19 hpc19 hmi19 hx15_19 hx14_19 (hmem19e ▸ hload6) rfl hi19
  have hstep20 : Step ⟨σ19, i19, _⟩ ⟨σ20, i20, _⟩ := hs20
  have hmem20e : σ20.mem = σ6.mem := by rw [hmem20, hmem19e]
  have hpc20 : σ20.regs.get? Register.PC = some (0x80004030#64) := by
    have := obs_alu_pc hobs20; rwa [show BitVec.addInt (0x8000402c#64) 4 = (0x80004030#64:BitVec 64) from by decide] at this
  have hx15_20 : σ20.regs.get? Register.x15 = some armPC := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [BitVec.add_comm, show ((0x80019fb8#64 : BitVec 64)) = BitVec.ofNat 64 stmtJumpTableBase from by
      simp only [stmtJumpTableBase], hsbtgt] at this
  have hsp_20 : σ20.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs20 Register.x2 (by decide) hsp_19
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  -- thread the arm-entry registers (x8=aStmt, x9=aInterp, x18=aRet, x19=aEnv, x1=r) through steps 15..20
  have hx8_16 : σ16.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs16 Register.x8 (by decide) hx8_15
  have hx8_17 : σ17.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs17 Register.x8 (by decide) hx8_16
  have hx8_18 : σ18.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs18 Register.x8 (by decide) hx8_17
  have hx8_19 : σ19.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs19 Register.x8 (by decide) hx8_18
  have hx8_20 : σ20.regs.get? Register.x8 = some aStmt := obs_alu_other' hobs20 Register.x8 (by decide) hx8_19
  have hx9_11 : σ11.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs11 Register.x9 (by decide) hx9_10
  have hx9_12 : σ12.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs12 Register.x9 (by decide) hx9_11
  have hx9_13 : σ13.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs13 Register.x9 (by decide) hx9_12
  have hx9_14 : σ14.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs14 Register.x9 (by decide) hx9_13
  have hx9_15 : σ15.regs.get? Register.x9 = some aInterp := obs_branch_nottaken_other' hobs15 Register.x9 (by decide) hx9_14
  have hx9_16 : σ16.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs16 Register.x9 (by decide) hx9_15
  have hx9_17 : σ17.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs17 Register.x9 (by decide) hx9_16
  have hx9_18 : σ18.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs18 Register.x9 (by decide) hx9_17
  have hx9_19 : σ19.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs19 Register.x9 (by decide) hx9_18
  have hx9_20 : σ20.regs.get? Register.x9 = some aInterp := obs_alu_other' hobs20 Register.x9 (by decide) hx9_19
  have hx18_12 : σ12.regs.get? Register.x18 = some aRet := obs_alu_other' hobs12 Register.x18 (by decide) hx18_11
  have hx18_13 : σ13.regs.get? Register.x18 = some aRet := obs_alu_other' hobs13 Register.x18 (by decide) hx18_12
  have hx18_14 : σ14.regs.get? Register.x18 = some aRet := obs_alu_other' hobs14 Register.x18 (by decide) hx18_13
  have hx18_15 : σ15.regs.get? Register.x18 = some aRet := obs_branch_nottaken_other' hobs15 Register.x18 (by decide) hx18_14
  have hx18_16 : σ16.regs.get? Register.x18 = some aRet := obs_alu_other' hobs16 Register.x18 (by decide) hx18_15
  have hx18_17 : σ17.regs.get? Register.x18 = some aRet := obs_alu_other' hobs17 Register.x18 (by decide) hx18_16
  have hx18_18 : σ18.regs.get? Register.x18 = some aRet := obs_alu_other' hobs18 Register.x18 (by decide) hx18_17
  have hx18_19 : σ19.regs.get? Register.x18 = some aRet := obs_alu_other' hobs19 Register.x18 (by decide) hx18_18
  have hx18_20 : σ20.regs.get? Register.x18 = some aRet := obs_alu_other' hobs20 Register.x18 (by decide) hx18_19
  have hx19_11 : σ11.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs11 Register.x19 (by decide) hx19_10
  have hx19_12 : σ12.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs12 Register.x19 (by decide) hx19_11
  have hx19_13 : σ13.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs13 Register.x19 (by decide) hx19_12
  have hx19_14 : σ14.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs14 Register.x19 (by decide) hx19_13
  have hx19_15 : σ15.regs.get? Register.x19 = some aEnv := obs_branch_nottaken_other' hobs15 Register.x19 (by decide) hx19_14
  have hx19_16 : σ16.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs16 Register.x19 (by decide) hx19_15
  have hx19_17 : σ17.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs17 Register.x19 (by decide) hx19_16
  have hx19_18 : σ18.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs18 Register.x19 (by decide) hx19_17
  have hx19_19 : σ19.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs19 Register.x19 (by decide) hx19_18
  have hx19_20 : σ20.regs.get? Register.x19 = some aEnv := obs_alu_other' hobs20 Register.x19 (by decide) hx19_19
  -- ra (x1) unchanged through steps 7..20
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_store_other_val' hobs6 Register.x1 (by decide) hra_5
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
  have hra_9 : σ9.regs.get? Register.x1 = some r := obs_alu_other' hobs9 Register.x1 (by decide) hra_8
  have hra_10 : σ10.regs.get? Register.x1 = some r := obs_alu_other' hobs10 Register.x1 (by decide) hra_9
  have hra_11 : σ11.regs.get? Register.x1 = some r := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have hra_12 : σ12.regs.get? Register.x1 = some r := obs_alu_other' hobs12 Register.x1 (by decide) hra_11
  have hra_13 : σ13.regs.get? Register.x1 = some r := obs_alu_other' hobs13 Register.x1 (by decide) hra_12
  have hra_14 : σ14.regs.get? Register.x1 = some r := obs_alu_other' hobs14 Register.x1 (by decide) hra_13
  have hra_15 : σ15.regs.get? Register.x1 = some r := obs_branch_nottaken_other' hobs15 Register.x1 (by decide) hra_14
  have hra_16 : σ16.regs.get? Register.x1 = some r := obs_alu_other' hobs16 Register.x1 (by decide) hra_15
  have hra_17 : σ17.regs.get? Register.x1 = some r := obs_alu_other' hobs17 Register.x1 (by decide) hra_16
  have hra_18 : σ18.regs.get? Register.x1 = some r := obs_alu_other' hobs18 Register.x1 (by decide) hra_17
  have hra_19 : σ19.regs.get? Register.x1 = some r := obs_alu_other' hobs19 Register.x1 (by decide) hra_18
  have hra_20 : σ20.regs.get? Register.x1 = some r := obs_alu_other' hobs20 Register.x1 (by decide) hra_19
  -- ============ 0x80004030: jr a5 → PC := armPC ============
  have htgtJr : (BitVec.update (armPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt armPC harmAl]; exact harmAl
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_80004030_es σ20 i20 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80004030#64) vmi20 armPC hG20 hpc20 hmi20 hx15_20 (hmem20e ▸ hload6) rfl htgtJr hi20
  have hstep21 : Step ⟨σ20, i20, _⟩ ⟨σ21, i21, _⟩ := hs21
  have hmem21e : σ21.mem = σ6.mem := by rw [hmem21, hmem20e]
  have hpc21 : σ21.regs.get? Register.PC = some armPC := by
    have := obs_jr_pc hobs21; rwa [ret_tgt armPC harmAl] at this
  have hx8_21 : σ21.regs.get? Register.x8 = some aStmt := obs_jr_other' hobs21 Register.x8 (by decide) hx8_20
  have hx9_21 : σ21.regs.get? Register.x9 = some aInterp := obs_jr_other' hobs21 Register.x9 (by decide) hx9_20
  have hx18_21 : σ21.regs.get? Register.x18 = some aRet := obs_jr_other' hobs21 Register.x18 (by decide) hx18_20
  have hx19_21 : σ21.regs.get? Register.x19 = some aEnv := obs_jr_other' hobs21 Register.x19 (by decide) hx19_20
  have hsp_21 : σ21.regs.get? Register.x2 = some (sp-176#64) := obs_jr_other' hobs21 Register.x2 (by decide) hsp_20
  have hra_21 : σ21.regs.get? Register.x1 = some r := obs_jr_other' hobs21 Register.x1 (by decide) hra_20
  obtain ⟨vmi21, hmi21⟩ := obs_jr_minstret hobs21
  -- output invariance across the 21 prologue+dispatch steps
  have hout21 : σ21.sailOutput = out0 := by
    rw [hobs21.out, sailOutput_sigmaPost_jump_x0, hobs20.out, sailOutput_sigmaPost_alu,
      hobs19.out, sailOutput_sigmaPost_alu, hobs18.out, sailOutput_sigmaPost_alu,
      hobs17.out, sailOutput_sigmaPost_alu, hobs16.out, sailOutput_sigmaPost_alu,
      hobs15.out, sailOutput_sigmaPost_branch_nottaken, hobs14.out, sailOutput_sigmaPost_alu,
      hobs13.out, sailOutput_sigmaPost_alu, hobs12.out, sailOutput_sigmaPost_alu,
      hobs11.out, sailOutput_sigmaPost_alu, hobs10.out, sailOutput_sigmaPost_alu,
      hobs9.out, sailOutput_sigmaPost_alu, hobs8.out, sailOutput_sigmaPost_alu,
      hobs7.out, sailOutput_sigmaPost_alu, hobs6.out, sailOutput_sigmaPost_store,
      hobs5.out, sailOutput_sigmaPost_store, hobs4.out, sailOutput_sigmaPost_store,
      hobs3.out, sailOutput_sigmaPost_store, hobs2.out, sailOutput_sigmaPost_store,
      hobs1.out, sailOutput_sigmaPost_alu]
    exact hout0
  have houtStr : String.join out0.toList = st.out := by
    have : Vsa.Machine.output c.σ = st.out := hout
    simp only [Vsa.Machine.output] at this; rw [← hout0]; exact this
  -- StoreRepr survives the five spills: σ6.mem agrees with c.σ.mem outside `[SL.lo,sp)`.
  have hstore6 : StoreRepr σ6.mem N A φf φc st.store :=
    hstoreSurv σ6.mem (fun a ha => by rw [hmem, ← hmemframe6 a ha])
  -- the four spill slots survive in σ6.mem
  have hslotRa : read64 σ6.mem (sp.toNat - 8) = some r.toNat := by
    rw [hmem6e, read64_writeMap8, sdData_toNat]
  have hslotS0 : read64 σ6.mem (sp.toNat - 16) = some v8.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem4e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem3e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem2e, read64_writeMap8, sdData_toNat]
  have hslotS1 : read64 σ6.mem (sp.toNat - 24) = some v9.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem4e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem3e, read64_writeMap8, sdData_toNat]
  have hslotS2 : read64 σ6.mem (sp.toNat - 32) = some v18.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem4e, read64_writeMap8, sdData_toNat]
  have hslotS3 : read64 σ6.mem (sp.toNat - 40) = some v19.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8, sdData_toNat]
  -- entry ghost frame reads for the spilled callee-saved registers
  have hgx8 : g Register.x8 = some v8 := by rw [← hframe Register.x8 (by decide)]; exact h8_0
  have hgx9 : g Register.x9 = some v9 := by rw [← hframe Register.x9 (by decide)]; exact h9_0
  have hgx18 : g Register.x18 = some v18 := by rw [← hframe Register.x18 (by decide)]; exact h18_0
  have hgx19 : g Register.x19 = some v19 := by rw [← hframe Register.x19 (by decide)]; exact h19_0
  have hgx2 : g Register.x2 = some sp := by rw [← hframe Register.x2 (by decide)]; exact hspReg
  -- blanket frame: callee-saved regs (excl x8/x9/x18/x19/x2) unchanged through 21 steps
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe21 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false → (Register.x2 == R) = false →
      σ21.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8 he9 he18 he19 he2
    have hab : AbiPreserved R = true := hR.1
    have h14 : (Register.x14 == R) = false := abi_ne' (by decide) hab
    have h15 : (Register.x15 == R) = false := abi_ne' (by decide) hab
    have h16 : (Register.x16 == R) = false := abi_ne' (by decide) hab
    have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h11 : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have h12 : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h13 : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hab
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have alu : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd v) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
    have str : ∀ {σa σb : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)},
        ReadsLikePost σb (sigmaPost_store σa pc vm m') →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
    have brn : ∀ {σa σb : MState} {pc vm : BitVec 64},
        ReadsLikePost σb (sigmaPost_branch_nottaken σa pc vm) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
    have jr : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
        ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    exact (jr hobs21).trans ((alu hobs20 h15).trans ((alu hobs19 h15).trans
      ((alu hobs18 h15).trans ((alu hobs17 h15).trans ((alu hobs16 h15).trans
      ((brn hobs15).trans ((alu hobs14 h15).trans ((alu hobs13 h14).trans
      ((alu hobs12 h14).trans ((alu hobs11 h16).trans ((alu hobs10 he18).trans
      ((alu hobs9 he19).trans ((alu hobs8 he9).trans ((alu hobs7 he8).trans
      ((str hobs6).trans ((str hobs5).trans ((str hobs4).trans ((str hobs3).trans
      ((str hobs2).trans (alu hobs1 he2))))))))))))))))))))
  have hframeArm : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false → (Register.x2 == R) = false →
      σ21.regs.get? R = g R := by
    intro R hR he8 he9 he18 he19 he2
    rw [hframe21 R hR he8 he9 he18 he19 he2]; exact hframe R hR
  -- assemble the full 21-step run + ExecArmEntryK
  refine ⟨⟨σ21, i21, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩, ?_, σ6.mem, v8, v9, v18, v19,
    hG21, hi21, hpc21, hx8_21, hx9_21, hx19_21, hx18_21, hsp_21, hra_21, ⟨_, hmi21⟩,
    hout21, houtStr, hmem21e, hmem21e ▸ hload6, hmem21e ▸ hstore6,
    hmem21e ▸ hslotRa, hmem21e ▸ hslotS0, hmem21e ▸ hslotS1, hmem21e ▸ hslotS2, hmem21e ▸ hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeArm, hmem21e ▸ hmemframe6,
    hsp176, ?_, ?_, ?_, ?_, hraAl⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
      ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
      ((Steps.single hstep19).trans ((Steps.single hstep20).trans (Steps.single hstep21))))))))))))))))))))
  · have := hsphi; have := hstkRam.2; omega       -- sp ≤ 2^32
  · have := hstkRam.1; have := hSLlo; omega        -- 2^31 ≤ sp
  · have := hstkWin; have := hSLlo; rw [htoh]; omega  -- tohost+16+176 ≤ sp
  · have := hsp16; omega                           -- sp % 8 = 0

/-! ## `execBrkSim` — the `ExecS.brk` simulation Triple

`execBlockA` (prologue+dispatch to `execArmBrk = 0x80004098`) ≫ `li a0,1` (the arm,
setting `x10 = 1 = StatusCode .brk`) ≫ `execBlockD` (shared epilogue). The block-A
residual is now discharged internally by `execBlockA`; the only remaining premises
are the jump-table slot pin (`hslot`, a `.rodata` fact) + its stack-disjointness
(`htableStk`) — exactly the geometry the expression-side leaves carry as
`EvalEntry` fields (`int_slot`/`table_stack_disjoint`). `hkind` (`read32 = 7`) is
derived from `ExecEntry.stmt : StmtRepr … .brk`. -/
theorem execBrkSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env .brk st .brk)
    (hslot : StmtSlotPinned 7 execArmBrk m0)
    (htableStk : stmtJumpTableBase + 4 * 7 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 7) :
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size st .brk sp r aRet m0) := by
  intro c hpre
  -- kind read `read32 m0 aStmt = 7` from the `.brk` StmtRepr (via `c.σ.mem = m0`)
  have hkind : read32 m0 aStmt.toNat = some 7 := by
    have := hpre.1.stmt; rw [hpre.1.mem] at this; cases this; assumption
  -- block A: prologue + dispatch → arm entry at execArmBrk = 0x80004098 (UNCONDITIONAL)
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env .brk
      sp r aInterp aStmt aEnv aRet execArmBrk m0 out0 :=
    execBlockA g N A SL φf φc st d env .brk 7 execArmBrk sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, ment, v8, v9, v18, v19, hArm⟩ := hBlockA c hpre
  obtain ⟨hGA, htickA, hpcA, hx8A, hx9A, hx19A, hx18A, hspA, hraA, ⟨vmiA, hmiA⟩,
    houtA, houtStrA, hmemA, hcodeA, hstoreA, hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeA, hmemframeA,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hArm
  -- arm: 0x80004098 `li a0,1` → x10 := 1 = StatusCode .brk, PC := 0x8000409c
  have hpcA' : cA.σ.regs.get? Register.PC = some (0x80004098#64) := by
    rw [hpcA]; rfl
  obtain ⟨σB, iB, hstepB', hiB, hGB, hmemB, hobsB⟩ :=
    site_80004098_es cA.σ cA.tick cA.steps (0x80004098#64) vmiA hGA hpcA' hmiA (hmemA ▸ hcodeA) rfl htickA
  have hstepB : Step cA ⟨σB, iB, cA.steps + 1⟩ := by cases cA; exact hstepB'
  have hmemBe : σB.mem = ment := by rw [hmemB]; exact hmemA
  have hpcB : σB.regs.get? Register.PC = some (0x8000409c#64) := by
    have := obs_alu_pc hobsB; rwa [show BitVec.addInt (0x80004098#64) 4 = (0x8000409c#64:BitVec 64) from by decide] at this
  have ha0B : σB.regs.get? Register.x10 = some (StatusCode .brk) := by
    have := obs_alu_rd hobsB (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12)) = StatusCode .brk from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hspB : σB.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other' hobsB Register.x2 (by decide) hspA
  obtain ⟨vmiB, hmiB⟩ := obs_alu_minstret hobsB
  have hcodeB : Exec_stmtLoaded σB.mem := by rw [hmemBe]; exact hcodeA
  -- the `li a0` is an ALU op that only writes x10, so it preserves the whole frame:
  have hframeB : ∀ R : Register, AbiPreservedNoise R → (Register.x10 == R) = false →
      σB.regs.get? R = cA.σ.regs.get? R := by
    intro R hR h10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    exact (hobsB.1 R hmc' hmt' hmip').trans
      (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' h10 hnpc' hmii')
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- block D: the shared epilogue → ExecExit
  obtain ⟨cD, hstepsD, hExit⟩ :=
    execBlockD g N A SL φf φc st.store.frames.size st.store.closures.size st .brk sp r aRet v8 v9 v18 v19 out0 m0 (by intro v hv; cases hv)
      ⟨σB, iB, cA.steps + 1⟩
      ⟨ment,
        hGB, hiB, hpcB, ha0B, hspB, ⟨_, hmiB⟩,
        by rw [hobsB.out, sailOutput_sigmaPost_alu]; exact houtA,
        houtStrA,
        hmemBe, hcodeA,
        hstoreA,
        -- PreExecEpilogue frame: restore-frame excludes s0/s1/s2/s3/sp; carry through li a0
        (by
          intro R hR he8 he9 he18 he19 he2
          have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hR.1
          rw [hframeB R hR h10]; exact hframeA R hR he8 he9 he18 he19 he2),
        hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
        hgx8, hgx9, hgx18, hgx19, hgx2,
        hmemframeA,
        hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩
  exact ⟨cD, (hstepsA.trans (Steps.single hstepB)).trans hstepsD, hExit⟩

/-! ## `execContSim` — the `ExecS.cont` simulation Triple

`execBlockA` (prologue+dispatch to `execArmCont = 0x800040b8`) ≫ the cont
epilogue-copy: `ld ra/s0/s1/s2/s3` (`0x800040b8..0x800040c8`), `li a0,2`
(`0x800040cc`, `x10 := 2 = StatusCode .cont`), `addi sp,sp,176`, `ret`. The `li a0`
sits BETWEEN the restores and `addi` (vs `brk`'s before-the-restores placement), so
the tail is threaded directly here rather than through `execBlockD`; the loads never
touch `x10`, so the mechanics are identical. The block-A residual is discharged
internally by `execBlockA`; only the slot pin (`hslot`) + its stack-disjointness
(`htableStk`) remain (`hkind`=`read32 = 8` from `ExecEntry.stmt`). -/
theorem execContSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env .cont st .cont)
    (hslot : StmtSlotPinned 8 execArmCont m0)
    (htableStk : stmtJumpTableBase + 4 * 8 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 8) :
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st.store.frames.size st.store.closures.size st .cont sp r aRet m0) := by
  intro c hpre
  have hkind : read32 m0 aStmt.toNat = some 8 := by
    have := hpre.1.stmt; rw [hpre.1.mem] at this; cases this; assumption
  have hBlockA : ExecBlockAGoal g N A SL φf φc st d env .cont
      sp r aInterp aStmt aEnv aRet execArmCont m0 out0 :=
    execBlockA g N A SL φf φc st d env .cont 8 execArmCont sp r aInterp aStmt aEnv aRet m0 out0
      (by omega) (by omega) hkind hslot (by decide) ⟨htableStk⟩
  obtain ⟨cA, hstepsA, ment, v8, v9, v18, v19, hArm⟩ := hBlockA c hpre
  obtain ⟨hGA, htickA, hpcA, hx8A, hx9A, hx19A, hx18A, hspA, hraA, ⟨vmiA, hmiA⟩,
    houtA, houtStrA, hmemA, hcodeA, hstoreA, hslotRa, hslotS0, hslotS1, hslotS2, hslotS3,
    hgx8, hgx9, hgx18, hgx19, hgx2, hframeA, hmemframeA,
    hsp176, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hArm
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have haRa : ((sp - 176#64) + sign_extend (m := 64) (0x0a8#12)).toNat = sp.toNat - 8 := es_off168 sp hsp176
  have haS0 : ((sp - 176#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 16 := es_off160 sp hsp176
  have haS1 : ((sp - 176#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 24 := es_off152 sp hsp176
  have haS2 : ((sp - 176#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 32 := es_off144 sp hsp176
  have haS3 : ((sp - 176#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 40 := es_off136 sp hsp176
  obtain ⟨ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, hra0, hra1, hra2, hra3, hra4, hra5, hra6, hra7, hraSext⟩ :=
    spill_roundtrip_ee ment (sp.toNat - 8) r hslotRa
  obtain ⟨s00, s01, s02, s03, s04, s05, s06, s07, hs00, hs01, hs02, hs03, hs04, hs05, hs06, hs07, hs0Sext⟩ :=
    spill_roundtrip_ee ment (sp.toNat - 16) v8 hslotS0
  obtain ⟨s10, s11, s12, s13, s14, s15, s16, s17, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs1Sext⟩ :=
    spill_roundtrip_ee ment (sp.toNat - 24) v9 hslotS1
  obtain ⟨s20, s21, s22, s23, s24, s25, s26, s27, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs2Sext⟩ :=
    spill_roundtrip_ee ment (sp.toNat - 32) v18 hslotS2
  obtain ⟨s30, s31, s32, s33, s34, s35, s36, s37, hs30, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs3Sext⟩ :=
    spill_roundtrip_ee ment (sp.toNat - 40) v19 hslotS3
  have hpcA' : cA.σ.regs.get? Register.PC = some (0x800040b8#64) := by rw [hpcA]; rfl
  -- ============ 0x800040b8: ld ra,168(sp) → x1 := r ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800040b8_es cA.σ cA.tick cA.steps (0x800040b8#64) vmiA (sp-176#64) ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
      hGA hpcA' hmiA hspA (hmemA.symm ▸ hcodeA) rfl
      (by rw [haRa]; omega) (by rw [haRa]; omega) (by rw [haRa, htoh]; right; omega) (by rw [haRa]; omega)
      (by rw [haRa, hmemA]; exact hra0) (by rw [haRa, hmemA]; exact hra1) (by rw [haRa, hmemA]; exact hra2)
      (by rw [haRa, hmemA]; exact hra3) (by rw [haRa, hmemA]; exact hra4) (by rw [haRa, hmemA]; exact hra5)
      (by rw [haRa, hmemA]; exact hra6) (by rw [haRa, hmemA]; exact hra7) htickA
  have hstep1 : Step cA ⟨σ1, i1, cA.steps + 1⟩ := by cases cA; exact hstep1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmemA
  have hpc1 : σ1.regs.get? Register.PC = some (0x800040bc#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x800040b8#64) 4 = (0x800040bc#64:BitVec 64) from by decide] at this
  have hra_1 : σ1.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hraSext] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs1 Register.x2 (by decide) hspA
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Exec_stmtLoaded σ1.mem := by rw [hmem1e]; exact hcodeA
  -- ============ 0x800040bc: ld s0,160(sp) → x8 := v8 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800040bc_es σ1 i1 (cA.steps + 1) (0x800040bc#64) vmi1 (sp-176#64) s00 s01 s02 s03 s04 s05 s06 s07
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl
      (by rw [haS0]; omega) (by rw [haS0]; omega) (by rw [haS0, htoh]; right; omega) (by rw [haS0]; omega)
      (by rw [haS0, hmem1e]; exact hs00) (by rw [haS0, hmem1e]; exact hs01) (by rw [haS0, hmem1e]; exact hs02)
      (by rw [haS0, hmem1e]; exact hs03) (by rw [haS0, hmem1e]; exact hs04) (by rw [haS0, hmem1e]; exact hs05)
      (by rw [haS0, hmem1e]; exact hs06) (by rw [haS0, hmem1e]; exact hs07) hi1
  have hstep2 : Step ⟨σ1, i1, cA.steps+1⟩ ⟨σ2, i2, cA.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800040c0#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x800040bc#64) 4 = (0x800040c0#64:BitVec 64) from by decide] at this
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs0Sext] at this
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Exec_stmtLoaded σ2.mem := by rw [hmem2e]; exact hcodeA
  -- ============ 0x800040c0: ld s1,152(sp) → x9 := v9 ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800040c0_es σ2 i2 (cA.steps + 1 + 1) (0x800040c0#64) vmi2 (sp-176#64) s10 s11 s12 s13 s14 s15 s16 s17
      hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haS1]; omega) (by rw [haS1]; omega) (by rw [haS1, htoh]; right; omega) (by rw [haS1]; omega)
      (by rw [haS1, hmem2e]; exact hs10) (by rw [haS1, hmem2e]; exact hs11) (by rw [haS1, hmem2e]; exact hs12)
      (by rw [haS1, hmem2e]; exact hs13) (by rw [haS1, hmem2e]; exact hs14) (by rw [haS1, hmem2e]; exact hs15)
      (by rw [haS1, hmem2e]; exact hs16) (by rw [haS1, hmem2e]; exact hs17) hi2
  have hstep3 : Step ⟨σ2, i2, cA.steps+1+1⟩ ⟨σ3, i3, cA.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = ment := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x800040c4#64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x800040c0#64) 4 = (0x800040c4#64:BitVec 64) from by decide] at this
  have hx9_3 : σ3.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs1Sext] at this
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 := obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Exec_stmtLoaded σ3.mem := by rw [hmem3e]; exact hcodeA
  -- ============ 0x800040c4: ld s2,144(sp) → x18 := v18 ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800040c4_es σ3 i3 (cA.steps + 1 + 1 + 1) (0x800040c4#64) vmi3 (sp-176#64) s20 s21 s22 s23 s24 s25 s26 s27
      hG3 hpc3 hmi3 hsp_3 hcode3 rfl
      (by rw [haS2]; omega) (by rw [haS2]; omega) (by rw [haS2, htoh]; right; omega) (by rw [haS2]; omega)
      (by rw [haS2, hmem3e]; exact hs20) (by rw [haS2, hmem3e]; exact hs21) (by rw [haS2, hmem3e]; exact hs22)
      (by rw [haS2, hmem3e]; exact hs23) (by rw [haS2, hmem3e]; exact hs24) (by rw [haS2, hmem3e]; exact hs25)
      (by rw [haS2, hmem3e]; exact hs26) (by rw [haS2, hmem3e]; exact hs27) hi3
  have hstep4 : Step ⟨σ3, i3, cA.steps+1+1+1⟩ ⟨σ4, i4, cA.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = ment := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x800040c8#64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x800040c4#64) 4 = (0x800040c8#64:BitVec 64) from by decide] at this
  have hx18_4 : σ4.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs2Sext] at this
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 := obs_alu_other' hobs4 Register.x8 (by decide) hx8_3
  have hx9_4 : σ4.regs.get? Register.x9 = some v9 := obs_alu_other' hobs4 Register.x9 (by decide) hx9_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hcode4 : Exec_stmtLoaded σ4.mem := by rw [hmem4e]; exact hcodeA
  -- ============ 0x800040c8: ld s3,136(sp) → x19 := v19 ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800040c8_es σ4 i4 (cA.steps + 1 + 1 + 1 + 1) (0x800040c8#64) vmi4 (sp-176#64) s30 s31 s32 s33 s34 s35 s36 s37
      hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haS3]; omega) (by rw [haS3]; omega) (by rw [haS3, htoh]; right; omega) (by rw [haS3]; omega)
      (by rw [haS3, hmem4e]; exact hs30) (by rw [haS3, hmem4e]; exact hs31) (by rw [haS3, hmem4e]; exact hs32)
      (by rw [haS3, hmem4e]; exact hs33) (by rw [haS3, hmem4e]; exact hs34) (by rw [haS3, hmem4e]; exact hs35)
      (by rw [haS3, hmem4e]; exact hs36) (by rw [haS3, hmem4e]; exact hs37) hi4
  have hstep5 : Step ⟨σ4, i4, cA.steps+1+1+1+1⟩ ⟨σ5, i5, cA.steps+1+1+1+1+1⟩ := hstep5'
  have hmem5e : σ5.mem = ment := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x800040cc#64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x800040c8#64) 4 = (0x800040cc#64:BitVec 64) from by decide] at this
  have hx19_5 : σ5.regs.get? Register.x19 = some v19 := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs3Sext] at this
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 := obs_alu_other' hobs5 Register.x8 (by decide) hx8_4
  have hx9_5 : σ5.regs.get? Register.x9 = some v9 := obs_alu_other' hobs5 Register.x9 (by decide) hx9_4
  have hx18_5 : σ5.regs.get? Register.x18 = some v18 := obs_alu_other' hobs5 Register.x18 (by decide) hx18_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hcode5 : Exec_stmtLoaded σ5.mem := by rw [hmem5e]; exact hcodeA
  -- ============ 0x800040cc: li a0,2 → x10 := 2 = StatusCode .cont ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_800040cc_es σ5 i5 (cA.steps + 1 + 1 + 1 + 1 + 1) (0x800040cc#64) vmi5 hG5 hpc5 hmi5 hcode5 rfl hi5
  have hstep6 : Step ⟨σ5, i5, cA.steps+1+1+1+1+1⟩ ⟨σ6, i6, cA.steps+1+1+1+1+1+1⟩ := hstep6'
  have hmem6e : σ6.mem = ment := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x800040d0#64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x800040cc#64) 4 = (0x800040d0#64:BitVec 64) from by decide] at this
  have ha0_6 : σ6.regs.get? Register.x10 = some (StatusCode .cont) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = StatusCode .cont from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other' hobs6 Register.x2 (by decide) hsp_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := obs_alu_other' hobs6 Register.x8 (by decide) hx8_5
  have hx9_6 : σ6.regs.get? Register.x9 = some v9 := obs_alu_other' hobs6 Register.x9 (by decide) hx9_5
  have hx18_6 : σ6.regs.get? Register.x18 = some v18 := obs_alu_other' hobs6 Register.x18 (by decide) hx18_5
  have hx19_6 : σ6.regs.get? Register.x19 = some v19 := obs_alu_other' hobs6 Register.x19 (by decide) hx19_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hcode6 : Exec_stmtLoaded σ6.mem := by rw [hmem6e]; exact hcodeA
  -- ============ 0x800040d0: addi sp,sp,176 → x2 := sp ============
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_800040d0_es σ6 i6 (cA.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x800040d0#64) vmi6 (sp-176#64) hG6 hpc6 hmi6 hsp_6 hcode6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, cA.steps+1+1+1+1+1+1⟩ ⟨σ7, i7, cA.steps+1+1+1+1+1+1+1⟩ := hstep7'
  have hmem7e : σ7.mem = ment := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x800040d4#64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x800040d0#64) 4 = (0x800040d4#64:BitVec 64) from by decide] at this
  have hsp_7 : σ7.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [sp_add176] at this
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha0_7 : σ7.regs.get? Register.x10 = some (StatusCode .cont) := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_alu_other' hobs7 Register.x8 (by decide) hx8_6
  have hx9_7 : σ7.regs.get? Register.x9 = some v9 := obs_alu_other' hobs7 Register.x9 (by decide) hx9_6
  have hx18_7 : σ7.regs.get? Register.x18 = some v18 := obs_alu_other' hobs7 Register.x18 (by decide) hx18_6
  have hx19_7 : σ7.regs.get? Register.x19 = some v19 := obs_alu_other' hobs7 Register.x19 (by decide) hx19_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hcode7 : Exec_stmtLoaded σ7.mem := by rw [hmem7e]; exact hcodeA
  -- ============ 0x800040d4: ret → PC := r ============
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r hraAl]; exact hraAl
  obtain ⟨σ8, i8, hstep8', hi8, hG8, hmem8, hobs8⟩ :=
    site_800040d4_es σ7 i7 (cA.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800040d4#64) vmi7 r hG7 hpc7 hmi7 hra_7 hcode7 rfl hrettgt hi7
  have hstep8 : Step ⟨σ7, i7, cA.steps+1+1+1+1+1+1+1⟩ ⟨σ8, i8, cA.steps+1+1+1+1+1+1+1+1⟩ := hstep8'
  have hmem8e : σ8.mem = ment := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs8
  have ha0_8 : σ8.regs.get? Register.x10 = some (StatusCode .cont) := obs_jr_other' hobs8 Register.x10 (by decide) ha0_7
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_jr_other' hobs8 Register.x1 (by decide) hra_7
  have hsp_8 : σ8.regs.get? Register.x2 = some sp := obs_jr_other' hobs8 Register.x2 (by decide) hsp_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 := obs_jr_other' hobs8 Register.x8 (by decide) hx8_7
  have hx9_8 : σ8.regs.get? Register.x9 = some v9 := obs_jr_other' hobs8 Register.x9 (by decide) hx9_7
  have hx18_8 : σ8.regs.get? Register.x18 = some v18 := obs_jr_other' hobs8 Register.x18 (by decide) hx18_7
  have hx19_8 : σ8.regs.get? Register.x19 = some v19 := obs_jr_other' hobs8 Register.x19 (by decide) hx19_7
  obtain ⟨vmi8, hmi8⟩ := obs_jr_minstret hobs8
  -- output invariance across the 8 cont-tail steps
  have hout8 : σ8.sailOutput = out0 := by
    rw [hobs8.out, sailOutput_sigmaPost_jump_x0, hobs7.out, sailOutput_sigmaPost_alu,
      hobs6.out, sailOutput_sigmaPost_alu, hobs5.out, sailOutput_sigmaPost_alu,
      hobs4.out, sailOutput_sigmaPost_alu, hobs3.out, sailOutput_sigmaPost_alu,
      hobs2.out, sailOutput_sigmaPost_alu, hobs1.out, sailOutput_sigmaPost_alu]; exact houtA
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe8 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x19 == R) = false → (Register.x2 == R) = false →
      (Register.x1 == R) = false → (Register.x10 == R) = false →
      σ8.regs.get? R = cA.σ.regs.get? R := by
    intro R hR he8 he9 he18 he19 he2 he1 he10
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have a : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd v) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
    have jr : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
        ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    exact (jr hobs8).trans ((a hobs7 he2).trans ((a hobs6 he10).trans ((a hobs5 he19).trans
      ((a hobs4 he18).trans ((a hobs3 he9).trans ((a hobs2 he8).trans (a hobs1 he1)))))))
  refine ⟨⟨σ8, i8, cA.steps+1+1+1+1+1+1+1+1⟩, ?_, ?_⟩
  · exact hstepsA.trans ((Steps.single hstep1).trans ((Steps.single hstep2).trans
      ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans
      ((Steps.single hstep6).trans ((Steps.single hstep7).trans (Steps.single hstep8))))))))
  · refine
      { good := hG8
        tick := hi8
        pc := hpc8
        a0 := ha0_8
        ra := hra_8
        spReg := hsp_8
        minstret := ⟨_, hmi8⟩
        store := ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, by rw [hmem8e]; exact hstoreA⟩
        out := ?_
        retval := ?_
        frame := ?_
        memFrame := ?_ }
    · show Vsa.Machine.output σ8 = st.out
      simp only [Vsa.Machine.output]; rw [hout8]; exact houtStrA
    · intro v hv; cases hv
    · intro R hR
      by_cases h8 : (Register.x8 == R) = true
      · have : R = Register.x8 := by rw [beq_iff_eq] at h8; exact h8.symm
        subst this; rw [hx8_8]; exact hgx8.symm
      by_cases h9 : (Register.x9 == R) = true
      · have : R = Register.x9 := by rw [beq_iff_eq] at h9; exact h9.symm
        subst this; rw [hx9_8]; exact hgx9.symm
      by_cases h18 : (Register.x18 == R) = true
      · have : R = Register.x18 := by rw [beq_iff_eq] at h18; exact h18.symm
        subst this; rw [hx18_8]; exact hgx18.symm
      by_cases h19 : (Register.x19 == R) = true
      · have : R = Register.x19 := by rw [beq_iff_eq] at h19; exact h19.symm
        subst this; rw [hx19_8]; exact hgx19.symm
      by_cases h2 : (Register.x2 == R) = true
      · have : R = Register.x2 := by rw [beq_iff_eq] at h2; exact h2.symm
        subst this; rw [hsp_8]; exact hgx2.symm
      · have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hR.1
        have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hR.1
        rw [hframe8 R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
          (by simpa using h19) (by simpa using h2) h1 h10]
        exact hframeA R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
          (by simpa using h19) (by simpa using h2)
    · intro a hstk _harena
      right; rw [hmem8e]; exact hmemframeA a hstk

end Vsa.Sim
