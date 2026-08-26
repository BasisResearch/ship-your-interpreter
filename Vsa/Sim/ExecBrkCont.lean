import Vsa.Sim.ExecSimCommon
import Vsa.Sim.Exec_stmtSites
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.EvalIntSim2

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
    (st' : Vsa.While.St) (status : Status)
    (sp r aRet : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String) (m0 : Mem)
    (hnotret : ∀ v, status ≠ .ret v) :
    Triple
      (fun c => ∃ mpre, PreExecEpilogue g N A SL φf φc st' status sp r aRet v8 v9 v18 v19 out0 m0 mpre c)
      (ExecExit g N A SL φf φc st' status sp r aRet m0) := by
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
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have ha0_1 : σ1.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
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
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have ha0_2 : σ2.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
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
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have ha0_3 : σ3.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 := obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
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
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have ha0_4 : σ4.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 := obs_alu_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx9_4 : σ4.regs.get? Register.x9 = some v9 := obs_alu_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_3
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
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have ha0_5 : σ5.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 := obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx9_5 : σ5.regs.get? Register.x9 = some v9 := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_4
  have hx18_5 : σ5.regs.get? Register.x18 = some v18 := obs_alu_other hobs5 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_4
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
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha0_6 : σ6.regs.get? Register.x10 = some (StatusCode status) := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := obs_alu_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx9_6 : σ6.regs.get? Register.x9 = some v9 := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_5
  have hx18_6 : σ6.regs.get? Register.x18 = some v18 := obs_alu_other hobs6 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_5
  have hx19_6 : σ6.regs.get? Register.x19 = some v19 := obs_alu_other hobs6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_5
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
  have ha0_7 : σ7.regs.get? Register.x10 = some (StatusCode status) := obs_jr_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_jr_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have hsp_7 : σ7.regs.get? Register.x2 = some sp := obs_jr_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_jr_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx9_7 : σ7.regs.get? Register.x9 = some v9 := obs_jr_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_6
  have hx18_7 : σ7.regs.get? Register.x18 = some v18 := obs_jr_other hobs7 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_6
  have hx19_7 : σ7.regs.get? Register.x19 = some v19 := obs_jr_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_6
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

/-! ## `execBrkSim` — the `ExecS.brk` simulation Triple

`execBlockA` (prologue+dispatch to `execArmBrk = 0x80004098`) ≫ `li a0,1` (the arm,
setting `x10 = 1 = StatusCode .brk`) ≫ `execBlockD` (shared epilogue). Conditional
only on the named `execBlockA` residual (`hBlockA`). -/
theorem execBrkSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env .brk st .brk)
    (hBlockA : ExecBlockAGoal g N A SL φf φc st d env .brk
      sp r aInterp aStmt aEnv aRet execArmBrk m0 out0) :
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env .brk sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st .brk sp r aRet m0) := by
  intro c hpre
  -- block A: prologue + dispatch → arm entry at execArmBrk = 0x80004098
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
  have hspB : σB.regs.get? Register.x2 = some (sp - 176#64) := obs_alu_other hobsB Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspA
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
    execBlockD g N A SL φf φc st .brk sp r aRet v8 v9 v18 v19 out0 m0 (by intro v hv; cases hv)
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
touch `x10`, so the mechanics are identical. Conditional only on `hBlockA`. -/
theorem execContSim
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) (out0 : Array String)
    (_hSpec : ExecS st d env .cont st .cont)
    (hBlockA : ExecBlockAGoal g N A SL φf φc st d env .cont
      sp r aInterp aStmt aEnv aRet execArmCont m0 out0) :
    Triple
      (fun c => ExecEntry g N A SL φf φc st d env .cont sp r aInterp aStmt aEnv aRet m0 c
        ∧ c.σ.sailOutput = out0)
      (ExecExit g N A SL φf φc st .cont sp r aRet m0) := by
  intro c hpre
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
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspA
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
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
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
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 := obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
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
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 := obs_alu_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx9_4 : σ4.regs.get? Register.x9 = some v9 := obs_alu_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_3
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
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 := obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx9_5 : σ5.regs.get? Register.x9 = some v9 := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_4
  have hx18_5 : σ5.regs.get? Register.x18 = some v18 := obs_alu_other hobs5 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_4
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
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp-176#64) := obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := obs_alu_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx9_6 : σ6.regs.get? Register.x9 = some v9 := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_5
  have hx18_6 : σ6.regs.get? Register.x18 = some v18 := obs_alu_other hobs6 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_5
  have hx19_6 : σ6.regs.get? Register.x19 = some v19 := obs_alu_other hobs6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_5
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
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have ha0_7 : σ7.regs.get? Register.x10 = some (StatusCode .cont) := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx9_7 : σ7.regs.get? Register.x9 = some v9 := obs_alu_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_6
  have hx18_7 : σ7.regs.get? Register.x18 = some v18 := obs_alu_other hobs7 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_6
  have hx19_7 : σ7.regs.get? Register.x19 = some v19 := obs_alu_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_6
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
  have ha0_8 : σ8.regs.get? Register.x10 = some (StatusCode .cont) := obs_jr_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_jr_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  have hsp_8 : σ8.regs.get? Register.x2 = some sp := obs_jr_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 := obs_jr_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_7
  have hx9_8 : σ8.regs.get? Register.x9 = some v9 := obs_jr_other hobs8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx9_7
  have hx18_8 : σ8.regs.get? Register.x18 = some v18 := obs_jr_other hobs8 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_7
  have hx19_8 : σ8.regs.get? Register.x19 = some v19 := obs_jr_other hobs8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_7
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
