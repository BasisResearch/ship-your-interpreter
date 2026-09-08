import Vsa.Sim.EvalChildArm
import Vsa.Sim.PinW
import Vsa.Sim.BridgeSegFramed

/-!
# `TruthyCopy` — the parametric condition-copy and `value_truthy` seam

After a condition child returns, the `while`, `if`, and `for` arms all copy the
24-byte result from the sub-result slot to `esp+16`, call `value_truthy`, and
branch on its answer.  `WhileGeomSuppliers` closed this seam for `while` with
`0x80004050`-specific files.  This file states it ONCE over a descriptor
`TruthyCopy` attached to an `EvalChildArm`:

* `TruthyCopy.Cert D T` — decided facts (the reflected copy's fold, its
  write log as three `sd`s, the `jal value_truthy` site);
* `copyReady_of_exitKit` — from the child's exit kit, park at `value_truthy`;
* `truthyReturn_of_copyReady` — the helper returns with the truthiness bit;
* `route_of_truthyReturn` — run any reflected branch route from that return;
* `normalExitPre_of_route` — a route that ends at a `li a0,0` is a
  `NormalExitTailPre`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`
bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) the `∃` here are the fixed StepObs site post
-- (`Cert.jal_site`), reached-config existentials of runs, and saved-register witnesses
-- inside named-field structures; all consumed through named fields.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

local notation "SpecSt" => Vsa.While.St

/-! ## The descriptor -/

/-- The copy-and-`value_truthy` seam of one condition arm. -/
structure TruthyCopy where
  /-- The reflected copy: three `ld` from the sub-result slot, `addi a0,sp,16`,
  three `sd` to `esp+16`; starts at the child's return PC. -/
  copySeg : List BBlock
  /-- PC of `jal value_truthy`. -/
  jalPC : BitVec 64
  /-- Decoded 21-bit `jal` immediate. -/
  jalImm : BitVec 21

namespace TruthyCopy

/-- The helper's link PC. -/
def retPC (T : TruthyCopy) : BitVec 64 := BitVec.addInt T.jalPC 4

/-- The three total loads of the copy, from the arm's sub-result slot. -/
def lds (D : EvalChildArm) (m : Mem) (esp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (esp.toNat + D.sretOff),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 8),
   EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 16)]

/-- The reflected outcome of the copy. -/
def out (D : EvalChildArm) (T : TruthyCopy) (esp s0 s1 s2 s3 : BitVec 64) (m : Mem) :
    SegEvalState :=
  evalBlocks T.copySeg (SegEvalState.init (EvalChildArm.regs esp s0 s1 s2 s3) (lds D m esp))

/-- The destination and the three `sd` addresses. -/
def dst (esp : BitVec 64) : BitVec 64 := esp + sign_extend (m := 64) (0x010#12)

/-- Facts about the descriptor alone. -/
structure Cert (D : EvalChildArm) (T : TruthyCopy) : Prop where
  /-- The sub-result slot sits above the copy destination `[esp+16, esp+40)`. -/
  src_lo : 40 ≤ D.sretOff
  chain_ok : ChainOK D.retPC [2, 8, 9, 18, 19] T.copySeg
  avoid_abi : WrChainAvoidAbi T.copySeg
  keys_out : ∀ esp s0 s1 s2 s3 m, KeysOK (keysG (out D T esp s0 s1 s2 s3 m).regs)
  ra_out : ∀ esp s0 s1 s2 s3 m, KeysAvoidRa (out D T esp s0 s1 s2 s3 m).regs
  end_pc : ∀ esp s0 s1 s2 s3 m,
    evalBlocksPC D.retPC
      (SegEvalState.init (EvalChildArm.regs esp s0 s1 s2 s3) (lds D m esp)) T.copySeg = T.jalPC
  a0_out : ∀ esp s0 s1 s2 s3 m, lookupG 10 (out D T esp s0 s1 s2 s3 m).regs = some (dst esp)
  sp_out : ∀ esp s0 s1 s2 s3 m, lookupG 2 (out D T esp s0 s1 s2 s3 m).regs = some esp
  log_eq : ∀ esp s0 s1 s2 s3 m,
    writeLog m (out D T esp s0 s1 s2 s3 m).log =
      writeMap8 (writeMap8 (writeMap8 m
        (esp + sign_extend (m := 64) (0x010#12)).toNat
        (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + D.sretOff)))))
        (esp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 8)))))
        (esp + sign_extend (m := 64) (0x020#12)).toNat
        (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + D.sretOff + 16))))
  jal_tgt : T.jalPC + sign_extend (m := 64) T.jalImm = 0x8000282c#64
  ret_clean : BitVec.update (T.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = T.retPC
  ret_align : (BitVec.update (T.retPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
  jal_site : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
    GoodState σ → σ.regs.get? Register.PC = some T.jalPC →
    σ.regs.get? Register.minstret = some vmi → Exec_stmtLoaded σ.mem → i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ T.jalPC vmi T.jalImm Register.x1
        (BitVec.addInt T.jalPC 4))
  /-- The copy's chain facts from the lowered-frame geometry. -/
  copy_facts : ∀ (m : Mem) (SL : StackLayout) (esp s0 s1 s2 s3 : BitVec 64),
    Exec_stmtLoaded m → SL.lo ≤ esp.toNat → esp.toNat + 136 ≤ SL.hi →
    0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000 → tohostAddr + 16 ≤ SL.lo →
    esp.toNat % 16 = 0 →
    ChainFacts m m (EvalChildArm.regs esp s0 s1 s2 s3) (lds D m esp) T.copySeg

/-! ## Byte-level facts about the copy -/

theorem sdData_sext_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 0 8 = b0 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 8 8 = b1 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 16 8 = b2 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 24 8 = b3 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 32 8 = b4 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 40 8 = b5 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 48 8 = b6 ∧
    (sdData_val (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))).extractLsb' 56 8 = b7 := by
  rw [sdData_val_id, sext_full]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     rw [word8_toNat_recon]; omega)

theorem dst_toNat (esp : BitVec 64) (hesp : esp.toNat + 40 ≤ 0x100000000) :
    (dst esp).toNat = esp.toNat + 16 := by
  unfold dst
  have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The copy's write log is a total 24-byte copy from the sub-result slot to
`esp+16` (the actual Sail load convention `getD 0`). -/
theorem writeLog_total (D : EvalChildArm) (T : TruthyCopy) (C : T.Cert D)
    (m : Mem) (esp s0 s1 s2 s3 : BitVec 64)
    (hesp : esp.toNat + D.sretOff + 24 ≤ 0x100000000) (hoff : 40 ≤ D.sretOff) :
    ∀ j, j < 24 →
      (writeLog m (out D T esp s0 s1 s2 s3 m).log)[esp.toNat + 16 + j]? =
        some ((m[esp.toNat + D.sretOff + j]?).getD 0) := by
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 32)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hsplt := esp.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hn16 := haddr 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn24 := haddr 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn32 := haddr 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  let k0 := (m[esp.toNat + D.sretOff]?).getD 0
  let k1 := (m[esp.toNat + D.sretOff + 1]?).getD 0
  let k2 := (m[esp.toNat + D.sretOff + 2]?).getD 0
  let k3 := (m[esp.toNat + D.sretOff + 3]?).getD 0
  let k4 := (m[esp.toNat + D.sretOff + 4]?).getD 0
  let k5 := (m[esp.toNat + D.sretOff + 5]?).getD 0
  let k6 := (m[esp.toNat + D.sretOff + 6]?).getD 0
  let k7 := (m[esp.toNat + D.sretOff + 7]?).getD 0
  let p0 := (m[esp.toNat + D.sretOff + 8]?).getD 0
  let p1 := (m[esp.toNat + D.sretOff + 8 + 1]?).getD 0
  let p2 := (m[esp.toNat + D.sretOff + 8 + 2]?).getD 0
  let p3 := (m[esp.toNat + D.sretOff + 8 + 3]?).getD 0
  let p4 := (m[esp.toNat + D.sretOff + 8 + 4]?).getD 0
  let p5 := (m[esp.toNat + D.sretOff + 8 + 5]?).getD 0
  let p6 := (m[esp.toNat + D.sretOff + 8 + 6]?).getD 0
  let p7 := (m[esp.toNat + D.sretOff + 8 + 7]?).getD 0
  let q0 := (m[esp.toNat + D.sretOff + 16]?).getD 0
  let q1 := (m[esp.toNat + D.sretOff + 16 + 1]?).getD 0
  let q2 := (m[esp.toNat + D.sretOff + 16 + 2]?).getD 0
  let q3 := (m[esp.toNat + D.sretOff + 16 + 3]?).getD 0
  let q4 := (m[esp.toNat + D.sretOff + 16 + 4]?).getD 0
  let q5 := (m[esp.toNat + D.sretOff + 16 + 5]?).getD 0
  let q6 := (m[esp.toNat + D.sretOff + 16 + 6]?).getD 0
  let q7 := (m[esp.toNat + D.sretOff + 16 + 7]?).getD 0
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := sdData_sext_bytes k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := sdData_sext_bytes p0 p1 p2 p3 p4 p5 p6 p7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := sdData_sext_bytes q0 q1 q2 q3 q4 q5 q6 q7
  intro j hj
  rw [C.log_eq, hn16, hn24, hn32]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
      j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨
      j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [EvalChildArm.wordLds8, bytesVal, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_0, eK0]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_1, eK1]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_2, eK2]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_3, eK3]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_4, eK4]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_5, eK5]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_6, eK6]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (esp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_7, eK7]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_0, eP0]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_1, eP1]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_2, eP2]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_3, eP3]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_4, eP4]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_5, eP5]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_6, eP6]
  · rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) _ _ (by omega), getElem_writeMap8_7, eP7]
  · rw [getElem_writeMap8_0, eQ0]
  · rw [getElem_writeMap8_1, eQ1]
  · rw [getElem_writeMap8_2, eQ2]
  · rw [getElem_writeMap8_3, eQ3]
  · rw [getElem_writeMap8_4, eQ4]
  · rw [getElem_writeMap8_5, eQ5]
  · rw [getElem_writeMap8_6, eQ6]
  · rw [getElem_writeMap8_7, eQ7]

/-- The copy changes only its 24-byte destination. -/
theorem writeLog_frame (D : EvalChildArm) (T : TruthyCopy) (C : T.Cert D)
    (m : Mem) (esp s0 s1 s2 s3 : BitVec 64)
    (hesp : esp.toNat + 40 ≤ 0x100000000) :
    ∀ k, ¬ (esp.toNat + 16 ≤ k ∧ k < esp.toNat + 40) →
      (writeLog m (out D T esp s0 s1 s2 s3 m).log)[k]? = m[k]? := by
  intro k hk
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 32)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hsplt := esp.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hn16 := haddr 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn24 := haddr 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn32 := haddr 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  rw [C.log_eq, hn16, hn24, hn32]
  rw [getElem_writeMap8_disjoint _ (esp.toNat + 32) k _ (by omega),
    getElem_writeMap8_disjoint _ (esp.toNat + 24) k _ (by omega),
    getElem_writeMap8_disjoint _ (esp.toNat + 16) k _ (by omega)]

/-- The copy preserves memory presence. -/
theorem memExtends (D : EvalChildArm) (T : TruthyCopy) (C : T.Cert D)
    (m : Mem) (esp s0 s1 s2 s3 : BitVec 64) :
    MemExtends m (writeLog m (out D T esp s0 s1 s2 s3 m).log) := by
  rw [C.log_eq]
  exact ((memExtends_writeMap8 m _ _).trans (memExtends_writeMap8 _ _ _)).trans
    (memExtends_writeMap8 _ _ _)

/-- Only the truthiness header crosses the copy. -/
theorem truthyHeader (D : EvalChildArm) (T : TruthyCopy) (C : T.Cert D)
    (m : Mem) (esp s0 s1 s2 s3 : BitVec 64) (v : Value)
    (hesp : esp.toNat + D.sretOff + 24 ≤ 0x100000000) (hoff : 40 ≤ D.sretOff)
    (hv : TruthyHeaderRepr m (esp.toNat + D.sretOff) v) :
    TruthyHeaderRepr (writeLog m (out D T esp s0 s1 s2 s3 m).log) (esp.toNat + 16) v :=
  truthyHeaderRepr_copy_total (writeLog_total D T C m esp s0 s1 s2 s3 hesp hoff) hv

/-! ## Parked at `value_truthy` -/

/-- Exact parked state after the copy and its `jal value_truthy`. -/
structure CopyReady (T : TruthyCopy)
    (gC : (R : Register) → Option (RegisterType R))
    (v : Value) (esp s0 s1 s2 s3 : BitVec 64)
    (mCopy : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x8000282c#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mCopy
  out : cfg.σ.sailOutput = out
  code : Exec_stmtLoaded mCopy
  truthy_loaded : Value_truthyLoaded mCopy
  header : TruthyHeaderRepr mCopy (dst esp).toNat v
  region : TruthyRegion (dst esp)
  a0 : cfg.σ.regs.get? Register.x10 = some (dst esp)
  ra : cfg.σ.regs.get? Register.x1 = some T.retPC
  sp : cfg.σ.regs.get? Register.x2 = some esp
  s0 : cfg.σ.regs.get? Register.x8 = some s0
  s1 : cfg.σ.regs.get? Register.x9 = some s1
  s2 : cfg.σ.regs.get? Register.x18 = some s2
  s3 : cfg.σ.regs.get? Register.x19 = some s3
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R

private theorem abiPreservedNoise_of_abi {R : Register}
    (hR : AbiPreserved R = true) : AbiPreservedNoise R := by
  cases R <;> simp [AbiPreserved, AbiPreservedNoise] at hR ⊢

/-- Execute the copy from the child's exit kit and stop at the helper entry. -/
theorem copyReady_of_exitKit (D : EvalChildArm) (CD : D.Cert) (T : TruthyCopy) (C : T.Cert D)
    {s : Stmt} {e : Expr}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem} (cfg : Config)
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hKit : D.ExitKit s gC N A SL φf' φc' st' v sp aStmt aRet mC cfg) :
    ∃ (mCopy : Mem) (cfgCopy : Config),
      Steps cfg cfgCopy ∧
      mCopy = writeLog cfg.σ.mem (out D T (sp - 176#64) aStmt aInterp aRet aEnv cfg.σ.mem).log ∧
      T.CopyReady gC v (sp - 176#64) aStmt aInterp aRet aEnv mCopy cfg.σ.sailOutput cfgCopy := by
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom CD
  have hsretRoom := CD.sret_room
  have hsretAl := CD.sret_align
  let mCopy : Mem := writeLog cfg.σ.mem (out D T (sp - 176#64) aStmt aInterp aRet aEnv cfg.σ.mem).log
  obtain ⟨hstackLo, hstackHi⟩ := hCarrier.stack_ram
  have hespLo : SL.lo ≤ (sp - 176#64).toNat := by rw [hesp]; omega
  have hespHi : (sp - 176#64).toNat + 136 ≤ SL.hi := by rw [hesp]; omega
  have hespAl : (sp - 176#64).toNat % 16 = 0 := by rw [hesp]; omega
  have hnowrap : (sp - 176#64).toNat + 40 ≤ 0x100000000 := by omega
  have hnowrapSrc : (sp - 176#64).toNat + D.sretOff + 24 ≤ 0x100000000 := by omega
  have hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfg.σ.mem[k]? :=
    writeLog_frame D T C cfg.σ.mem (sp - 176#64) aStmt aInterp aRet aEnv hnowrap
  have hcodeCopy : Exec_stmtLoaded mCopy := by
    apply loaded_exec_stmt_agree cfg.σ.mem mCopy _ hKit.code
    intro k hklo hkhi
    exact hcopyFrame k (by
      intro hd
      rcases hCarrier.code_stack_disjoint with hs | hs <;> omega)
  have hEvalAgree : ∀ k, EvalCallFootprint k → mCopy[k]? = cfg.σ.mem[k]? := by
    intro k hk
    apply hcopyFrame k
    have hs := hKit.ground.eval_call.outsideStack hk
    omega
  obtain ⟨_interp, _vint, htruthyLoaded, _intSlot, _nbs, _kind⟩ :=
    hKit.ground.eval_call.pins mCopy hEvalAgree
  have hHeaderSrc : TruthyHeaderRepr cfg.σ.mem ((sp - 176#64).toNat + D.sretOff) v := by
    have h := hKit.header
    rwa [hsret, ← hesp] at h
  have hoff40 : 40 ≤ D.sretOff := C.src_lo
  have hHeaderCopy : TruthyHeaderRepr mCopy ((sp - 176#64).toNat + 16) v :=
    truthyHeader D T C cfg.σ.mem (sp - 176#64) aStmt aInterp aRet aEnv v hnowrapSrc hoff40 hHeaderSrc
  have hL : GHolds cfg.σ (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv) := by
    simp only [EvalChildArm.regs, GHolds, gprGet]
    exact ⟨(hKit.frame Register.x2 (by decide)).trans hCarrier.spReg,
      (hKit.frame Register.x8 (by decide)).trans hCarrier.s0,
      (hKit.frame Register.x9 (by decide)).trans hCarrier.s1,
      (hKit.frame Register.x18 (by decide)).trans hCarrier.s2,
      (hKit.frame Register.x19 (by decide)).trans hCarrier.s3, True.intro⟩
  have hfacts : ChainFacts cfg.σ.mem cfg.σ.mem (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv)
      (lds D cfg.σ.mem (sp - 176#64)) T.copySeg :=
    C.copy_facts cfg.σ.mem SL (sp - 176#64) aStmt aInterp aRet aEnv hKit.code hespLo hespHi
      ⟨hstackLo, hstackHi⟩ hCarrier.stack_win hespAl
  obtain ⟨vm, hmi⟩ := hKit.minstret
  obtain ⟨σCopy, iCopy, hsCopy, hiCopy, hgoodCopy, hpcCopy, hraCopy,
      hmiCopy, hregsCopy, hmemCopy, houtCopy, hframeCopy⟩ :=
    bridgeOfSegOut T.copySeg (EvalChildArm.regs (sp - 176#64) aStmt aInterp aRet aEnv)
      (lds D cfg.σ.mem (sp - 176#64)) cfg.σ cfg.tick cfg.steps D.retPC 0x8000282c#64 T.retPC vm
      cfg.σ.mem hKit.good hKit.pc hmi rfl hL
      (by change KeysOK [2, 8, 9, 18, 19]; decide) hfacts hKit.tick
      C.chain_ok C.avoid_abi (C.keys_out _ _ _ _ _ _) (C.ra_out _ _ _ _ _ _)
      (by
        intro σ i u hG hi hpc hmi hm _
        obtain ⟨vm, hvm⟩ := hmi
        rw [C.end_pc] at hpc
        have hc : Exec_stmtLoaded σ.mem := by rw [hm]; exact hcodeCopy
        obtain ⟨σ2, i2, hs2, hi2, hG2, hm2, ho2⟩ := C.jal_site σ i u vm hG hpc hvm hc hi
        exact jalStepO_of_obs hs2 hi2 hG2 hm2 ho2 C.jal_tgt)
  have hRegs' : GHolds σCopy (out D T (sp - 176#64) aStmt aInterp aRet aEnv cfg.σ.mem).regs := hregsCopy
  let cfgCopy : Config := ⟨σCopy, iCopy, cfg.steps + evalBlocksFuel T.copySeg + 1⟩
  have hmemCopy' : σCopy.mem = mCopy := hmemCopy
  have hbufNat : (dst (sp - 176#64)).toNat = (sp - 176#64).toNat + 16 := dst_toNat (sp - 176#64) hnowrap
  have hbufRegion : TruthyRegion (dst (sp - 176#64)) := by
    refine { align := ?_, lo := ?_, hi := ?_, win := ?_ }
    · rw [hbufNat]; omega
    · rw [hbufNat]; omega
    · rw [hbufNat]; omega
    · rw [hbufNat]; have := hCarrier.stack_win; omega
  have hx2Copy : σCopy.regs.get? Register.x2 = some (sp - 176#64) :=
    (hframeCopy Register.x2 (by decide)).trans
      ((hKit.frame Register.x2 (by decide)).trans hCarrier.spReg)
  have hx8Copy : σCopy.regs.get? Register.x8 = some aStmt :=
    (hframeCopy Register.x8 (by decide)).trans
      ((hKit.frame Register.x8 (by decide)).trans hCarrier.s0)
  have hx9Copy : σCopy.regs.get? Register.x9 = some aInterp :=
    (hframeCopy Register.x9 (by decide)).trans
      ((hKit.frame Register.x9 (by decide)).trans hCarrier.s1)
  have hx18Copy : σCopy.regs.get? Register.x18 = some aRet :=
    (hframeCopy Register.x18 (by decide)).trans
      ((hKit.frame Register.x18 (by decide)).trans hCarrier.s2)
  have hx19Copy : σCopy.regs.get? Register.x19 = some aEnv :=
    (hframeCopy Register.x19 (by decide)).trans
      ((hKit.frame Register.x19 (by decide)).trans hCarrier.s3)
  have hx10Copy : σCopy.regs.get? Register.x10 = some (dst (sp - 176#64)) := by
    simpa only [gprGet] using (gholds_lookup _ hRegs' (C.a0_out (sp - 176#64) aStmt aInterp aRet aEnv _))
  refine ⟨mCopy, cfgCopy, hsCopy, rfl, ?_⟩
  refine
    { good := hgoodCopy
      tick := hiCopy
      pc := hpcCopy
      minstret := hmiCopy
      mem := hmemCopy'
      out := houtCopy
      code := hcodeCopy
      truthy_loaded := htruthyLoaded
      header := by rw [hbufNat]; exact hHeaderCopy
      region := hbufRegion
      a0 := hx10Copy
      ra := hraCopy
      sp := hx2Copy
      s0 := hx8Copy
      s1 := hx9Copy
      s2 := hx18Copy
      s3 := hx19Copy
      frame := ?_ }
  intro R hR
  exact (hframeCopy R hR).trans (hKit.frame R (abiPreservedNoise_of_abi hR))

/-! ## The helper's return -/

private theorem notWrittenT_of_abiPreserved (R : Register)
    (hR : AbiPreserved R = true) : NotWrittenT R := by
  cases R <;> simp_all [AbiPreserved, NotWrittenT]

/-- The parked state after `value_truthy` returns with the truthiness bit. -/
structure TruthyReturn (T : TruthyCopy)
    (gC : (R : Register) → Option (RegisterType R))
    (esp s0 s1 s2 s3 : BitVec 64) (mCopy : Mem) (out : Array String) (b : Bool)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some T.retPC
  a0 : cfg.σ.regs.get? Register.x10 = some (cond b (1#64) (0#64))
  ra : cfg.σ.regs.get? Register.x1 = some T.retPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mCopy
  out : cfg.σ.sailOutput = out
  code : Exec_stmtLoaded mCopy
  sp : cfg.σ.regs.get? Register.x2 = some esp
  s0 : cfg.σ.regs.get? Register.x8 = some s0
  s1 : cfg.σ.regs.get? Register.x9 = some s1
  s2 : cfg.σ.regs.get? Register.x18 = some s2
  s3 : cfg.σ.regs.get? Register.x19 = some s3
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R

/-- Run the header-only truthiness helper from its parked state. -/
theorem truthyReturn_of_copyReady (D : EvalChildArm) (T : TruthyCopy) (C : T.Cert D)
    (N : NativeAddrs) (φc : Addr → Nat)
    {gC : (R : Register) → Option (RegisterType R)} {v : Value}
    {esp s0 s1 s2 s3 : BitVec 64} {mCopy : Mem} {out : Array String} {cfgCopy : Config}
    (hReady : T.CopyReady gC v esp s0 s1 s2 s3 mCopy out cfgCopy) :
    ∃ cfg' : Config, Steps cfgCopy cfg' ∧
      T.TruthyReturn gC esp s0 s1 s2 s3 mCopy out v.truthy cfg' := by
  have hPre : truthy_header_pre (fun R => cfgCopy.σ.regs.get? R) (dst esp) T.retPC N φc v
      mCopy out cfgCopy :=
    ⟨hReady.good, hReady.mem.symm ▸ hReady.truthy_loaded, hReady.mem, hReady.pc, hReady.a0,
      hReady.ra, hReady.minstret, hReady.tick, hReady.header, hReady.region, C.ret_align,
      hReady.out, fun _ _ => rfl⟩
  obtain ⟨cT, hsT, hG, hpc, ha0, hra, hmi, htick, hmem, hout, hframe⟩ :=
    value_truthy_header_spec (fun R => cfgCopy.σ.regs.get? R) (dst esp) T.retPC N φc v
      mCopy out cfgCopy hPre
  refine ⟨cT, hsT, ?_⟩
  exact
    { good := hG
      tick := htick
      pc := by rw [hpc, C.ret_clean]
      a0 := ha0
      ra := hra
      minstret := hmi
      mem := hmem
      out := hout
      code := hReady.code
      sp := (hframe Register.x2 (notWrittenT_of_abiPreserved _ (by decide))).trans hReady.sp
      s0 := (hframe Register.x8 (notWrittenT_of_abiPreserved _ (by decide))).trans hReady.s0
      s1 := (hframe Register.x9 (notWrittenT_of_abiPreserved _ (by decide))).trans hReady.s1
      s2 := (hframe Register.x18 (notWrittenT_of_abiPreserved _ (by decide))).trans hReady.s2
      s3 := (hframe Register.x19 (notWrittenT_of_abiPreserved _ (by decide))).trans hReady.s3
      frame := fun R hR =>
        (hframe R (notWrittenT_of_abiPreserved R hR)).trans (hReady.frame R hR) }

/-! ## A reflected branch route from the return -/

/-- Callee-saved registers other than `s0`: a route may reload `s0` with the
selected branch while preserving everything else the frame owns. -/
def abiButS0 (R : Register) : Bool := AbiPreserved R && !(Register.x8 == R)

theorem abiButS0_noise : ∀ rr ∈ noiseRegs, abiButS0 rr = false := by decide

/-- The truthiness bit plus the six live frame registers. -/
def routeL (status esp ra s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(10, status), (2, esp), (1, ra), (8, s0), (9, s1), (18, s2), (19, s3)]

/-- A parked in-frame state from which a reflected route may run: the route
key in `a0`, the return address, and the five live frame registers.  Both the
`value_truthy` return and a statement child's return convert to it. -/
structure RouteReady (gC : (R : Register) → Option (RegisterType R))
    (pcR a0 esp ra s0 s1 s2 s3 : BitVec 64) (mR : Mem) (out : Array String)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some pcR
  a0 : cfg.σ.regs.get? Register.x10 = some a0
  ra : cfg.σ.regs.get? Register.x1 = some ra
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mR
  out : cfg.σ.sailOutput = out
  sp : cfg.σ.regs.get? Register.x2 = some esp
  s0 : cfg.σ.regs.get? Register.x8 = some s0
  s1 : cfg.σ.regs.get? Register.x9 = some s1
  s2 : cfg.σ.regs.get? Register.x18 = some s2
  s3 : cfg.σ.regs.get? Register.x19 = some s3
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R

/-- The helper's return is route-ready with the truthiness bit as the key. -/
theorem TruthyReturn.toRouteReady {T : TruthyCopy}
    {gC : (R : Register) → Option (RegisterType R)}
    {esp s0 s1 s2 s3 : BitVec 64} {mCopy : Mem} {out : Array String} {b : Bool} {cfg : Config}
    (hR : T.TruthyReturn gC esp s0 s1 s2 s3 mCopy out b cfg) :
    RouteReady gC T.retPC (cond b (1#64) (0#64)) esp T.retPC s0 s1 s2 s3 mCopy out cfg :=
  { good := hR.good, tick := hR.tick, pc := hR.pc, a0 := hR.a0, ra := hR.ra
    minstret := hR.minstret, mem := hR.mem, out := hR.out, sp := hR.sp
    s0 := hR.s0, s1 := hR.s1, s2 := hR.s2, s3 := hR.s3, frame := hR.frame }

/-- The state at the end of a reflected route. -/
structure RouteHead (bs : List BBlock) (endPC : BitVec 64) (L : GRegs)
    (lds : List (List (BitVec 8))) (mCopy : Mem) (out : Array String)
    (gC : (R : Register) → Option (RegisterType R)) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some endPC
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = writeLog mCopy (evalBlocks bs (SegEvalState.init L lds)).log
  out : cfg.σ.sailOutput = out
  regs : GHolds cfg.σ (evalBlocks bs (SegEvalState.init L lds)).regs
  frame : ∀ R, abiButS0 R = true → cfg.σ.regs.get? R = gC R

/-- Run a memory-pure or load-only reflected route from any parked state whose
pinned registers hold `L`. -/
theorem route_of_gholds (bs : List BBlock) (endPC : BitVec 64) (L : GRegs)
    (lds : List (List (BitVec 8)))
    {gC : (R : Register) → Option (RegisterType R)}
    {pcR : BitVec 64} {mR : Mem} {out : Array String} {cfg : Config}
    (hgood : GoodState cfg.σ) (htick : cfg.tick < 2)
    (hpc : cfg.σ.regs.get? Register.PC = some pcR)
    (hmi : ∃ w, cfg.σ.regs.get? Register.minstret = some w)
    (hmem : cfg.σ.mem = mR) (hout : cfg.σ.sailOutput = out)
    (hL : GHolds cfg.σ L) (hkeys : KeysOK (keysG L))
    (hframe : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = gC R)
    (hwf : ChainOK pcR (keysG L) bs)
    (hend : evalBlocksPC pcR (SegEvalState.init L lds) bs = endPC)
    (havoid : WrChainAvoids abiButS0 bs)
    (hfacts : ChainFacts mR mR L lds bs) :
    ∃ cfg' : Config, Steps cfg cfg' ∧ RouteHead bs endPC L lds mR out gC cfg' := by
  obtain ⟨vm, hvm⟩ := hmi
  have hfactsT : ChainFacts cfg.σ.mem cfg.σ.mem L lds bs := by
    rw [hmem]; exact hfacts
  obtain ⟨σB, iB, hsB, hiB, hGB, hmemB, houtB, hpcB, hmiB, hregsB, hframeB⟩ :=
    segEval_sound bs cfg.σ cfg.tick cfg.steps pcR vm L lds hgood hpc hvm hL hkeys hfactsT hwf htick
  refine ⟨⟨σB, iB, cfg.steps + evalBlocksFuel bs⟩, hsB, ?_⟩
  exact
    { good := hGB
      tick := hiB
      pc := by rw [hpcB, hend]
      minstret := hmiB
      mem := by rw [hmemB, hmem]
      out := by rw [houtB, hout]
      regs := hregsB
      frame := fun R hR' =>
        (hframeB R (noise_avoids abiButS0_noise hR') (wrChain_avoids havoid hR')).trans
          (hframe R (by unfold abiButS0 at hR'; exact (Bool.and_eq_true _ _).mp hR' |>.1)) }

/-- Run a reflected route (branches on the key, possibly with statement-node
loads) from a route-ready state. -/
theorem route_of_ready (bs : List BBlock) (endPC : BitVec 64)
    (lds : List (List (BitVec 8)))
    {gC : (R : Register) → Option (RegisterType R)}
    {pcR a0 esp ra s0 s1 s2 s3 : BitVec 64} {mR : Mem} {out : Array String} {cfg : Config}
    (hR : RouteReady gC pcR a0 esp ra s0 s1 s2 s3 mR out cfg)
    (hwf : ChainOK pcR [10, 2, 1, 8, 9, 18, 19] bs)
    (hend : evalBlocksPC pcR (SegEvalState.init (routeL a0 esp ra s0 s1 s2 s3) lds) bs = endPC)
    (havoid : WrChainAvoids abiButS0 bs)
    (hfacts : ChainFacts mR mR (routeL a0 esp ra s0 s1 s2 s3) lds bs) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      RouteHead bs endPC (routeL a0 esp ra s0 s1 s2 s3) lds mR out gC cfg' := by
  have hL : GHolds cfg.σ (routeL a0 esp ra s0 s1 s2 s3) := by
    simp only [routeL, GHolds, gprGet]
    exact ⟨hR.a0, hR.sp, hR.ra, hR.s0, hR.s1, hR.s2, hR.s3, True.intro⟩
  exact route_of_gholds bs endPC _ lds hR.good hR.tick hR.pc hR.minstret hR.mem hR.out hL
    (by change KeysOK [10, 2, 1, 8, 9, 18, 19]; decide) hR.frame
    (by change ChainOK pcR [10, 2, 1, 8, 9, 18, 19] bs; exact hwf) hend havoid hfacts

/-- Run a reflected route (a branch on the truthiness bit, possibly with a
statement-node load) from the helper's return. -/
theorem route_of_truthyReturn (T : TruthyCopy) (bs : List BBlock) (endPC : BitVec 64)
    (lds : List (List (BitVec 8)))
    {gC : (R : Register) → Option (RegisterType R)} {b : Bool}
    {esp s0 s1 s2 s3 : BitVec 64} {mCopy : Mem} {out : Array String} {cfg : Config}
    (hR : T.TruthyReturn gC esp s0 s1 s2 s3 mCopy out b cfg)
    (hwf : ChainOK T.retPC [10, 2, 1, 8, 9, 18, 19] bs)
    (hend : evalBlocksPC T.retPC
      (SegEvalState.init (routeL (cond b (1#64) (0#64)) esp T.retPC s0 s1 s2 s3) lds) bs = endPC)
    (havoid : WrChainAvoids abiButS0 bs)
    (hfacts : ChainFacts mCopy mCopy (routeL (cond b (1#64) (0#64)) esp T.retPC s0 s1 s2 s3)
      lds bs) :
    ∃ cfg' : Config, Steps cfg cfg' ∧
      RouteHead bs endPC (routeL (cond b (1#64) (0#64)) esp T.retPC s0 s1 s2 s3) lds
        mCopy out gC cfg' :=
  route_of_ready bs endPC lds hR.toRouteReady hwf hend havoid hfacts

/-! ## A normal completion after a route -/

/-- A route that ends at the arm's `li a0,0` with the copied memory is the
parametric normal-exit head.  The exit facts are those of the child's widened
exit; the copy changed only `[esp+16, esp+40)`. -/
theorem normalExitPre_of_route (D : EvalChildArm) (CD : D.Cert) {s : Stmt} {e : Expr}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : SpecSt} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC mCopy : Mem}
    (hCarrier : D.Carrier s e g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (cfgX : Config)
    (hExitD : EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size
      st' v (sp - 176#64) D.retPC (D.sret (sp - 176#64)) mC cfgX)
    (hpf : PhiExtends φf φf' st.store.frames.size)
    (hpc : PhiExtends φc φc' st.store.closures.size)
    (hStoreSurv : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfgX.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store)
    (hKit : D.ExitKit s gC N A SL φf' φc' st' v sp aStmt aRet mC cfgX)
    (hcopyFrame : ∀ k, ¬ ((sp - 176#64).toNat + 16 ≤ k ∧ k < (sp - 176#64).toNat + 40) →
      mCopy[k]? = cfgX.σ.mem[k]?)
    (hcopyExt : MemExtends cfgX.σ.mem mCopy)
    (hcode : Exec_stmtLoaded mCopy)
    (liPC : BitVec 64) (cfgR : Config)
    (hgood : GoodState cfgR.σ) (htick : cfgR.tick < 2)
    (hpcR : cfgR.σ.regs.get? Register.PC = some liPC)
    (hmi : ∃ w, cfgR.σ.regs.get? Register.minstret = some w)
    (hmemR : cfgR.σ.mem = mCopy)
    (houtR : cfgR.σ.sailOutput = cfgX.σ.sailOutput)
    (hframeR : ∀ R, abiButS0 R = true → cfgR.σ.regs.get? R = gC R) :
    NormalExitTailPre liPC g N A SL φf φc φf' φc'
      st.store.frames.size st.store.closures.size st' sp r aRet m0 cfgR := by
  rcases hExitD with ⟨hExit, hExt, _hWords, _⟩
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom CD
  have hsretRoom := CD.sret_room
  have hCopyOutside : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → mCopy[k]? = cfgX.σ.mem[k]? := by
    intro k hk
    apply hcopyFrame k
    rw [hesp]
    intro hw
    exact hk ⟨by omega, by omega⟩
  have hSaved : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mCopy mC := by
    intro k hk
    rw [hcopyFrame k (by rw [hesp]; omega)]
    rcases hExit.memFrame k
        (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq
  have hSavedRead (off : Nat) (hlo : 8 ≤ off) (hhi : off ≤ 40) :
      read64 mCopy (sp.toNat - off) = read64 mC (sp.toNat - off) :=
    read64_agreeP hSaved (fun k hk => ⟨by omega, by omega⟩)
  refine
    { good := hgood
      tick := htick
      pc := hpcR
      minstret := hmi
      spReg := (hframeR Register.x2 (by decide)).trans hCarrier.spReg
      code := by rw [hmemR]; exact hcode
      out := by
        change String.join cfgR.σ.sailOutput.toList = st'.out
        rw [houtR]
        exact hKit.out
      frames := hpf
      closures := hpc
      storeSurvives := ?_
      saved_ra := by rw [hmemR]; exact (hSavedRead 8 (by omega) (by omega)).trans hCarrier.saved_ra
      saved_s0 := ?_
      saved_s1 := ?_
      saved_s2 := ?_
      saved_s3 := ?_
      parentSp := hCarrier.parentSp
      frame := ?_
      memExtends := by rw [hmemR]; exact (hCarrier.mem_extends.trans hExt).trans hcopyExt
      memFrame := ?_
      spRoom := h176
      spHi := Nat.le_trans hSLhi hCarrier.stack_ram.2
      spLo := Nat.le_trans hCarrier.stack_ram.1 (by omega)
      spWin := by have := hCarrier.stack_win; omega
      spAlign := by omega
      retAlign := hCarrier.ra_align }
  · rw [hmemR]
    intro m' hag
    apply hStoreSurv m'
    intro k hk
    exact (hCopyOutside k (by
      intro hs
      exact hk ⟨hs.1, Nat.lt_of_lt_of_le hs.2 hSLhi⟩)).symm.trans (hag k hk)
  · rw [hmemR]
    obtain ⟨v8, hs8, hg8⟩ := hCarrier.saved_s0
    exact ⟨v8, (hSavedRead 16 (by omega) (by omega)).trans hs8, hg8⟩
  · rw [hmemR]
    obtain ⟨v9, hs9, hg9⟩ := hCarrier.saved_s1
    exact ⟨v9, (hSavedRead 24 (by omega) (by omega)).trans hs9, hg9⟩
  · rw [hmemR]
    obtain ⟨v18, hs18, hg18⟩ := hCarrier.saved_s2
    exact ⟨v18, (hSavedRead 32 (by omega) (by omega)).trans hs18, hg18⟩
  · rw [hmemR]
    obtain ⟨v19, hs19, hg19⟩ := hCarrier.saved_s3
    exact ⟨v19, (hSavedRead 40 (by omega) (by omega)).trans hs19, hg19⟩
  · intro R hR he8 he9 he18 he19 he2
    have hg : gC R = g R := by
      rcases hCarrier.frame R hR with hspecial | heq
      · rcases hspecial with rfl | rfl | rfl | rfl | rfl
        · simp at he8
        · simp at he9
        · simp at he18
        · simp at he19
        · simp at he2
      · exact heq
    have hP : abiButS0 R = true := by
      unfold abiButS0; rw [hR.1, he8]; rfl
    exact (hframeR R hP).trans hg
  · intro k hstk hA
    apply Or.inr
    rw [hmemR, hCopyOutside k hstk]
    rcases hExit.memFrame k
        (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA with hr | heq
    · exfalso
      rw [hsret] at hr
      exact hstk ⟨by omega, by omega⟩
    · exact heq.trans (hCarrier.mem_frame k hstk)

#print axioms TruthyCopy.copyReady_of_exitKit
#print axioms TruthyCopy.truthyReturn_of_copyReady
#print axioms TruthyCopy.route_of_truthyReturn
#print axioms TruthyCopy.normalExitPre_of_route

end TruthyCopy
end Vsa.Sim
