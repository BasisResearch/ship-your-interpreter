import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.ExecBrkCont
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.ReprCopy
import Vsa.Sim.PinW
import Vsa.Sim.SegReadback
import Vsa.Sim.SegEffect
import Vsa.Sim.rows.StmtWhileBodyArmStagePre

/-!
# Exact `exec_stmt` while status routes

These rows cover only the finite instructions after the recursive body returns:

* `.brk`: `0x80004088 -> 0x80004090`;
* `.ret`: `0x80004088 -> 0x80004150`;
* `.normal`/`.cont`: `0x80004088 -> 0x80004034`.

They preserve memory and output and expose all live while-frame ABI registers.
They do not claim the missing marshalling from `ExecExitD` into `SegPreO`, nor
the epilogues beginning at `0x80004090` and `0x80004150`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Reload the condition result, copy its three words to `sp+16`, and park at
the `jal value_truthy` seam. -/
#derive_case execWhileCondCopySeg chain
  [(0x80004050#64, 0x05013683#32),
   (0x80004054#64, 0x05813703#32),
   (0x80004058#64, 0x06013783#32),
   (0x8000405c#64, 0x01010513#32),
   (0x80004060#64, 0x00d13823#32),
   (0x80004064#64, 0x00e13c23#32),
   (0x80004068#64, 0x02f13023#32)]

def execWhileCondCopyL (sp s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(2, sp), (8, s0), (9, s1), (18, s2), (19, s3)]

/-- One total 64-bit machine read, written as the eight positional bytes used
by the reflected evaluator. -/
def execWhileWordLds (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0,
   (m[a + 3]?).getD 0, (m[a + 4]?).getD 0, (m[a + 5]?).getD 0,
   (m[a + 6]?).getD 0, (m[a + 7]?).getD 0]

/-- The three total machine reads made by the condition-result copy. -/
def execWhileCondCopyLds (m : Mem) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [execWhileWordLds m (sp.toNat + 80),
   execWhileWordLds m (sp.toNat + 88),
   execWhileWordLds m (sp.toNat + 96)]

/-- Memory facts for the seven-instruction condition-result copy, derived from
the lowered loop frame rather than assumed per instruction. -/
theorem execWhileCondCopy_facts_of_stack
    (m : Mem) (SL : StackLayout)
    (esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Vsa.Sim.Code.Exec_stmtLoaded m)
    (hlo : SL.lo ≤ esp.toNat)
    (hhi : esp.toNat + 104 ≤ SL.hi)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo)
    (halign : esp.toNat % 16 = 0) :
    ChainFacts m m (execWhileCondCopyL esp s0 s1 s2 s3)
      (execWhileCondCopyLds m esp) execWhileCondCopySeg := by
  have hhi32 : esp.toNat + 104 ≤ 0x100000000 :=
    Nat.le_trans hhi hram.2
  have hesp32 : esp.toNat < 0x100000000 := by omega
  have htohost : tohostAddr + 16 ≤ esp.toNat :=
    Nat.le_trans hwin hlo
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 104)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha16 := haddr 0x010#12 16 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have ha24 := haddr 0x018#12 24 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have ha32 := haddr 0x020#12 32 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have ha80 := haddr 0x050#12 80 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have ha88 := haddr 0x058#12 88 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have ha96 := haddr 0x060#12 96 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  unfold execWhileCondCopySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · -- ld a3,80(sp)
    change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x050#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x050#12)).toNat) ∧
      (esp + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x050#12)).toNat
        (execWhileWordLds m (esp.toNat + 80)))
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ha80]; omega
    · rw [ha80]; omega
    · right; rw [ha80]; omega
    · rw [ha80]; omega
    · rw [ha80]
      simp only [execWhileCondCopyLds, execWhileWordLds, LPins8,
        List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
      repeat' apply And.intro <;> trivial
  · -- ld a4,88(sp)
    change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x058#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x058#12)).toNat) ∧
      (esp + sign_extend (m := 64) (0x058#12)).toNat % 8 = 0) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x058#12)).toNat
        (execWhileWordLds m (esp.toNat + 88)))
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ha88]; omega
    · rw [ha88]; omega
    · right; rw [ha88]; omega
    · rw [ha88]; omega
    · rw [ha88]
      simp only [execWhileCondCopyLds, execWhileWordLds, LPins8,
        List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
      repeat' apply And.intro <;> trivial
  · -- ld a5,96(sp)
    change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x060#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x060#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x060#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x060#12)).toNat) ∧
      (esp + sign_extend (m := 64) (0x060#12)).toNat % 8 = 0) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x060#12)).toNat
        (execWhileWordLds m (esp.toNat + 96)))
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ha96]; omega
    · rw [ha96]; omega
    · right; rw [ha96]; omega
    · rw [ha96]; omega
    · rw [ha96]
      simp only [execWhileCondCopyLds, execWhileWordLds, LPins8,
        List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
      repeat' apply And.intro <;> trivial
  · -- sd a3,16(sp)
    change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha16]; omega
    · rw [ha16]; omega
    · rw [ha16]; omega
    · rw [ha16]; omega
  · -- sd a4,24(sp)
    change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha24]; omega
    · rw [ha24]; omega
    · rw [ha24]; omega
    · rw [ha24]; omega
  · -- sd a5,32(sp)
    change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha32]; omega
    · rw [ha32]; omega
    · rw [ha32]; omega
    · rw [ha32]; omega

/-- The reflected copy prefix computes exactly three adjacent `sd` writes.
This is an evaluator identity, before any semantic representation argument. -/
theorem execWhileCondCopy_writeLog_eq (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) :
    writeLog m (evalBlocks execWhileCondCopySeg
      (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3)
        (execWhileCondCopyLds m sp))).log =
      writeMap8 (writeMap8 (writeMap8 m
        (sp + sign_extend (m := 64) (0x010#12)).toNat
        (sdData_val (bytesVal MKind.ld (execWhileWordLds m (sp.toNat + 80)))))
        (sp + sign_extend (m := 64) (0x018#12)).toNat
        (sdData_val (bytesVal MKind.ld (execWhileWordLds m (sp.toNat + 88)))))
        (sp + sign_extend (m := 64) (0x020#12)).toNat
        (sdData_val (bytesVal MKind.ld
          (execWhileWordLds m (sp.toNat + 96)))) := by
  rfl

private theorem execWhile_sdData_sext_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
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

/-- The computed write log is a total 24-byte copy from `sp+80` to `sp+16`.
This states the actual Sail load convention (`getD 0`), not byte-presence. -/
theorem execWhileCondCopy_writeLog_total (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64)
    (hsp : sp.toNat + 104 ≤ 0x100000000) :
    ∀ j, j < 24 →
      (writeLog m (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3)
          (execWhileCondCopyLds m sp))).log)[sp.toNat + 16 + j]? =
        some ((m[sp.toNat + 80 + j]?).getD 0) := by
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 32)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (sp + sign_extend (m := 64) off).toNat = sp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hsplt := sp.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hn16 := haddr 0x010#12 16 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have hn24 := haddr 0x018#12 24 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have hn32 := haddr 0x020#12 32 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  let k0 := (m[sp.toNat + 80]?).getD 0
  let k1 := (m[sp.toNat + 80 + 1]?).getD 0
  let k2 := (m[sp.toNat + 80 + 2]?).getD 0
  let k3 := (m[sp.toNat + 80 + 3]?).getD 0
  let k4 := (m[sp.toNat + 80 + 4]?).getD 0
  let k5 := (m[sp.toNat + 80 + 5]?).getD 0
  let k6 := (m[sp.toNat + 80 + 6]?).getD 0
  let k7 := (m[sp.toNat + 80 + 7]?).getD 0
  let p0 := (m[sp.toNat + 88]?).getD 0
  let p1 := (m[sp.toNat + 88 + 1]?).getD 0
  let p2 := (m[sp.toNat + 88 + 2]?).getD 0
  let p3 := (m[sp.toNat + 88 + 3]?).getD 0
  let p4 := (m[sp.toNat + 88 + 4]?).getD 0
  let p5 := (m[sp.toNat + 88 + 5]?).getD 0
  let p6 := (m[sp.toNat + 88 + 6]?).getD 0
  let p7 := (m[sp.toNat + 88 + 7]?).getD 0
  let q0 := (m[sp.toNat + 96]?).getD 0
  let q1 := (m[sp.toNat + 96 + 1]?).getD 0
  let q2 := (m[sp.toNat + 96 + 2]?).getD 0
  let q3 := (m[sp.toNat + 96 + 3]?).getD 0
  let q4 := (m[sp.toNat + 96 + 4]?).getD 0
  let q5 := (m[sp.toNat + 96 + 5]?).getD 0
  let q6 := (m[sp.toNat + 96 + 6]?).getD 0
  let q7 := (m[sp.toNat + 96 + 7]?).getD 0
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ :=
    execWhile_sdData_sext_bytes k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ :=
    execWhile_sdData_sext_bytes p0 p1 p2 p3 p4 p5 p6 p7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ :=
    execWhile_sdData_sext_bytes q0 q1 q2 q3 q4 q5 q6 q7
  intro j hj
  rw [execWhileCondCopy_writeLog_eq, hn16, hn24, hn32]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
      j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨
      j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [execWhileWordLds, bytesVal, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_0, eK0]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_1, eK1]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_2, eK2]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_3, eK3]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_4, eK4]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_5, eK5]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_6, eK6]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_disjoint _ (sp.toNat + 24) _ _ (by omega),
      getElem_writeMap8_7, eK7]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_0, eP0]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_1, eP1]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_2, eP2]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_3, eP3]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_4, eP4]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_5, eP5]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_6, eP6]
  · rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) _ _ (by omega),
      getElem_writeMap8_7, eP7]
  · rw [getElem_writeMap8_0, eQ0]
  · rw [getElem_writeMap8_1, eQ1]
  · rw [getElem_writeMap8_2, eQ2]
  · rw [getElem_writeMap8_3, eQ3]
  · rw [getElem_writeMap8_4, eQ4]
  · rw [getElem_writeMap8_5, eQ5]
  · rw [getElem_writeMap8_6, eQ6]
  · rw [getElem_writeMap8_7, eQ7]

/-- The copy prefix transports precisely the truthiness header.  It makes no
claim that an indirect CString/closure payload survives the stack writes. -/
theorem execWhileCondCopy_truthyHeader (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) (v : Vsa.While.Value)
    (hsp : sp.toNat + 104 ≤ 0x100000000)
    (hv : TruthyHeaderRepr m (sp.toNat + 80) v) :
    TruthyHeaderRepr
      (writeLog m (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3)
          (execWhileCondCopyLds m sp))).log)
      (sp.toNat + 16) v :=
  truthyHeaderRepr_copy_total
    (execWhileCondCopy_writeLog_total m sp s0 s1 s2 s3 hsp) hv

/-- The concrete condition-copy log changes only its 24-byte destination. -/
theorem execWhileCondCopy_writeLog_frame (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64)
    (hsp : sp.toNat + 104 ≤ 0x100000000) :
    ∀ k, ¬ (sp.toNat + 16 ≤ k ∧ k < sp.toNat + 40) →
      (writeLog m (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3)
          (execWhileCondCopyLds m sp))).log)[k]? = m[k]? := by
  intro k hk
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 32)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (sp + sign_extend (m := 64) off).toNat = sp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hsplt := sp.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hn16 := haddr 0x010#12 16 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have hn24 := haddr 0x018#12 24 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  have hn32 := haddr 0x020#12 32 (by omega)
    (by apply BitVec.eq_of_toNat_eq; decide)
  rw [execWhileCondCopy_writeLog_eq, hn16, hn24, hn32]
  rw [getElem_writeMap8_disjoint _ (sp.toNat + 32) k _ (by omega),
    getElem_writeMap8_disjoint _ (sp.toNat + 24) k _ (by omega),
    getElem_writeMap8_disjoint _ (sp.toNat + 16) k _ (by omega)]

/- Exact `jal value_truthy` site at `0x8000406c`. -/
theorem site_8000406c_whileO (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x8000406c#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Exec_stmtLoaded σ.mem) (hi : i < 2) :
    JalStepO 0x8000282c#64 0x80004070#64 σ i u := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_8000406c hmem
  obtain ⟨σ', i', hs, hi', hG', hm', hobs⟩ :=
    stepObs_jal σ i u 0x8000406c#64 vminstret 0xfc0fe0ef#32 0x1fe7c0#21
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt 0x8000406c#64 4)
      0xef#8 0xe0#8 0x0f#8 0xfc#8 hG hpc hminstret hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide) (by
        apply BitVec.eq_of_toNat_eq
        decide) (by
        apply BitVec.eq_of_toNat_eq
        decide)
      (Vsa.Sim.DecodeTable.decode_fc0fe0ef (afterPrelude σ)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by exact wX_bits_x1 _ (BitVec.addInt 0x8000406c#64 4)) hi
  exact jalStepO_of_obs hs hi' hG' hm' hobs (by
    apply BitVec.eq_of_toNat_eq
    decide)

#print axioms site_8000406c_whileO

/- Exact finite prefix through the `jal value_truthy`.  The sole remaining
instruction-local input is the absent `0x8000406c` jal site. -/
theorem execWhileCondCopyCallBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem)
    (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80004050#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (execWhileCondCopyL sp s0 s1 s2 s3))
    (hfacts : ChainFacts σ.mem σ.mem
      (execWhileCondCopyL sp s0 s1 s2 s3) lds execWhileCondCopySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks execWhileCondCopySeg
      (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks execWhileCondCopySeg
      (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3) lds)).regs)
    (hcodeAfter : Exec_stmtLoaded (writeLog m0
      (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3) lds)).log)) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩
        ⟨σ', i', u + evalBlocksFuel execWhileCondCopySeg + 1⟩ ∧
      i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some 0x8000282c#64 ∧
      σ'.regs.get? Register.x1 = some 0x80004070#64 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3) lds)).regs ∧
      σ'.mem = writeLog m0 (evalBlocks execWhileCondCopySeg
        (SegEvalState.init (execWhileCondCopyL sp s0 s1 s2 s3) lds)).log ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true →
        σ'.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSegOut execWhileCondCopySeg
    (execWhileCondCopyL sp s0 s1 s2 s3) lds σ i u 0x80004050#64
    0x8000282c#64 0x80004070#64 vminstret m0 hG hpc hminstret hmem hL
    (by
      have hk : keysG (execWhileCondCopyL sp s0 s1 s2 s3) =
          [2, 8, 9, 18, 19] := rfl
      rw [hk]
      decide)
    hfacts hi
    (by
      have hk : keysG (execWhileCondCopyL sp s0 s1 s2 s3) =
          [2, 8, 9, 18, 19] := rfl
      rw [hk]
      show ChainOK 0x80004050#64 [2, 8, 9, 18, 19]
        execWhileCondCopySeg
      decide)
    (by show WrChainAvoidAbi execWhileCondCopySeg; decide)
    hKeysOut hRaOut
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _
  obtain ⟨vm, hvm⟩ := hmi'
  have hpc406c : σ'.regs.get? Register.PC = some 0x8000406c#64 := by
    rw [hpc']
    rfl
  exact site_8000406c_whileO σ' i' u' vm hG' hpc406c hvm
    (hmem' ▸ hcodeAfter) hi'

#print axioms execWhileCondCopyCallBridge

/- Exact `jal exec_stmt` site at `0x80004084`. -/
theorem site_80004084_whileO (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80004084#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Exec_stmtLoaded σ.mem) (hi : i < 2) :
    JalStepO 0x80003fe0#64 0x80004088#64 σ i u := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.exec_stmt_at_80004084 hmem
  obtain ⟨σ', i', hs, hi', hG', hm', hobs⟩ :=
    stepObs_jal σ i u 0x80004084#64 vminstret 0xf5dff0ef#32 0x1fff5c#21
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt 0x80004084#64 4)
      0xef#8 0xf0#8 0xdf#8 0xf5#8 hG hpc hminstret hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide) (by
        apply BitVec.eq_of_toNat_eq
        decide) (by
        apply BitVec.eq_of_toNat_eq
        decide)
      (Vsa.Sim.DecodeTable.decode_f5dff0ef (afterPrelude σ)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by exact wX_bits_x1 _ (BitVec.addInt 0x80004084#64 4)) hi
  exact jalStepO_of_obs hs hi' hG' hm' hobs (by
    apply BitVec.eq_of_toNat_eq
    decide)

/-- The body-pointer load at `0x80004074`. -/
def execWhileBodyLds (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [execWhileWordLds m (aStmt.toNat + 16)]

/-- Exact output-preserving body-head marshalling through the recursive call
site.  This is only the finite machine cut; `ExecEntry` is supplied separately. -/
theorem execWhileBodyCallBridge
    (σ : MState) (i u : Nat) (vminstret : BitVec 64)
    (sp s0 s2 s3 s1 : BitVec 64) (m0 : Mem)
    (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80004074#64)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (stmtWhileBodyL sp s0 s2 s3 s1))
    (hfacts : ChainFacts σ.mem σ.mem
      (stmtWhileBodyL sp s0 s2 s3 s1) lds stmtWhileBodySeg)
    (hi : i < 2)
    (hKeysOut : KeysOK (keysG (evalBlocks stmtWhileBodySeg
      (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks stmtWhileBodySeg
      (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) lds)).regs)
    (hcodeAfter : Exec_stmtLoaded (writeLog m0
      (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) lds)).log)) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩
        ⟨σ', i', u + evalBlocksFuel stmtWhileBodySeg + 1⟩ ∧
      i' < 2 ∧ GoodState σ' ∧
      σ'.regs.get? Register.PC = some 0x80003fe0#64 ∧
      σ'.regs.get? Register.x1 = some 0x80004088#64 ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) lds)).regs ∧
      σ'.mem = writeLog m0 (evalBlocks stmtWhileBodySeg
        (SegEvalState.init (stmtWhileBodyL sp s0 s2 s3 s1) lds)).log ∧
      σ'.sailOutput = σ.sailOutput ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true →
        σ'.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSegOut stmtWhileBodySeg
    (stmtWhileBodyL sp s0 s2 s3 s1) lds σ i u 0x80004074#64
    0x80003fe0#64 0x80004088#64 vminstret m0 hG hpc hminstret hmem hL
    (by
      have hk : keysG (stmtWhileBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
      rw [hk]
      decide)
    hfacts hi
    (by
      have hk : keysG (stmtWhileBodyL sp s0 s2 s3 s1) = [2, 8, 18, 19, 9] := rfl
      rw [hk]
      show ChainOK 0x80004074#64 [2, 8, 18, 19, 9] stmtWhileBodySeg
      decide)
    (by show WrChainAvoidAbi stmtWhileBodySeg; decide)
    hKeysOut hRaOut
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _
  obtain ⟨vm, hvm⟩ := hmi'
  have hpc4084 : σ'.regs.get? Register.PC = some 0x80004084#64 := by
    rw [hpc']
    rfl
  exact site_80004084_whileO σ' i' u' vm hG' hpc4084 hvm
    (hmem' ▸ hcodeAfter) hi'

#print axioms execWhileBodyCallBridge

/- The body status plus the five live while-frame registers. -/
def execWhileRouteL (status sp ra s0 s1 s2 s3 : BitVec 64) : GRegs :=
  [(10, status), (2, sp), (1, ra), (8, s0), (9, s1), (18, s2), (19, s3)]

/- Body status is `.brk` (`a0 = 1`), so the `bne` falls through. -/
#derive_case execWhileBreakRouteSeg chain
  [(0x80004088#64, 0x00100793#32)]
    terminator ⟨0x8000408c#64, 0xfaf514e3#32, 0xe3#8, 0x14#8, 0xf5#8, 0xfa#8,
      .br bop.BNE false, 10, 15, 0x1fa8#13, 0#21, 0#12⟩

/- Body status is `.ret` (`a0 = 3`): take the first branch to the status check,
then take the ret branch. -/
#derive_case execWhileRetRouteSeg chain
  [(0x80004088#64, 0x00100793#32)]
    terminator ⟨0x8000408c#64, 0xfaf514e3#32, 0xe3#8, 0x14#8, 0xf5#8, 0xfa#8,
      .br bop.BNE true, 10, 15, 0x1fa8#13, 0#21, 0#12⟩ ;;
  [(0x80004034#64, 0x00300793#32)]
    terminator ⟨0x80004038#64, 0x10f50c63#32, 0x63#8, 0x0c#8, 0xf5#8, 0x10#8,
      .br bop.BEQ true, 10, 15, 0x0118#13, 0#21, 0#12⟩

/- Body status is `.normal` or `.cont` (`a0 = 0` or `2`): take the first
branch and stop at the indexed recursive boundary before the ret check. -/
#derive_case execWhileLoopRouteSeg chain
  [(0x80004088#64, 0x00100793#32)]
    terminator ⟨0x8000408c#64, 0xfaf514e3#32, 0xe3#8, 0x14#8, 0xf5#8, 0xfa#8,
      .br bop.BNE true, 10, 15, 0x1fa8#13, 0#21, 0#12⟩

theorem execWhileBreakRoute_facts (m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (execWhileRouteL 1#64 sp ra s0 s1 s2 s3) []
      execWhileBreakRouteSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  all_goals
    seg_guard_close [execWhileRouteL,
      show (mkLine 0x80004088#64 0x00100793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rd = 15 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rs1 = 0 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).imm = 0x001#12 from rfl]

theorem execWhileRetRoute_facts (m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (execWhileRouteL 3#64 sp ra s0 s1 s2 s3) []
      execWhileRetRouteSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  all_goals
    seg_guard_close [execWhileRouteL,
      show (mkLine 0x80004088#64 0x00100793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rd = 15 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rs1 = 0 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).imm = 0x001#12 from rfl,
      show (mkLine 0x80004034#64 0x00300793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004034#64 0x00300793#32).rd = 15 from rfl,
      show (mkLine 0x80004034#64 0x00300793#32).rs1 = 0 from rfl,
      show (mkLine 0x80004034#64 0x00300793#32).imm = 0x003#12 from rfl]

theorem execWhileLoopNormalRoute_facts (m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (execWhileRouteL 0#64 sp ra s0 s1 s2 s3) []
      execWhileLoopRouteSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  all_goals
    seg_guard_close [execWhileRouteL,
      show (mkLine 0x80004088#64 0x00100793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rd = 15 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rs1 = 0 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).imm = 0x001#12 from rfl]

theorem execWhileLoopContRoute_facts (m : Mem)
    (sp ra s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (execWhileRouteL 2#64 sp ra s0 s1 s2 s3) []
      execWhileLoopRouteSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  all_goals
    seg_guard_close [execWhileRouteL,
      show (mkLine 0x80004088#64 0x00100793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rd = 15 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).rs1 = 0 from rfl,
      show (mkLine 0x80004088#64 0x00100793#32).imm = 0x001#12 from rfl]

/- The truthy result (`a0 = 1`) makes `beqz` fall through to the body head. -/
#derive_case execWhileTruthyBranchSeg chain
  []
    terminator ⟨0x80004070#64, 0x02050063#32, 0x63#8, 0x00#8, 0x05#8, 0x02#8,
      .br bop.BEQ false, 10, 0, 0x0020#13, 0#21, 0#12⟩

def ExecWhileRoutePost (bs : List BBlock) (endPC : BitVec 64)
    (status sp ra s0 s1 s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0
    (evalBlocks bs (SegEvalState.init
      (execWhileRouteL status sp ra s0 s1 s2 s3) lds)).log ∧
  c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some endPC ∧
  GHolds c.σ (evalBlocks bs (SegEvalState.init
    (execWhileRouteL status sp ra s0 s1 s2 s3) lds)).regs

/-- Status-route precondition with the caller's ABI frame retained. -/
def ExecWhileRoutePreF (bs : List BBlock)
    (g : (R : Register) → Option (RegisterType R))
    (status sp ra s0 s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (m0 : Mem) (out0 : Array String) (c : Config) : Prop :=
  SegPreO bs (execWhileRouteL status sp ra s0 s1 s2 s3) lds
    pc0 m0 out0 c ∧
  ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R

/-- Exact core effect of the finite while status routes. -/
def execWhileRouteEffect : FrameEffect where
  regs := fun R => AbiPreserved R = true
  mem := fun _ => True
  output := True

/-- Generic framed reflected route.  Concrete break, return, and loop paths
instantiate only `ChainOK`, their end PC, and ABI write avoidance. -/
theorem execWhileRouteFramed
    (bs : List BBlock) (endPC : BitVec 64)
    (g : (R : Register) → Option (RegisterType R))
    (status sp ra s0 s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (m0 : Mem) (out0 : Array String)
    (hwf : ChainOK pc0
      (keysG (execWhileRouteL status sp ra s0 s1 s2 s3)) bs)
    (hend : evalBlocksPC pc0
      (SegEvalState.init (execWhileRouteL status sp ra s0 s1 s2 s3) lds)
      bs = endPC)
    (havoid : WrChainAvoidAbi bs)
    (hwrite : writeLog m0 (evalBlocks bs (SegEvalState.init
      (execWhileRouteL status sp ra s0 s1 s2 s3) lds)).log = m0) :
    FramedTriple execWhileRouteEffect
      (ExecWhileRoutePreF bs g status sp ra s0 s1 s2 s3 lds pc0 m0 out0)
      (fun c =>
        ExecWhileRoutePost bs endPC status sp ra s0 s1 s2 s3 lds m0 out0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧ ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  refine ⟨?_⟩
  intro c hpre
  rcases hpre with ⟨⟨⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys,
    hfacts, htick⟩, hout⟩, hframe⟩
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', hmi', hregs,
      hsegFrame⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm
      (execWhileRouteL status sp ra s0 s1 s2 s3) lds
      hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  rw [hout] at hout'
  have hpcEnd : σ'.regs.get? Register.PC = some endPC := by
    rw [hpc', hend]
  let c' : Config := ⟨σ', i', c.steps + evalBlocksFuel bs⟩
  have hmemFrame : c'.σ.mem = c.σ.mem := by
    exact hmem'.trans (hwrite.trans hmem.symm)
  have houtFrame : c'.σ.sailOutput = c.σ.sailOutput := by
    exact hout'.trans hout.symm
  refine ⟨c', ?_, ?_⟩
  · refine ⟨⟨hG', hmem', hout', hpcEnd, hregs⟩, ?_, hi', hmi'⟩
    intro R hR
    exact (abiFrame_of_wrChain havoid hsegFrame R hR).trans (hframe R hR)
  · refine ⟨hs, ?_⟩
    exact
      { regs := ⟨fun R hR => abiFrame_of_wrChain havoid hsegFrame R hR⟩
        mem := fun a _ => congrArg (fun m : Mem => m[a]?) hmemFrame
        output := fun _ => houtFrame }

/-- The truthy branch contains no store.  Its reflected write log is empty. -/
theorem execWhileTruthyBranch_writeLog_eq (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) :
    writeLog m (evalBlocks execWhileTruthyBranchSeg
      (SegEvalState.init
        (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) [])).log = m := by
  rfl

theorem execWhileTruthyBranch_facts (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) []
      execWhileTruthyBranchSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · show guardB bop.BEQ
      (srcVal 10 (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3))
      (srcVal 0 (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3)) = false
    simp [execWhileRouteL, srcVal, lookupG, guardB]

theorem execWhileTruthyBranchRow
    (status sp ra s0 s1 s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple
      (SegPreO execWhileTruthyBranchSeg
        (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004070#64 m0 out0)
      (ExecWhileRoutePost execWhileTruthyBranchSeg 0x80004074#64
        status sp ra s0 s1 s2 s3 lds m0 out0) := by
  apply segToTripleOut execWhileTruthyBranchSeg
    (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004070#64 m0 out0 _
    (by
      have h : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
          [10, 2, 1, 8, 9, 18, 19] := rfl
      rw [h]
      show ChainOK 0x80004070#64 [10, 2, 1, 8, 9, 18, 19]
        execWhileTruthyBranchSeg
      decide)
  intro σ' i' u' hG' _ hmem' hout' hpc' _ hregs
  refine ⟨hG', hmem', hout', ?_, hregs⟩
  rw [hpc']
  rfl

/- A helper-call boundary whose semantic `ValueRepr` is retained.  In
particular, the bool case supplies the canonical `{0,1}` payload through
`ValueRepr`; this interface has no raw truthiness-payload premise. -/
def ExecWhileTruthyHeaderPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String)
    (c : Config) : Prop :=
  truthy_header_pre g buf 0x80004070#64 N φc v m0 out0 c ∧
  Exec_stmtLoaded m0 ∧ v.truthy = true ∧
  g Register.x2 = some sp ∧ g Register.x8 = some s0 ∧
  g Register.x9 = some s1 ∧ g Register.x18 = some s2 ∧
  g Register.x19 = some s3

/- The verified helper summary followed by the decoded truthy branch. -/
theorem execWhileTruthyHeaderToBodyHead
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (ExecWhileTruthyHeaderPre g N φc v buf sp s0 s1 s2 s3 m0 out0)
      (ExecWhileRoutePost execWhileTruthyBranchSeg 0x80004074#64
        1#64 sp 0x80004070#64 s0 s1 s2 s3 [] m0 out0) := by
  intro c hpre
  obtain ⟨htruthy, hcode, hv, hgsp, hgs0, hgs1, hgs2, hgs3⟩ := hpre
  obtain ⟨cT, hsT, hG, hpc, ha0, hra, hmi, htick, hmem, hout, hframe⟩ :=
    value_truthy_header_spec g buf 0x80004070#64 N φc v m0 out0 c htruthy
  have hpc' : cT.σ.regs.get? Register.PC = some 0x80004070#64 := by
    rw [hpc]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    decide
  have ha0' : cT.σ.regs.get? Register.x10 = some 1#64 := by
    simpa [hv] using ha0
  have hsp' : cT.σ.regs.get? Register.x2 = some sp := by
    rw [hframe Register.x2 (by decide), hgsp]
  have hs0' : cT.σ.regs.get? Register.x8 = some s0 := by
    rw [hframe Register.x8 (by decide), hgs0]
  have hs1' : cT.σ.regs.get? Register.x9 = some s1 := by
    rw [hframe Register.x9 (by decide), hgs1]
  have hs2' : cT.σ.regs.get? Register.x18 = some s2 := by
    rw [hframe Register.x18 (by decide), hgs2]
  have hs3' : cT.σ.regs.get? Register.x19 = some s3 := by
    rw [hframe Register.x19 (by decide), hgs3]
  have hL : GHolds cT.σ
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) := by
    simp only [execWhileRouteL, GHolds, gprGet]
    exact ⟨ha0', hsp', hra, hs0', hs1', hs2', hs3', True.intro⟩
  have hseg : SegPreO execWhileTruthyBranchSeg
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) []
      0x80004070#64 m0 out0 cT := by
    refine ⟨⟨hG, hmem, hpc', hmi, hL, ?_, ?_, htick⟩, hout⟩
    · have hk : keysG
          (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) =
          [10, 2, 1, 8, 9, 18, 19] := rfl
      rw [hk]
      decide
    · rw [hmem]
      exact execWhileTruthyBranch_facts m0 sp s0 s1 s2 s3 hcode
  obtain ⟨cB, hsB, hpost⟩ := execWhileTruthyBranchRow
    1#64 sp 0x80004070#64 s0 s1 s2 s3 [] m0 out0 cT hseg
  exact ⟨cB, hsT.trans hsB, hpost⟩

private theorem notWrittenT_of_abiPreserved (R : Register)
    (hR : Vsa.Alloc.AbiPreserved R = true) : NotWrittenT R := by
  cases R <;> simp_all [Vsa.Alloc.AbiPreserved, NotWrittenT]

/-- Framed form of the truthy helper and branch.  This retains the
callee-preserved registers needed by the enclosing while frame. -/
theorem execWhileTruthyHeaderToBodyHead_framed
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (ExecWhileTruthyHeaderPre g N φc v buf sp s0 s1 s2 s3 m0 out0)
      (fun c => ExecWhileRoutePost execWhileTruthyBranchSeg 0x80004074#64
          1#64 sp 0x80004070#64 s0 s1 s2 s3 [] m0 out0 c ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧
        ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  intro c hpre
  obtain ⟨htruthy, hcode, hv, hgsp, hgs0, hgs1, hgs2, hgs3⟩ := hpre
  obtain ⟨cT, hsT, hG, hpc, ha0, hra, hmi, htick, hmem, hout, hframe⟩ :=
    value_truthy_header_spec g buf 0x80004070#64 N φc v m0 out0 c htruthy
  have hpc' : cT.σ.regs.get? Register.PC = some 0x80004070#64 := by
    rw [hpc]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    decide
  have ha0' : cT.σ.regs.get? Register.x10 = some 1#64 := by
    simpa [hv] using ha0
  have hsp' : cT.σ.regs.get? Register.x2 = some sp := by
    rw [hframe Register.x2 (notWrittenT_of_abiPreserved _ (by decide)), hgsp]
  have hs0' : cT.σ.regs.get? Register.x8 = some s0 := by
    rw [hframe Register.x8 (notWrittenT_of_abiPreserved _ (by decide)), hgs0]
  have hs1' : cT.σ.regs.get? Register.x9 = some s1 := by
    rw [hframe Register.x9 (notWrittenT_of_abiPreserved _ (by decide)), hgs1]
  have hs2' : cT.σ.regs.get? Register.x18 = some s2 := by
    rw [hframe Register.x18 (notWrittenT_of_abiPreserved _ (by decide)), hgs2]
  have hs3' : cT.σ.regs.get? Register.x19 = some s3 := by
    rw [hframe Register.x19 (notWrittenT_of_abiPreserved _ (by decide)), hgs3]
  have hL : GHolds cT.σ
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) := by
    simp only [execWhileRouteL, GHolds, gprGet]
    exact ⟨ha0', hsp', hra, hs0', hs1', hs2', hs3', True.intro⟩
  have hfacts := execWhileTruthyBranch_facts m0 sp s0 s1 s2 s3 hcode
  have hfactsT : ChainFacts cT.σ.mem cT.σ.mem
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) []
      execWhileTruthyBranchSeg := by
    simpa only [hmem] using hfacts
  obtain ⟨σB, iB, hsB, hiB, hGB, hmemB, houtB, hpcB, hmiB,
      hregsB, hframeB⟩ :=
    segEval_sound execWhileTruthyBranchSeg cT.σ cT.tick cT.steps
      0x80004070#64 (Classical.choose hmi)
      (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) []
      hG hpc' (Classical.choose_spec hmi) hL
      (by
        have hk : keysG
            (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) =
            [10, 2, 1, 8, 9, 18, 19] := rfl
        rw [hk]
        decide)
      hfactsT
      (by
        have hk : keysG
            (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) =
            [10, 2, 1, 8, 9, 18, 19] := rfl
        rw [hk]
        show ChainOK 0x80004070#64 [10, 2, 1, 8, 9, 18, 19]
          execWhileTruthyBranchSeg
        decide)
      htick
  have hmemB' : σB.mem = writeLog m0
      (evalBlocks execWhileTruthyBranchSeg
        (SegEvalState.init
          (execWhileRouteL 1#64 sp 0x80004070#64 s0 s1 s2 s3) [])).log := by
    rw [hmem] at hmemB
    exact hmemB
  have houtB' : σB.sailOutput = out0 := by rw [houtB, hout]
  refine ⟨⟨σB, iB, cT.steps + evalBlocksFuel execWhileTruthyBranchSeg⟩,
    hsT.trans hsB, ?_, ?_, hiB, hmiB⟩
  · exact ⟨hGB, hmemB', houtB', by rw [hpcB]; rfl, hregsB⟩
  · intro R hR
    exact (abiFrame_of_wrChain (by
      show WrChainAvoidAbi execWhileTruthyBranchSeg
      decide) hframeB R hR).trans
        (hframe R (notWrittenT_of_abiPreserved R hR))

/-- Compatibility interface for callers that still own the full value
representation.  The finite helper proof itself consumes only the header. -/
def ExecWhileTruthyPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String)
    (c : Config) : Prop :=
  truthy_pre g buf 0x80004070#64 N φc v m0 out0 c ∧
  Exec_stmtLoaded m0 ∧ v.truthy = true ∧
  g Register.x2 = some sp ∧ g Register.x8 = some s0 ∧
  g Register.x9 = some s1 ∧ g Register.x18 = some s2 ∧
  g Register.x19 = some s3

theorem execWhileTruthyToBodyHead
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (ExecWhileTruthyPre g N φc v buf sp s0 s1 s2 s3 m0 out0)
      (ExecWhileRoutePost execWhileTruthyBranchSeg 0x80004074#64
        1#64 sp 0x80004070#64 s0 s1 s2 s3 [] m0 out0) := by
  intro c hpre
  rcases hpre with ⟨htruthy, hcode, hv, hgsp, hgs0, hgs1, hgs2, hgs3⟩
  have hheader : truthy_header_pre g buf 0x80004070#64 N φc v m0 out0 c := by
    rcases htruthy with ⟨hG, hloaded, hmem, hpc, ha0, hra, hmi, htick,
      hrepr, hreg, halign, hout, hframe⟩
    exact ⟨hG, hloaded, hmem, hpc, ha0, hra, hmi, htick,
      truthyHeaderRepr_of_valueRepr hrepr, hreg, halign, hout, hframe⟩
  exact execWhileTruthyHeaderToBodyHead g N φc v buf sp s0 s1 s2 s3 m0 out0 c
    ⟨hheader, hcode, hv, hgsp, hgs0, hgs1, hgs2, hgs3⟩

theorem execWhileBreakRouteRow
    (status sp ra s0 s1 s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple
      (SegPreO execWhileBreakRouteSeg
        (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0)
      (ExecWhileRoutePost execWhileBreakRouteSeg 0x80004090#64
        status sp ra s0 s1 s2 s3 lds m0 out0) := by
  apply segToTripleOut execWhileBreakRouteSeg
    (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0 _
    (by
      have h : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
          [10, 2, 1, 8, 9, 18, 19] := rfl
      rw [h]
      show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
        execWhileBreakRouteSeg
      decide)
  intro σ' i' u' hG' _ hmem' hout' hpc' _ hregs
  refine ⟨hG', hmem', hout', ?_, hregs⟩
  rw [hpc']
  rfl

theorem execWhileRetRouteRow
    (status sp ra s0 s1 s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple
      (SegPreO execWhileRetRouteSeg
        (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0)
      (ExecWhileRoutePost execWhileRetRouteSeg 0x80004150#64
        status sp ra s0 s1 s2 s3 lds m0 out0) := by
  apply segToTripleOut execWhileRetRouteSeg
    (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0 _
    (by
      have h : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
          [10, 2, 1, 8, 9, 18, 19] := rfl
      rw [h]
      show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
        execWhileRetRouteSeg
      decide)
  intro σ' i' u' hG' _ hmem' hout' hpc' _ hregs
  refine ⟨hG', hmem', hout', ?_, hregs⟩
  rw [hpc']
  rfl

theorem execWhileLoopRouteRow
    (status sp ra s0 s1 s2 s3 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String) :
    Triple
      (SegPreO execWhileLoopRouteSeg
        (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0)
      (ExecWhileRoutePost execWhileLoopRouteSeg 0x80004034#64
        status sp ra s0 s1 s2 s3 lds m0 out0) := by
  apply segToTripleOut execWhileLoopRouteSeg
    (execWhileRouteL status sp ra s0 s1 s2 s3) lds 0x80004088#64 m0 out0 _
    (by
      have h : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
          [10, 2, 1, 8, 9, 18, 19] := rfl
      rw [h]
      show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
        execWhileLoopRouteSeg
      decide)
  intro σ' i' u' hG' _ hmem' hout' hpc' _ hregs
  refine ⟨hG', hmem', hout', ?_, hregs⟩
  rw [hpc']
  rfl

theorem execWhileBreakRouteRow_framed
    (g : (R : Register) → Option (RegisterType R))
    (status sp ra s0 s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (out0 : Array String) :
    FramedTriple execWhileRouteEffect
      (ExecWhileRoutePreF execWhileBreakRouteSeg g status sp ra s0 s1 s2 s3
        lds 0x80004088#64 m0 out0)
      (fun c =>
        ExecWhileRoutePost execWhileBreakRouteSeg 0x80004090#64
          status sp ra s0 s1 s2 s3 lds m0 out0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧ ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  apply execWhileRouteFramed execWhileBreakRouteSeg 0x80004090#64 g
    status sp ra s0 s1 s2 s3 lds 0x80004088#64 m0 out0
  · have hk : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
        [10, 2, 1, 8, 9, 18, 19] := rfl
    rw [hk]
    show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
      execWhileBreakRouteSeg
    decide
  · rfl
  · decide
  · rfl

theorem execWhileRetRouteRow_framed
    (g : (R : Register) → Option (RegisterType R))
    (status sp ra s0 s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (out0 : Array String) :
    FramedTriple execWhileRouteEffect
      (ExecWhileRoutePreF execWhileRetRouteSeg g status sp ra s0 s1 s2 s3
        lds 0x80004088#64 m0 out0)
      (fun c =>
        ExecWhileRoutePost execWhileRetRouteSeg 0x80004150#64
          status sp ra s0 s1 s2 s3 lds m0 out0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧ ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  apply execWhileRouteFramed execWhileRetRouteSeg 0x80004150#64 g
    status sp ra s0 s1 s2 s3 lds 0x80004088#64 m0 out0
  · have hk : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
        [10, 2, 1, 8, 9, 18, 19] := rfl
    rw [hk]
    show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
      execWhileRetRouteSeg
    decide
  · rfl
  · decide
  · rfl

theorem execWhileLoopRouteRow_framed
    (g : (R : Register) → Option (RegisterType R))
    (status sp ra s0 s1 s2 s3 : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (out0 : Array String) :
    FramedTriple execWhileRouteEffect
      (ExecWhileRoutePreF execWhileLoopRouteSeg g status sp ra s0 s1 s2 s3
        lds 0x80004088#64 m0 out0)
      (fun c =>
        ExecWhileRoutePost execWhileLoopRouteSeg 0x80004034#64
          status sp ra s0 s1 s2 s3 lds m0 out0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧ ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  apply execWhileRouteFramed execWhileLoopRouteSeg 0x80004034#64 g
    status sp ra s0 s1 s2 s3 lds 0x80004088#64 m0 out0
  · have hk : keysG (execWhileRouteL status sp ra s0 s1 s2 s3) =
        [10, 2, 1, 8, 9, 18, 19] := rfl
    rw [hk]
    show ChainOK 0x80004088#64 [10, 2, 1, 8, 9, 18, 19]
      execWhileLoopRouteSeg
    decide
  · rfl
  · decide
  · rfl

#print axioms execWhileBreakRouteRow
#print axioms execWhileRetRouteRow
#print axioms execWhileLoopRouteRow
#print axioms execWhileBreakRouteRow_framed
#print axioms execWhileRetRouteRow_framed
#print axioms execWhileLoopRouteRow_framed

end Vsa.Sim
