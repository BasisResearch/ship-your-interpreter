import Vsa.Sim.TruthyCopy
import Vsa.Sim.TruthyCopySites
import Vsa.Sim.rows.EvalChildArmForCond

/-!
# `TruthyCopyFor` — the for-loop instance of the copy-and-`value_truthy` seam

The for-loop condition's copy (`0x80004284`: `ld a3,104(sp); ld a4,112(sp);
ld a5,120(sp); addi a0,sp,16; sd a3,16(sp); sd a4,24(sp); sd a5,32(sp);
jal value_truthy`) and its falsy route (`beqz a0` taken at `0x800042a4` into
the normal exit at `0x80004090`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case forCondCopySeg chain
  [(0x80004284#64, 0x06813683#32),
   (0x80004288#64, 0x07013703#32),
   (0x8000428c#64, 0x07813783#32),
   (0x80004290#64, 0x01010513#32),
   (0x80004294#64, 0x00d13823#32),
   (0x80004298#64, 0x00e13c23#32),
   (0x8000429c#64, 0x02f13023#32)]

/-- The for-loop condition's copy seam. -/
def forTruthy : TruthyCopy :=
  { copySeg := forCondCopySeg
    jalPC := 0x800042a0#64
    jalImm := 0x1fe58c#21 }

theorem forCondCopy_facts
    (m : Mem) (SL : StackLayout) (esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m)
    (hlo : SL.lo ≤ esp.toNat) (hhi : esp.toNat + 136 ≤ SL.hi)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo) (halign : esp.toNat % 16 = 0) :
    ChainFacts m m (EvalChildArm.regs esp s0 s1 s2 s3)
      (TruthyCopy.lds forCondArm m esp) forCondCopySeg := by
  have hhi32 : esp.toNat + 136 ≤ 0x100000000 := Nat.le_trans hhi hram.2
  have htohost : tohostAddr + 16 ≤ esp.toNat := Nat.le_trans hwin hlo
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 128)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha16 := haddr 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha24 := haddr 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha32 := haddr 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha104 := haddr 0x068#12 104 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha112 := haddr 0x070#12 112 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha120 := haddr 0x078#12 120 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  unfold forCondCopySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x068#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x068#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x068#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha104]; omega
    · rw [ha104]; omega
    · right; rw [ha104]; omega
    · rw [ha104]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x070#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x070#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x070#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104 + 8)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha112]; omega
    · rw [ha112]; omega
    · right; rw [ha112]; omega
    · rw [ha112]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x078#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x078#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x078#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 104 + 16)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha120]; omega
    · rw [ha120]; omega
    · right; rw [ha120]; omega
    · rw [ha120]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha16] <;> omega
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha24] <;> omega
  · change (0x80000000 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha32] <;> omega

theorem forTruthy_cert : forTruthy.Cert forCondArm where
  src_lo := by decide
  chain_ok := by
    change ChainOK 0x80004284#64 [2, 8, 9, 18, 19] forCondCopySeg; decide
  avoid_abi := by change WrChainAvoidAbi forCondCopySeg; decide
  keys_out := by intros; change KeysOK [10, 15, 14, 13, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [10, 15, 14, 13, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  a0_out := by intros; rfl
  sp_out := by intros; rfl
  log_eq := by intros; rfl
  jal_tgt := by decide
  ret_clean := by decide
  ret_align := by decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_800042a0_tc σ i u _ vmi hG hpc hmi hmem rfl hi
  copy_facts := forCondCopy_facts

-- Falsy: the `beqz` at `0x800042a4` is taken into the normal exit at `0x80004090`.
#derive_case forFalsySeg chain
  []
    terminator ⟨0x800042a4#64, 0xde0506e3#32, 0xe3#8, 0x06#8, 0x05#8, 0xde#8,
      .br bop.BEQ true, 10, 0, 0x1dec#13, 0#21, 0#12⟩

theorem forFalsy_facts (m : Mem) (esp s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m (TruthyCopy.routeL 0#64 esp forTruthy.retPC s0 s1 s2 s3) [] forFalsySeg := by
  unfold forFalsySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BEQ (0#64) (0#64) = true
    decide

#print axioms forTruthy_cert
#print axioms forFalsy_facts

end Vsa.Sim
