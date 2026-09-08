import Vsa.Sim.TruthyCopy
import Vsa.Sim.TruthyCopySites
import Vsa.Sim.rows.EvalChildArmIf

/-!
# `TruthyCopyIf` — the if instance of the copy-and-`value_truthy` seam

The `if` condition's copy (`0x800041fc`: `ld a2,56(sp); ld a3,64(sp);
ld a5,72(sp); addi a0,sp,16; sd a2,16(sp); sd a3,24(sp); sd a5,32(sp);
jal value_truthy`) and its three reflected routes after the helper returns at
`0x8000421c` (`li a6,8; auipc a4; addi a4; beqz a0`):

* falsy without `else`: `ld s0,24(s0); bnez s0` not taken → `0x800042d4`;
* falsy with `else`: `ld s0,24(s0); bnez s0` taken → `0x80004014`;
* truthy: `ld s0,16(s0); j 0x80004014`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case ifCondCopySeg chain
  [(0x800041fc#64, 0x03813603#32),
   (0x80004200#64, 0x04013683#32),
   (0x80004204#64, 0x04813783#32),
   (0x80004208#64, 0x01010513#32),
   (0x8000420c#64, 0x00c13823#32),
   (0x80004210#64, 0x00d13c23#32),
   (0x80004214#64, 0x02f13023#32)]

/-- The if condition's copy seam. -/
def ifTruthy : TruthyCopy :=
  { copySeg := ifCondCopySeg
    jalPC := 0x80004218#64
    jalImm := 0x1fe614#21 }

theorem ifCondCopy_facts
    (m : Mem) (SL : StackLayout) (esp s0 s1 s2 s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m)
    (hlo : SL.lo ≤ esp.toNat) (hhi : esp.toNat + 136 ≤ SL.hi)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo) (halign : esp.toNat % 16 = 0) :
    ChainFacts m m (EvalChildArm.regs esp s0 s1 s2 s3)
      (TruthyCopy.lds ifCondArm m esp) ifCondCopySeg := by
  have hhi32 : esp.toNat + 136 ≤ 0x100000000 := Nat.le_trans hhi hram.2
  have htohost : tohostAddr + 16 ≤ esp.toNat := Nat.le_trans hwin hlo
  have haddr (off : BitVec 12) (n : Nat) (hn : n ≤ 104)
      (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
      (esp + sign_extend (m := 64) off).toNat = esp.toNat + n := by
    rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha16 := haddr 0x010#12 16 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha24 := haddr 0x018#12 24 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha32 := haddr 0x020#12 32 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha56 := haddr 0x038#12 56 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha64 := haddr 0x040#12 64 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha72 := haddr 0x048#12 72 (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  unfold ifCondCopySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x038#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x038#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x038#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 56)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha56]; omega
    · rw [ha56]; omega
    · right; rw [ha56]; omega
    · rw [ha56]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x040#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x040#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x040#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 56 + 8)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha64]; omega
    · rw [ha64]; omega
    · right; rw [ha64]; omega
    · rw [ha64]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x048#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x048#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x048#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 56 + 16)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha72]; omega
    · rw [ha72]; omega
    · right; rw [ha72]; omega
    · rw [ha72]
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

theorem ifTruthy_cert : ifTruthy.Cert ifCondArm where
  src_lo := by decide
  chain_ok := by
    change ChainOK 0x800041fc#64 [2, 8, 9, 18, 19] ifCondCopySeg; decide
  avoid_abi := by change WrChainAvoidAbi ifCondCopySeg; decide
  keys_out := by intros; change KeysOK [10, 15, 13, 12, 2, 8, 9, 18, 19]; decide
  ra_out := by intros; change ∀ n ∈ [10, 15, 13, 12, 2, 8, 9, 18, 19], n ≠ 1; decide
  end_pc := by intros; rfl
  a0_out := by intros; rfl
  sp_out := by intros; rfl
  log_eq := by intros; rfl
  jal_tgt := by decide
  ret_clean := by decide
  ret_align := by decide
  jal_site := fun σ i u vmi hG hpc hmi hmem hi =>
    site_80004218_tc σ i u _ vmi hG hpc hmi hmem rfl hi
  copy_facts := ifCondCopy_facts

/-! ## The three routes after `value_truthy` returns at `0x8000421c` -/

-- Falsy, no `else`: the `beqz` is taken, `ld s0,24(s0)` reads the null else
-- pointer, and `bnez s0` falls through to the `li a0,0` at `0x800042d4`.
#derive_case ifFalsyNoElseSeg chain
  [(0x8000421c#64, 0x00800813#32),
   (0x80004220#64, 0x00016717#32),
   (0x80004224#64, 0xd9870713#32)]
    terminator ⟨0x80004228#64, 0x0a050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0a#8,
      .br bop.BEQ true, 10, 0, 0x00a4#13, 0#21, 0#12⟩
  ;;
  [(0x800042cc#64, 0x01843403#32)]
    terminator ⟨0x800042d0#64, 0xd40412e3#32, 0xe3#8, 0x12#8, 0x04#8, 0xd4#8,
      .br bop.BNE false, 8, 0, 0x1d44#13, 0#21, 0#12⟩

-- Falsy with `else`: `bnez s0` is taken into the re-dispatch at `0x80004014`.
#derive_case ifFalsyElseSeg chain
  [(0x8000421c#64, 0x00800813#32),
   (0x80004220#64, 0x00016717#32),
   (0x80004224#64, 0xd9870713#32)]
    terminator ⟨0x80004228#64, 0x0a050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0a#8,
      .br bop.BEQ true, 10, 0, 0x00a4#13, 0#21, 0#12⟩
  ;;
  [(0x800042cc#64, 0x01843403#32)]
    terminator ⟨0x800042d0#64, 0xd40412e3#32, 0xe3#8, 0x12#8, 0x04#8, 0xd4#8,
      .br bop.BNE true, 8, 0, 0x1d44#13, 0#21, 0#12⟩

-- Truthy: the `beqz` falls through, `ld s0,16(s0)` selects the `then`
-- branch, and `j 0x80004014` re-dispatches.
#derive_case ifTruthySeg chain
  [(0x8000421c#64, 0x00800813#32),
   (0x80004220#64, 0x00016717#32),
   (0x80004224#64, 0xd9870713#32)]
    terminator ⟨0x80004228#64, 0x0a050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0a#8,
      .br bop.BEQ false, 10, 0, 0x00a4#13, 0#21, 0#12⟩
  ;;
  [(0x8000422c#64, 0x01043403#32)]
    terminator ⟨0x80004230#64, 0xde5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xde#8,
      .j, 0, 0, 0#13, 0x1ffde4#21, 0#12⟩

/-- The one statement-node load of an if route. -/
def ifRouteLds (m : Mem) (aStmt : BitVec 64) (off : Nat) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (aStmt.toNat + off)]

#print axioms ifTruthy_cert


end Vsa.Sim

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The else-pointer field of an if node is a readable eight-byte window. -/
theorem ifRoute_field_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    {c : Expr} {t : Stmt} {oe : Option Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t oe)) (off : Nat)
    (hoff : off + 8 ≤ 40) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 off) :
    (0x80000000 ≤ (aStmt + sign_extend (m := 64) imm).toNat ∧
      (aStmt + sign_extend (m := 64) imm).toNat + 8 ≤ 0x100000000 ∧
      ((aStmt + sign_extend (m := 64) imm).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) imm).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) imm).toNat
      (EvalChildArm.wordLds8 m (aStmt.toNat + off)) := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hn := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) imm).toNat = aStmt.toNat + off := by
    rw [himm, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hn.hi_ge
    have := hr.hi_ram
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hn.lo_le; omega
  · have := hr.hi_ram; have := hn.hi_ge; omega
  · right; have := hr.win; have := hn.lo_le; omega
  · simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
    trivial

/-- Chain facts of the falsy-no-`else` route: the `beqz` on `a0 = 0` is taken
and the null else pointer keeps `bnez` from firing. -/
theorem ifFalsyNoElse_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    {c : Expr} {t : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t none))
    (hcode : Exec_stmtLoaded m)
    (hnull : read64 m (aStmt.toNat + 24) = some 0)
    (esp s1 s2 s3 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL 0#64 esp ifTruthy.retPC aStmt s1 s2 s3)
      (ifRouteLds m aStmt 24) ifFalsyNoElseSeg := by
  have hzero := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 24) 0#64 hnull
  unfold ifFalsyNoElseSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BEQ (0#64) (0#64) = true
    decide
  · exact ifRoute_field_facts hg 24 (by omega) (0x018#12) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 24)) != 0#64) = false
    rw [hzero]
    decide

/-- Chain facts of the falsy-with-`else` route: the `beqz` on `a0 = 0` is
taken and the non-null else pointer makes `bnez` fire into the re-dispatch. -/
theorem ifFalsyElse_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    {c : Expr} {t e : Stmt} {aElse : BitVec 64}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t (some e)))
    (hcode : Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + 24) = some aElse.toNat) (hne : aElse ≠ 0#64)
    (esp s1 s2 s3 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL 0#64 esp ifTruthy.retPC aStmt s1 s2 s3)
      (ifRouteLds m aStmt 24) ifFalsyElseSeg := by
  have hval := EvalChildArm.bytesVal_ld_wordLds m (aStmt.toNat + 24) aElse hread
  unfold ifFalsyElseSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BEQ (0#64) (0#64) = true
    decide
  · exact ifRoute_field_facts hg 24 (by omega) (0x018#12) (by apply BitVec.eq_of_toNat_eq; decide)
  · change (bytesVal MKind.ld (EvalChildArm.wordLds8 m (aStmt.toNat + 24)) != 0#64) = true
    rw [hval]
    exact bne_iff_ne.mpr hne

/-- Chain facts of the truthy route: the `beqz` on `a0 = 1` falls through and
`ld s0,16(s0)` reads the `then` pointer before the unconditional jump. -/
theorem ifTruthy_facts
    {m : Mem} {SL : StackLayout} {A : Arena} {sp aRet aStmt : BitVec 64}
    {c : Expr} {t : Stmt} {oe : Option Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.ifStmt c t oe))
    (hcode : Exec_stmtLoaded m)
    (esp s1 s2 s3 : BitVec 64) :
    ChainFacts m m (TruthyCopy.routeL 1#64 esp ifTruthy.retPC aStmt s1 s2 s3)
      (ifRouteLds m aStmt 16) ifTruthySeg := by
  unfold ifTruthySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change guardB bop.BEQ (1#64) (0#64) = false
    decide
  · exact ifRoute_field_facts hg 16 (by omega) (0x010#12) (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms ifFalsyNoElse_facts
#print axioms ifFalsyElse_facts
#print axioms ifTruthy_facts

end Vsa.Sim
