import Vsa.Sim.EvalIntSim
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.DivSites2
import Vsa.Sim.DivSpec2
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 gate assembly: `EvalIntSimGoal` proof (part 2)

This file completes the `EvalE.int` simulation Triple begun in `EvalIntSim.lean`,
composing the 26 verified sites of `EvalExprSites.lean` plus the `value_int_spec`
callee jal into `EvalIntSimGoal` (the M4 gate).
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

/-! ## Block A — `Eval_exprLoaded` survives a stack-window `sd` spill

The code region is `[0x80003164, 0x80003fe0)` (contiguous, chunks 0..57). A
prologue `sd` writes an 8-byte window disjoint from that region. -/
theorem loaded_eval_expr_writeMap8_ee (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a8 + 8 ≤ 0x80003164 ∨ 0x80003fe0 ≤ a8)
    (h : Eval_exprLoaded mem) : Eval_exprLoaded (writeMap8 mem a8 d) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38,
    c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eval_exprChunk0] at c0 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk1] at c1 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk2] at c2 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk3] at c3 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk4] at c4 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk5] at c5 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk6] at c6 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk7] at c7 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk8] at c8 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk9] at c9 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk10] at c10 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk11] at c11 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk12] at c12 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk13] at c13 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk14] at c14 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk15] at c15 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk16] at c16 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk17] at c17 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk18] at c18 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk19] at c19 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk20] at c20 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk21] at c21 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk22] at c22 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk23] at c23 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk24] at c24 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk25] at c25 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk26] at c26 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk27] at c27 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk28] at c28 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk29] at c29 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk30] at c30 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk31] at c31 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk32] at c32 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk33] at c33 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk34] at c34 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk35] at c35 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk36] at c36 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk37] at c37 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk38] at c38 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk39] at c39 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk40] at c40 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk41] at c41 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk42] at c42 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk43] at c43 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk44] at c44 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk45] at c45 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk46] at c46 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk47] at c47 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk48] at c48 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk49] at c49 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk50] at c50 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk51] at c51 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk52] at c52 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk53] at c53 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk54] at c54 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk55] at c55 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk56] at c56 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk57] at c57 ⊢; repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## Address arithmetic for the frame + spill windows

`sp_sub1088`/`sp_add1088`/`spill_addr` are the value-independent frame/spill
address helpers, extracted to `EvalSimCommon.lean` (shared with the epilogue and
the null/bool/str/var leaf cases). -/

/-! ## Block A — the prologue + dispatch, landing at the arm entry `0x80003408`

`ArmEntry` collects the machine facts true at PC `0x80003408` (the `ld a1,8(a2)`
arm) after the 19-instruction prologue + jump-table dispatch. The memory is
`m0` plus the four spill windows; every code/AST fact survives (proved via
`loaded_eval_expr_writeMap8_ee` and `code_agree_of_stack_write8_ee`). -/

/-- Machine post-state of the prologue at the `.int` arm entry. `ment` is the
post-memory (m0 + 4 spills); `g` the entry ghost frame; `out0` the entry console
output. The `sailOutput`-invariance field (`c.σ.sailOutput = out0`) is threaded
through the 19 prologue steps via `ReadsLikePost.out` + `sailOutput_sigmaPost_*`
(no step touches the HTIF console — enabled by the enriched `ReadsLikePost`). -/
def ArmEntry (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (n : Int)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config) : Prop :=
  -- `ArmEntry … n` is the `.int` instance of the case-INDEPENDENT arm-entry
  -- predicate `ArmEntryK` (`EvalSimCommon.lean`), specialized at the int arm's
  -- landing PC `0x80003408`, its callee-code predicate `Value_intLoaded`, and the
  -- evaluated expression `.int n`. Every other field (spill slots, lowered `sp`,
  -- store/frame/memFrame facts, geometric region facts) is shared verbatim across
  -- the sibling `null`/`bool`/`str`/`var` leaf cases.
  ArmEntryK g N A SL φf φc st (0x80003408#64) Value_intLoaded (.int n)
    sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c

/-! ### Kind-bytes extraction: `ExprRepr … (.int n)` forces the four kind bytes 0. -/
theorem int_kind_bytes {m : Mem} {a : Nat} {n : Int} (h : ExprRepr m a (.int n)) :
    m[a]? = some (0#8) ∧ m[a + 1]? = some (0#8) ∧ m[a + 2]? = some (0#8) ∧ m[a + 3]? = some (0#8) := by
  obtain ⟨hk, _⟩ := exprRepr_int_payload h
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes m a 0 hk
  have l0 := b0.isLt; have l1 := b1.isLt; have l2 := b2.isLt; have l3 := b3.isLt
  have e0 : b0 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e1 : b1 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e2 : b2 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  have e3 : b3 = 0#8 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  exact ⟨e0 ▸ hb0, e1 ▸ hb1, e2 ▸ hb2, e3 ▸ hb3⟩

/-! ### Kind-bytes for a general tag `k`: `read32 m a = some k` (k < 128) forces the
four kind bytes to reassemble (LE) to `k`, and both the signed (`lw`, x14) and
unsigned (`lwu`, x15) extensions fold to `ofNat 64 k`. Generalizes the
`.int`-specific `int_kind_bytes` (which pins them all to `0#8`). -/
theorem kind_bytes {m : Mem} {a k : Nat} (hk : read32 m a = some k) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k :=
  read32_bytes m a k hk

/-- `lwu`'s zero-extend of the LE kind word folds to `ofNat 64 k` for `k < 128`. -/
theorem zext_kind (b0 b1 b2 b3 : BitVec 8) (k : Nat) (hk : k < 128)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = k) :
    (zero_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)) : BitVec 64)
      = BitVec.ofNat 64 k := by
  have hlt : ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)).toNat = k := by
    rw [word_toNat_recon]; exact hrec
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hlt,
    Nat.mod_eq_of_lt (show k < 2^64 by omega)]

/-! ## Block A composed: prologue + dispatch → arm entry -/

theorem read64_writeMap8_disjoint_ee (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-! ## `blockA_k` — the case-INDEPENDENT prologue + jump-table dispatch

Generalizes `blockA_ee`'s proof over the dispatched leaf kind. The three
int-specific couplings of the dispatch are now hypotheses:

* **kind tag `k`** (`hkind : read32 m0 aExpr.toNat = some k`, with `k ≤ 10` for the
  `bltu` default-arm not-taken check and `k < 128` for the kind-word folding). The
  two kind reads (`lw`→x14, `lwu`→x15) both fold to `ofNat 64 k` (`sext_kind`/
  `zext_kind`) instead of `.int`'s hard `0`.
* **arm PC `armPC` + slot pin** (`hslot : KindSlotPinned k armPC m0`) — the slot at
  `jumpTableBase + 4*k` sign-extends+base to `armPC`; the `jr` lands at `armPC`.
* **callee-loaded `calleeLoaded`** carried through the spills
  (`hcallee : calleeLoaded m0`, survival `hcalleeSurv`).

Every other field (spills, `sp` lowering, store/frame/geometric facts) is shared,
taken as explicit hypotheses (the shared subset of `EvalEntry`). `blockA_ee`
re-derives the int case by instantiating `k := 0`, `armPC := 0x80003408`,
`calleeLoaded := Value_intLoaded`, discharging `hslot` from `IntSlotPinned` via
`int_slot_kindPinned` and `hcalleeSurv` from `loaded_int_writeMap8`. -/
theorem blockA_k
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (e : Expr) (k : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (out0 : Array String)
    -- shared entry facts (the case-independent subset of `EvalEntry`):
    (hkle : k ≤ 10) (hklt : k < 128)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hslot : KindSlotPinned k armPC m0) (hcallee : calleeLoaded m0)
    (hcalleeSurv : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
      SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd))
    (hexprSurv : ∀ m' : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) → ExprRepr m' aExpr.toNat e)
    (harmAl : armPC.toNat % 4 = 0)
    (htableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k) :
    Triple
      (fun c => (GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry) ∧
        c.σ.regs.get? Register.x10 = some sret ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x12 = some aExpr ∧
        c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        StackOK SL sp (1088 + 1088) ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
        c.σ.mem = m0 ∧ Eval_exprLoaded c.σ.mem ∧
        ExprRepr c.σ.mem aExpr.toNat e ∧
        StoreRepr c.σ.mem N A φf φc st.store ∧
        (∀ m' : Mem, (∀ kk, ¬ (SL.lo ≤ kk ∧ kk < SL.hi) →
            ¬ (sret.toNat ≤ kk ∧ kk < sret.toNat + 24) → c.σ.mem[kk]? = m'[kk]?) →
          StoreRepr m' N A φf φc st.store) ∧
        OutRepr c.σ st ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R) ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        aExpr.toNat % 8 = 0 ∧
        (0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000) ∧
        tohostAddr + 16 ≤ aExpr.toNat ∧
        sret.toNat % 8 = 0 ∧ (0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000) ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        (0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000) ∧ tohostAddr + 16 ≤ SL.lo ∧
        ((∃ v, c.σ.regs.get? Register.x8 = some v) ∧
          (∃ v, c.σ.regs.get? Register.x9 = some v) ∧
          (∃ v, c.σ.regs.get? Register.x18 = some v)))
        ∧ c.σ.sailOutput = out0)
      (fun c => ∃ ment v8 v9 v18,
        ArmEntryK g N A SL φf φc st armPC calleeLoaded e sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        -- wave 47e (`LeafExitPin`): the arm-entry memory is the four prologue
        -- spills over `m0` — presence-preserving.  Surfaced so the leaf
        -- `blockC_*` can pin their exit memory (`LeafMemPin`).
        MemExtends m0 ment) := by
  intro c hpre'
  obtain ⟨hpre, hout0⟩ := hpre'
  obtain ⟨hG, htick, hpc, ha0, ha1, ha2, hra, hraAl, hspReg, hstackOK, ⟨vmi, hmi⟩,
    hmem, hcode, hexpr, hstore, hstoreSurv, hout, hframe,
    hcodeStk, hexprStk, hexprAl, hexprRam, hexprWin,
    hsretAl, hsretRam, hsretWin, hsretVi, hsretStk, hsretEvalCode, hstkRam, hstkWin,
    ⟨⟨v8, h8_0⟩, ⟨v9, h9_0⟩, ⟨v18, h18_0⟩⟩⟩ := hpre
  have hviCode : calleeLoaded c.σ.mem := hmem ▸ hcallee
  have hintSlot : KindSlotPinned k armPC c.σ.mem := hmem ▸ hslot
  have hload0 : Eval_exprLoaded c.σ.mem := hcode
  have haddr0 : (aExpr + sign_extend (m := 64) (0x000#12)).toNat = aExpr.toNat := by
    rw [sext_zero, BitVec.add_zero]
  obtain ⟨hkb0v, hkb1v, hkb2v, hkb3v, hkb0, hkb1, hkb2, hkb3, hkrec⟩ := kind_bytes (hmem ▸ hkind)
  obtain ⟨hSLlo, hsphi, hsp16⟩ := hstackOK
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hpc164 : c.σ.regs.get? Register.PC = some (0x80003164#64 : BitVec 64) := by rw [hpc]; rfl
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- ============ 0x80003164: lw a4,0(a2) → x14 := k (kind) ============
  have hhtif_e : (aExpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (aExpr + sign_extend (m := 64) (0x000#12)).toNat := by
    right; rw [haddr0]; rw [htoh]; have := hexprWin; rw [htoh] at this; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80003164_ee c.σ c.tick c.steps (0x80003164#64) vmi aExpr hkb0v hkb1v hkb2v hkb3v
      hG hpc164 hmi ha2 hload0 rfl
      (by rw [haddr0]; have := hexprRam.1; omega)
      (by rw [haddr0]; have := hexprRam.2; omega) hhtif_e
      (by rw [haddr0]; have := hexprAl; omega)
      (by rw [haddr0]; exact hkb0) (by rw [haddr0]; exact hkb1)
      (by rw [haddr0]; exact hkb2) (by rw [haddr0]; exact hkb3) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003168#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80003164#64) 4 = (0x80003168#64:BitVec 64) from by decide] at this
  -- x14 := sign_extend (kind bytes) = ofNat 64 k  (`k < 128`)
  have hx14_1 : σ1.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_kind hkb0v hkb1v hkb2v hkb3v k hklt hkrec] at this
  have ha2_1 : σ1.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 : σ1.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 : σ1.regs.get? Register.x1 = some r := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hsp_1 : σ1.regs.get? Register.x2 = some sp := obs_alu_other' hobs1 Register.x2 (by decide) hspReg
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  -- ============ 0x80003168: addi sp,sp,-1088 → x2 := sp - 1088 ============
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80003168_ee σ1 i1 (c.steps + 1) (0x80003168#64) vmi1 sp hG1 hpc1 hmi1 hsp_1 (hmem1e ▸ hload0) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hs2
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2, hmem1e]
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000316c#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80003168#64) 4 = (0x8000316c#64:BitVec 64) from by decide] at this
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub1088] at this
  have ha2_2 : σ2.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have ha0_2 : σ2.regs.get? Register.x10 = some sret := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 : σ2.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have h8_1 : σ1.regs.get? Register.x8 = some v8 := obs_alu_other' hobs1 Register.x8 (by decide) h8_0
  have h8_2 : σ2.regs.get? Register.x8 = some v8 := obs_alu_other' hobs2 Register.x8 (by decide) h8_1
  have h18_1 : σ1.regs.get? Register.x18 = some v18 := obs_alu_other' hobs1 Register.x18 (by decide) h18_0
  have h18_2 : σ2.regs.get? Register.x18 = some v18 := obs_alu_other' hobs2 Register.x18 (by decide) h18_1
  have h9_1 : σ1.regs.get? Register.x9 = some v9 := obs_alu_other' hobs1 Register.x9 (by decide) h9_0
  have h9_2 : σ2.regs.get? Register.x9 = some v9 := obs_alu_other' hobs2 Register.x9 (by decide) h9_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- KindSlotPinned survives a writeMap8 disjoint from [table+4k, table+4k+4)
  have intslot_wm8 : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8*8)),
      (a8 + 8 ≤ jumpTableBase + 4 * k ∨ jumpTableBase + 4 * k + 4 ≤ a8) →
      KindSlotPinned k armPC mem → KindSlotPinned k armPC (writeMap8 mem a8 dd) := by
    intro mem a8 dd hdis hh
    obtain ⟨t0, t1, t2, t3, p0, p1, p2, p3, ptgt⟩ := hh
    refine ⟨t0, t1, t2, t3, ?_, ?_, ?_, ?_, ptgt⟩
    · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p0
    · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p1
    · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p2
    · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; exact p3
  -- generic spill-step: prove code/callee/slot survive at addr sp-k
  -- ============ 0x8000316c: sd s0,1072(sp') → mem[sp-16] := v8 ============
  have hoff430 : (sign_extend (m := 64) (0x430#12) : BitVec 64).toNat = 1072 := by decide
  have haddr3 : ((sp - 1088#64) + sign_extend (m := 64) (0x430#12)).toNat = sp.toNat - 16 :=
    spill_addr sp (0x430#12) 16 (by rw [hoff430]) (by omega) hsp1088
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000316c_ee σ2 i2 (c.steps+1+1) (0x8000316c#64) vmi2 (sp-1088#64) v8 hG2 hpc2 hmi2 hsp_2 h8_2 (hmem2e ▸ hload0) rfl
      (by rw [haddr3]; have := hstkRam.1; omega) (by rw [haddr3]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haddr3]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haddr3]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hs3
  have hmem3e : σ3.mem = writeMap8 c.σ.mem (sp.toNat - 16) (sdData_val v8) := by
    rw [hmem3, mem_afterNextPC, hmem2e, haddr3]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003170#64) := by
    have := obs_store_pc_val hobs3; rwa [show BitVec.addInt (0x8000316c#64) 4 = (0x80003170#64:BitVec 64) from by decide] at this
  have hload3 : Eval_exprLoaded σ3.mem := by
    rw [hmem3e]; exact loaded_eval_expr_writeMap8_ee c.σ.mem (sp.toNat-16) (sdData_val v8) (by have := hcodeStk; omega) hload0
  have hvi3 : calleeLoaded σ3.mem := by
    rw [hmem3e]; exact hcalleeSurv c.σ.mem (sp.toNat-16) (sdData_val v8) (by omega) (by omega) hviCode
  have hslot3 : KindSlotPinned k armPC σ3.mem := by
    rw [hmem3e]; exact intslot_wm8 c.σ.mem (sp.toNat-16) (sdData_val v8) (by have := htableStk; omega) hintSlot
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs3 Register.x2 (by decide) hsp_2
  have ha2_3 : σ3.regs.get? Register.x12 = some aExpr := obs_store_other_val' hobs3 Register.x12 (by decide) ha2_2
  have ha0_3 : σ3.regs.get? Register.x10 = some sret := obs_store_other_val' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 : σ3.regs.get? Register.x11 = some aEnv := obs_store_other_val' hobs3 Register.x11 (by decide) ha1_2
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_store_other_val' hobs3 Register.x1 (by decide) hra_2
  have h18_3 : σ3.regs.get? Register.x18 = some v18 := obs_store_other_val' hobs3 Register.x18 (by decide) h18_2
  have h9_3 : σ3.regs.get? Register.x9 = some v9 := obs_store_other_val' hobs3 Register.x9 (by decide) h9_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  -- ============ 0x80003170: sd s2,1056(sp') → mem[sp-32] := v18 ============
  have hoff420 : (sign_extend (m := 64) (0x420#12) : BitVec 64).toNat = 1056 := by decide
  have haddr4 : ((sp - 1088#64) + sign_extend (m := 64) (0x420#12)).toNat = sp.toNat - 32 :=
    spill_addr sp (0x420#12) 32 (by rw [hoff420]) (by omega) hsp1088
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80003170_ee σ3 i3 (c.steps+1+1+1) (0x80003170#64) vmi3 (sp-1088#64) v18 hG3 hpc3 hmi3 hsp_3 h18_3 hload3 rfl
      (by rw [haddr4]; have := hstkRam.1; omega) (by rw [haddr4]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haddr4]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haddr4]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hs4
  have hmem4e : σ4.mem = writeMap8 σ3.mem (sp.toNat - 32) (sdData_val v18) := by
    rw [hmem4, mem_afterNextPC, haddr4]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80003174#64) := by
    have := obs_store_pc_val hobs4; rwa [show BitVec.addInt (0x80003170#64) 4 = (0x80003174#64:BitVec 64) from by decide] at this
  have hload4 : Eval_exprLoaded σ4.mem := by
    rw [hmem4e]; exact loaded_eval_expr_writeMap8_ee σ3.mem (sp.toNat-32) (sdData_val v18) (by have := hcodeStk; omega) hload3
  have hvi4 : calleeLoaded σ4.mem := by
    rw [hmem4e]; exact hcalleeSurv σ3.mem (sp.toNat-32) (sdData_val v18) (by omega) (by omega) hvi3
  have hslot4 : KindSlotPinned k armPC σ4.mem := by
    rw [hmem4e]; exact intslot_wm8 σ3.mem (sp.toNat-32) (sdData_val v18) (by have := htableStk; omega) hslot3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs4 Register.x2 (by decide) hsp_3
  have ha2_4 : σ4.regs.get? Register.x12 = some aExpr := obs_store_other_val' hobs4 Register.x12 (by decide) ha2_3
  have ha0_4 : σ4.regs.get? Register.x10 = some sret := obs_store_other_val' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 : σ4.regs.get? Register.x11 = some aEnv := obs_store_other_val' hobs4 Register.x11 (by decide) ha1_3
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_store_other_val' hobs4 Register.x1 (by decide) hra_3
  have h9_4 : σ4.regs.get? Register.x9 = some v9 := obs_store_other_val' hobs4 Register.x9 (by decide) h9_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  -- ============ 0x80003174: sd ra,1080(sp') → mem[sp-8] := r ============
  have hoff438 : (sign_extend (m := 64) (0x438#12) : BitVec 64).toNat = 1080 := by decide
  have haddr5 : ((sp - 1088#64) + sign_extend (m := 64) (0x438#12)).toNat = sp.toNat - 8 :=
    spill_addr sp (0x438#12) 8 (by rw [hoff438]) (by omega) hsp1088
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80003174_ee σ4 i4 (c.steps+1+1+1+1) (0x80003174#64) vmi4 (sp-1088#64) r hG4 hpc4 hmi4 hsp_4 hra_4 hload4 rfl
      (by rw [haddr5]; have := hstkRam.1; omega) (by rw [haddr5]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haddr5]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haddr5]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps+1+1+1+1⟩ ⟨σ5, i5, c.steps+1+1+1+1+1⟩ := hs5
  have hmem5e : σ5.mem = writeMap8 σ4.mem (sp.toNat - 8) (sdData_val r) := by
    rw [hmem5, mem_afterNextPC, haddr5]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003178#64) := by
    have := obs_store_pc_val hobs5; rwa [show BitVec.addInt (0x80003174#64) 4 = (0x80003178#64:BitVec 64) from by decide] at this
  have hload5 : Eval_exprLoaded σ5.mem := by
    rw [hmem5e]; exact loaded_eval_expr_writeMap8_ee σ4.mem (sp.toNat-8) (sdData_val r) (by have := hcodeStk; omega) hload4
  have hvi5 : calleeLoaded σ5.mem := by
    rw [hmem5e]; exact hcalleeSurv σ4.mem (sp.toNat-8) (sdData_val r) (by omega) (by omega) hvi4
  have hslot5 : KindSlotPinned k armPC σ5.mem := by
    rw [hmem5e]; exact intslot_wm8 σ4.mem (sp.toNat-8) (sdData_val r) (by have := htableStk; omega) hslot4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs5 Register.x2 (by decide) hsp_4
  have ha2_5 : σ5.regs.get? Register.x12 = some aExpr := obs_store_other_val' hobs5 Register.x12 (by decide) ha2_4
  have ha0_5 : σ5.regs.get? Register.x10 = some sret := obs_store_other_val' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 : σ5.regs.get? Register.x11 = some aEnv := obs_store_other_val' hobs5 Register.x11 (by decide) ha1_4
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_store_other_val' hobs5 Register.x1 (by decide) hra_4
  have h9_5 : σ5.regs.get? Register.x9 = some v9 := obs_store_other_val' hobs5 Register.x9 (by decide) h9_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret_val hobs5
  -- ============ 0x80003178: sd s1,1064(sp') → mem[sp-24] := v9 ============
  have hoff428 : (sign_extend (m := 64) (0x428#12) : BitVec 64).toNat = 1064 := by decide
  have haddr6 : ((sp - 1088#64) + sign_extend (m := 64) (0x428#12)).toNat = sp.toNat - 24 :=
    spill_addr sp (0x428#12) 24 (by rw [hoff428]) (by omega) hsp1088
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80003178_ee σ5 i5 (c.steps+1+1+1+1+1) (0x80003178#64) vmi5 (sp-1088#64) v9 hG5 hpc5 hmi5 hsp_5 h9_5 hload5 rfl
      (by rw [haddr6]; have := hstkRam.1; omega) (by rw [haddr6]; have := hsphi; have := hstkRam.2; omega)
      (by rw [haddr6]; rw [htoh]; have := hstkWin; rw [htoh] at this; omega) (by rw [haddr6]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps+1+1+1+1+1⟩ ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ := hs6
  have hmem6e : σ6.mem = writeMap8 σ5.mem (sp.toNat - 24) (sdData_val v9) := by
    rw [hmem6, mem_afterNextPC, haddr6]
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000317c#64) := by
    have := obs_store_pc_val hobs6; rwa [show BitVec.addInt (0x80003178#64) 4 = (0x8000317c#64:BitVec 64) from by decide] at this
  have hload6 : Eval_exprLoaded σ6.mem := by
    rw [hmem6e]; exact loaded_eval_expr_writeMap8_ee σ5.mem (sp.toNat-24) (sdData_val v9) (by have := hcodeStk; omega) hload5
  have hvi6 : calleeLoaded σ6.mem := by
    rw [hmem6e]; exact hcalleeSurv σ5.mem (sp.toNat-24) (sdData_val v9) (by omega) (by omega) hvi5
  have hslot6 : KindSlotPinned k armPC σ6.mem := by
    rw [hmem6e]; exact intslot_wm8 σ5.mem (sp.toNat-24) (sdData_val v9) (by have := htableStk; omega) hslot5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp-1088#64) := obs_store_other_val' hobs6 Register.x2 (by decide) hsp_5
  have ha2_6 : σ6.regs.get? Register.x12 = some aExpr := obs_store_other_val' hobs6 Register.x12 (by decide) ha2_5
  have ha0_6 : σ6.regs.get? Register.x10 = some sret := obs_store_other_val' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 : σ6.regs.get? Register.x11 = some aEnv := obs_store_other_val' hobs6 Register.x11 (by decide) ha1_5
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_store_other_val' hobs6 Register.x1 (by decide) hra_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret_val hobs6
  -- σ6.mem agrees with m0 (= c.σ.mem) outside the stack window `[SL.lo, sp)`.
  have hagreeM06 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = σ6.mem[a]? := by
    intro a ha
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), ← hmem]
  have hexpr6 : ExprRepr σ6.mem aExpr.toNat e := hexprSurv σ6.mem hagreeM06
  -- track x14 = ofNat k through the spills (set at 0x3164, mem/reg passthrough)
  have hx14_2 : σ2.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs2 Register.x14 (by decide) hx14_1
  have hx14_3 : σ3.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_store_other_val' hobs3 Register.x14 (by decide) hx14_2
  have hx14_4 : σ4.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_store_other_val' hobs4 Register.x14 (by decide) hx14_3
  have hx14_5 : σ5.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_store_other_val' hobs5 Register.x14 (by decide) hx14_4
  have hx14_6 : σ6.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_store_other_val' hobs6 Register.x14 (by decide) hx14_5
  -- ============ 0x8000317c: li a5,10 → x15 := 10 ============
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000317c_ee σ6 i6 (c.steps+1+1+1+1+1+1) (0x8000317c#64) vmi6 hG6 hpc6 hmi6 hload6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hmem7e : σ7.mem = σ6.mem := hmem7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003180#64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x8000317c#64) 4 = (0x80003180#64:BitVec 64) from by decide] at this
  have hx15_7 : σ7.regs.get? Register.x15 = some (10#64) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x00a#12) : BitVec 64) = 10#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_7 : σ7.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs7 Register.x14 (by decide) hx14_6
  have ha2_7 : σ7.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs7 Register.x12 (by decide) ha2_6
  have ha0_7 : σ7.regs.get? Register.x10 = some sret := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have ha1_7 : σ7.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs7 Register.x11 (by decide) ha1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  -- ============ 0x80003180: mv s0,a2 → x8 := aExpr ============
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80003180_ee σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80003180#64) vmi7 aExpr hG7 hpc7 hmi7 ha2_7 (hmem7e ▸ hload6) rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ ⟨σ8, i8, _⟩ := hs8
  have hmem8e : σ8.mem = σ6.mem := by rw [hmem8, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80003184#64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80003180#64) 4 = (0x80003184#64:BitVec 64) from by decide] at this
  have hx14_8 : σ8.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs8 Register.x14 (by decide) hx14_7
  have hx15_8 : σ8.regs.get? Register.x15 = some (10#64) := obs_alu_other' hobs8 Register.x15 (by decide) hx15_7
  have ha1_8 : σ8.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs8 Register.x11 (by decide) ha1_7
  have ha0_8 : σ8.regs.get? Register.x10 = some sret := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
  have ha2_8 : σ8.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs8 Register.x12 (by decide) ha2_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  -- ============ 0x80003184: mv s2,a1 → x18 := aEnv ============
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80003184_ee σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80003184#64) vmi8 aEnv hG8 hpc8 hmi8 ha1_8 (hmem8e ▸ hload6) rfl hi8
  have hstep9 : Step ⟨σ8, i8, _⟩ ⟨σ9, i9, _⟩ := hs9
  have hmem9e : σ9.mem = σ6.mem := by rw [hmem9, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003188#64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80003184#64) 4 = (0x80003188#64:BitVec 64) from by decide] at this
  have hx14_9 : σ9.regs.get? Register.x14 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs9 Register.x14 (by decide) hx14_8
  have hx15_9 : σ9.regs.get? Register.x15 = some (10#64) := obs_alu_other' hobs9 Register.x15 (by decide) hx15_8
  have ha0_9 : σ9.regs.get? Register.x10 = some sret := obs_alu_other' hobs9 Register.x10 (by decide) ha0_8
  have ha2_9 : σ9.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs9 Register.x12 (by decide) ha2_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  -- ============ 0x80003188: bltu a5,a4 NOT taken (10 <u k = false, `k ≤ 10`) ============
  have hbltu : zopz0zI_u (10#64) (BitVec.ofNat 64 k) = false := by
    have hkeq : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 by omega)]
    unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
    apply decide_eq_false
    rw [Int.not_lt, hkeq, show (10#64 : BitVec 64).toNat = 10 from by decide]
    exact Int.ofNat_le.mpr (by omega)
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80003188_nottaken_ee σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80003188#64) vmi9 (10#64) (BitVec.ofNat 64 k)
      hG9 hpc9 hmi9 hx15_9 hx14_9 (hmem9e ▸ hload6) rfl hbltu hi9
  have hstep10 : Step ⟨σ9, i9, _⟩ ⟨σ10, i10, _⟩ := hs10
  have hmem10e : σ10.mem = σ6.mem := by rw [hmem10, hmem9e]
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000318c#64) := by
    have := obs_branch_nottaken_pc hobs10; rwa [show BitVec.addInt (0x80003188#64) 4 = (0x8000318c#64:BitVec 64) from by decide] at this
  have ha2_10 : σ10.regs.get? Register.x12 = some aExpr := obs_branch_nottaken_other' hobs10 Register.x12 (by decide) ha2_9
  have ha0_10 : σ10.regs.get? Register.x10 = some sret := obs_branch_nottaken_other' hobs10 Register.x10 (by decide) ha0_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp-1088#64) := obs_branch_nottaken_other' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_branch_nottaken_minstret hobs10
  -- kind bytes in σ6.mem (= σ10.mem) for the lwu: survive the 4 disjoint spills
  have hkb0' : σ6.mem[aExpr.toNat]? = some hkb0v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega)]; exact hkb0
  have hkb1' : σ6.mem[aExpr.toNat + 1]? = some hkb1v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega)]; exact hkb1
  have hkb2' : σ6.mem[aExpr.toNat + 2]? = some hkb2v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega)]; exact hkb2
  have hkb3' : σ6.mem[aExpr.toNat + 3]? = some hkb3v := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega),
        getElem_writeMap8_disjoint _ _ _ _ (by have := hexprStk; omega)]; exact hkb3
  -- ============ 0x8000318c: lwu a5,0(a2) → x15 := ofNat k (kind, zero-ext) ============
  have hhtif_e2 : (aExpr + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (aExpr + sign_extend (m := 64) (0x000#12)).toNat := by
    right; rw [haddr0, htoh]; have := hexprWin; rw [htoh] at this; omega
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000318c_ee σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x8000318c#64) vmi10 aExpr hkb0v hkb1v hkb2v hkb3v
      hG10 hpc10 hmi10 ha2_10 (hmem10e ▸ hload6) rfl
      (by rw [haddr0]; have := hexprRam.1; omega) (by rw [haddr0]; have := hexprRam.2; omega) hhtif_e2
      (by rw [haddr0]; have := hexprAl; omega)
      (by rw [haddr0, hmem10e]; exact hkb0') (by rw [haddr0, hmem10e]; exact hkb1')
      (by rw [haddr0, hmem10e]; exact hkb2') (by rw [haddr0, hmem10e]; exact hkb3') hi10
  have hstep11 : Step ⟨σ10, i10, _⟩ ⟨σ11, i11, _⟩ := hs11
  have hmem11e : σ11.mem = σ6.mem := by rw [hmem11, hmem10e]
  have hpc11 : σ11.regs.get? Register.PC = some (0x80003190#64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x8000318c#64) 4 = (0x80003190#64:BitVec 64) from by decide] at this
  have hx15_11 : σ11.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [zext_kind hkb0v hkb1v hkb2v hkb3v k hklt hkrec] at this
  have ha2_11 : σ11.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs11 Register.x12 (by decide) ha2_10
  have ha0_11 : σ11.regs.get? Register.x10 = some sret := obs_alu_other' hobs11 Register.x10 (by decide) ha0_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  -- ============ 0x80003190: auipc a4 → x14 := 0x8001a190 ============
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80003190_ee σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80003190#64) vmi11 hG11 hpc11 hmi11 (hmem11e ▸ hload6) rfl hi11
  have hstep12 : Step ⟨σ11, i11, _⟩ ⟨σ12, i12, _⟩ := hs12
  have hmem12e : σ12.mem = σ6.mem := by rw [hmem12, hmem11e]
  have hpc12 : σ12.regs.get? Register.PC = some (0x80003194#64) := by
    have := obs_alu_pc hobs12; rwa [show BitVec.addInt (0x80003190#64) 4 = (0x80003194#64:BitVec 64) from by decide] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some (0x8001a190#64) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x80003190#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12) : BitVec 64) = 0x8001a190#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_12 : σ12.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs12 Register.x15 (by decide) hx15_11
  have ha2_12 : σ12.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs12 Register.x12 (by decide) ha2_11
  have ha0_12 : σ12.regs.get? Register.x10 = some sret := obs_alu_other' hobs12 Register.x10 (by decide) ha0_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs12 Register.x2 (by decide) hsp_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  -- ============ 0x80003194: addi a4,a4,-568 → x14 := 0x80019f58 (table base) ============
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80003194_ee σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80003194#64) vmi12 (0x8001a190#64) hG12 hpc12 hmi12 hx14_12 (hmem12e ▸ hload6) rfl hi12
  have hstep13 : Step ⟨σ12, i12, _⟩ ⟨σ13, i13, _⟩ := hs13
  have hmem13e : σ13.mem = σ6.mem := by rw [hmem13, hmem12e]
  have hpc13 : σ13.regs.get? Register.PC = some (0x80003198#64) := by
    have := obs_alu_pc hobs13; rwa [show BitVec.addInt (0x80003194#64) 4 = (0x80003198#64:BitVec 64) from by decide] at this
  have hx14_13 : σ13.regs.get? Register.x14 = some (0x80019f58#64) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x8001a190#64 : BitVec 64) + sign_extend (m := 64) (0xdc8#12) : BitVec 64) = 0x80019f58#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_13 : σ13.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs13 Register.x15 (by decide) hx15_12
  have ha0_13 : σ13.regs.get? Register.x10 = some sret := obs_alu_other' hobs13 Register.x10 (by decide) ha0_12
  have ha2_13 : σ13.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs13 Register.x12 (by decide) ha2_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs13 Register.x2 (by decide) hsp_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  -- ============ 0x80003198: mv s1,a0 → x9 := sret ============
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80003198_ee σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80003198#64) vmi13 sret hG13 hpc13 hmi13 ha0_13 (hmem13e ▸ hload6) rfl hi13
  have hstep14 : Step ⟨σ13, i13, _⟩ ⟨σ14, i14, _⟩ := hs14
  have hmem14e : σ14.mem = σ6.mem := by rw [hmem14, hmem13e]
  have hpc14 : σ14.regs.get? Register.PC = some (0x8000319c#64) := by
    have := obs_alu_pc hobs14; rwa [show BitVec.addInt (0x80003198#64) 4 = (0x8000319c#64:BitVec 64) from by decide] at this
  have hx9_14 : σ14.regs.get? Register.x9 = some sret := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hx14_14 : σ14.regs.get? Register.x14 = some (0x80019f58#64) := obs_alu_other' hobs14 Register.x14 (by decide) hx14_13
  have hx15_14 : σ14.regs.get? Register.x15 = some (BitVec.ofNat 64 k) := obs_alu_other' hobs14 Register.x15 (by decide) hx15_13
  have ha0_14 : σ14.regs.get? Register.x10 = some sret := obs_alu_other' hobs14 Register.x10 (by decide) ha0_13
  have ha2_14 : σ14.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs14 Register.x12 (by decide) ha2_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs14 Register.x2 (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  -- ============ 0x8000319c: slli a5,a5,2 → x15 := k <<< 2 = ofNat (4*k) ============
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8000319c_ee σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000319c#64) vmi14 (BitVec.ofNat 64 k) hG14 hpc14 hmi14 hx15_14 (hmem14e ▸ hload6) rfl hi14
  have hstep15 : Step ⟨σ14, i14, _⟩ ⟨σ15, i15, _⟩ := hs15
  have hmem15e : σ15.mem = σ6.mem := by rw [hmem15, hmem14e]
  have hpc15 : σ15.regs.get? Register.PC = some (0x800031a0#64) := by
    have := obs_alu_pc hobs15; rwa [show BitVec.addInt (0x8000319c#64) 4 = (0x800031a0#64:BitVec 64) from by decide] at this
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
  have hx15_15 : σ15.regs.get? Register.x15 = some (BitVec.ofNat 64 (4 * k)) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hshleq] at this
  have hx14_15 : σ15.regs.get? Register.x14 = some (0x80019f58#64) := obs_alu_other' hobs15 Register.x14 (by decide) hx14_14
  have hx9_15 : σ15.regs.get? Register.x9 = some sret := obs_alu_other' hobs15 Register.x9 (by decide) hx9_14
  have ha0_15 : σ15.regs.get? Register.x10 = some sret := obs_alu_other' hobs15 Register.x10 (by decide) ha0_14
  have ha2_15 : σ15.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs15 Register.x12 (by decide) ha2_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs15 Register.x2 (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  -- ============ 0x800031a0: add a5,a5,a4 → x15 := 4*k + table = ofNat (jumpTableBase + 4*k) ============
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_800031a0_ee σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800031a0#64) vmi15 (BitVec.ofNat 64 (4 * k)) (0x80019f58#64) hG15 hpc15 hmi15 hx15_15 hx14_15 (hmem15e ▸ hload6) rfl hi15
  have hstep16 : Step ⟨σ15, i15, _⟩ ⟨σ16, i16, _⟩ := hs16
  have hmem16e : σ16.mem = σ6.mem := by rw [hmem16, hmem15e]
  have hpc16 : σ16.regs.get? Register.PC = some (0x800031a4#64) := by
    have := obs_alu_pc hobs16; rwa [show BitVec.addInt (0x800031a0#64) 4 = (0x800031a4#64:BitVec 64) from by decide] at this
  have hx15_16 : σ16.regs.get? Register.x15 = some (BitVec.ofNat 64 (jumpTableBase + 4 * k)) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((BitVec.ofNat 64 (4 * k)) + (0x80019f58#64) : BitVec 64) = BitVec.ofNat 64 (jumpTableBase + 4 * k) from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      rw [show (BitVec.ofNat 64 (4 * k)).toNat = 4 * k from by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * k < 2^64 by omega)]]
      rw [show (0x80019f58#64 : BitVec 64).toNat = 0x80019f58 from by decide]
      rw [show (BitVec.ofNat 64 (jumpTableBase + 4 * k)).toNat = jumpTableBase + 4 * k from by
            rw [BitVec.toNat_ofNat]; simp only [jumpTableBase]
            rw [Nat.mod_eq_of_lt (show 0x80019f58 + 4*k < 2^64 by omega)]]
      simp only [jumpTableBase]
      rw [Nat.mod_eq_of_lt (show 4*k + 0x80019f58 < 2^64 by omega)]; omega] at this
  have hx14_16 : σ16.regs.get? Register.x14 = some (0x80019f58#64) := obs_alu_other' hobs16 Register.x14 (by decide) hx14_15
  have hx9_16 : σ16.regs.get? Register.x9 = some sret := obs_alu_other' hobs16 Register.x9 (by decide) hx9_15
  have ha0_16 : σ16.regs.get? Register.x10 = some sret := obs_alu_other' hobs16 Register.x10 (by decide) ha0_15
  have ha2_16 : σ16.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs16 Register.x12 (by decide) ha2_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs16 Register.x2 (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  -- slot bytes at `table + 4k` in σ6.mem (= σ16.mem)
  have hslot16 : KindSlotPinned k armPC σ16.mem := by rw [hmem16e]; exact hslot6
  obtain ⟨sb0, sb1, sb2, sb3, hsb0, hsb1, hsb2, hsb3, hsbtgt⟩ := hslot16
  -- the slot base as a Nat: `(ofNat (table+4k)).toNat = table + 4k` (small, < 2^64)
  have hslotBaseNat : (BitVec.ofNat 64 (jumpTableBase + 4 * k)).toNat = jumpTableBase + 4 * k := by
    simp only [BitVec.toNat_ofNat, jumpTableBase]; rw [Nat.mod_eq_of_lt (by omega)]
  -- ============ 0x800031a4: lw a5,0(a5) → x15 := sext(slot bytes) ============
  have haddrT : ((BitVec.ofNat 64 (jumpTableBase + 4 * k) : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = jumpTableBase + 4 * k := by rw [sext_zero, BitVec.add_zero]; exact hslotBaseNat
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_800031a4_ee σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800031a4#64) vmi16 (BitVec.ofNat 64 (jumpTableBase + 4 * k))
      sb0 sb1 sb2 sb3 hG16 hpc16 hmi16 hx15_16 (hmem16e ▸ hload6) rfl
      (by rw [haddrT]; simp only [jumpTableBase]; omega) (by rw [haddrT]; simp only [jumpTableBase]; omega)
      (by rw [haddrT]; left; simp only [jumpTableBase]; rw [htoh]; omega) (by rw [haddrT]; simp only [jumpTableBase]; omega)
      (by rw [haddrT]; exact hsb0) (by rw [haddrT]; exact hsb1)
      (by rw [haddrT]; exact hsb2) (by rw [haddrT]; exact hsb3) hi16
  have hstep17 : Step ⟨σ16, i16, _⟩ ⟨σ17, i17, _⟩ := hs17
  have hmem17e : σ17.mem = σ6.mem := by rw [hmem17, hmem16e]
  have hpc17 : σ17.regs.get? Register.PC = some (0x800031a8#64) := by
    have := obs_alu_pc hobs17; rwa [show BitVec.addInt (0x800031a4#64) 4 = (0x800031a8#64:BitVec 64) from by decide] at this
  have hx15_17 : σ17.regs.get? Register.x15 = some (sign_extend (m := 64) ((((sb3.append sb2).append sb1).append sb0) : BitVec (8*4))) :=
    obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_17 : σ17.regs.get? Register.x14 = some (0x80019f58#64) := obs_alu_other' hobs17 Register.x14 (by decide) hx14_16
  have hx9_17 : σ17.regs.get? Register.x9 = some sret := obs_alu_other' hobs17 Register.x9 (by decide) hx9_16
  have ha0_17 : σ17.regs.get? Register.x10 = some sret := obs_alu_other' hobs17 Register.x10 (by decide) ha0_16
  have ha2_17 : σ17.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs17 Register.x12 (by decide) ha2_16
  have hsp_17 : σ17.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs17 Register.x2 (by decide) hsp_16
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  -- ============ 0x800031a8: add a5,a5,a4 → x15 := sext(slot) + table = armPC ============
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_800031a8_ee σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800031a8#64) vmi17
      (sign_extend (m := 64) ((((sb3.append sb2).append sb1).append sb0) : BitVec (8*4)))
      (0x80019f58#64) hG17 hpc17 hmi17 hx15_17 hx14_17 (hmem17e ▸ hload6) rfl hi17
  have hstep18 : Step ⟨σ17, i17, _⟩ ⟨σ18, i18, _⟩ := hs18
  have hmem18e : σ18.mem = σ6.mem := by rw [hmem18, hmem17e]
  have hpc18 : σ18.regs.get? Register.PC = some (0x800031ac#64) := by
    have := obs_alu_pc hobs18; rwa [show BitVec.addInt (0x800031a8#64) 4 = (0x800031ac#64:BitVec 64) from by decide] at this
  have hx15_18 : σ18.regs.get? Register.x15 = some armPC := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0x80019f58#64 : BitVec 64)) = BitVec.ofNat 64 jumpTableBase from by
      simp only [jumpTableBase], hsbtgt] at this
  have hx9_18 : σ18.regs.get? Register.x9 = some sret := obs_alu_other' hobs18 Register.x9 (by decide) hx9_17
  have ha0_18 : σ18.regs.get? Register.x10 = some sret := obs_alu_other' hobs18 Register.x10 (by decide) ha0_17
  have ha2_18 : σ18.regs.get? Register.x12 = some aExpr := obs_alu_other' hobs18 Register.x12 (by decide) ha2_17
  have hsp_18 : σ18.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs18 Register.x2 (by decide) hsp_17
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  -- thread ra (x1) through the register-only steps 7..18 (unchanged from σ6)
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have hra_8 : σ8.regs.get? Register.x1 = some r := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
  have hra_9 : σ9.regs.get? Register.x1 = some r := obs_alu_other' hobs9 Register.x1 (by decide) hra_8
  have hra_10 : σ10.regs.get? Register.x1 = some r := obs_branch_nottaken_other' hobs10 Register.x1 (by decide) hra_9
  have hra_11 : σ11.regs.get? Register.x1 = some r := obs_alu_other' hobs11 Register.x1 (by decide) hra_10
  have hra_12 : σ12.regs.get? Register.x1 = some r := obs_alu_other' hobs12 Register.x1 (by decide) hra_11
  have hra_13 : σ13.regs.get? Register.x1 = some r := obs_alu_other' hobs13 Register.x1 (by decide) hra_12
  have hra_14 : σ14.regs.get? Register.x1 = some r := obs_alu_other' hobs14 Register.x1 (by decide) hra_13
  have hra_15 : σ15.regs.get? Register.x1 = some r := obs_alu_other' hobs15 Register.x1 (by decide) hra_14
  have hra_16 : σ16.regs.get? Register.x1 = some r := obs_alu_other' hobs16 Register.x1 (by decide) hra_15
  have hra_17 : σ17.regs.get? Register.x1 = some r := obs_alu_other' hobs17 Register.x1 (by decide) hra_16
  have hra_18 : σ18.regs.get? Register.x1 = some r := obs_alu_other' hobs18 Register.x1 (by decide) hra_17
  -- ============ 0x800031ac: jr a5 → PC := armPC ============
  have htgtJr : (BitVec.update (armPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt armPC harmAl]; exact harmAl
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_800031ac_ee σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800031ac#64) vmi18 armPC hG18 hpc18 hmi18 hx15_18 (hmem18e ▸ hload6) rfl htgtJr hi18
  have hstep19 : Step ⟨σ18, i18, _⟩ ⟨σ19, i19, _⟩ := hs19
  have hmem19e : σ19.mem = σ6.mem := by rw [hmem19, hmem18e]
  have hpc19 : σ19.regs.get? Register.PC = some armPC := by
    have := obs_jr_pc hobs19
    rwa [ret_tgt armPC harmAl] at this
  have hx9_19 : σ19.regs.get? Register.x9 = some sret := obs_jr_other' hobs19 Register.x9 (by decide) hx9_18
  have ha0_19 : σ19.regs.get? Register.x10 = some sret := obs_jr_other' hobs19 Register.x10 (by decide) ha0_18
  have ha2_19 : σ19.regs.get? Register.x12 = some aExpr := obs_jr_other' hobs19 Register.x12 (by decide) ha2_18
  have hsp_19 : σ19.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other' hobs19 Register.x2 (by decide) hsp_18
  have hra_19 : σ19.regs.get? Register.x1 = some r := obs_jr_other' hobs19 Register.x1 (by decide) hra_18
  obtain ⟨vmi19, hmi19⟩ := obs_jr_minstret hobs19
  -- output invariance across the 19 prologue steps: no step touches `sailOutput`.
  -- Each `hobsK.out` gives `σK.sailOutput = (sigmaPost_* …).sailOutput`, and the
  -- per-class `sailOutput_sigmaPost_* = σ(K-1).sailOutput`; chain to `c.σ.sailOutput = out0`.
  have hout19 : σ19.sailOutput = out0 := by
    rw [hobs19.out, sailOutput_sigmaPost_jump_x0, hobs18.out, sailOutput_sigmaPost_alu,
      hobs17.out, sailOutput_sigmaPost_alu, hobs16.out, sailOutput_sigmaPost_alu,
      hobs15.out, sailOutput_sigmaPost_alu, hobs14.out, sailOutput_sigmaPost_alu,
      hobs13.out, sailOutput_sigmaPost_alu, hobs12.out, sailOutput_sigmaPost_alu,
      hobs11.out, sailOutput_sigmaPost_alu, hobs10.out, sailOutput_sigmaPost_branch_nottaken,
      hobs9.out, sailOutput_sigmaPost_alu, hobs8.out, sailOutput_sigmaPost_alu,
      hobs7.out, sailOutput_sigmaPost_alu, hobs6.out, sailOutput_sigmaPost_store,
      hobs5.out, sailOutput_sigmaPost_store, hobs4.out, sailOutput_sigmaPost_store,
      hobs3.out, sailOutput_sigmaPost_store, hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_alu]
    exact hout0
  -- the four spill slots survive in `σ6.mem`. Slot layout (from the spill order):
  --   σ3 = wm8 m0  (sp-16) v8;  σ4 = wm8 σ3 (sp-32) v18;
  --   σ5 = wm8 σ4  (sp-8) r;    σ6 = wm8 σ5 (sp-24) v9.
  -- Read each back through the later disjoint spills to its own write.
  have hslotRa : read64 σ6.mem (sp.toNat - 8) = some r.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8, sdData_toNat]
  have hslotS0 : read64 σ6.mem (sp.toNat - 16) = some v8.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem4e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem3e, read64_writeMap8, sdData_toNat]
  have hslotS1 : read64 σ6.mem (sp.toNat - 24) = some v9.toNat := by
    rw [hmem6e, read64_writeMap8, sdData_toNat]
  have hslotS2 : read64 σ6.mem (sp.toNat - 32) = some v18.toNat := by
    rw [hmem6e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem5e, read64_writeMap8_disjoint_ee _ _ _ _ (by omega),
        hmem4e, read64_writeMap8, sdData_toNat]
  -- `g x8/x9/x18 = some v8/v9/v18` from the entry frame + spill_defined reads
  have hgx8 : g Register.x8 = some v8 := by
    rw [← hframe Register.x8 (by decide)]; exact h8_0
  have hgx9 : g Register.x9 = some v9 := by
    rw [← hframe Register.x9 (by decide)]; exact h9_0
  have hgx18 : g Register.x18 = some v18 := by
    rw [← hframe Register.x18 (by decide)]; exact h18_0
  have hgx2 : g Register.x2 = some sp := by
    rw [← hframe Register.x2 (by decide)]; exact hspReg
  have houtStr : String.join out0.toList = st.out := by
    have : Vsa.Machine.output c.σ = st.out := hout
    simp only [Vsa.Machine.output] at this; rw [← hout0]; exact this
  -- StoreRepr survives the 4 spills: σ6.mem agrees with c.σ.mem outside `[SL.lo,sp)`.
  have hagree6 : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
      ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → c.σ.mem[k]? = σ6.mem[k]? := by
    intro k hk _
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]
  have hstore6 : StoreRepr σ6.mem N A φf φc st.store :=
    hstoreSurv σ6.mem (fun k hk hr =>
      hagree6 k (fun hcon => hk ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hsphi⟩) hr)
  -- memFrame: σ6.mem = m0 outside the stack window (spills all inside `[SL.lo,sp)`)
  have hmemframe6 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → σ6.mem[a]? = m0[a]? := by
    intro a ha
    rw [hmem6e, hmem5e, hmem4e, hmem3e]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), ← hmem]
  -- `store_survives` transported to σ6.mem: any m' agreeing with σ6.mem outside the
  -- window also agrees with c.σ.mem outside it (compose through hagree6).
  have hstoreSurv6 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        σ6.mem[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hm'
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hsphi⟩
    exact (hagree6 k hk1' hk2).trans (hm' k hk1 hk2)
  -- the arm-entry blanket frame: callee-saved regs (excl. x8/x9/x18/x2) unchanged
  -- through the prologue (prologue rds are x14/x15/x2/x8/x18/x9; x14/x15 are
  -- caller-saved so `abi_ne` handles them; x2/x8/x18/x9 are the exclusions).
  -- caller-saved ≠ ABI-preserved: `(X == R) = false` for X ∈ {x14, x15}.
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- raw register-frame step: `σ' R = σ R` for a non-tick, non-rd register, via
  -- `hobs.1` (`σ' R = spost R`) composed with the class frame lemma (`spost R = σ R`).
  have hframe19 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ19.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8 he9 he18 he2
    have hab : AbiPreserved R = true := hR.1
    have h14 : (Register.x14 == R) = false := abi_ne' (by decide) hab
    have h15 : (Register.x15 == R) = false := abi_ne' (by decide) hab
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    -- one raw ALU frame step: σ' R = σ R
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
    -- chain σ19 → σ18 → … → σ1 → c.σ
    exact (jr hobs19).trans ((alu hobs18 h15).trans ((alu hobs17 h15).trans
      ((alu hobs16 h15).trans ((alu hobs15 h15).trans ((alu hobs14 he9).trans
      ((alu hobs13 h14).trans ((alu hobs12 h14).trans ((alu hobs11 h15).trans
      ((brn hobs10).trans ((alu hobs9 he18).trans ((alu hobs8 he8).trans
      ((alu hobs7 h15).trans ((str hobs6).trans ((str hobs5).trans ((str hobs4).trans
      ((str hobs3).trans ((alu hobs2 he2).trans (alu hobs1 h14))))))))))))))))))
  have hframeArm : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ19.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    rw [hframe19 R hR he8 he9 he18 he2]; exact hframe R hR
  -- ===== call-point register facts: x11=aEnv (a1 untouched after `mv s2,a1`),
  -- x8=aExpr (`mv s0,a2` @σ8), x18=aEnv (`mv s2,a1` @σ9), threaded to σ19. =====
  have hsext0e : ∀ w : BitVec 64, (w + sign_extend (m := 64) (0x000#12) : BitVec 64) = w := by
    intro w; rw [sext_zero, BitVec.add_zero]
  -- x8 := aExpr at σ8 (`mv s0,a2`), then unchanged σ9..σ19
  have hx8_8 : σ8.regs.get? Register.x8 = some aExpr := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsext0e] at this
  have hx8_9 : σ9.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs9 Register.x8 (by decide) hx8_8
  have hx8_10 : σ10.regs.get? Register.x8 = some aExpr := obs_branch_nottaken_other' hobs10 Register.x8 (by decide) hx8_9
  have hx8_11 : σ11.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs11 Register.x8 (by decide) hx8_10
  have hx8_12 : σ12.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs12 Register.x8 (by decide) hx8_11
  have hx8_13 : σ13.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs13 Register.x8 (by decide) hx8_12
  have hx8_14 : σ14.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs14 Register.x8 (by decide) hx8_13
  have hx8_15 : σ15.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs15 Register.x8 (by decide) hx8_14
  have hx8_16 : σ16.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs16 Register.x8 (by decide) hx8_15
  have hx8_17 : σ17.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs17 Register.x8 (by decide) hx8_16
  have hx8_18 : σ18.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs18 Register.x8 (by decide) hx8_17
  have hx8_19 : σ19.regs.get? Register.x8 = some aExpr := obs_jr_other' hobs19 Register.x8 (by decide) hx8_18
  -- x18 := aEnv at σ9 (`mv s2,a1`), then unchanged σ10..σ19
  have hx18_9 : σ9.regs.get? Register.x18 = some aEnv := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsext0e] at this
  have hx18_10 : σ10.regs.get? Register.x18 = some aEnv := obs_branch_nottaken_other' hobs10 Register.x18 (by decide) hx18_9
  have hx18_11 : σ11.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs11 Register.x18 (by decide) hx18_10
  have hx18_12 : σ12.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs12 Register.x18 (by decide) hx18_11
  have hx18_13 : σ13.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs13 Register.x18 (by decide) hx18_12
  have hx18_14 : σ14.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs14 Register.x18 (by decide) hx18_13
  have hx18_15 : σ15.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs15 Register.x18 (by decide) hx18_14
  have hx18_16 : σ16.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs16 Register.x18 (by decide) hx18_15
  have hx18_17 : σ17.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs17 Register.x18 (by decide) hx18_16
  have hx18_18 : σ18.regs.get? Register.x18 = some aEnv := obs_alu_other' hobs18 Register.x18 (by decide) hx18_17
  have hx18_19 : σ19.regs.get? Register.x18 = some aEnv := obs_jr_other' hobs19 Register.x18 (by decide) hx18_18
  -- x11 = aEnv: `a1` last threaded to σ8 (`ha1_8`); no later step writes x11, thread to σ19
  have ha1_9 : σ9.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs9 Register.x11 (by decide) ha1_8
  have ha1_10 : σ10.regs.get? Register.x11 = some aEnv := obs_branch_nottaken_other' hobs10 Register.x11 (by decide) ha1_9
  have ha1_11 : σ11.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs11 Register.x11 (by decide) ha1_10
  have ha1_12 : σ12.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs12 Register.x11 (by decide) ha1_11
  have ha1_13 : σ13.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs13 Register.x11 (by decide) ha1_12
  have ha1_14 : σ14.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs14 Register.x11 (by decide) ha1_13
  have ha1_15 : σ15.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs15 Register.x11 (by decide) ha1_14
  have ha1_16 : σ16.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs16 Register.x11 (by decide) ha1_15
  have ha1_17 : σ17.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs17 Register.x11 (by decide) ha1_16
  have ha1_18 : σ18.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs18 Register.x11 (by decide) ha1_17
  have ha1_19 : σ19.regs.get? Register.x11 = some aEnv := obs_jr_other' hobs19 Register.x11 (by decide) ha1_18
  -- presence: the arm-entry memory is the 4-spill `writeMap8` chain over `m0`
  have hpresM : MemExtends m0 σ6.mem := by
    rw [hmem6e, hmem5e, hmem4e, hmem3e, ← hmem]
    exact (((memExtends_writeMap8 _ _ _).trans (memExtends_writeMap8 _ _ _)).trans
      (memExtends_writeMap8 _ _ _)).trans (memExtends_writeMap8 _ _ _)
  -- assemble the full 19-step run + ArmEntryK
  refine ⟨⟨σ19, i19, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩, ?_, σ6.mem, v8, v9, v18, ⟨hG19, hi19, hpc19, ha0_19, hx9_19, ha2_19, hsp_19, hra_19,
    ⟨_, hmi19⟩, hout19, hmem19e, hmem19e ▸ hload6, hmem19e ▸ hvi6, hmem19e ▸ hexpr6,
    houtStr,
    hexprAl, hexprRam.1, hexprRam.2, hexprWin,
    hmem19e ▸ hslotRa, hmem19e ▸ hslotS0, hmem19e ▸ hslotS1, hmem19e ▸ hslotS2,
    hmem19e ▸ hmemframe6,
    hgx8, hgx9, hgx18, hgx2, hmem19e ▸ hstore6, hmem19e ▸ hstoreSurv6, hframeArm,
    hsretAl, hsretRam.1, hsretRam.2, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, ?_, ?_, ?_, ?_, hstkRam.1, hstkWin, ?_, hraAl, ha1_19, hx8_19, hx18_19⟩,
    hpresM⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
      ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
      (Steps.single hstep19))))))))))))))))))
  · have := hsphi; have := hstkRam.2; omega          -- sp ≤ 2^32
  · have := hstkRam.1; have := hSLlo; omega           -- 2^31 ≤ sp
  · have := hstkWin; have := hSLlo; rw [htoh]; omega   -- tohost+16+1088 ≤ sp
  · have := hsp16; omega                              -- sp % 8 = 0 (from % 16)
  · have := hSLlo; omega                              -- SL.lo + 1088 ≤ sp

/-! ## `blockA_ee` — the `.int` instance of `blockA_k`

Re-derives the original int prologue+dispatch Triple by instantiating `blockA_k`
at `k := 0`, `armPC := 0x80003408`, `calleeLoaded := Value_intLoaded`,
`e := .int n`. The six generic dispatch hypotheses are discharged from the
`EvalEntry` fields: the kind tag from `exprRepr_int_payload` (`read32 = 0`), the
slot pin from `int_slot` via `int_slot_kindPinned`, the callee from
`value_int_code`, callee-survival from `loaded_int_writeMap8`, `ExprRepr`
survival from the int payload reads across the disjoint spills, and the geometric
`table_stack_disjoint`. Output type `ArmEntry … = ArmEntryK … 0x80003408
Value_intLoaded (.int n)` (definitional). -/
theorem blockA_ee
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr) (n : Int)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d a (.int n) sp r sret aEnv aExpr m0 c
        ∧ c.σ.sailOutput = out0)
      (fun c => ∃ ment v8 v9 v18,
        ArmEntry g N A SL φf φc st n sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        MemExtends m0 ment) := by
  intro c hpre'
  obtain ⟨he, hout0⟩ := hpre'
  -- the int kind tag + payload reads (in `m0`), for `hkind`/`hexprSurv`
  obtain ⟨hkm0, hpm0⟩ := exprRepr_int_payload (he.mem ▸ he.expr)
  exact blockA_k g N A SL φf φc st (.int n) 0 (0x80003408#64) Value_intLoaded
    sp r sret aEnv aExpr m0 out0
    (by omega) (by omega)
    (by simpa using hkm0)
    (int_slot_kindPinned (he.mem ▸ he.int_slot)) (he.mem ▸ he.value_int_code)
    (fun mem a8 dd hlo hhi hh => by
      have hvi := he.vicode_stack_disjoint
      have := he.stackOK.1
      exact loaded_int_writeMap8 mem a8 dd (by omega) hh)
    (fun m' hag => by
      -- ExprRepr m' aExpr (.int n) from the int kind + payload reads (agree outside window)
      have hstk := he.expr_stack_disjoint
      have hlo := he.stackOK.1
      refine ExprRepr.int ?_ ?_
      · -- read32 m' aExpr = read32 m0 aExpr = some 0
        have hb := read32_bytes m0 aExpr.toNat 0 hkm0
        obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := hb
        simp only [read32, readLE, bind, Option.bind]
        rw [← hag aExpr.toNat (by omega), ← hag (aExpr.toNat + 1) (by omega),
            ← hag (aExpr.toNat + 2) (by omega), ← hag (aExpr.toNat + 3) (by omega),
            hb0, hb1, hb2, hb3]
        simp only []; apply congrArg some; omega
      · -- readI64 m' (aExpr+8) = readI64 m0 (aExpr+8) = some n
        simp only [readI64] at hpm0 ⊢
        obtain ⟨p, hp64, hpeq⟩ := Option.map_eq_some_iff.mp hpm0
        have hb := read64_bytes m0 (aExpr.toNat + 8) p hp64
        obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ := hb
        have hread' : read64 m' (aExpr.toNat + 8) = some p := by
          simp only [read64, readLE, bind, Option.bind]
          rw [← hag (aExpr.toNat + 8) (by omega), ← hag (aExpr.toNat + 8 + 1) (by omega),
              ← hag (aExpr.toNat + 8 + 2) (by omega), ← hag (aExpr.toNat + 8 + 3) (by omega),
              ← hag (aExpr.toNat + 8 + 4) (by omega), ← hag (aExpr.toNat + 8 + 5) (by omega),
              ← hag (aExpr.toNat + 8 + 6) (by omega), ← hag (aExpr.toNat + 8 + 7) (by omega),
              e0, e1, e2, e3, e4, e5, e6, e7]
          simp only []; apply congrArg some; omega
        rw [hread']; exact congrArg some hpeq)
    (by decide)
    (by have := he.table_stack_disjoint; simp only [jumpTableBase]; omega)
    -- feed the shared entry facts (case-independent subset of `EvalEntry`)
    c ⟨⟨he.good, he.tick, he.pc, he.a0, he.a1, he.a2, he.ra, he.ra_align, he.spReg,
    he.stackOK, he.minstret, he.mem, he.code, he.expr, he.store, he.store_survives, he.out,
    he.frame, he.code_stack_disjoint, he.expr_stack_disjoint, he.expr_align, he.expr_ram,
    he.expr_win, he.sret_align, he.sret_ram, he.sret_win, he.sret_vicode_disjoint,
    he.sret_stack_disjoint, he.sret_evalcode_disjoint, he.stack_ram, he.stack_win,
    he.spill_defined⟩, hout0⟩


end Vsa.Sim
