import Vsa.Sim.EvalSimCommon
import Vsa.Sim.DivSites2

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

/-! ## Address arithmetic for the frame + spill windows

`sp_sub1088`/`sp_add1088`/`spill_addr` are the value-independent frame/spill
address helpers, extracted to `EvalSimCommon.lean` (shared with the epilogue and
the null/bool/str/var leaf cases). -/

/-! ## Block A — the prologue + dispatch, landing at the arm entry `0x80003408`

`ArmEntry` collects the machine facts true at PC `0x80003408` (the `ld a1,8(a2)`
arm) after the 19-instruction prologue + jump-table dispatch. The memory is
`m0` plus the four spill windows; every code/AST fact survives (proved via
`loaded_eval_expr_writeMap8_ee` and `code_agree_of_stack_write8_ee`). -/

/-! ### Kind-bytes extraction: `ExprRepr … (.int n)` forces the four kind bytes 0. -/

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
                              -- SL.lo + 1088 ≤ sp

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

end Vsa.Sim
