import Vsa.While.Cost
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalIntSim2

/-!
# Layer 4 — M4 pilot RECURSIVE case: `evalNegSim` (the `EvalE.neg` case)

Composes the `EX_UNARY`/`neg` simulation Triple in the mutual-recursor motive
shape (`EvalIH` — `EvalEntry → EvalExitD`), from the four blocks landed earlier:

```
blockA_k (prologue + dispatch → ArmEntryK @0x800035e0)
  ≫ blockB_unary (arm head + recursive call, composed with the IH → SubEvalReturn @0x800035ec)
  ≫ blockC_neg   (post-call neg tail → PreEpilogueV .int(wrap64 -n) @0x800033ec)
  ≫ blockD_v     (shared epilogue → EvalExit .int(wrap64 -n))
```

The widened `blockA_k`/`ArmEntryK` (`EvalSimCommon.lean`) now expose the recursive
call-point register facts (`x11 = interp*`, `x8 = aExpr`, `x18 = interp*`) at the
arm-entry config, so the arm-register residual (`hArmRegs`) and the entry-ghost
bridge are DISCHARGED HERE by taking the call-point ghost `gpre := c1.σ.regs.get?`
(making the frame `rfl`) and reading the three registers off the widened
`ArmEntryK`. The `EvalExitD` upgrade (`hUpg`) is DISCHARGED via `blockC_neg`'s
widened `PreEpilogueVD` output (which now carries `MemExtends m0 mpre` +
`[SL.lo,SL.hi)`-survival) fed through `blockD_v_rec` (`EvalRecCommon.lean`).

`evalNegSim` is thus unconditional except for:
* `NegExtras` — the operand-node `ExprRepr`+geometry, the extra 1088-byte
  recursive stack headroom, the arena/code/table disjunctions and the `EX_UNARY`
  slot pin (residual #1, the recursive-case program-structure facts a full
  `EvalEntry` widening / M6 Layout would supply);
* `hMcallPop` — the pre-call memory is fully populated (residual #3, an M6 Layout
  fact: `blockC_neg`'s dead-byte `ld`s of the sub-`Value` padding need presence).

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

/-! ## `NegExtras` — the recursive-case facts beyond `EvalEntry`

Everything `blockB_unary`/`blockC_neg` demand that the leaf `EvalEntry` structure
does not carry. `gpre` is the call-point ghost register file (the frame at the
`jal eval_expr`), `aIn` the live `interp*` in `x11`, `aOperand` the operand node
address, `esub` the operand expression. These are the "ArmEntryK widening"
residual (memory `m4-recursive-cases.md` #1) plus `blockC_neg`'s entry-ghost
bridge; a future `blockA_k` widening + full stack-layout derivation discharges
them. -/
structure NegExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (st : Vsa.While.St) (esub : Expr)
    (sp sret aExpr aOperand : BitVec 64)
    (m0 : Mem) : Prop where
  -- ===== EX_UNARY jump-table slot pin (static image fact) =====
  slot8 : KindSlotPinned 8 (0x800035e0#64) m0
  -- the whole `.unary .neg esub` node (AST subtree) survives any memory change
  -- confined to the stack window `[SL.lo, sp)` (the prologue spills). The AST is
  -- disjoint from the C stack, but a generic `ExprRepr`-survival lemma over an
  -- arbitrary sub-tree is not available, so it is threaded here (residual #1).
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.unary .neg esub)
  -- ===== operand-node geometry (the ArmEntryK/EvalEntry widening residual) =====
  pay : read64 m0 (aExpr.toNat + 16) = some aOperand.toNat
  operand_repr : ExprRepr m0 aOperand.toNat esub
  expr24 : aExpr.toNat + 24 ≤ 0x100000000
  -- the WHOLE 24-byte unary node is disjoint from the scribbled stack window
  -- (`EvalEntry.expr_stack_disjoint` only covers the 16-byte leaf slot).
  expr24_stk : aExpr.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  op_align : aOperand.toNat % 8 = 0
  op_lo : 0x80000000 ≤ aOperand.toNat
  op_hi : aOperand.toNat + 16 ≤ 0x100000000
  op_win : tohostAddr + 16 ≤ aOperand.toNat
  op_stk : aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat
  sp_headroom : SL.lo + 3264 ≤ sp.toNat
  sp_SLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhi_ram : SL.hi ≤ 0x100000000
  code_stk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  vicode_stk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  -- covers BOTH the dispatch slot 8 `[0x80019f78, +4)` (read by `blockA_k`) and
  -- the table base `[0x80019f58, +4)` (needed by `blockB_unary`).
  table_stk : (0x80019f84 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  -- ===== blockC_neg extras (op-token geometry) =====
  expr_align4 : aExpr.toNat % 4 = 0
  expr_win8 : tohostAddr + 8 ≤ aExpr.toNat
  expr_A : aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_sub : aExpr.toNat + 16 ≤ sp.toNat - 944 ∨ sp.toNat - 944 + 24 ≤ aExpr.toNat
  vi_arena : A.hi ≤ 0x8000280c ∨ 0x8000281c ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi

/-! ## `EvalNegSimGoal` — the `EvalE.neg` projection of the simulation

In the `EvalIH` motive shape (`EvalEntry → EvalExitD`, mirroring
`Scaffold.motive_EvalE` with `EvalExit` upgraded), taking the sub-derivation's
induction hypothesis `EvalIH st d env esub st' (.int n)`.

Conditional ONLY on:
* `NegExtras` — the operand-node `ExprRepr`+geometry, the extra 1088-byte
  recursive stack headroom, the arena/code/table disjunctions and the `EX_UNARY`
  slot pin (residual #1, program-structure facts an `EvalEntry` widening supplies);
* `hMcallPop` — the pre-call memory is fully populated (residual #3, M6 Layout).

The arm-register facts (`x11 = interp*`, the call-point ghost bridge) and the
`EvalExitD` upgrade are now DISCHARGED internally from the widened
`ArmEntryK`/`blockC_neg`/`blockD_v_rec` machinery. -/
def EvalNegSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (n : Int)
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem),
    EvalIH st d env esub st' (.int n) →
    EvalE st d env (.unary .neg esub) st' (.int (wrap64 (-n))) →
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv aExpr m0 c ∧
        NegExtras N A SL st esub sp sret aExpr aOperand m0 ∧
        -- Layout residuals (M6): WAVE 47i (`McallPopTotality` amendment) — the
        -- pre-recursive-call memory is populated ONLY on the actual dead-byte
        -- read footprint (the lowered-frame window `[sp-1120, sp)` holding the
        -- sub-`Value` padding `[subsret+4,+8) ∪ [subsret+16,+24)`, plus the
        -- node line-word `[aExpr+4, aExpr+8)`), and presence-extends `m0`.
        -- The old total-population oracle is REFUTED
        -- (`experiments/fleet/obstructions/McallPopTotality.lean`).
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          ∀ a : Nat,
            (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
              (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
            (∃ b, mcall[a]? = some b)) ∧
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          MemExtends m0 mcall))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.int (wrap64 (-n))) sp r sret m0)

/-- `read32 m aExpr = some 8` from `ExprRepr m aExpr (.unary op esub)`. -/
theorem exprRepr_unary_kind {m : Mem} {a : Nat} {op : UnOp} {esub : Expr}
    (h : ExprRepr m a (.unary op esub)) : read32 m a = some 8 := by
  cases h with | unary hk _ _ _ => exact hk

/-- `IntSlotPinned` (four `.rodata` byte pins at `[jumpTableBase, +4)`) survives a
disjoint 8-byte store. -/
theorem intSlot_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ jumpTableBase ∨ jumpTableBase + 4 ≤ a8) (h : IntSlotPinned mem) :
    IntSlotPinned (writeMap8 mem a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; assumption)

/-- Transport an `EvalExit` along a `PhiExtends` on both maps: an exit witnessed
at the extended maps `φfe`/`φce` is also an exit at the entry maps `φf`/`φc`, by
composing the `PhiExtends` prefixes in the `result`/`store` existentials (every
other `EvalExit` field is φ-independent). -/
theorem evalExit_of_phiExtends
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φfe φce : Addr → Nat}
    {nf nc nf' nc' : Nat}
    {st' : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hpfe : PhiExtends φf φfe nf)
    (hpce : PhiExtends φc φce nc)
    (h : EvalExit g N A SL φfe φce nf' nc' st' v sp r sret m0 c)
    (hmf : nf ≤ nf') (hmc : nc ≤ nc') :
    EvalExit g N A SL φf φc nf nc st' v sp r sret m0 c := by
  obtain ⟨φc1, hpc1, hval⟩ := h.result
  obtain ⟨φf2, φc2, hpf2, hpc2, hstore⟩ := h.store
  exact
    { good := h.good, tick := h.tick, pc := h.pc, a0 := h.a0, ra := h.ra,
      spReg := h.spReg, minstret := h.minstret, out := h.out, frame := h.frame,
      memFrame := h.memFrame
      result := ⟨φc1, hpce.trans (PhiExtends.mono hmc hpc1), hval⟩
      store := ⟨φf2, φc2, hpfe.trans (PhiExtends.mono hmf hpf2),
        hpce.trans (PhiExtends.mono hmc hpc2), hstore⟩ }

/-- **`evalNegSim`**: the `EvalE.neg` (EX_UNARY, negation) recursive case of the
simulation, in the `EvalIH` motive shape. Composes `blockA_k` (prologue+dispatch
→ widened `ArmEntryK`), `blockB_unary` (arm head + recursive call ⋈ IH →
`SubEvalReturn`), `blockC_neg` (post-call neg tail → `PreEpilogueVD .int(wrap64 -n)`),
and `blockD_v_rec` (shared epilogue → `EvalExitD`).

The arm-register facts and the entry-ghost bridge are discharged by taking the
call-point ghost `gpre := c1.σ.regs.get?` (frame is `rfl`) and reading `x11`/`x8`/
`x18` off the widened `ArmEntryK`; the `EvalExitD` upgrade is discharged by
`blockC_neg`'s `PreEpilogueVD` + `blockD_v_rec`. Conditional ONLY on `NegExtras`
(residual #1) and `hMcallPop` (residual #3). -/
theorem evalNegSim : EvalNegSimGoal := by
  intro g N A SL φf φc st st' d env esub n sp r sret aEnv aExpr aOperand
    m0 hIH _hEvalE
  intro c ⟨hc, hx, hFramePop, hMemExtRes⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0 ===
  have hkm0 : read32 m0 aExpr.toNat = some 8 := exprRepr_unary_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, v13c1, hArm, _hpresM, hx13c1⟩ :=
    blockA_k g N A SL φf φc st (.unary .neg esub) 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl, hnb⟩ := hcl
        have hvicodeD := hc.vicode_stack_disjoint
        have htableD := hc.table_stack_disjoint
        refine ⟨loaded_int_writeMap8 mem a8 dd (by omega) hvi, ?_, ?_⟩
        · exact intSlot_writeMap8 mem a8 dd (by simp only [jumpTableBase]; omega) hsl
        · exact nbsPins_writeMap8 mem a8 dd (by omega) (by omega) hnb)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.x13_defined⟩⟩, rfl⟩
  -- destructure a COPY of the widened `ArmEntryK` (keeping `hArm` intact for
  -- `blockB_unary`): the last three fields `hAEx11`/`hAEx8`/`hAEx18` are the NEW
  -- call-point register facts; `hArmg8/9/18/2` the entry ghost; `hArmMemM0` the
  -- stack-window memframe; `hArmFrame` the entry-ghost frame.
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  -- the call-point ghost `gpre := fun R => c1.σ.regs.get? R` — the frame is then
  -- definitional (`rfl`), and `x11`/`x8`/`x18` come off the widened `ArmEntryK`.
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  -- entry-ghost bridge `∀R AbiPresNoise off-excl → gpre R = g R` = `ArmEntryK` frame.
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  -- `ment ↔ m0` outside the stack window (from `ArmEntryK`'s memframe)
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  -- transport `pay`/`operand_repr` from `m0` to `ment` (AST disjoint from stack)
  have hExprMent : ExprRepr ment aExpr.toNat (.unary .neg esub) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (unOpTok .neg) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  -- the operand pointer read at `ment` equals `aOperand` (same as at `m0`)
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some aOperand.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aOperand.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hpeq : p = aOperand.toNat := by
    have := hpayMent.symm.trans hpayMent'; exact Option.some.inj this
  subst hpeq
  have hOperandReprMent : ExprRepr ment aOperand.toNat esub := hsubReprMent
  -- WAVE 47i: the child's entry-ground bundle from `hc.ground` (ONE kit call).
  have hsp1088N : 1088 ≤ sp.toNat := by
    have := hx.sp_headroom; have := hc.stack_ram.1; omega
  have hspsubN : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsubsretN : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat
      = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088N
  have hgroundChild : EvalGround ment SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aOperand.toNat esub :=
    (hc.mem ▸ hc.ground).child_at
      (fun lo hi hin => exprIn_unary_child hin aOperand.toNat hpayMent')
      hMentM0 hc.table_stack_disjoint hx.sp_SLhi
      (by omega)
      (by rw [hsubsretN]; have := hx.sp_headroom; have := hc.stack_ram.1; omega)
      (by rw [hsubsretN]; omega)
  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec ===
  obtain ⟨c2, hs2, hSub⟩ :=
    blockB_unary g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .neg esub (.int n)
      sp r sret aExpr aEnv aOperand v8 v9 v18 c.σ.sailOutput m0 hIH
      c1 ⟨ment, hArm, hx11c1, ⟨v13c1, hx13c1⟩, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hpayMent', hOperandReprMent, hgroundChild, hx.expr24,
        hx.op_align, hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega), hx.arena_stk, hx.arena_code,
        -- ITEM ZERO B1: the operand's child budget, DERIVED from the entry's
        -- budgeted fields (`StackOK.child` + the `.unary` pass-through).
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.unary UnOp.neg esub).stackNeed
                = evalFrame + esub.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            simp only [h1, h2, evalFrame]; omega),
        Expr.bodiesBound_unary hc.expr_bodies,
        hc.store_bodies⟩
  -- unpack blockB's output: the pre-call memory `mcall`, the SubEvalReturn, and
  -- the `mcall ↔ m0` frame outside the stack window.
  obtain ⟨mcall, hSubR, hMcallM0stk⟩ := hSub
  -- `mcall` agrees with `m0` outside the stack window `[SL.lo, sp)`.
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  -- OutRepr at c2 (the sub-call preserves the console-output correspondence)
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  -- `Value_intLoaded mcall` (from `m0`, agreement on `value_int`'s code region,
  -- which is disjoint from the scribbled stack window).
  have hVintM0 : Value_intLoaded m0 := hc.mem ▸ hc.value_int_code
  have hVintMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hc.vicode_stack_disjoint; omega)).symm) hVintM0
  -- `mcall ↔ m0` outside stack ∪ arena (blockC's `hMcallM0`)
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  -- the stack-populated fact for `mcall` (Layout residual)
  have hStackPop : ∀ a : Nat,
      (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
        (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
      ∃ b, mcall[a]? = some b := hFramePop mcall hAgM0
  have hMemExtM0mc : MemExtends m0 mcall := hMemExtRes mcall hAgM0
  -- `ExprRepr mcall aExpr (.unary .neg esub)` (AST survives the stack scribble)
  have hExprMcall : ExprRepr mcall aExpr.toNat (.unary .neg esub) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  -- === block C: post-call neg tail → PreEpilogueV .int(wrap64 -n) @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD⟩ :=
    blockC_neg (fun R => c1.σ.regs.get? R) g N A SL φf φc
      st.store.frames.size st.store.closures.size
      st' n sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0
      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hStackPop, hMemExtM0mc,
        hx.expr_align4, hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_vicode_disjoint_int, hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVintMcall, hx.code_stk, (by have := hx.vicode_stk; omega), hx.vi_arena,
        hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge⟩
  · -- === block D: shared epilogue → EvalExitD .int(wrap64 -n) (via blockD_v_rec) ===
    obtain ⟨c4, hs4, hExitDe⟩ :=
      blockD_v_rec g N A SL φfe φce st' (.int (wrap64 (-n))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
        c3 ⟨mpreC, hPreD⟩
    -- transport the widened exit back to the entry maps φf/φc (the goal's maps)
    obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
    have hStoreLe := evalE_store_mono _hEvalE
    have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.int (wrap64 (-n))) sp r sret m0 c4 :=
      evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
    exact ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hExit, hMemExt,
      φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
      hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

end Vsa.Sim
