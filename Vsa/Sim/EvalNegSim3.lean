import Vsa.Sim.EvalNegSim2
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

`blockA_k` produces `ArmEntryK`, but `blockB_unary` and `blockC_neg` need facts
BEYOND the leaf `EvalEntry` structure carries (the "ArmEntryK widening residual",
memory `m4-recursive-cases.md` #1): the live `a1 = interp*`, the call-point ghost
frame `gpre`, the operand node's `ExprRepr` + geometry, the extra 1088-byte
recursive stack headroom, the entry-ghost bridge, and the arena/code/table
disjointness facts. These are collected in the `NegExtras` bundle below and taken
as an explicit hypothesis, exactly as `evalVarSim` is conditional on
`env_get_found`. `blockD_v` produces `EvalExit`; the recursive motive needs
`EvalExitD` (`= EvalExit + MemExtends m0 mem + [SL.lo,SL.hi)`-survival, residual
#2); the two upgrade clauses are taken as `hMemExt`/`hSurvSL` witnesses at the
produced exit configuration.

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
    (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (esub : Expr)
    (sp r sret aExpr aEnv aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  -- ===== EX_UNARY jump-table slot pin (static image fact) =====
  slot8 : KindSlotPinned 8 (0x800035e0#64) m0
  -- the whole `.unary .neg esub` node (AST subtree) survives any memory change
  -- confined to the stack window `[SL.lo, sp)` (the prologue spills). The AST is
  -- disjoint from the C stack, but a generic `ExprRepr`-survival lemma over an
  -- arbitrary sub-tree is not available, so it is threaded here (residual #1).
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.unary .neg esub)
  -- ===== blockB_unary extras (the ArmEntryK widening residual) =====
  gpre_x8 : gpre Register.x8 = some aExpr
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
  vicode_stk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c
  -- covers BOTH the dispatch slot 8 `[0x80019f78, +4)` (read by `blockA_k`) and
  -- the table base `[0x80019f58, +4)` (needed by `blockB_unary`).
  table_stk : (0x80019f7c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  -- ===== blockC_neg extras (op-token geometry, entry-ghost bridge) =====
  expr_align4 : aExpr.toNat % 4 = 0
  expr_win8 : tohostAddr + 8 ≤ aExpr.toNat
  expr_A : aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_sub : aExpr.toNat + 16 ≤ sp.toNat - 944 ∨ sp.toNat - 944 + 24 ≤ aExpr.toNat
  vi_arena : A.hi ≤ 0x8000280c ∨ 0x8000281c ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  -- the ENTRY ghost `g` holds the spilled callee-saved values (restored by the
  -- epilogue) and agrees with `gpre` off s0/s1/s2/sp (the prologue bridge).
  g_x8 : g Register.x8 = some v8
  g_x9 : g Register.x9 = some v9
  g_x18 : g Register.x18 = some v18
  g_x2 : g Register.x2 = some sp
  bridge : ∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false →
    gpre R = g R

/-! ## `EvalNegSimGoal` — the `EvalE.neg` projection of the simulation

In the `EvalIH` motive shape (`EvalEntry → EvalExitD`, mirroring
`Scaffold.motive_EvalE` with `EvalExit` upgraded), taking the sub-derivation's
induction hypothesis `EvalIH st d env esub st' (.int n)`.

Conditional on:
* `NegExtras` — the recursive-case machine facts beyond `EvalEntry` (residual #1);
* `hMemExt`/`hSurvSL` — the `EvalExitD` presence/survival upgrade of the produced
  `EvalExit`, evaluated at the exit config (residual #2). These are stated as
  quantified upgrade obligations so the produced exit config feeds them. -/
def EvalNegSimGoal : Prop :=
  ∀ (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (n : Int)
    (sp r sret aEnv aExpr aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (m0 : Mem),
    EvalIH st d env esub st' (.int n) →
    EvalE st d env (.unary .neg esub) st' (.int (wrap64 (-n))) →
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.unary .neg esub) sp r sret aEnv aExpr m0 c ∧
        NegExtras g gpre N A SL φf φc st esub sp r sret aExpr aEnv aIn aOperand v8 v9 v18 m0 c ∧
        -- residual #1 (the `blockA_k`/`ArmEntryK` widening): at the arm-entry config
        -- `c1` (dispatch landing, `0x800035e0`), the live `a1 = interp*` and the
        -- call-point ghost frame `gpre` (which the current `ArmEntryK` does not
        -- expose). A widened `blockA_k` that threads `x11`/`x8`/`x18` through the
        -- prologue+dispatch discharges this.
        (∀ (c1 : Config) (ment : Mem),
          ArmEntryK g N A SL φf φc st (0x800035e0#64) UnaryArmCallee (.unary .neg esub)
            sp r sret aExpr v8 v9 v18 c.σ.sailOutput m0 ment c1 →
          c1.σ.regs.get? Register.x11 = some aIn ∧
          (∀ R : Register, AbiPreservedNoise R → c1.σ.regs.get? R = gpre R) ∧
          (∃ w, gpre Register.x18 = some w)) ∧
        -- Layout residual (M6): the pre-recursive-call memory (any memory agreeing
        -- with `m0` outside the scribbled stack window `[SL.lo, sp)`) is fully
        -- populated. `blockC_neg`'s dead-byte `ld`s of the sub-`Value` padding
        -- `[subsret+4,+8) ∪ [subsret+16,+24)` need this presence; it is discharged
        -- by the M6 stack-layout (`m0` populated everywhere, spills are inserts).
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          ∀ a : Nat, ∃ b, mcall[a]? = some b) ∧
        -- residual #2: the two `EvalExitD` upgrade witnesses, at the eventual exit
        -- config, are supplied as an obligation parameterized over any config whose
        -- memory dominates the entry's (produced by the tail's `writeMap8` inserts).
        (∀ c' : Config,
          EvalExit g N A SL φf φc st' (.int (wrap64 (-n))) sp r sret m0 c' →
          MemExtends m0 c'.σ.mem ∧
          ∃ φf' φc' : Addr → Nat,
            PhiExtends φf φf' st'.store.frames.size ∧
            PhiExtends φc φc' st'.store.closures.size ∧
            ∀ m' : Mem,
              (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c'.σ.mem[k]? = m'[k]?) →
              StoreRepr m' N A φf' φc' st'.store))
      (EvalExitD g N A SL φf φc st' (.int (wrap64 (-n))) sp r sret m0)

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
    {st' : Vsa.While.St} {v : Value} {sp r sret : BitVec 64} {m0 : Mem} {c : Config}
    (hpfe : PhiExtends φf φfe st'.store.frames.size)
    (hpce : PhiExtends φc φce st'.store.closures.size)
    (h : EvalExit g N A SL φfe φce st' v sp r sret m0 c) :
    EvalExit g N A SL φf φc st' v sp r sret m0 c := by
  obtain ⟨φc1, hpc1, hval⟩ := h.result
  obtain ⟨φf2, φc2, hpf2, hpc2, hstore⟩ := h.store
  exact
    { good := h.good, tick := h.tick, pc := h.pc, a0 := h.a0, ra := h.ra,
      spReg := h.spReg, minstret := h.minstret, out := h.out, frame := h.frame,
      memFrame := h.memFrame
      result := ⟨φc1, hpce.trans hpc1, hval⟩
      store := ⟨φf2, φc2, hpfe.trans hpf2, hpce.trans hpc2, hstore⟩ }

/-- **`evalNegSim`**: the `EvalE.neg` (EX_UNARY, negation) recursive case of the
simulation, in the `EvalIH` motive shape. Composes `blockA_k` (prologue+dispatch
→ `ArmEntryK`), `blockB_unary` (arm head + recursive call ⋈ IH → `SubEvalReturn`),
`blockC_neg` (post-call neg tail → `PreEpilogueV .int(wrap64 -n)`), and `blockD_v`
(shared epilogue → `EvalExit`), then upgrades to `EvalExitD` via the supplied
residual witness. Conditional on `NegExtras` (residual #1) and the exit-upgrade
obligation (residual #2). -/
theorem evalNegSim : EvalNegSimGoal := by
  intro g gpre N A SL φf φc st st' d env esub n sp r sret aEnv aExpr aIn aOperand
    v8 v9 v18 m0 hIH _hEvalE
  intro c ⟨hc, hx, hArmRegs, hMcallPop, hUpg⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → ArmEntryK @0x800035e0 (via blockA_k) ===
  have hkm0 : read32 m0 aExpr.toNat = some 8 := exprRepr_unary_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, w8, w9, w18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.unary .neg esub) 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl⟩ := hcl
        have hvicodeD := hc.vicode_stack_disjoint
        have htableD := hc.table_stack_disjoint
        refine ⟨loaded_int_writeMap8 mem a8 dd (by omega) hvi, ?_⟩
        exact intSlot_writeMap8 mem a8 dd (by simp only [jumpTableBase]; omega) hsl)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        hc.spill_defined⟩, rfl⟩
  -- blockA's spilled ghost values `w8/w9/w18` coincide with the `NegExtras`
  -- values `v8/v9/v18` (both are `g x{8,9,18}`).
  have hArmg8 : g Register.x8 = some w8 := hArm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hArmg9 : g Register.x9 = some w9 := hArm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hArmg18 : g Register.x18 = some w18 := hArm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw8 : v8 = w8 := by have := hx.g_x8.symm.trans hArmg8; exact Option.some.inj this
  have hw9 : v9 = w9 := by have := hx.g_x9.symm.trans hArmg9; exact Option.some.inj this
  have hw18 : v18 = w18 := by have := hx.g_x18.symm.trans hArmg18; exact Option.some.inj this
  subst hw8 hw9 hw18
  -- the arm-entry register facts (residual #1, discharged by `hArmRegs`)
  obtain ⟨hx11c1, hgpreframe, hgpre18⟩ := hArmRegs c1 ment hArm
  -- `ment ↔ m0` outside the stack window (from `ArmEntryK`'s memframe)
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? :=
    hArm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec ===
  obtain ⟨c2, hs2, hSub⟩ :=
    blockB_unary g gpre N A SL φf φc st st' d env .neg esub (.int n)
      sp r sret aExpr aIn aOperand v8 v9 v18 c.σ.sailOutput m0 hIH
      c1 ⟨ment, hArm, hx11c1, hgpreframe, ⟨aExpr, hx.gpre_x8⟩, hgpre18,
        hpayMent', hOperandReprMent, hx.expr24,
        hx.op_align, hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega), hx.arena_stk, hx.arena_code⟩
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
  have hStackPop : ∀ a : Nat, ∃ b, mcall[a]? = some b := hMcallPop mcall hAgM0
  -- `ExprRepr mcall aExpr (.unary .neg esub)` (AST survives the stack scribble)
  have hExprMcall : ExprRepr mcall aExpr.toNat (.unary .neg esub) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  -- === block C: post-call neg tail → PreEpilogueV .int(wrap64 -n) @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPre⟩ :=
    blockC_neg gpre g N A SL φf φc st' n sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0
      c2 ⟨mcall, hSubR, hx.gpre_x8, hExprMcall, hStackPop,
        hx.expr_align4, hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_vicode_disjoint, hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVintMcall, hx.code_stk, (by have := hx.vicode_stk; omega), hx.vi_arena,
        hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hx.g_x8, hx.g_x9, hx.g_x18, hx.g_x2, hx.bridge⟩
  · -- === block D: shared epilogue → EvalExit .int(wrap64 -n) ===
    obtain ⟨c4, hs4, hExitE⟩ :=
      blockD_v g N A SL φfe φce st' (.int (wrap64 (-n))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
        c3 ⟨mpreC, hPre⟩
    -- transport the exit back to the entry maps φf/φc (the goal's maps)
    have hExit : EvalExit g N A SL φf φc st' (.int (wrap64 (-n))) sp r sret m0 c4 :=
      evalExit_of_phiExtends hpfe hpce hExitE
    -- === upgrade EvalExit → EvalExitD via the supplied residual witness ===
    refine ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hExit, ?_⟩
    obtain ⟨hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hUpg c4 hExit
    exact ⟨hMemExt, φf', φc', hpf', hpc', hSurv⟩

end Vsa.Sim
