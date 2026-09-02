import Vsa.Sim.EvalBinSim
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalIntSim2

/-!
# `BinArmBridge` — the EX_BINARY arm entry bridge (`blockA_binaryArm`)

The single missing link for all 10 binary-op table rows.  The landed
`eval<Op>Sim` theorems (`evalAddSim`/`evalSubSim`/…/`evalEqNeSim`) start from the
`ArmEntryK`-∃ entry with `blockA_k` **factored out**; feeding them from the
recursor premise `hBinary` requires the arm bridge

```
EvalEntry (.binary op el er)  →  (the `blockB_binary`/`eval<Op>Sim` entry
                                  ∃ ment, ArmEntryK@0x800034e8 ∧ BinExtras ∧ …)
```

i.e. the EX_BINARY arm of `eval_expr`'s kind-dispatch (`ExprKind` tag `k = 6`,
jump-table slot `0x80019f70` → arm PC `0x800034e8`).  This is **one** proof
serving all 10 ops: the span from the `eval_expr` entry to the two-operand head
`0x800034e8` is entirely operator-INDEPENDENT (the operator token is not even
read until `0x8000351c`, after both recursive calls).

The proof is `evalNegSim`'s block-A pattern (`EvalNegSim3.lean`) transposed to
the binary node: run `blockA_k` with `(k := 6, armPC := 0x800034e8,
e := .binary op el er, calleeLoaded := UnaryArmCallee)`, then repackage its
`ArmEntryK` output with the binary-arm `BinExtras` + register/repr conjuncts that
`blockB_binary` consumes.  The `gpre` call-point ghost is taken `:= c1.σ.regs.get?`
(so the frame is `rfl`) and `x11`/`x8`/`x18`/`x19` are read off the widened
`ArmEntryK`; the two operand pointers + their `ExprRepr` are peeled from the
node's `ExprRepr ment aExpr (.binary op el er)` (`ExprRepr.binary`, offsets 16/24).

Conditional (like `NegExtras`) only on the geometry residuals bundled as
`BinArmExtras` — the tag-6 slot pin, the two-operand geometry, the deep-recursion
headroom, and the AST-survival + memory-population closures that an M6 Layout /
`EvalCaseGeom` widening supplies.

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

/-! ## `BinArmExtras` — the binary-arm facts beyond `EvalEntry`

The `NegExtras` analogue for the two-operand arm.  Everything `blockA_k`'s
dispatch + `blockB_binary`'s head demand that the shared `EvalEntry` structure
does not already carry, stated over the entry memory `m0` (so it can be threaded
by an `EvalCaseGeom` widening / M6 Layout).  `aLOp`/`aROp` are the two operand
node addresses; the survival closures transport `ExprRepr`/population across the
prologue spills into the arm-entry memory `ment`. -/
structure BinArmExtras
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (op : BinOp) (el er : Expr)
    (sp r sret aExpr aLOp aROp : BitVec 64)
    (m0 : Mem) : Prop where
  -- ===== EX_BINARY jump-table slot pin (static image fact, tag 6 → 0x800034e8) =====
  slot6 : KindSlotPinned 6 (0x800034e8#64) m0
  -- the whole `.binary op el er` node (AST subtree) survives any memory change
  -- confined to the stack window `[SL.lo, sp)` (the prologue spills).
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.binary op el er)
  -- ===== the two operand-pointer words, read off the node at the ENTRY memory
  -- `m0` (the `NegExtras.pay` analogue; identifies the node's `l`/`r` fields with
  -- the operand nodes named `aLOp`/`aROp`). =====
  pay_l : read64 m0 (aExpr.toNat + 16) = some aLOp.toNat
  pay_r : read64 m0 (aExpr.toNat + 24) = some aROp.toNat
  -- the whole 32-byte node is disjoint from the scribbled stack window (needed to
  -- transport the two pointer reads from `m0` to the arm-entry `ment`).
  expr32_stk : aExpr.toNat + 32 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  -- ===== LEFT-operand geometry (BinExtras.lop_*) =====
  lop_align : aLOp.toNat % 8 = 0
  lop_ram : 0x80000000 ≤ aLOp.toNat ∧ aLOp.toNat + 16 ≤ 0x100000000
  lop_win : tohostAddr + 16 ≤ aLOp.toNat
  lop_stk : aLOp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLOp.toNat
  lexpr_surv : ∀ m : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m0[k]? = m[k]?) → ExprRepr m aLOp.toNat el
  -- ===== RIGHT-operand geometry (BinExtras.rop_*) =====
  rop_align : aROp.toNat % 8 = 0
  rop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000
  rop_win : tohostAddr + 16 ≤ aROp.toNat
  rop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat
  rop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat
  rop_arena : aROp.toNat + 16 ≤ A.lo ∨ A.hi ≤ aROp.toNat
  rexpr_surv : ∀ m : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) → m0[k]? = m[k]?) →
    ExprRepr m aROp.toNat er
  -- ===== node geometry (BinExtras.node_*) =====
  node_hi : aExpr.toNat + 32 ≤ 0x100000000
  node_stk : aExpr.toNat + 32 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  node_arena : aExpr.toNat + 32 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  -- ===== deep recursive headroom + alignment + bounds (BinExtras) =====
  sproom : SL.lo + 4352 ≤ sp.toNat
  spSLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  -- covers BOTH the EX_BINARY dispatch slot 6 `[0x80019f58 + 24, +4)` (read by
  -- `blockA_k`'s `jr`) and the table base `[0x80019f58, +4)` (read by `blockB_binary`).
  tableStk : (0x80019f58 : Nat) + 28 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  arenaVi : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
  arenaTable : A.hi ≤ 0x80019f58 ∨ 0x80019f58 + 44 ≤ A.lo
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  -- WAVE 48k: the `frame_pop` field is DELETED, not supplied.  It demanded HASHMAP
  -- PRESENCE on `[sp-1120, sp)` — the callee's own, as-yet-unwritten entry frame —
  -- and was machine-refuted as an entry premise
  -- (`experiments/fleet/obstructions/FramePopRamTotalityVerdict48j.lean`).  The
  -- load layer now consumes the model's TOTAL read (`readByte = getD 0`), so the
  -- dead reloads over that window need nothing at all.  Five waves (48e-48j) tried
  -- to supply this field; the right move was to remove the demand.
  -- ===== ghost-frame presence of `s3`(x19): the outer `g` has a live `x19` (a
  -- callee-saved register that `blockA_k`'s frame ties `c1.regs x19 = g x19` to).
  -- `EvalEntry.spill_defined` only covers `s0`/`s1`/`s2`, so `x19` is threaded here. =====
  gx19_pres : ∃ w, g Register.x19 = some w
  -- WAVE 48i (CURE 3): the `x13_pres` machine-liveness ∀-closure was DROPPED — it is
  -- now DISCHARGED intrinsically by `blockA_k`'s 3rd output (`c1.regs x13 = some v13`,
  -- the CURE-A x13 σ1..σ19 thread), so `blockA_binaryArm` no longer needs the closure.
  -- WAVE 48f: the `mem_ext : ∀m … → MemExtends m0 m` closure was DROPPED — it is
  -- over-quantified and machine-REFUTED as stated
  -- (`experiments/fleet/obstructions/BinArmExtrasMemExtOverquant.lean`), AND it is
  -- REDUNDANT: `blockA_k` already produces the concrete `MemExtends m0 ment`
  -- intrinsically (its 2nd output `_hpresM`, `EvalIntSim2.lean:326`).
  -- `blockA_binaryArm` now threads that concrete fact instead of this closure.

/-! ## `blockA_binaryArm` — the EX_BINARY arm entry bridge

`EvalEntry (.binary op el er) → the `blockB_binary` entry`.  The op-independent
prologue+dispatch multiplier for the whole binary-op family: composes with any of
the 10 `eval<Op>Sim` (all of which START from exactly this entry).  The remaining
`eval<Op>Sim` conjuncts NOT produced here (the op-specific `∀c' TwoSubReturn →
<Op>Resid` post-dispatch slot and the outer `g`-bridge) are the row-level
residuals that thread THROUGH this bridge to `eval<Op>Sim` unchanged. -/
theorem blockA_binaryArm
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (op : BinOp) (el er : Expr)
    (sp r sret aEnv aExpr aLOp aROp : BitVec 64)
    (m0 : Mem)
    (hX : BinArmExtras g N A SL op el er sp r sret aExpr aLOp aROp m0) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.binary op el er) sp r sret aEnv aExpr m0 c)
      (fun c => ∃ (gpre : (R : Register) → Option (RegisterType R))
          (aEnvReg v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ArmEntryK g N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry
        -- (derived HERE from `hc.ground` — the bridge owns the `EvalEntry`).
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er)) := by
  intro c hc
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- `read32 m0 aExpr = some 6` (EX_BINARY tag) from the node's `ExprRepr`.
  have hkm0 : read32 m0 aExpr.toNat = some 6 := by
    have := hc.mem ▸ hc.expr
    cases this with | binary hk _ _ _ _ _ => exact hk
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800034e8 ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, v13, hArm, hpresM, hx13out⟩ :=
    blockA_k g N A SL φf φc st (.binary op el er) 6 (0x800034e8#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hX.slot6
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot, hc.mem ▸ hc.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl, hnb⟩ := hcl
        refine ⟨loaded_int_writeMap8 mem a8 dd (by
          have := hc.vicode_stack_disjoint; omega) hvi, ?_, ?_⟩
        · exact intSlot_writeMap8 mem a8 dd (by
            have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega) hsl
        · exact nbsPins_writeMap8 mem a8 dd
            (by have := hc.vicode_stack_disjoint; omega)
            (by have := hc.table_stack_disjoint; omega) hnb)
      (fun m' hag => hX.expr_survives m' hag)
      (by decide)
      (by have := hX.tableStk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.x13_defined⟩⟩, rfl⟩
  -- Destructure a COPY of the widened `ArmEntryK` (keep `hArm` intact for output).
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    _hArmg8, _hArmg9, _hArmg18, _hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  -- The call-point ghost `gpre := c1.σ.regs.get?` (inlined in the refine below).
  -- `ment ↔ m0` outside the stack window (from the widened `ArmEntryK` memframe).
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  -- Transport the node's `ExprRepr` from `m0` to `ment`.
  have hExprMent : ExprRepr ment aExpr.toNat (.binary op el er) :=
    hX.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  -- Peel the two operand pointers + sub-`ExprRepr` from the `.binary` node.
  obtain ⟨lp, rp, hkb, htokb, hlpb, hlReprMent, hrpb, hrReprMent⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 6 ∧
      read32 ment (aExpr.toNat + 8) = some (binOpTok op) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with
    | binary hk htok hl hle hr hre => exact ⟨_, _, hk, htok, hl, hle, hr, hre⟩
  -- `AgreeP` witness: `ment` and `m0` agree outside the scribbled stack window.
  have hAgP : AgreeP (fun a => ¬ (SL.lo ≤ a ∧ a < sp.toNat)) ment m0 := hMentM0
  -- Transport the two operand-pointer reads from `m0` (the extras' `pay_l`/`pay_r`)
  -- to `ment` (the whole 32-byte node is disjoint from the stack window).
  have hpayLment : read64 ment (aExpr.toNat + 16) = some aLOp.toNat := by
    rw [read64_agreeP hAgP (fun k hk => by rcases hX.expr32_stk with h | h <;> omega)]
    exact hX.pay_l
  have hpayRment : read64 ment (aExpr.toNat + 24) = some aROp.toNat := by
    rw [read64_agreeP hAgP (fun k hk => by rcases hX.expr32_stk with h | h <;> omega)]
    exact hX.pay_r
  -- Identify the node's peeled operand pointers `lp`/`rp` with `aLOp`/`aROp`.
  have hlpEq : lp = aLOp.toNat := Option.some.inj (hlpb.symm.trans hpayLment)
  have hrpEq : rp = aROp.toNat := Option.some.inj (hrpb.symm.trans hpayRment)
  subst hlpEq; subst hrpEq
  -- Now `hlReprMent : ExprRepr ment aLOp.toNat el` and likewise for `er`.
  -- Assemble the `BinExtras` record from the `BinArmExtras` geometry.
  have hBE : BinExtras N A SL el er ment sp sret aExpr aLOp aROp :=
    { lop_align := hX.lop_align, lop_ram := hX.lop_ram, lop_win := hX.lop_win,
      lop_stk := hX.lop_stk
      lexpr_surv := fun m hm => hX.lexpr_surv m (fun k hk =>
        (hMentM0 k (by have := hX.spSLhi; omega)).symm.trans (hm k hk))
      rop_align := hX.rop_align, rop_ram := hX.rop_ram, rop_win := hX.rop_win,
      rop_stk := hX.rop_stk, rop_stkfull := hX.rop_stkfull, rop_arena := hX.rop_arena
      rexpr_surv := fun m hm => hX.rexpr_surv m (fun k hk hk' =>
        (hMentM0 k (by have := hX.spSLhi; omega)).symm.trans (hm k hk hk'))
      node_hi := hX.node_hi, node_stk := hX.node_stk, node_arena := hX.node_arena
      sproom := hX.sproom, spSLhi := hX.spSLhi, sp16 := hX.sp16, SLhiRam := hX.SLhiRam
      codeStk := hX.codeStk, viStk := hX.viStk,
      tableStk := hX.tableStk.imp (fun h => by omega) (fun h => h)
      arenaStk := hX.arenaStk, arenaCode := hX.arenaCode, arenaVi := hX.arenaVi,
      arenaTable := hX.arenaTable, sret_inSL := hX.sret_inSL }
  -- `MemExtends m0 ment`: the prologue spills are memory inserts, so `ment`
  -- presence-extends `m0` — WAVE 48f: taken DIRECTLY from `blockA_k`'s intrinsic
  -- 2nd output `hpresM` (the dropped `mem_ext` closure was redundant with this).
  have hMemExt : MemExtends m0 ment := hpresM
  -- `x19` (s3) is callee-saved (`AbiPreservedNoise`, ∉ {x8,x9,x18,x2}), so
  -- `blockA_k`'s frame gives `c1.regs x19 = g x19`; presence follows from the
  -- ghost-frame presence fact `hX.gx19_pres`.
  obtain ⟨v19, hgx19⟩ := hX.gx19_pres
  have hx19c1 : c1.σ.regs.get? Register.x19 = some v19 := by
    rw [hArmFrame Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hgx19
  -- `x13` (a3, a caller-save temp) is NOT preserved/exposed by `blockA_k`'s frame.
  -- WAVE 48i (CURE 3): its arm-entry presence is now the blockA_k 3rd output
  -- `hx13out : c1.regs x13 = some v13` (CURE A threaded x13 σ1..σ19), DISCHARGING
  -- what the dropped `x13_pres` ∀-closure used to supply.  Bound as `aEnvReg := v13`.
  have hx13c1 : c1.σ.regs.get? Register.x13 = some v13 := hx13out
  -- Realign the ArmEntryK `out0` from the passed `c.σ.sailOutput` to the goal's
  -- `c1.σ.sailOutput` (equal by the blockA_k output invariant `_hAout`).
  have hArm' : ArmEntryK g N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
      sp r sret aExpr aEnv v8 v9 v18 c1.σ.sailOutput m0 ment c1 := _hAout.symm ▸ hArm
  refine ⟨c1, hs1, (fun R => c1.σ.regs.get? R), v13, v8, v9, v18, v19, ment, hArm', hBE,
    hAEx11, hx13c1, hx19c1, (fun R _ => rfl), ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩, hAEx8, hAEx18,
    hx19c1, hpayLment, hlReprMent, hpayRment, hrReprMent, hMemExt,
    (hc.mem ▸ hc.ground).transport_offstack hc.table_stack_disjoint hX.spSLhi hMentM0⟩

/-- **`blockA_binaryArm_budgeted`** — `blockA_binaryArm` with the ITEM ZERO B1
budget conjuncts APPENDED to its post (the amended `blockB_binary` pre-tail).
The five entry-derivable conjuncts (both children's `StackOK.child` steps, both
`bodiesBound` projections, the LEFT store-bodies) are DERIVED from the
`EvalEntry`'s budgeted fields here, ONCE; the post-LEFT store-bodies
(`st'`-dependent, spec-side preservation) is the single threaded premise.
This is the ONE named destructurer/repacker beside `blockA_binaryArm`'s
∃/∧-tower post — consumers marshal through it, never by positional splits. -/
theorem blockA_binaryArm_budgeted
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (op : BinOp) (el er : Expr)
    (sp r sret aEnv aExpr aLOp aROp : BitVec 64)
    (m0 : Mem)
    (hX : BinArmExtras g N A SL op el er sp r sret aExpr aLOp aROp m0)
    (hstoreBodiesR : Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget) :
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.binary op el er) sp r sret aEnv aExpr m0 c)
      (fun c => ∃ (gpre : (R : Register) → Option (RegisterType R))
          (aEnvReg v8 v9 v18 v19 : BitVec 64) (ment : Mem),
        ArmEntryK g N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle (pass-through).
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget) := by
  intro c hc
  obtain ⟨c1, hs1, gpre, aEnvReg, v8, v9, v18, v19, ment, hArm, hBX,
    hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt⟩ :=
    blockA_binaryArm g N A SL φf φc st d env op el er sp r sret aEnv aExpr aLOp aROp m0 hX c hc
  have h1 : (Expr.binary op el er).stackNeed
      = evalFrame + max el.stackNeed er.stackNeed := rfl
  have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
  exact ⟨c1, hs1, gpre, aEnvReg, v8, v9, v18, v19, ment, hArm, hBX,
    hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hc.stackBudget.child (by decide)
      (by have hm := Nat.le_max_left el.stackNeed er.stackNeed
          simp only [h1, h2, evalFrame]; omega),
    (Expr.bodiesBound_binary hc.expr_bodies).1,
    hc.store_bodies,
    hc.stackBudget.child (by decide)
      (by have hm := Nat.le_max_right el.stackNeed er.stackNeed
          simp only [h1, h2, evalFrame]; omega),
    (Expr.bodiesBound_binary hc.expr_bodies).2,
    hstoreBodiesR⟩

#print axioms blockA_binaryArm_budgeted
