import Vsa.Sim.rows.BinArmBridge
import Vsa.Sim.ReprSurvival

/-!
# `ArmDispatchCombinator` — the ONE parametric eval arm-dispatch bridge (wave 44)

Group A of the `*ArmDispatch` residual class (`AssignArmDispatch` @
`rows/AssignArmStagePre.lean`, `CallArmDispatch` @ `rows/CallArmStagePre.lean`):
each demands the dispatch run `EvalEntry (kind e) → ` the arm-head entry bundle
(a widened `ArmEntryK` at the arm's jump-table landing PC plus child-payload /
survival / geometry conjuncts).  The machine content is `blockA_k`
(`EvalIntSim2.lean`) — landed, case-independent — so the ONLY honest residual is
the entry-side extras record `EvalArmHeadExtras` below (the `BinArmExtras`
pattern of `rows/BinArmBridge.lean`, single-child-arm shape).

`evalArmDispatch_of_slot` is the parametric combinator: for ANY
`(k, armPC, e, ce, payOff, nodeHi)` it runs `blockA_k` off the extras and
produces EXACTLY the Mid tower the `*ArmDispatch` defs quantify (α/defeq at each
instantiation — see `rows/ArmDispatchInstancesEval.lean`).

The one machine fact `blockA_k`'s statement drops is the liveness of `a3`(x13)
at the arm entry (the dispatch span `0x80003164 → armPC` never writes `a3`, but
`ArmEntryK`'s frame only covers callee-saved registers).  It stays the SAME
named closure `x13_pres` that `BinArmExtras` already carries — one shared
residual shape, not a per-arm variant.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
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

/-! ## `EvalArmHeadExtras` — the shared Group-A dispatch residual

Everything `blockA_k`'s dispatch + the arm-head Mid demand that `EvalEntry` does
not carry, stated over the ENTRY memory `m0` (threadable by an M6 Layout /
`EvalCaseGeom` widening).  The single-child specialization of `BinArmExtras`:
`aChild` is the arm's one payload pointer (the assign RHS node / the call callee
node), read off the node at `aExpr + payOff`; `nodeHi` is the node span consumed
by the arm (`24` for assign, `16` for call). -/
structure EvalArmHeadExtras
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (k : Nat) (armPC : BitVec 64) (e ce : Expr) (payOff nodeHi : Nat)
    (sp sret aExpr aChild : BitVec 64)
    (m0 : Mem) : Prop where
  /-- The tag-`k` jump-table slot pin (static image fact; `LayoutJumpTableGen`
  supplies it from the 4 rodata byte pins). -/
  slot : KindSlotPinned k armPC m0
  /-- The whole node's `ExprRepr` survives any change confined to the stack
  window (the prologue spills). -/
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat e
  /-- The child payload pointer, read off the node at the entry memory. -/
  pay : read64 m0 (aExpr.toNat + payOff) = some aChild.toNat
  /-- The child node's `ExprRepr` survives any change confined to the stack
  window. -/
  child_surv : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aChild.toNat ce
  node_hi : aExpr.toNat + nodeHi ≤ 0x100000000
  /-- The consumed node span is disjoint from the stack window (transports the
  payload read `m0 → ment`). -/
  node_stk : aExpr.toNat + nodeHi ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  child_align : aChild.toNat % 8 = 0
  child_lo : 0x80000000 ≤ aChild.toNat
  child_hi : aChild.toNat + 16 ≤ 0x100000000
  child_win : tohostAddr + 16 ≤ aChild.toNat
  child_stk : aChild.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aChild.toNat
  /-- WAVE 47i: the child's entry-ground bundle at the entry memory, PARENT
  windows (the supplier re-cuts `EvalEntry.ground` by `child_node`). -/
  ground : EvalGround m0 SL A sp sret aChild.toNat ce
  sproom : SL.lo + 3264 ≤ sp.toNat
  spSLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  /-- The tag-`k` jump-table slot is disjoint from the stack window (the
  `blockA_k` `jr` read). -/
  tableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k
  /-- The table BASE slot (slot 0) is disjoint from the stack window (the Mid's
  `IntSlotPinned`-shaped conjunct downstream arms re-read). -/
  tableStk0 : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  /-- Machine-liveness of `a3`(x13) at the arm entry: the dispatch span
  `0x80003164 → armPC` never writes `a3` (only `a4`/`a5` + the spills), so any
  config reached there with the arm-entry frame + PC has a live `x13`.  A
  caller-save temp NOT covered by `blockA_k`'s (callee-saved) frame — the ONE
  register-liveness residual a `blockA_k` widening (tracking `x13` across
  dispatch) would discharge.  Identical to `BinArmExtras.x13_pres`. -/
  x13_pres : ∀ c1 : Vsa.Machine.Config,
    (∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      c1.σ.regs.get? R = g R) →
    c1.σ.regs.get? Register.PC = some armPC →
    ∃ w, c1.σ.regs.get? Register.x13 = some w

/-! ## `evalArmDispatch_of_slot` — the parametric Group-A combinator

Runs `blockA_k` off the extras, then transports the child payload/repr across
the prologue spills and assembles the arm-head Mid tower the `*ArmDispatch`
residuals demand.  `gpre := c1.σ.regs.get?` (the reached frame — so the ghost
frame conjunct is `rfl`); `aIn := aEnv` (the untouched `a1`); `aEnv3` from the
`x13_pres` liveness closure. -/
theorem evalArmDispatch_of_slot
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (k : Nat) (armPC : BitVec 64) (e ce : Expr) (payOff nodeHi : Nat)
    (sp r0 sret aEnv aExpr aChild : BitVec 64) (m0 : Mem) (c : Config)
    (hkle : k ≤ 10) (hklt : k < 128) (harmAl : armPC.toNat % 4 = 0)
    (hpayHi : payOff + 8 ≤ nodeHi)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hX : EvalArmHeadExtras g N A SL k armPC e ce payOff nodeHi sp sret aExpr aChild m0)
    (hE : EvalEntry g N A SL φf φc st d env e sp r0 sret aEnv aExpr m0 c) :
    Triple (fun c'' => c'' = c)
      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))
        (aIn aCh aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64),
        ∃ ment,
        ArmEntryK g N A SL φf φc st armPC UnaryArmCallee e
          sp r0 sret aExpr aIn v8 v9 v18 c'.σ.sailOutput m0 ment c' ∧
        c'.σ.regs.get? Register.x11 = some aIn ∧
        c'.σ.regs.get? Register.x13 = some aEnv3 ∧
        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        read64 ment (aExpr.toNat + payOff) = some aCh.toNat ∧
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
          ExprRepr m' aCh.toNat ce) ∧
        -- WAVE 47i: the child's entry-ground bundle at the arm memory.
        EvalGround ment SL A sp sret aCh.toNat ce ∧
        aExpr.toNat + nodeHi ≤ 0x100000000 ∧
        aCh.toNat % 8 = 0 ∧
        0x80000000 ≤ aCh.toNat ∧ aCh.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aCh.toNat ∧
        (aCh.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aCh.toNat) ∧
        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
        ((0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)) := by
  intro c'' heq
  subst heq
  -- === block A: prologue + dispatch → widened ArmEntryK @armPC ===
  obtain ⟨c1, hs1, ment, v8, v9, v18, _v13, hArm, _hpresM, _hx13⟩ :=
    blockA_k g N A SL φf φc st e k armPC UnaryArmCallee
      sp r0 sret aEnv aExpr m0 c''.σ.sailOutput
      hkle hklt
      hkind
      hX.slot
      ⟨hE.mem ▸ hE.value_int_code, hE.mem ▸ hE.int_slot, hE.mem ▸ hE.nbs_pins⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl, hnb⟩ := hcl
        refine ⟨loaded_int_writeMap8 mem a8 dd (by
          have := hE.vicode_stack_disjoint; omega) hvi, ?_, ?_⟩
        · exact intSlot_writeMap8 mem a8 dd (by
            have := hE.table_stack_disjoint; simp only [jumpTableBase]; omega) hsl
        · exact nbsPins_writeMap8 mem a8 dd
            (by have := hE.vicode_stack_disjoint; omega)
            (by have := hE.table_stack_disjoint; omega) hnb)
      (fun m' hag => hX.expr_survives m' hag)
      harmAl
      hX.tableStk
      c'' ⟨⟨hE.good, hE.tick, hE.pc, hE.a0, hE.a1, hE.a2, hE.ra, hE.ra_align, hE.spReg,
        hE.stackOK, hE.minstret, hE.mem, hE.code, hE.expr, hE.store, hE.store_survives, hE.out,
        hE.frame, hE.code_stack_disjoint, hE.expr_stack_disjoint, hE.expr_align, hE.expr_ram,
        hE.expr_win, hE.sret_align, hE.sret_ram, hE.sret_win, hE.sret_vicode_disjoint_int,
        hE.sret_stack_disjoint, hE.sret_evalcode_disjoint, hE.stack_ram, hE.stack_win,
        ⟨hE.spill_defined.1, hE.spill_defined.2.1, hE.spill_defined.2.2, hE.x13_defined⟩⟩, rfl⟩
  -- Destructure a COPY of the widened `ArmEntryK` (keep `hArm` intact for output).
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    _hArmg8, _hArmg9, _hArmg18, _hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hAgP : AgreeP (fun a => ¬ (SL.lo ≤ a ∧ a < sp.toNat)) ment m0 := hMentM0
  -- Transport the payload read from `m0` (extras) to the arm-entry `ment`.
  have hpayMent : read64 ment (aExpr.toNat + payOff) = some aChild.toNat := by
    rw [read64_agreeP hAgP (fun kk hk => by rcases hX.node_stk with h | h <;> omega)]
    exact hX.pay
  -- The child survival at `ment`: compose the extras' `m0`-closure with the
  -- arm-entry memframe.
  have hchildSurvMent : ∀ m' : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →
      ExprRepr m' aChild.toNat ce :=
    fun m' hag => hX.child_surv m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))
  -- WAVE 47i: the child ground at `ment` (off-stack transport of the
  -- extras' PARENT-window bundle).
  have hGroundMent : EvalGround ment SL A sp sret aChild.toNat ce :=
    hX.ground.transport_offstack hX.tableStk0 hX.spSLhi hMentM0
  -- `x13` liveness at the reached arm entry (the named closure).
  obtain ⟨aEnv3, hx13c1⟩ := hX.x13_pres c1 hArmFrame _hApc
  -- Realign the ArmEntryK `out0` to the reached `c1.σ.sailOutput`.
  have hArm' : ArmEntryK g N A SL φf φc st armPC UnaryArmCallee e
      sp r0 sret aExpr aEnv v8 v9 v18 c1.σ.sailOutput m0 ment c1 := _hAout.symm ▸ hArm
  exact ⟨c1, hs1, (fun R => c1.σ.regs.get? R), aEnv, aChild, aEnv3, v8, v9, v18, ment,
    hArm', hAEx11, hx13c1, (fun R _ => rfl), ⟨aExpr, hAEx8⟩, ⟨aEnv, hAEx18⟩,
    hpayMent, hchildSurvMent, hGroundMent, hX.node_hi,
    hX.child_align, hX.child_lo, hX.child_hi, hX.child_win, hX.child_stk,
    hX.sproom, hX.spSLhi, hX.sp16, hX.SLhiRam,
    hX.codeStk, hX.viStk, hX.tableStk0, hX.arenaStk, hX.arenaCode⟩

#print axioms evalArmDispatch_of_slot

end Vsa.Sim
