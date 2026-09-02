import Vsa.Sim.EvalRecCommon
import Vsa.Sim.EntryGroundKit
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.BinHeadSites
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 RECURSIVE case: the two-operand head `blockB_binary`

The `EX_BINARY` arm of `eval_expr` (`ExprKind` tag `k = 6`, jump-table slot
bytes `90 95 fe ff` @ `0x80019f70`, arm PC `0x800034e8`). Unlike the unary
arm, it evaluates BOTH operands with two nested recursive `jal eval_expr`
calls before dispatching on the operator. Decoded machine path
(`experiments/pctrace.md` + objdump):

```
800034e8: ld   a2,16(a2)      -- a2 := e->left  (first operand ptr)
800034ec: addi a0,sp,120      -- a0 := sret_L = (sp-1088)+120 = sp-968
800034f0: sd   s3,1048(sp)    -- spill s3   → sp-40
800034f4: sd   a3,0(sp)       -- spill a3(env) → sp-1088
800034f8: jal  eval_expr      -- LEFT call; ra := 0x800034fc
-- post-left: --
800034fc: ld   a2,24(s0)      -- a2 := e->right (second operand ptr; s0 = node)
80003500: ld   a3,0(sp)       -- a3 := env (reload)
80003504: lw   a6,120(sp)     -- a6 := left-value low word (dead here; reload/respill)
80003508: addi a0,sp,144      -- a0 := sret_R = (sp-1088)+144 = sp-944
8000350c: mv   a1,s2          -- a1 := interp*
80003510: ld   s3,128(sp)     -- s3 := left-value payload (dead here)
80003514: sd   a6,0(sp)       -- respill a6 → sp-1088
80003518: jal  eval_expr      -- RIGHT call; ra := 0x8000351c
-- dispatch @0x8000351c on the operator token → add/sub/mul/…/cmp tails --
```

**`blockB_binary`** is the reusable TWO-operand head: from the dispatch landing
(`ArmEntryK` at `0x800034e8`, expression `.binary op l r`) plus the recursive
extras, it evaluates `l` (consuming `IH_l`, producing `vl` at `sp-968`) and then
`r` in the FIRST call's output state (consuming `IH_r`, producing `vr` at
`sp-944`), and lands control at `0x8000351c` with BOTH sub-values represented
(`vl@sp-968`, `vr@sp-944`), the store re-represented for the second call's output
state `st''`, the outer spill slots intact, `eval_expr` loaded, and the
`EvalExitD`-style presence/survival widenings. The two recursive calls are each
discharged by `armTail_rec` (`EvalRecCommon.lean`); the intermediate straight-line
handling threads `mcall1 → mcall2` and the left value's survival across the right
call (its buffer `[sp-968, sp-944)` is disjoint from the right call's frame, arena
and right-sret window).

Mind the recursive stack headroom: two nested sub-frames need
`SL.lo + 2·1088 + 1088 ≤ sp`; `blockB_binary` carries `SL.lo + 4352 ≤ sp`.

Conditional (like `blockB_unary`) only on geometry residuals bundled as
`BinExtras` + the pre-call layout facts `hMcallPop`-style.

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

/-- A `read64` is unaffected by a disjoint 8-byte store (local copy; the
`EnvNewSpec` version is out of closure). -/
theorem read64_writeMap8_disj (mem : Mem) (a a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  simp only [read64, readLE]
  rw [getElem_writeMap8_disjoint mem a8 a d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega),
    getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)]

/-- Eight present bytes give a `read64` as `some V.toNat` for a suitable
`V : BitVec 64` (the little-endian reassembly). -/
theorem read64_bv_of_present (m : Mem) (a : Nat)
    (h0 : ∃ b, m[a]? = some b) (h1 : ∃ b, m[a+1]? = some b) (h2 : ∃ b, m[a+2]? = some b)
    (h3 : ∃ b, m[a+3]? = some b) (h4 : ∃ b, m[a+4]? = some b) (h5 : ∃ b, m[a+5]? = some b)
    (h6 : ∃ b, m[a+6]? = some b) (h7 : ∃ b, m[a+7]? = some b) :
    ∃ V : BitVec 64, read64 m a = some V.toNat := by
  obtain ⟨b0, hb0⟩ := h0; obtain ⟨b1, hb1⟩ := h1; obtain ⟨b2, hb2⟩ := h2
  obtain ⟨b3, hb3⟩ := h3; obtain ⟨b4, hb4⟩ := h4; obtain ⟨b5, hb5⟩ := h5
  obtain ⟨b6, hb6⟩ := h6; obtain ⟨b7, hb7⟩ := h7
  have hread : read64 m a = some
      (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))) := by
    simp only [read64, readLE, bind, Option.bind, pure, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      Nat.mul_zero, Nat.add_zero]
  refine ⟨sign_extend (m := 64)
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)), ?_⟩
  rw [hread, sext_full]; apply congrArg
  exact (word8_toNat_recon b0 b1 b2 b3 b4 b5 b6 b7).symm

/-! ## `TwoSubReturn` — the post-second-call package (both sub-values live)

The machine state a binary arm holds at `0x8000351c` (after BOTH recursive
calls return): control at the dispatch PC, `sp` still lowered, `s1 = sret`
(the OUTER result buffer), callee-saved registers restored to the call-point
frame `gpre`; the RIGHT sub-value `vr` represented at `sp-944` and the LEFT
sub-value `vl` still represented at `sp-968`; the store re-represented for the
SECOND call's output state `st''` (+ survival on `[SL.lo, SL.hi)`); the four
outer spill slots intact; `eval_expr` loaded; memory framed to the case-entry
memory `m0` outside `[SL.lo, sp)` and presence-extended. -/
def TwoSubReturn
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (vl vr : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x8000351c#64) ∧
  c.σ.regs.get? Register.x1 = some (0x8000351c#64) ∧
  c.σ.regs.get? Register.x9 = some sret ∧
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  OutRepr c.σ st'' ∧
  -- callee-saved frame relative to `gpre`, EXCEPT `s3 (x19)` which the arm
  -- clobbers mid-body (`ld s3,128(sp)`) after spilling it at `sp-40`; the
  -- binary epilogue restores it from that slot (below).
  (∀ R : Register, AbiPreservedNoise R → (Register.x19 == R) = false →
    c.σ.regs.get? R = gpre R) ∧
  -- the `s3` spill slot `[sp-40, sp-32)` still holds the entry `s3` value.
  (∃ w, gpre Register.x19 = some w ∧ read64 c.σ.mem (sp.toNat - 40) = some w.toNat) ∧
  -- the store is re-represented at the FINAL maps, exposed as a two-phase chain:
  -- `φf/φc → φfm/φcm` (left sub-derivation's exit maps, ENTRY-sized agreement)
  -- → `φf'/φc'` (right sub-derivation's exit maps, sized by the right call's
  -- ENTRY state `st'`). Rows compose to the ROW-entry-sized agreements
  -- `φf → φf'` via `evalE_store_mono` (store counts only grow).
  (∃ φfm φcm : Addr → Nat,
    PhiExtends φf φfm nf ∧
    PhiExtends φc φcm nc ∧
    (∃ φcr : Addr → Nat, PhiExtends φcm φcr st'.store.closures.size ∧
      ValueRepr c.σ.mem N φcr (sp.toNat - 944) vr) ∧
    (∃ φcl : Addr → Nat, ValueRepr c.σ.mem N φcl (sp.toNat - 968) vl) ∧
    (∃ φf' φc' : Addr → Nat,
      PhiExtends φfm φf' st'.store.frames.size ∧
      PhiExtends φcm φc' st'.store.closures.size ∧
      StoreRepr c.σ.mem N A φf' φc' st''.store ∧
      (∀ m' : Mem,
        (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf' φc' st''.store))) ∧
  Eval_exprLoaded c.σ.mem ∧
  read64 c.σ.mem (sp.toNat - 8) = some r.toNat ∧
  read64 c.σ.mem (sp.toNat - 16) = some v8.toNat ∧
  read64 c.σ.mem (sp.toNat - 24) = some v9.toNat ∧
  read64 c.σ.mem (sp.toNat - 32) = some v18.toNat ∧
  MemExtends m0 c.σ.mem ∧
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) → c.σ.mem[a]? = m0[a]?)

/-! ## `BinExtras` — the binary-arm geometry residual bundle

Beyond `ArmEntryK` (which pins the node + entry registers + entry store) and the
two induction hypotheses, `blockB_binary` needs a bundle of pure program-structure
facts, analogous to `NegExtras` for the unary arm but doubled (two operands) and
with two extra classes:

* **operand geometry** for BOTH operands (align/RAM/HTIF-window; disjointness of
  each operand node from the deep stack region);
* **deep recursive headroom** `SL.lo + 4352 ≤ sp` (TWO nested sub-frames plus the
  arm's own frame: `1088·3 + 1088` slack), `sp % 16 = 0`;
* **AST-vs-stack/arena disjointness** for the RIGHT operand node — it is read
  (`ld a2,24(s0)`) and its `ExprRepr` re-derived AFTER the left call returns, so it
  must survive the left sub-call's stack scribble and any arena allocation;
* **second-frame slot presence** (`hSlot2`): the four spill slots of the RIGHT
  call's own frame `[sp-1120, sp-1088)` are populated in the pre-call memory — an
  M6 Layout fact (like `hMcallPop`), stated for the entry memory and transported.

The right-operand pointer / `ExprRepr` come from the `.binary` node's `ExprRepr`
(offset 24), so they are NOT separate hypotheses — only the geometry + survival
disjointness are.  The env register `a3` at arm entry is opaque (`aEnvReg`); the
sub-calls take `a1 = interp*`, not `a3`, so its concrete value is irrelevant. -/
structure BinExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (el er : Expr) (ment : Mem)
    (sp sret aExpr aLOp aROp : BitVec 64) : Prop where
  -- LEFT operand geometry
  lop_align : aLOp.toNat % 8 = 0
  lop_ram : 0x80000000 ≤ aLOp.toNat ∧ aLOp.toNat + 16 ≤ 0x100000000
  lop_win : tohostAddr + 16 ≤ aLOp.toNat
  lop_stk : aLOp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLOp.toNat
  -- LEFT operand `ExprRepr` survives the arm's own stack scribble (AST is outside
  -- `[SL.lo, SL.hi)`): a layout-dischargeable survival function, analogous to
  -- `store_survives`.
  lexpr_surv : ∀ m : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ment[k]? = m[k]?) → ExprRepr m aLOp.toNat el
  -- RIGHT operand geometry
  rop_align : aROp.toNat % 8 = 0
  rop_ram : 0x80000000 ≤ aROp.toNat ∧ aROp.toNat + 16 ≤ 0x100000000
  rop_win : tohostAddr + 16 ≤ aROp.toNat
  rop_stk : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aROp.toNat
  -- RIGHT operand node survives the left sub-call: disjoint from stack + arena
  rop_stkfull : aROp.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aROp.toNat
  rop_arena : aROp.toNat + 16 ≤ A.lo ∨ A.hi ≤ aROp.toNat
  -- RIGHT operand `ExprRepr` survives BOTH the stack scribble AND the left
  -- sub-call's arena allocation (it is read after the left call returns).
  rexpr_surv : ∀ m : Mem,
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) → ment[k]? = m[k]?) →
    ExprRepr m aROp.toNat er
  -- the node itself is 32 bytes (offsets 16 and 24 are read); the WHOLE 32-byte
  -- node is disjoint from the stack and the arena (its `[aExpr+24, aExpr+32)`
  -- right-operand-pointer word is read after the left call returns).
  node_hi : aExpr.toNat + 32 ≤ 0x100000000
  node_stk : aExpr.toNat + 32 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  node_arena : aExpr.toNat + 32 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  -- deep recursive headroom + alignment + bounds
  sproom : SL.lo + 4352 ≤ sp.toNat
  spSLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  -- code/table/arena vs stack disjointness (as in `blockB_unary`)
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : (0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec
  tableStk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arenaStk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arenaCode : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  -- `value_int` code `[0x8000280c, 0x8000281c)` and the jump-table word disjoint
  -- from the arena (so they survive the left sub-call's allocation).
  arenaVi : A.hi ≤ 0x800027ec ∨ 0x8000282c ≤ A.lo
  arenaTable : A.hi ≤ 0x80019f58 ∨ 0x80019f58 + 44 ≤ A.lo
  -- the outer sret buffer lies inside the whole stack region `[SL.lo, SL.hi)`
  -- (so the left store-survival clause, phrased over `[SL.lo, SL.hi)`, covers it).
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi

/-! ## `blockB_binary` — the reusable TWO-operand recursive head -/

theorem blockB_binary
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (op : BinOp) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hIHl : EvalIH st d env el st' vl)
    (hIHr : EvalIH st' d env er st'' vr)
    -- LEFT-value survival across the RIGHT sub-call: a layout-level residual (like
    -- `store_survives`). The left value at `sp-968` keeps its representation under
    -- any memory change confined to the right sub-call's frame `[SL.lo, sp-1088)`,
    -- the arena `[A.lo, A.hi)` (the right call may allocate — its new bytes must not
    -- clobber the left value's own arena payload), or the right sret window
    -- `[sp-944, sp-920)`. For non-string `vl` (e.g. the `int`-pilot) it is vacuous.
    (hVlSurv : ∀ (φ : Addr → Nat) (m m' : Mem),
      ValueRepr m N φ (sp.toNat - 968) vl →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → m[k]? = m'[k]?) →
      ValueRepr m' N φ (sp.toNat - 968) vl) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        -- ===== recursive-case register extras =====
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧   -- s3 (callee-saved, spilled)
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        -- ===== the two operand pointers, read off the `.binary` node =====
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        -- ===== frame populated (M6 Layout residual, `hMcallPop`-style): the whole
        -- lowered frame plus the right call's own spill slots is populated. =====
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, ment[a]? = some b)) ∧
        -- the arm-entry memory presence-extends the case-entry memory (M6 Layout).
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry
        -- (children derived inside via the `EntryGroundKit` combinators).
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`), threaded
        -- from the parent `.binary op el er` node's budget by the arm-entry
        -- supplier (RIGHT store-bodies via eval-preservation at that layer).
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (fun c =>
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' vl vr sp r sret v8 v9 v18 m0 c) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8, hg18, hgx8v, hgx18v, hgx19v,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hgroundP,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,
    _hAEx11, _hAEx8, _hAEx18⟩ := hArm
  obtain ⟨hviInt, hviSlot, hnbs⟩ : Value_intLoaded ment ∧ IntSlotPinned ment ∧ NBSPins ment := hviCode
  have hnodehi := hBE.node_hi
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088' : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  -- abi_ne' helper (reused)
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- address arithmetic
  have h16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have haddr16 : (aExpr + sign_extend (m := 64) (0x010#12)).toNat = aExpr.toNat + 16 := by
    rw [h16, BitVec.toNat_add]
    have hv : (16#64 : BitVec 64).toNat = 16 := by decide
    rw [hv]; omega
  -- left-operand-pointer bytes
  obtain ⟨lp0, lp1, lp2, lp3, lp4, lp5, lp6, lp7, hlp0, hlp1, hlp2, hlp3, hlp4, hlp5, hlp6, hlp7, hlpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 16) aLOp hpayL
  -- ============ 0x800034e8: ld a2,16(a2) → x12 := aLOp ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800034e8_ee c.σ c.tick c.steps (0x800034e8#64) vmi aExpr lp0 lp1 lp2 lp3 lp4 lp5 lp6 lp7
      hG hpc hmi ha2 (hmem ▸ hcode) rfl
      (by rw [haddr16]; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, htoh]; right; omega) (by rw [haddr16]; omega)
      (by rw [haddr16, hmem]; exact hlp0) (by rw [haddr16, hmem]; exact hlp1)
      (by rw [haddr16, hmem]; exact hlp2) (by rw [haddr16, hmem]; exact hlp3)
      (by rw [haddr16, hmem]; exact hlp4) (by rw [haddr16, hmem]; exact hlp5)
      (by rw [haddr16, hmem]; exact hlp6) (by rw [haddr16, hmem]; exact hlp7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800034ec#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800034e8#64) 4 = (0x800034ec#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some aLOp := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlpsext] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hx11_1 : σ1.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs1 Register.x11 (by decide) hx11
  have hx13_1 : σ1.regs.get? Register.x13 = some aEnvReg := obs_alu_other' hobs1 Register.x13 (by decide) hx13
  have hx19_1 : σ1.regs.get? Register.x19 = some v19 := obs_alu_other' hobs1 Register.x19 (by decide) hx19
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800034ec: addi a0,sp,120 → x10 := (sp-1088)+120 = sp-968 ============
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800034ec_ee σ1 i1 (c.steps + 1) (0x800034ec#64) vmi1 (sp - 1088#64)
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800034f0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800034ec#64) 4 = (0x800034f0#64 : BitVec 64) from by decide] at this
  have hsretL : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088'
  have ha0_2 : σ2.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hx11_2 : σ2.regs.get? Register.x11 = some aEnv := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some aLOp := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some aEnvReg := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1
  have hx19_2 : σ2.regs.get? Register.x19 = some v19 := obs_alu_other' hobs2 Register.x19 (by decide) hx19_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- spill addresses for the two stores
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by omega) hsp1088'
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  -- ============ 0x800034f0: sd s3,1048(sp) → m_a at sp-40 ============
  let ma : Mem := writeMap8 ment (sp.toNat - 40) (sdData_val v19)
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800034f0_ee σ2 i2 (c.steps + 1 + 1) (0x800034f0#64) vmi2 (sp - 1088#64) v19
      hG2 hpc2 hmi2 hsp_2 hx19_2 hcode2 rfl
      (by rw [haddr1048]; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048, htoh]; omega) (by rw [haddr1048]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ma := by
    rw [hmem3, mem_afterNextPC, haddr1048, hmem2e]
  have hpc3 : σ3.regs.get? Register.PC = some (0x800034f4#64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x800034f0#64) 4 = (0x800034f4#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_store_other_val' hobs3 Register.x10 (by decide) ha0_2
  have hs1_3 := obs_store_other_val' hobs3 Register.x9 (by decide) hs1_2
  have hx11_3 := obs_store_other_val' hobs3 Register.x11 (by decide) hx11_2
  have hx12_3 := obs_store_other_val' hobs3 Register.x12 (by decide) hx12_2
  have hx13_3 := obs_store_other_val' hobs3 Register.x13 (by decide) hx13_2
  have hsp_3 := obs_store_other_val' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by
    rw [hmem3e]
    exact loaded_eval_expr_agreeP ment ma
      (fun k hk => (getElem_writeMap8_disjoint ment (sp.toNat-40) k (sdData_val v19)
        (by rcases hBE.codeStk with h | h <;> omega)).symm) hcode
  -- ============ 0x800034f4: sd a3,0(sp) → mcall1 at sp-1088 ============
  let mcall1 : Mem := writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800034f4_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x800034f4#64) vmi3 (sp - 1088#64) aEnvReg
      hG3 hpc3 hmi3 hsp_3 hx13_3 hcode3 rfl
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; omega) (by rw [haddr0]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = mcall1 := by
    rw [hmem4, mem_afterNextPC, haddr0, hmem3e]
  have hpc4 : σ4.regs.get? Register.PC = some (0x800034f8#64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x800034f4#64) 4 = (0x800034f8#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other_val' hobs4 Register.x10 (by decide) ha0_3
  have hx13_4 := obs_store_other_val' hobs4 Register.x13 (by decide) hx13_3
  have hs1_4 := obs_store_other_val' hobs4 Register.x9 (by decide) hs1_3
  have hx11_4 := obs_store_other_val' hobs4 Register.x11 (by decide) hx11_3
  have hx12_4 := obs_store_other_val' hobs4 Register.x12 (by decide) hx12_3
  have hsp_4 := obs_store_other_val' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_store]; exact hout3
  have hcodema : Eval_exprLoaded ma := by rw [← hmem3e]; exact hcode3
  have hcode4 : Eval_exprLoaded σ4.mem := by
    rw [hmem4e]
    exact loaded_eval_expr_agreeP ma mcall1
      (fun k hk => (getElem_writeMap8_disjoint ma (sp.toNat-1088) k (sdData_val aEnvReg)
        (by rcases hBE.codeStk with h | h <;> omega)).symm) hcodema
  --------------------------------------------------------------------------
  -- Agreement `ment ↔ mcall1` outside the stack region `[SL.lo, sp)`.
  -- Both stores (sp-40, sp-1088) land inside `[SL.lo, sp)`; nothing else moves.
  --------------------------------------------------------------------------
  have hAgMcall1 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ment[k]? = mcall1[k]? := by
    intro k hk
    show ment[k]? = (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg))[k]?
    rw [getElem_writeMap8_disjoint ma (sp.toNat - 1088) k (sdData_val aEnvReg) (by omega)]
    show ment[k]? = (writeMap8 ment (sp.toNat - 40) (sdData_val v19))[k]?
    rw [getElem_writeMap8_disjoint ment (sp.toNat - 40) k (sdData_val v19) (by omega)]
  -- `Value_intLoaded` / `IntSlotPinned` survive both stack stores
  have hviInt1 : Value_intLoaded mcall1 :=
    loaded_value_int_agreeP ment mcall1
      (fun a ha => hAgMcall1 a (by rcases hBE.viStk with h | h <;> omega)) hviInt
  have hviSlot1 : IntSlotPinned mcall1 := by
    apply intSlot_writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega)
    exact intSlot_writeMap8 ment (sp.toNat - 40) (sdData_val v19)
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega) hviSlot
  have hnbs1 : NBSPins mcall1 :=
    hnbs.survive_stack hBE.viStk hBE.tableStk hAgMcall1
  -- `StoreRepr mcall1 st.store` + its survival, from the entry survival clause
  have hstore1 : StoreRepr mcall1 N A φf φc st.store :=
    hstoreSurv mcall1 (fun k hk1 _ => hAgMcall1 k (fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩))
  have hstoreSurv1 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
        mcall1[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by
    intro m' hag
    refine hstoreSurv m' (fun k hk1 hk2 => ?_)
    have hk1' : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun hcon =>
      hk1 ⟨hcon.1, Nat.lt_of_lt_of_le hcon.2 hBE.spSLhi⟩
    rw [hAgMcall1 k hk1']; exact hag k hk1 hk2
  -- `ExprRepr mcall1 aLOp el`
  have hspSLhi := hBE.spSLhi
  have hsproom := hBE.sproom
  have hexprL1 : ExprRepr mcall1 aLOp.toNat el :=
    hBE.lexpr_surv mcall1 (fun k hk => hAgMcall1 k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩))
  -- the four spill slots survive both stores (sp-40, sp-1088 vs sp-8/16/24/32).
  -- `mcall1 = writeMap8 (writeMap8 ment (sp-40) _) (sp-1088) _`; peel each store.
  have hslotpeel : ∀ (a : Nat) (v : BitVec 64), sp.toNat - 32 ≤ a → a + 8 ≤ sp.toNat →
      read64 ment a = some v.toNat → read64 mcall1 a = some v.toNat := by
    intro a v ha1 ha2 hr
    show read64 (writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg)) a = some v.toNat
    rw [read64_writeMap8_disj ma a (sp.toNat - 1088) (sdData_val aEnvReg) (by omega)]
    show read64 (writeMap8 ment (sp.toNat - 40) (sdData_val v19)) a = some v.toNat
    rw [read64_writeMap8_disj ment a (sp.toNat - 40) (sdData_val v19) (by omega)]
    exact hr
  have hslotRa1 : read64 mcall1 (sp.toNat - 8) = some r.toNat :=
    hslotpeel (sp.toNat - 8) r (by omega) (by omega) hslotRa
  have hslotS01 : read64 mcall1 (sp.toNat - 16) = some v8.toNat :=
    hslotpeel (sp.toNat - 16) v8 (by omega) (by omega) hslotS0
  have hslotS11 : read64 mcall1 (sp.toNat - 24) = some v9.toNat :=
    hslotpeel (sp.toNat - 24) v9 (by omega) (by omega) hslotS1
  have hslotS21 : read64 mcall1 (sp.toNat - 32) = some v18.toNat :=
    hslotpeel (sp.toNat - 32) v18 (by omega) (by omega) hslotS2
  -- the ghost frame `gpre` survives the two ALU writes (x12, x10) and the two
  -- stack stores (no reg writes): σ4 regs = c regs on AbiPreservedNoise.
  have hframe4 : ∀ R : Register, AbiPreservedNoise R → σ4.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans
        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    rw [f4, f3, f2, f1]; exact hgframe R hR'
  have hcodemcall1 : Eval_exprLoaded mcall1 := by rw [← hmem4e]; exact hcode4
  -- the two operand-buffer addresses
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 := hsretL
  -- WAVE 47i: the LEFT child's entry-ground bundle (kit moves 1+2+3).
  have hspsubB : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hGroundM1 : EvalGround mcall1 SL A sp sret aExpr.toNat (.binary op el er) :=
    hgroundP.transport_offstack hBE.tableStk hBE.spSLhi
      (fun a ha => (hAgMcall1 a ha).symm)
  have hpayL1 : read64 mcall1 (aExpr.toNat + 16) = some aLOp.toNat := by
    rw [evalGround_ast_read64_agree hgroundP hBE.spSLhi
      (fun a ha => (hAgMcall1 a ha).symm) (off := 16) (by omega)]
    exact hpayL
  have hGroundL : EvalGround mcall1 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aLOp.toNat el :=
    hGroundM1.child_params (fun lo hi hin => exprIn_binary_left hin aLOp.toNat hpayL1)
      hBE.tableStk hBE.spSLhi (by omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
      (by rw [hsub968]; have := hBE.sproom; have := hSLlo; omega)
  ------------------------------------------------------------------------------
  -- LEFT recursive call, via `armTail_rec` (subsret = sp-968, retPC = 0x800034fc).
  ------------------------------------------------------------------------------
  obtain ⟨cL, hsL, hpostL⟩ :=
    armTail_rec gpre N A SL φf φc st st' d env el vl
      (0x800034f8#64) (0x800034fc#64) (0x1ffc6c#21)
      sp r sret ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) aEnv aLOp v8 v9 v18
      out0 mcall1
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_800034f8_ee σ i u (0x800034f8#64) vmi hGσ hpcσ hmiσ hcodeσ rfl hiσ)
      hIHl
      ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩
      ⟨hG4, hi4, hpc4, ha0_4, hs1_4, hx11_4, ⟨_, hx13_4⟩, hx12_4, hsp_4, ⟨vmi4, hmi4⟩,
        hout4, houtStr, hmem4e, hcodemcall1, hviInt1, hviSlot1, hnbs1, hGroundL, hexprL1, hstore1, hstoreSurv1,
        hframe4, ⟨hg8, hg18⟩,
        hslotRa1, hslotS01, hslotS11, hslotS21,
        hBE.lop_align, hBE.lop_ram.1, hBE.lop_ram.2, hBE.lop_win, hBE.lop_stk,
        (by rw [hsub968]; omega), (by rw [hsub968]; omega), (by rw [hsub968]; omega),
        (by omega), hBE.spSLhi, hBE.sp16, (by omega), hSLlo, hBE.SLhiRam, hSLwin,
        hBE.codeStk, hBE.viStk, hBE.tableStk, hBE.arenaStk, hBE.arenaCode,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL⟩
  -- unpack the LEFT `SubEvalReturn`
  obtain ⟨hGL, htickL, hpcL, ha0L, hraL, hs1L, hspL, ⟨vmiL, hmiL⟩, houtL, hframeL,
    ⟨φcvL, hpcvL, hvalL⟩, hstoreBundleL, hcodeL,
    hslotRaL, hslotS0L, hslotS1L, hslotS2L, hmemFrameL, hMemExtL⟩ := hpostL
  obtain ⟨φf1, φc1, hpf1, hpc1', hstore1', hstoreSurv1'⟩ := hstoreBundleL
  -- `s0 = aExpr`, `s2 = aEnv` restored by the left call's frame (via gpre)
  have hx8L : cL.σ.regs.get? Register.x8 = some aExpr := (hframeL Register.x8 (by decide)).trans hgx8v
  have hx18L : cL.σ.regs.get? Register.x18 = some aEnv := (hframeL Register.x18 (by decide)).trans hgx18v
  -- === transport the right-operand pointer `read64 (aExpr+24) = aROp` to cL.mem ===
  -- ment ↔ mcall1 (outside stack), mcall1 ↔ cL.mem (left memFrame outside
  -- [SL.lo, sp-1088) ∪ A ∪ [sp-968,+24)). The node is disjoint from all three.
  have hAgNode : ∀ k : Nat, aExpr.toNat + 24 ≤ k → k < aExpr.toNat + 32 →
      ment[k]? = cL.σ.mem[k]? := by
    intro k hk1 hk2
    have e1 : ment[k]? = mcall1[k]? := hAgMcall1 k (by rcases hBE.node_stk with h | h <;> omega)
    have e2 : mcall1[k]? = cL.σ.mem[k]? := by
      rcases hmemFrameL k (by rcases hBE.node_stk with h | h <;> omega)
        (by rcases hBE.node_arena with h | h <;> omega) with hin | heq
      · exact absurd hin (by rcases hBE.node_stk with h | h <;> omega)
      · exact heq.symm
    rw [e1, e2]
  obtain ⟨rp0, rp1, rp2, rp3, rp4, rp5, rp6, rp7, hrp0, hrp1, hrp2, hrp3, hrp4, hrp5, hrp6, hrp7, hrpsext⟩ :=
    spill_roundtrip_ee ment (aExpr.toNat + 24) aROp hpayR
  -- the node-24 bytes at cL.mem
  have hr24_0 : cL.σ.mem[aExpr.toNat + 24]? = some rp0 := (hAgNode _ (by omega) (by omega)).symm.trans hrp0
  have hr24_1 : cL.σ.mem[aExpr.toNat + 24 + 1]? = some rp1 := (hAgNode _ (by omega) (by omega)).symm.trans hrp1
  have hr24_2 : cL.σ.mem[aExpr.toNat + 24 + 2]? = some rp2 := (hAgNode _ (by omega) (by omega)).symm.trans hrp2
  have hr24_3 : cL.σ.mem[aExpr.toNat + 24 + 3]? = some rp3 := (hAgNode _ (by omega) (by omega)).symm.trans hrp3
  have hr24_4 : cL.σ.mem[aExpr.toNat + 24 + 4]? = some rp4 := (hAgNode _ (by omega) (by omega)).symm.trans hrp4
  have hr24_5 : cL.σ.mem[aExpr.toNat + 24 + 5]? = some rp5 := (hAgNode _ (by omega) (by omega)).symm.trans hrp5
  have hr24_6 : cL.σ.mem[aExpr.toNat + 24 + 6]? = some rp6 := (hAgNode _ (by omega) (by omega)).symm.trans hrp6
  have hr24_7 : cL.σ.mem[aExpr.toNat + 24 + 7]? = some rp7 := (hAgNode _ (by omega) (by omega)).symm.trans hrp7
  -- frame populated in cL.mem (ment populated + two MemExtends inserts)
  have hMemExtMent1 : MemExtends ment mcall1 :=
    (memExtends_writeMap8 ment (sp.toNat - 40) (sdData_val v19)).trans
      (memExtends_writeMap8 ma (sp.toNat - 1088) (sdData_val aEnvReg))
  have hPopCL : ∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, cL.σ.mem[a]? = some b) := by
    intro a h1 h2
    obtain ⟨b, hb⟩ := hMentPop a h1 h2
    obtain ⟨b', hb'⟩ := hMemExtMent1 a b hb
    exact hMemExtL a b' hb'
  -- addresses for the intermediate reads/stores (all `(sp-1088)+off`)
  have hoff24_s0 : (aExpr + sign_extend (m := 64) (0x018#12)).toNat = aExpr.toNat + 24 := by
    have hs : (sign_extend (m := 64) (0x018#12) : BitVec 64) = 24#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (24#64 : BitVec 64).toNat = 24 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  have haddr0' : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088'
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088'
  have haddr144' : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088'
  -- present bytes for the reads (env @sp-1088, lw @sp-968, s3 @sp-960)
  obtain ⟨eb0, heb0⟩ := hPopCL (sp.toNat - 1088) (by omega) (by omega)
  obtain ⟨eb1, heb1⟩ := hPopCL (sp.toNat - 1088 + 1) (by omega) (by omega)
  obtain ⟨eb2, heb2⟩ := hPopCL (sp.toNat - 1088 + 2) (by omega) (by omega)
  obtain ⟨eb3, heb3⟩ := hPopCL (sp.toNat - 1088 + 3) (by omega) (by omega)
  obtain ⟨eb4, heb4⟩ := hPopCL (sp.toNat - 1088 + 4) (by omega) (by omega)
  obtain ⟨eb5, heb5⟩ := hPopCL (sp.toNat - 1088 + 5) (by omega) (by omega)
  obtain ⟨eb6, heb6⟩ := hPopCL (sp.toNat - 1088 + 6) (by omega) (by omega)
  obtain ⟨eb7, heb7⟩ := hPopCL (sp.toNat - 1088 + 7) (by omega) (by omega)
  obtain ⟨wb0, hwb0⟩ := hPopCL (sp.toNat - 968) (by omega) (by omega)
  obtain ⟨wb1, hwb1⟩ := hPopCL (sp.toNat - 968 + 1) (by omega) (by omega)
  obtain ⟨wb2, hwb2⟩ := hPopCL (sp.toNat - 968 + 2) (by omega) (by omega)
  obtain ⟨wb3, hwb3⟩ := hPopCL (sp.toNat - 968 + 3) (by omega) (by omega)
  obtain ⟨sb0, hsb0⟩ := hPopCL (sp.toNat - 960) (by omega) (by omega)
  obtain ⟨sb1, hsb1⟩ := hPopCL (sp.toNat - 960 + 1) (by omega) (by omega)
  obtain ⟨sb2, hsb2⟩ := hPopCL (sp.toNat - 960 + 2) (by omega) (by omega)
  obtain ⟨sb3, hsb3⟩ := hPopCL (sp.toNat - 960 + 3) (by omega) (by omega)
  obtain ⟨sb4, hsb4⟩ := hPopCL (sp.toNat - 960 + 4) (by omega) (by omega)
  obtain ⟨sb5, hsb5⟩ := hPopCL (sp.toNat - 960 + 5) (by omega) (by omega)
  obtain ⟨sb6, hsb6⟩ := hPopCL (sp.toNat - 960 + 6) (by omega) (by omega)
  obtain ⟨sb7, hsb7⟩ := hPopCL (sp.toNat - 960 + 7) (by omega) (by omega)
  -- ============ 0x800034fc: ld a2,24(s0) → x12 := aROp ============
  obtain ⟨τ1, j1, ht1', hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_800034fc_ee cL.σ cL.tick cL.steps (0x800034fc#64) vmiL aExpr rp0 rp1 rp2 rp3 rp4 rp5 rp6 rp7
      hGL hpcL hmiL hx8L hcodeL rfl
      (by rw [hoff24_s0]; omega) (by rw [hoff24_s0]; omega)
      (by rw [hoff24_s0, htoh]; right; omega) (by rw [hoff24_s0]; omega)
      (by rw [hoff24_s0]; exact hr24_0) (by rw [hoff24_s0]; exact hr24_1)
      (by rw [hoff24_s0]; exact hr24_2) (by rw [hoff24_s0]; exact hr24_3)
      (by rw [hoff24_s0]; exact hr24_4) (by rw [hoff24_s0]; exact hr24_5)
      (by rw [hoff24_s0]; exact hr24_6) (by rw [hoff24_s0]; exact hr24_7) htickL
  have hstepτ1 : Step cL ⟨τ1, j1, cL.steps + 1⟩ := by cases cL; exact ht1'
  have hmemτ1e : τ1.mem = cL.σ.mem := hmemτ1
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x80003500#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x800034fc#64) 4 = (0x80003500#64 : BitVec 64) from by decide] at this
  have hx12τ1 : τ1.regs.get? Register.x12 = some aROp := by
    have := obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hrpsext] at this
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1L
  have hx18τ1 : τ1.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18L
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspL
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = cL.σ.sailOutput := by rw [hoτ1.out, sailOutput_sigmaPost_alu]
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcodeL
  -- ============ 0x80003500: ld a3,0(sp) → x13 := env (dead) ============
  obtain ⟨τ2, j2, ht2', hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_80003500_ee τ1 j1 (cL.steps + 1) (0x80003500#64) vmiτ1 (sp - 1088#64)
      eb0 eb1 eb2 eb3 eb4 eb5 eb6 eb7 hGτ1 hpcτ1 hmiτ1 hspτ1 hcodeτ1 rfl
      (by rw [haddr0']; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', htoh]; right; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', hmemτ1e]; exact heb0) (by rw [haddr0', hmemτ1e]; exact heb1)
      (by rw [haddr0', hmemτ1e]; exact heb2) (by rw [haddr0', hmemτ1e]; exact heb3)
      (by rw [haddr0', hmemτ1e]; exact heb4) (by rw [haddr0', hmemτ1e]; exact heb5)
      (by rw [haddr0', hmemτ1e]; exact heb6) (by rw [haddr0', hmemτ1e]; exact heb7) hj1
  have hstepτ2 : Step ⟨τ1, j1, cL.steps + 1⟩ ⟨τ2, j2, cL.steps + 1 + 1⟩ := ht2'
  have hmemτ2e : τ2.mem = cL.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003504#64) := by
    have := obs_alu_pc hoτ2
    rwa [show BitVec.addInt (0x80003500#64) 4 = (0x80003504#64 : BitVec 64) from by decide] at this
  have hx12τ2 : τ2.regs.get? Register.x12 = some aROp := obs_alu_other hoτ2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ1
  -- wave 48h (CURE A): `ld a3,0(sp)` writes x13 (the reloaded env for the RIGHT
  -- sub-call); thread its existence to τ7 for `armTail_rec`'s x13-defined premise.
  have hx13τ2 : τ2.regs.get? Register.x13 = some
      (sign_extend (m := 64) ((((((((eb7.append eb6).append eb5).append eb4).append eb3).append eb2).append eb1).append eb0) : BitVec (8 * 8))) :=
    obs_alu_rd hoτ2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_alu_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hx18τ2 : τ2.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_alu_minstret hoτ2
  have houtτ2 : τ2.sailOutput = cL.σ.sailOutput := by rw [hoτ2.out, sailOutput_sigmaPost_alu]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcodeL
  -- ============ 0x80003504: lw a6,120(sp) → x16 (dead) ============
  obtain ⟨τ3, j3, ht3', hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003504_ee τ2 j2 (cL.steps + 1 + 1) (0x80003504#64) vmiτ2 (sp - 1088#64)
      wb0 wb1 wb2 wb3 hGτ2 hpcτ2 hmiτ2 hspτ2 hcodeτ2 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmemτ2e]; exact hwb0) (by rw [haddr120, hmemτ2e]; exact hwb1)
      (by rw [haddr120, hmemτ2e]; exact hwb2) (by rw [haddr120, hmemτ2e]; exact hwb3) hj2
  have hstepτ3 : Step ⟨τ2, j2, cL.steps + 1 + 1⟩ ⟨τ3, j3, cL.steps + 1 + 1 + 1⟩ := ht3'
  have hmemτ3e : τ3.mem = cL.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x80003508#64) := by
    have := obs_alu_pc hoτ3
    rwa [show BitVec.addInt (0x80003504#64) 4 = (0x80003508#64 : BitVec 64) from by decide] at this
  have hx16τ3 : τ3.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12τ3 : τ3.regs.get? Register.x12 = some aROp := obs_alu_other hoτ3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ2
  have hx13τ3 := obs_alu_other hoτ3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_alu_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hx18τ3 : τ3.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_alu_minstret hoτ3
  have houtτ3 : τ3.sailOutput = cL.σ.sailOutput := by rw [hoτ3.out, sailOutput_sigmaPost_alu]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcodeL
  -- ============ 0x80003508: addi a0,sp,144 → x10 := sp-944 ============
  obtain ⟨τ4, j4, ht4', hj4, hGτ4, hmemτ4, hoτ4⟩ :=
    site_80003508_ee τ3 j3 (cL.steps + 1 + 1 + 1) (0x80003508#64) vmiτ3 (sp - 1088#64)
      hGτ3 hpcτ3 hmiτ3 hspτ3 hcodeτ3 rfl hj3
  have hstepτ4 : Step ⟨τ3, j3, cL.steps + 1 + 1 + 1⟩ ⟨τ4, j4, cL.steps + 1 + 1 + 1 + 1⟩ := ht4'
  have hmemτ4e : τ4.mem = cL.σ.mem := by rw [hmemτ4]; exact hmemτ3e
  have hpcτ4 : τ4.regs.get? Register.PC = some (0x8000350c#64) := by
    have := obs_alu_pc hoτ4
    rwa [show BitVec.addInt (0x80003508#64) 4 = (0x8000350c#64 : BitVec 64) from by decide] at this
  have ha0τ4 : τ4.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_rd hoτ4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12τ4 : τ4.regs.get? Register.x12 = some aROp := obs_alu_other hoτ4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ3
  have hx13τ4 := obs_alu_other hoτ4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ3
  have hs1τ4 : τ4.regs.get? Register.x9 = some sret := obs_alu_other hoτ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ3
  have hx16τ4 : τ4.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ3
  have hx18τ4 : τ4.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ4 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ3
  have hspτ4 : τ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ3
  obtain ⟨vmiτ4, hmiτ4⟩ := obs_alu_minstret hoτ4
  have houtτ4 : τ4.sailOutput = cL.σ.sailOutput := by rw [hoτ4.out, sailOutput_sigmaPost_alu]; exact houtτ3
  have hcodeτ4 : Eval_exprLoaded τ4.mem := by rw [hmemτ4e]; exact hcodeL
  -- ============ 0x8000350c: mv a1,s2 → x11 := aEnv ============
  obtain ⟨τ5, j5, ht5', hj5, hGτ5, hmemτ5, hoτ5⟩ :=
    site_8000350c_ee τ4 j4 (cL.steps + 1 + 1 + 1 + 1) (0x8000350c#64) vmiτ4 aEnv
      hGτ4 hpcτ4 hmiτ4 hx18τ4 hcodeτ4 rfl hj4
  have hstepτ5 : Step ⟨τ4, j4, cL.steps + 1 + 1 + 1 + 1⟩ ⟨τ5, j5, cL.steps + 1 + 1 + 1 + 1 + 1⟩ := ht5'
  have hmemτ5e : τ5.mem = cL.σ.mem := by rw [hmemτ5]; exact hmemτ4e
  have hpcτ5 : τ5.regs.get? Register.PC = some (0x80003510#64) := by
    have := obs_alu_pc hoτ5
    rwa [show BitVec.addInt (0x8000350c#64) 4 = (0x80003510#64 : BitVec 64) from by decide] at this
  have hx11τ5 : τ5.regs.get? Register.x11 = some aEnv := by
    have := obs_alu_rd hoτ5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (aEnv + sign_extend (m := 64) (0x000#12)) = aEnv from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
      rw [this]; have := aEnv.isLt; omega] at this
  have ha0τ5 : τ5.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_other hoτ5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ4
  have hx12τ5 : τ5.regs.get? Register.x12 = some aROp := obs_alu_other hoτ5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ4
  have hx13τ5 := obs_alu_other hoτ5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ4
  have hs1τ5 : τ5.regs.get? Register.x9 = some sret := obs_alu_other hoτ5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ4
  have hx16τ5 : τ5.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ4
  have hspτ5 : τ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ4
  obtain ⟨vmiτ5, hmiτ5⟩ := obs_alu_minstret hoτ5
  have houtτ5 : τ5.sailOutput = cL.σ.sailOutput := by rw [hoτ5.out, sailOutput_sigmaPost_alu]; exact houtτ4
  have hcodeτ5 : Eval_exprLoaded τ5.mem := by rw [hmemτ5e]; exact hcodeL
  -- ============ 0x80003510: ld s3,128(sp) → x19 (dead) ============
  obtain ⟨τ6, j6, ht6', hj6, hGτ6, hmemτ6, hoτ6⟩ :=
    site_80003510_ee τ5 j5 (cL.steps + 1 + 1 + 1 + 1 + 1) (0x80003510#64) vmiτ5 (sp - 1088#64)
      sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 hGτ5 hpcτ5 hmiτ5 hspτ5 hcodeτ5 rfl
      (by rw [haddr128]; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, htoh]; right; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, hmemτ5e]; exact hsb0) (by rw [haddr128, hmemτ5e]; exact hsb1)
      (by rw [haddr128, hmemτ5e]; exact hsb2) (by rw [haddr128, hmemτ5e]; exact hsb3)
      (by rw [haddr128, hmemτ5e]; exact hsb4) (by rw [haddr128, hmemτ5e]; exact hsb5)
      (by rw [haddr128, hmemτ5e]; exact hsb6) (by rw [haddr128, hmemτ5e]; exact hsb7) hj5
  have hstepτ6 : Step ⟨τ5, j5, cL.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨τ6, j6, cL.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht6'
  have hmemτ6e : τ6.mem = cL.σ.mem := by rw [hmemτ6]; exact hmemτ5e
  have hpcτ6 : τ6.regs.get? Register.PC = some (0x80003514#64) := by
    have := obs_alu_pc hoτ6
    rwa [show BitVec.addInt (0x80003510#64) 4 = (0x80003514#64 : BitVec 64) from by decide] at this
  have ha0τ6 : τ6.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_other hoτ6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ5
  have hx11τ6 : τ6.regs.get? Register.x11 = some aEnv := obs_alu_other hoτ6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ5
  have hx12τ6 : τ6.regs.get? Register.x12 = some aROp := obs_alu_other hoτ6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ5
  have hx13τ6 := obs_alu_other hoτ6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ5
  have hs1τ6 : τ6.regs.get? Register.x9 = some sret := obs_alu_other hoτ6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ5
  have hx16τ6 : τ6.regs.get? Register.x16 = some
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))) :=
    obs_alu_other hoτ6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ5
  have hspτ6 : τ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ5
  obtain ⟨vmiτ6, hmiτ6⟩ := obs_alu_minstret hoτ6
  have houtτ6 : τ6.sailOutput = cL.σ.sailOutput := by rw [hoτ6.out, sailOutput_sigmaPost_alu]; exact houtτ5
  have hcodeτ6 : Eval_exprLoaded τ6.mem := by rw [hmemτ6e]; exact hcodeL
  -- ============ 0x80003514: sd a6,0(sp) → mcall2 at sp-1088 ============
  let mcall2 : Mem := writeMap8 cL.σ.mem (sp.toNat - 1088)
    (sdData_val (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4))))
  obtain ⟨τ7, j7, ht7', hj7, hGτ7, hmemτ7, hoτ7⟩ :=
    site_80003514_ee τ6 j6 (cL.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003514#64) vmiτ6 (sp - 1088#64)
      (sign_extend (m := 64) ((((wb3.append wb2).append wb1).append wb0) : BitVec (8*4)))
      hGτ6 hpcτ6 hmiτ6 hspτ6 hx16τ6 hcodeτ6 rfl
      (by rw [haddr0']; omega) (by rw [haddr0']; omega)
      (by rw [haddr0', htoh]; omega) (by rw [haddr0']; omega) hj6
  have hstepτ7 : Step ⟨τ6, j6, cL.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ7, j7, cL.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht7'
  have hmemτ7e : τ7.mem = mcall2 := by rw [hmemτ7, mem_afterNextPC, haddr0', hmemτ6e]
  have hpcτ7 : τ7.regs.get? Register.PC = some (0x80003518#64) := by
    have := obs_store_pc_val hoτ7
    rwa [show BitVec.addInt (0x80003514#64) 4 = (0x80003518#64 : BitVec 64) from by decide] at this
  have ha0τ7 := obs_store_other_val hoτ7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0τ6
  have hx11τ7 := obs_store_other_val hoτ7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ6
  have hx12τ7 := obs_store_other_val hoτ7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ6
  have hx13τ7 := obs_store_other_val hoτ7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ6
  have hs1τ7 := obs_store_other_val hoτ7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ6
  have hspτ7 := obs_store_other_val hoτ7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ6
  obtain ⟨vmiτ7, hmiτ7⟩ := obs_store_minstret_val hoτ7
  have houtτ7 : τ7.sailOutput = cL.σ.sailOutput := by rw [hoτ7.out, sailOutput_sigmaPost_store]; exact houtτ6
  have hcodeτ7 : Eval_exprLoaded mcall2 :=
    loaded_eval_expr_agreeP cL.σ.mem mcall2
      (fun k hk => (getElem_writeMap8_disjoint cL.σ.mem (sp.toNat-1088) k _
        (by rcases hBE.codeStk with h | h <;> omega)).symm) hcodeL
  ----------------------------------------------------------------------------
  -- RIGHT `armTail_rec` precondition for `mcall2` (sp' = sp-1088, st', φf1/φc1).
  ----------------------------------------------------------------------------
  -- agreement `cL.mem ↔ mcall2` outside the stack region `[SL.lo, sp)`.
  have hAgMcall2 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → cL.σ.mem[k]? = mcall2[k]? := by
    intro k hk
    show cL.σ.mem[k]? = (writeMap8 cL.σ.mem (sp.toNat - 1088) _)[k]?
    rw [getElem_writeMap8_disjoint cL.σ.mem (sp.toNat - 1088) k _ (by omega)]
  -- `StoreRepr mcall2 st'.store` + survival, from the left survival clause
  have hstore2 : StoreRepr mcall2 N A φf1 φc1 st'.store :=
    hstoreSurv1' mcall2 (fun k hk => hAgMcall2 k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩))
  have hstoreSurv2 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mcall2[k]? = m'[k]?) →
      StoreRepr m' N A φf1 φc1 st'.store := by
    intro m' hag
    -- outside [SL.lo, SL.hi): mcall2 = cL.mem = m' (the sp-1088 write and the
    -- outer sret window both sit inside [SL.lo, SL.hi))
    have hsretInSL := hBE.sret_inSL
    refine hstoreSurv1' m' (fun k hk => ?_)
    rw [hAgMcall2 k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩)]
    exact hag k hk
      (fun ⟨ha, hb⟩ => hk ⟨by omega, by omega⟩)
  -- `ExprRepr mcall2 aROp er`
  have hexprR2 : ExprRepr mcall2 aROp.toNat er := by
    refine hBE.rexpr_surv mcall2 (fun k hk1 hk2 => ?_)
    have e1 : ment[k]? = mcall1[k]? := hAgMcall1 k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩)
    have e2 : mcall1[k]? = cL.σ.mem[k]? := by
      rcases hmemFrameL k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩) hk2 with hin | heq
      · exact absurd hin (fun ⟨ha, hb⟩ => hk1 ⟨by omega, by omega⟩)
      · exact heq.symm
    have e3 : cL.σ.mem[k]? = mcall2[k]? := hAgMcall2 k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩)
    rw [e1, e2, e3]
  -- `Value_intLoaded` / `IntSlotPinned` for mcall2 (ment → cL.mem → mcall2)
  have hAgMentCL : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      ment[k]? = cL.σ.mem[k]? := by
    intro k hk1 hk2
    have e1 : ment[k]? = mcall1[k]? := hAgMcall1 k hk1
    rcases hmemFrameL k (fun ⟨ha, hb⟩ => hk1 ⟨ha, by omega⟩) hk2 with hin | heq
    · exact absurd hin (fun ⟨ha, hb⟩ => hk1 ⟨by omega, by omega⟩)
    · rw [e1, heq]
  have hviInt2 : Value_intLoaded mcall2 :=
    loaded_value_int_agreeP ment mcall2 (fun a ha => by
      rw [hAgMentCL a (by rcases hBE.viStk with h | h <;> omega)
        (by rcases hBE.arenaVi with h | h <;> omega)]
      exact hAgMcall2 a (by rcases hBE.viStk with h | h <;> omega)) hviInt
  have hviSlotCL : IntSlotPinned cL.σ.mem := by
    obtain ⟨p0, p1, p2, p3⟩ := hviSlot
    have ag : ∀ i : Nat, i < 4 → ment[jumpTableBase + i]? = cL.σ.mem[jumpTableBase + i]? :=
      fun i hi => hAgMentCL (jumpTableBase + i)
        (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h <;> omega)
        (by simp only [jumpTableBase]; rcases hBE.arenaTable with h | h <;> omega)
    exact ⟨(ag 0 (by omega)).symm.trans p0, (ag 1 (by omega)).symm.trans p1,
      (ag 2 (by omega)).symm.trans p2, (ag 3 (by omega)).symm.trans p3⟩
  have hviSlot2 : IntSlotPinned mcall2 :=
    intSlot_writeMap8 cL.σ.mem (sp.toNat - 1088) _
      (by simp only [jumpTableBase]; rcases hBE.tableStk with h | h
          · right; omega
          · left; omega) hviSlotCL
  have hnbsCL : NBSPins cL.σ.mem :=
    hnbs.transport
      (fun a ha => hAgMentCL a (by rcases hBE.viStk with h | h <;> omega)
        (by rcases hBE.arenaVi with h | h <;> omega))
      (fun a ha => hAgMentCL a (by rcases hBE.tableStk with h | h <;> omega)
        (by rcases hBE.arenaTable with h | h <;> omega))
  have hnbs2 : NBSPins mcall2 :=
    hnbsCL.survive_stack hBE.viStk hBE.tableStk hAgMcall2
  -- the RIGHT frame's four spill slots `[sp-1120, sp-1088)`: present in cL.mem,
  -- survive the `sp-1088` store (disjoint below it). Fresh witnesses r2/v82/v92/v182.
  have hslotpeel2 : ∀ (a : Nat), sp.toNat - 1120 ≤ a → a + 8 ≤ sp.toNat - 1088 →
      ∃ V : BitVec 64, read64 mcall2 a = some V.toNat := by
    intro a ha1 ha2
    obtain ⟨V, hV⟩ := read64_bv_of_present cL.σ.mem a
      (hPopCL a (by omega) (by omega)) (hPopCL (a+1) (by omega) (by omega))
      (hPopCL (a+2) (by omega) (by omega)) (hPopCL (a+3) (by omega) (by omega))
      (hPopCL (a+4) (by omega) (by omega)) (hPopCL (a+5) (by omega) (by omega))
      (hPopCL (a+6) (by omega) (by omega)) (hPopCL (a+7) (by omega) (by omega))
    exact ⟨V, by
      show read64 (writeMap8 cL.σ.mem (sp.toNat - 1088) _) a = some V.toNat
      rw [read64_writeMap8_disj cL.σ.mem a (sp.toNat - 1088) _ (by omega)]; exact hV⟩
  obtain ⟨r2, hr2⟩ := hslotpeel2 (sp.toNat - 1096) (by omega) (by omega)
  obtain ⟨v82, hv82⟩ := hslotpeel2 (sp.toNat - 1104) (by omega) (by omega)
  obtain ⟨v92, hv92⟩ := hslotpeel2 (sp.toNat - 1112) (by omega) (by omega)
  obtain ⟨v182, hv182⟩ := hslotpeel2 (sp.toNat - 1120) (by omega) (by omega)
  -- rewrite the slot addresses into `sp' - 8/16/24/32` form (`sp' = sp - 1088`)
  have hspsub' : (sp - 1088#64).toNat = sp.toNat - 1088 := hspsub
  -- the RIGHT call's ghost is the actual post-intermediate register file `gR7`.
  -- `gR7` agrees with `gpre` on every AbiPreservedNoise register EXCEPT `x19`
  -- (`s3`), which `ld s3,128(sp)` clobbers (all other intermediate writes are
  -- caller-saved x10/x11/x12/x13/x16, invisible to the frame).
  have hframeτ7_excl : ∀ R : Register, AbiPreservedNoise R → (Register.x19 == R) = false →
      τ7.regs.get? R = gpre R := by
    intro R hR h19R
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have h13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have h16R : (Register.x16 == R) = false := abi_ne' (by decide) hab
    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have h11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have f1 : τ1.regs.get? R = cL.σ.regs.get? R :=
      (hoτ1.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)
    have f2 : τ2.regs.get? R = τ1.regs.get? R :=
      (hoτ2.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h13R hnpcR hmiiR)
    have f3 : τ3.regs.get? R = τ2.regs.get? R :=
      (hoτ3.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h16R hnpcR hmiiR)
    have f4 : τ4.regs.get? R = τ3.regs.get? R :=
      (hoτ4.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)
    have f5 : τ5.regs.get? R = τ4.regs.get? R :=
      (hoτ5.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h11R hnpcR hmiiR)
    have f6 : τ6.regs.get? R = τ5.regs.get? R :=
      (hoτ6.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h19R hnpcR hmiiR)
    have f7 : τ7.regs.get? R = τ6.regs.get? R :=
      (hoτ7.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    rw [f7, f6, f5, f4, f3, f2, f1]; exact hframeL R hR'
  -- gpre x8/x18 witnesses for armTail_rec
  have hgpre8 : (∃ w, gpre Register.x8 = some w) := ⟨aExpr, hgx8v⟩
  have hgpre18 : (∃ w, gpre Register.x18 = some w) := ⟨aEnv, hgx18v⟩
  -- output correspondence for the RIGHT call: its `out0` is `cL.σ.sailOutput`
  -- and `OutRepr cL.σ st'` says `String.join cL.σ.sailOutput.toList = st'.out`.
  have houtStrR : String.join cL.σ.sailOutput.toList = st'.out := houtL
  have houtτ7' : τ7.sailOutput = cL.σ.sailOutput := houtτ7
  -- witnesses for the RIGHT ghost `gR7 := τ7.regs.get?`: s0/s2 restored (≠x19)
  have hgR7_8 : τ7.regs.get? Register.x8 = some aExpr :=
    (hframeτ7_excl Register.x8 (by decide) (by decide)).trans hgx8v
  have hgR7_18 : τ7.regs.get? Register.x18 = some aEnv :=
    (hframeτ7_excl Register.x18 (by decide) (by decide)).trans hgx18v
  -- the OUTER spill slots survive into `mcall2` (they survive both the left
  -- sub-call — from the left `SubEvalReturn` — and the `sp-1088` respill store).
  have hslotRa2 : read64 mcall2 (sp.toNat - 8) = some r.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 8) (sp.toNat - 1088) _ (by omega)]; exact hslotRaL
  have hslotS02 : read64 mcall2 (sp.toNat - 16) = some v8.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 16) (sp.toNat - 1088) _ (by omega)]; exact hslotS0L
  have hslotS12 : read64 mcall2 (sp.toNat - 24) = some v9.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 24) (sp.toNat - 1088) _ (by omega)]; exact hslotS1L
  have hslotS22 : read64 mcall2 (sp.toNat - 32) = some v18.toNat := by
    rw [read64_writeMap8_disj cL.σ.mem (sp.toNat - 32) (sp.toNat - 1088) _ (by omega)]; exact hslotS2L
  -- WAVE 47i: the RIGHT child's entry-ground bundle — parent ground carried
  -- ACROSS the left sub-call (`transport_via`, per-window agreement chains),
  -- then the kit child conversion.
  have hGroundM2 : EvalGround mcall2 SL A sp sret aExpr.toNat (.binary op el er) := by
    have hj : jumpTableBase = 0x80019f58 := rfl
    refine hgroundP.transport_via (fun a h1 h2 => ?_) (fun lo hi spec a h1 h2 => ?_)
    · rw [hj] at h1 h2
      have hnst : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
        rcases hBE.tableStk with h | h <;> omega
      have e1 : ment[a]? = mcall1[a]? := hAgMcall1 a hnst
      have e2 : mcall1[a]? = cL.σ.mem[a]? := by
        rcases hmemFrameL a (by rcases hBE.tableStk with h | h <;> omega)
          (by rcases hBE.arenaTable with h | h <;> omega) with hin | heq
        · exact absurd hin (by
            have := hBE.sproom; rcases hBE.tableStk with h | h <;> omega)
        · exact heq.symm
      have e3 : cL.σ.mem[a]? = mcall2[a]? := hAgMcall2 a hnst
      rw [e1, e2, e3]
    · have hnst : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
        intro hcon
        rcases spec.stack_disjoint with h | h
        · have := hBE.spSLhi; omega
        · omega
      have e1 : ment[a]? = mcall1[a]? := hAgMcall1 a hnst
      have e2 : mcall1[a]? = cL.σ.mem[a]? := by
        rcases hmemFrameL a (by
            intro hcon
            rcases spec.stack_disjoint with h | h
            · have := hBE.spSLhi; omega
            · have := hBE.spSLhi; omega)
          (by rcases spec.arena_disjoint with h | h <;> omega) with hin | heq
        · exact absurd hin (by
            rcases spec.stack_disjoint with h | h
            · have := hBE.sproom; omega
            · have := hBE.spSLhi; omega)
        · exact heq.symm
      have e3 : cL.σ.mem[a]? = mcall2[a]? := hAgMcall2 a hnst
      rw [e1, e2, e3]
  have hpayR2' : read64 mcall2 (aExpr.toNat + 24) = some aROp.toNat := by
    have hAgNode2 : ∀ k : Nat, aExpr.toNat + 24 ≤ k → k < aExpr.toNat + 32 →
        ment[k]? = mcall2[k]? := fun k hk1 hk2 => by
      rw [hAgNode k hk1 hk2]
      exact hAgMcall2 k (by rcases hBE.node_stk with h | h <;> omega)
    rw [← read64_agreeP (P := fun k => aExpr.toNat + 24 ≤ k ∧ k < aExpr.toNat + 32)
      (fun k hk => hAgNode2 k hk.1 hk.2) (fun k hk => ⟨by omega, by omega⟩)]
    exact hpayR
  have hGroundR : EvalGround mcall2 SL A (sp - 1088#64)
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aROp.toNat er :=
    hGroundM2.child_params (fun lo hi hin => exprIn_binary_right hin aROp.toNat hpayR2')
      hBE.tableStk hBE.spSLhi (by omega)
      (by rw [haddr144']; have := hBE.sproom; have := hSLlo; omega)
      (by rw [haddr144']; have := hBE.sproom; have := hSLlo; omega)
  ----------------------------------------------------------------------------
  -- RIGHT recursive call, via `armTail_rec` (armTail `sp` = the arm's outer `sp`;
  -- the callee lowers to sp-2176; subsret = sp-944, retPC = 0x8000351c).
  ----------------------------------------------------------------------------
  obtain ⟨cR, hsR, hpostR⟩ :=
    armTail_rec (fun R => τ7.regs.get? R) N A SL φf1 φc1 st' st'' d env er vr
      (0x80003518#64) (0x8000351c#64) (0x1ffc4c#21)
      sp r sret ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aEnv aROp
      v8 v9 v18 cL.σ.sailOutput mcall2
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80003518_ee σ i u (0x80003518#64) vmi hGσ hpcσ hmiσ hcodeσ rfl hiσ)
      hIHr
      ⟨τ7, j7, cL.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hGτ7, hj7, hpcτ7, ha0τ7, hs1τ7, hx11τ7, ⟨_, hx13τ7⟩, hx12τ7, hspτ7, ⟨vmiτ7, hmiτ7⟩,
        houtτ7', houtStrR, hmemτ7e, hcodeτ7, hviInt2, hviSlot2, hnbs2, hGroundR, hexprR2, hstore2, hstoreSurv2,
        (fun R hR => rfl), ⟨⟨aExpr, hgR7_8⟩, ⟨aEnv, hgR7_18⟩⟩,
        hslotRa2, hslotS02, hslotS12, hslotS22,
        hBE.rop_align, hBE.rop_ram.1, hBE.rop_ram.2, hBE.rop_win, hBE.rop_stk,
        (by rw [haddr144']; omega), (by rw [haddr144']; omega), (by rw [haddr144']; omega),
        (by omega), hBE.spSLhi, hBE.sp16, (by omega), hSLlo, hBE.SLhiRam, hSLwin,
        hBE.codeStk, hBE.viStk, hBE.tableStk, hBE.arenaStk, hBE.arenaCode,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  -- unpack the RIGHT `SubEvalReturn`
  obtain ⟨hGR, htickR, hpcR, ha0R, hraR, hs1R, hspR, ⟨vmiR, hmiR⟩, houtR, hframeR,
    ⟨φcvR, hpcvR, hvalR⟩, hstoreBundleR, hcodeR,
    hslotRaR, hslotS0R, hslotS1R, hslotS2R, hmemFrameR, hMemExtR⟩ := hpostR
  obtain ⟨φf2, φc2, hpf2, hpc2'', hstore2', hstoreSurv2'⟩ := hstoreBundleR
  have hsub944R : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 := haddr144'
  have hvalR944 : ValueRepr cR.σ.mem N φcvR (sp.toNat - 944) vr := by
    rw [hsub944R] at hvalR; exact hvalR
  -- === LEFT value survival across the RIGHT sub-call ===
  -- agreement cL.mem ↔ cR.mem outside [SL.lo,sp-1088) ∪ A ∪ [sp-944,+24)
  have hAgLR : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → cL.σ.mem[k]? = cR.σ.mem[k]? := by
    intro k h1 h2 h3
    have e1 : cL.σ.mem[k]? = mcall2[k]? := by
      show cL.σ.mem[k]? = (writeMap8 cL.σ.mem (sp.toNat - 1088) _)[k]?
      rw [getElem_writeMap8_disjoint cL.σ.mem (sp.toNat - 1088) k _ (by omega)]
    have e2 : mcall2[k]? = cR.σ.mem[k]? := by
      rcases hmemFrameR k (fun ⟨ha, hb⟩ => h1 ⟨ha, by omega⟩) h2 with hin | heq
      · exact absurd hin (by rw [hsub944R] at *; exact h3)
      · exact heq.symm
    rw [e1, e2]
  have hvalL968 : ValueRepr cL.σ.mem N φcvL (sp.toNat - 968) vl := by
    rw [hsub968] at hvalL; exact hvalL
  have hvalL_R : ValueRepr cR.σ.mem N φcvL (sp.toNat - 968) vl :=
    hVlSurv φcvL cL.σ.mem cR.σ.mem hvalL968 (fun k h1 h2 h3 => hAgLR k h1 h2 h3)
  -- bring `vr` and `vl` under a common φ-map: `φcvR` extends `φc` (right) and `φcvL`
  -- extends `φc` (left) — but `vl` was represented at `φcvL`. We expose both at `φcvR`
  -- via the closure-monotonicity of `ValueRepr` — for the `TwoSubReturn` we simply
  -- keep them at their own maps by widening the existential to a single `φcvR` and
  -- re-deriving `vl` at `φcvR` (the left value's closure indices, if any, are a
  -- prefix that `φcvR ⊇ φc` also fixes; here we thread `φcvR`).
  -- Frame: bridge `gR7` back to `gpre` (all AbiPreservedNoise except x19).
  have hframeGpre : ∀ R : Register, AbiPreservedNoise R → (Register.x19 == R) = false →
      cR.σ.regs.get? R = gpre R := by
    intro R hR h19
    exact (hframeR R hR).trans (hframeτ7_excl R hR h19)
  -- s3 spill slot `[sp-40, sp-32)` survives both sub-calls + the respill store:
  -- it holds the entry `s3` value `v19` (spilled at 0x800034f0, disjoint from all).
  have hs3spill : read64 cR.σ.mem (sp.toNat - 40) = some v19.toNat := by
    -- ment[sp-40] respilled to v19 (ma), survives to cR.mem
    have hma40 : read64 ma (sp.toNat - 40) = some v19.toNat := by
      have := read64_writeMap8 ment (sp.toNat - 40) (sdData_val v19)
      rw [this, sdData_toNat]
    -- ma → mcall1 (sp-1088 write, disjoint), mcall1 → cL.mem (left memFrame),
    -- cL.mem → mcall2 (sp-1088 write), mcall2 → cR.mem (right memFrame)
    have hmcall1_40 : read64 mcall1 (sp.toNat - 40) = some v19.toNat := by
      show read64 (writeMap8 ma (sp.toNat - 1088) _) (sp.toNat - 40) = some v19.toNat
      rw [read64_writeMap8_disj ma (sp.toNat - 40) (sp.toNat - 1088) _ (by omega)]; exact hma40
    have hcL_40 : read64 cL.σ.mem (sp.toNat - 40) = some v19.toNat := by
      rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
        (a := sp.toNat - 40) (m := mcall1) (m' := cL.σ.mem)
        (fun a ha => ?_) (fun j hj => ⟨by omega, by omega⟩)]
      · exact hmcall1_40
      · rcases hmemFrameL a (by omega) (by rcases hBE.arenaStk with h | h <;> omega) with hin | heq
        · exact absurd hin (by omega)
        · exact heq.symm
    rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (a := sp.toNat - 40) (m := cL.σ.mem) (m' := cR.σ.mem)
      (fun a ha => hAgLR a (by omega) (by rcases hBE.arenaStk with h | h <;> omega) (by omega))
      (fun j hj => ⟨by omega, by omega⟩)]
    exact hcL_40
  -- assemble `TwoSubReturn`
  have hchain : Steps c cR :=
    (Steps.single hstep1).trans <| (Steps.single hstep2).trans <| (Steps.single hstep3).trans <|
      (Steps.single hstep4).trans <| hsL.trans <| (Steps.single hstepτ1).trans <|
      (Steps.single hstepτ2).trans <| (Steps.single hstepτ3).trans <| (Steps.single hstepτ4).trans <|
      (Steps.single hstepτ5).trans <| (Steps.single hstepτ6).trans <| (Steps.single hstepτ7).trans hsR
  refine ⟨cR, hchain,
    hGR, htickR, hpcR, hraR, hs1R, hspR, ⟨vmiR, hmiR⟩, houtR, hframeGpre,
    ⟨v19, hgx19v, hs3spill⟩,
    ⟨φf1, φc1, hpf1, hpc1',
      ⟨φcvR, hpcvR, hvalR944⟩, ⟨φcvL, hvalL_R⟩,
      ⟨φf2, φc2, hpf2, hpc2'', hstore2', hstoreSurv2'⟩⟩,
    hcodeR, hslotRaR, hslotS0R, hslotS1R, hslotS2R, ?_, ?_⟩
  · -- MemExtends m0 cR.mem (chain: m0 → ment → mcall1 → cL.mem → mcall2 → cR.mem)
    exact hMemExtM0.trans (hMemExtMent1.trans (hMemExtL.trans
      ((memExtends_writeMap8 cL.σ.mem (sp.toNat - 1088) _).trans hMemExtR)))
  · -- memframe m0 outside [SL.lo, sp) ∪ A: cR.mem = m0 there (chain of frames)
    intro a hstk harn
    have e_m0_ment : m0[a]? = ment[a]? := (hmemframe_m0 a hstk).symm
    have e_ment_mcall1 : ment[a]? = mcall1[a]? := hAgMcall1 a hstk
    have e_mcall1_cL : mcall1[a]? = cL.σ.mem[a]? := by
      rcases hmemFrameL a (fun ⟨hlo, hhi⟩ => hstk ⟨hlo, by omega⟩) harn with hin | heq
      · exact absurd hin (fun ⟨hlo, hhi⟩ => hstk ⟨by omega, by omega⟩)
      · exact heq.symm
    have e_cL_mcall2 : cL.σ.mem[a]? = mcall2[a]? := hAgMcall2 a hstk
    have e_mcall2_cR : mcall2[a]? = cR.σ.mem[a]? := by
      rcases hmemFrameR a (fun ⟨hlo, hhi⟩ => hstk ⟨hlo, by omega⟩) harn with hin | heq
      · exact absurd hin (by rw [hsub944R]; intro ⟨hlo, hhi⟩; exact hstk ⟨by omega, by omega⟩)
      · exact heq.symm
    rw [e_mcall2_cR.symm, e_cL_mcall2.symm, e_mcall1_cL.symm, e_ment_mcall1.symm, e_m0_ment.symm]

end Vsa.Sim
