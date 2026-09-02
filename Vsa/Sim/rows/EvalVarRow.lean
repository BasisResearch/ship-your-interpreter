import Vsa.Sim.EvalLeafD
import Vsa.Sim.TermCaseBundle

/-!
# `EvalVarRow` — the `hVar` term-side case row (conditional leaf_bridge)

The `EvalE.var` premise of `term_sim_of_cases`/`execSeq_sim_of_cases`
(`TermCaseBundle.lean:41`) is

    ∀ st d env x v (a : st.store.get? env x = some v),
      mEvalE st d env (.var x) st v (EvalE.var st d env x v a)

which is `EvalIH st d env (.var x) st v` = `∀ ghosts, Triple (EvalEntry …) (EvalExitD …)`
by definitional unfolding (`EvalRecCommon.EvalIH`).  `evalVarSimD`
(`EvalLeafD.lean:186`) discharges exactly that Triple, but from the RICHER entry
`EvalVarEntry` (which carries, beyond the 32 shared `EvalEntry` fields, the var-arm
geometry AND the honest `env_get`-FOUND-case caller-linkage oracle `env_get_found`).

So `eval_var_row` is a **conditional leaf_bridge** (survey §5, deviation 3): the
same shape as `eval_null_row`/`eval_str_row` (`rows/TermRouting.lean`) — build
`EvalVarEntry` from the 32 shared `EvalEntry` projections plus a per-case residual
`VarLeafResid`, then apply `evalVarSimD` — EXCEPT the residual additionally carries
the `env_get_found` **`Triple` oracle** (keyed on the entry config `c`, since its
statement mentions `c.σ.sailOutput`/`m0 = c.σ.mem`).  This is the ONE genuinely-open
`O`-class field of `hVar`; the rest of `VarLeafResid` is `G`-class geometry.

The `env_get_found` oracle is DISCHARGEABLE (no longer "designed but not proven"):
`EnvGetSpec9.env_get_found_uncond''` proves the whole immediate-frame FOUND case
(prologue ≫ scan `Triple.loop` ≫ strcmp cross-call ≫ HIT-tail) UNCONDITIONALLY
modulo honest caller geometry (`FoundSt` + `FrameStackDisj`).  What remains between
`env_get_found_uncond''` and `EvalVarEntry.env_get_found` is the eval-var-arm CALL
LINKAGE bridge (arg-setup prefix `0x80003434→jal env_get`, `FoundSt` construction
from the arm's live state, and the `env_get` post → `VarPostCall` repackaging), a
`callSeg`-style machine splice.  Until that bridge lands, the row threads
`env_get_found` as the named residual — exactly the survey's "conditional
leaf_bridge" for `hVar`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.TermSimAssembly

namespace Vsa.Sim.Rows

local notation "SpecSt" => Vsa.While.St

/-- The var-leaf residual: the geometry `EvalVarEntry` carries beyond `EvalEntry`
(`var_stack_disjoint`, `sret_arena_disjoint`, `env_get_code`,
`env_get_stack_disjoint`, `var_slot`, `table_stack_disjoint`), the honest
`env_get`-FOUND-case caller-linkage oracle `env_get_found` (the ONE open `O`-class
field), and the `LeafWiden` exit widening.  ∀-closed over the layout ghosts AND the
entry config `c` (the oracle's statement mentions `c.σ.mem`/`c.σ.sailOutput`). -/
def VarLeafResid (st : SpecSt) (x : String) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.var x) sp r sret aEnv aExpr m0 c →
    -- var-name CString disjoint from the live stack frame
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + x.length < SL.lo ∨ sp.toNat ≤ p) ∧
    -- sret disjoint from the store's arena (the copy writes only `[sret, sret+24)`)
    (sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat) ∧
    Vsa.Sim.Code.Env_getLoaded c.σ.mem ∧
    ((0x80002cdc : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80002c10) ∧
    Vsa.Sim.VarSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 20 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 16) ∧
    -- the honest `env_get`-FOUND-case contract (open `O`-class oracle):
    Triple
      (fun c' => ∃ ment v8 v9 v18,
        Vsa.Sim.ArmEntryK g N A SL φf φc st (0x80003434#64) Vsa.Sim.Code.Env_getLoaded (.var x)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c')
      (fun c' => ∃ mpc v8 v9 v18,
        Vsa.Sim.VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 c.σ.sailOutput m0 mpc c') ∧
    Vsa.Sim.LeafWiden g N A SL φf φc st v sp r sret m0

/-- Route `hVar` → `evalVarSimD`, bridging `EvalEntry → EvalVarEntry`.

Conditional: the residual `VarLeafResid` threads the `env_get_found` caller-linkage
oracle (see the header — dischargeable from `env_get_found_uncond''` once the
eval-var-arm call bridge lands). -/
theorem eval_var_row (hR : ∀ st x v, VarLeafResid st x v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
      (a : st.store.get? env x = some v),
      mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a) := by
  intro st d env x v hlookup
  show Vsa.Sim.EvalIH st d env (.var x) st v
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  intro c hc
  obtain ⟨hvsd, hsad, hegc, hegsd, hvs, htsd, hfound, hW⟩ :=
    hR st x v g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  have hEntry : Vsa.Sim.EvalVarEntry g N A SL φf φc st d env x v sp r sret aEnv aExpr m0 c :=
    { good := hc.good, tick := hc.tick, pc := hc.pc, a0 := hc.a0, a1 := hc.a1, a2 := hc.a2,
      ra := hc.ra, ra_align := hc.ra_align, spReg := hc.spReg, stackOK := hc.stackOK,
      stackBudget := hc.stackBudget, expr_bodies := hc.expr_bodies, store_bodies := hc.store_bodies,
      minstret := hc.minstret, mem := hc.mem, code := hc.code, expr := hc.expr, store := hc.store,
      store_survives := hc.store_survives, out := hc.out, frame := hc.frame,
      code_stack_disjoint := hc.code_stack_disjoint, expr_stack_disjoint := hc.expr_stack_disjoint,
      expr_align := hc.expr_align, expr_ram := hc.expr_ram, expr_win := hc.expr_win,
      sret_align := hc.sret_align, sret_ram := hc.sret_ram, sret_win := hc.sret_win,
      sret_vicode_disjoint := hc.sret_vicode_disjoint, sret_stack_disjoint := hc.sret_stack_disjoint,
      sret_evalcode_disjoint := hc.sret_evalcode_disjoint, stack_ram := hc.stack_ram,
      stack_win := hc.stack_win, spill_defined := hc.spill_defined,
      var_stack_disjoint := hvsd, sret_arena_disjoint := hsad, env_get_code := hegc,
      env_get_stack_disjoint := hegsd, var_slot := hvs, table_stack_disjoint := htsd,
      env_get_found := hfound }
  exact Vsa.Sim.evalVarSimD g N A SL φf φc st d env x v sp r sret aEnv aExpr m0
    (EvalE.var st d env x v hlookup) hW c hEntry

/-- **Slot-verify.** `eval_var_row` fills the EXACT `hVar` minor-premise slot of
`term_sim_of_cases` (`TermCaseBundle.TermCases.hVar`): the type below is the
verbatim premise type; the term type-checks iff the row's conclusion matches it. -/
theorem eval_var_row_fills_hVar (hR : ∀ st x v, VarLeafResid st x v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
      (a : st.store.get? env x = some v),
      mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a) :=
  eval_var_row hR

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.eval_var_row
#print axioms Vsa.Sim.Rows.eval_var_row_fills_hVar
