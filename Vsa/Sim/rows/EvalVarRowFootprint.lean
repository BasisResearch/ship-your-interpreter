import Vsa.Sim.rows.EvalVarRow
import Vsa.Sim.ExitFootprint

/-!
# `EvalVarRowFootprint` — the variable leaf at the footprint-carrying exit
(IH tower, Level 1B)

The four literal leaves reach `EvalIHF noArenaFoot` for free (`LeafFootprint.lean`:
their pinned exit's `LeafMemPin.agree` IS the `noArenaFoot` footprint).  The
variable leaf has no pinned sibling, because the `env_get` FOUND-case contract it
consumes (`VarPostCall`, `EvalVarSim.lean`) states its memory frame with the ARENA
CARVED OUT:

    ∀ a, ¬ (SL.lo ≤ a < sp) → ¬ (A.lo ≤ a < A.hi) →
      (sret ≤ a < sret+24) ∨ mpc[a]? = m0[a]?

`env_get` never touches the arena — its whole write set is `[out, out+24) ∪
[sp0-64, sp0)` with `out = (sp-1088)+0xf0` and `sp0 = sp-1088`, both inside the
caller's live stack window `[SL.lo, sp)` (the entry's `StackOK SL sp 2176` leaves
1152 bytes below `sp-1088`).  That precise frame IS proved:
`EnvGetSpec10.env_get_found_framed` carries
`∀ a, EnvGetFootprint out sp0 a → m'[a]? = m0[a]?`.  It is DROPPED when the call
seam repackages the callee post into `VarPostCall` (`VarCallLinkage.finalMemFrame`,
`rows/EvalVarBridge.lean`, is stated arena-carved).

So this file threads the missing conjunct as a residual on the arm's own oracle:

* `VarPostCallPin SL sp m0 mpc` — the call-return memory is the entry memory
  outside the live stack window (no arena drift).  Supplier:
  `EnvGetFramedPost`'s frame + the entry stack geometry
  (`Vsa.Sim.envGetFramedPost_pin`, `rows/EvalVarBridgeCallee.lean`).
* `VarLeafResidF` — the pinned sibling of `Rows.VarLeafResid`: the SAME six
  geometry conjuncts and the same identity-map widener, with the `env_get_found`
  oracle's post strengthened by `VarPostCallPin`.  `varLeafResid_of_F` projects it
  back to the landed residual, so nothing downstream changes.
* `evalVarIHF` / `eval_var_rowF` — the variable leaf at `EvalIHF noArenaFoot`
  (the EXACT footprint family of the four literal leaves; no window mismatch),
  through `Vsa.Sim.evalVarSimQ` (which retains the call-return memory and the
  arm's own three-word copy window `[sret, sret+24)`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
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

/-- **The missing `env_get` write-set conjunct.**  The `env_get` call-return memory
`mpc` is the arm-entry memory `m0` outside the caller's live stack window
`[SL.lo, sp)`: `env_get` writes only its own frame `[sp-1152, sp-1088)` and the
result buffer `[(sp-1088)+0xf0, +24)`, both inside that window, and it never
allocates.  Supplier: `Vsa.Sim.envGetFramedPost_pin`
(`rows/EvalVarBridgeCallee.lean`) over `EnvGetSpec10.env_get_found_framed`. -/
def VarPostCallPin (SL : StackLayout) (sp : BitVec 64) (m0 mpc : Mem) : Prop :=
  ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mpc[a]? = m0[a]?

set_option linter.unusedVariables false in
/-- **The pinned var-leaf residual** — `Rows.VarLeafResid` with the `env_get_found`
oracle's post carrying `VarPostCallPin`.  Every other field is verbatim, so
`varLeafResid_of_F` projects it onto the landed residual. -/
def VarLeafResidF (st : SpecSt) (x : String) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    st.store.get? env x = some v →
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.var x) sp r sret aEnv aExpr m0 c →
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + x.length < SL.lo ∨ sp.toNat ≤ p) ∧
    (sret.toNat + 24 ≤ A.lo ∨ A.hi ≤ sret.toNat) ∧
    Vsa.Sim.Code.Env_getLoaded c.σ.mem ∧
    ((0x80002cdc : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80002c10) ∧
    Vsa.Sim.VarSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 20 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 16) ∧
    Triple
      (fun c' => ∃ ment v8 v9 v18,
        Vsa.Sim.ArmEntryK g N A SL φf φc st (0x80003434#64) Vsa.Sim.Code.Env_getLoaded (.var x)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c' ∧
        c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)))
      (fun c' => ∃ mpc v8 v9 v18,
        Vsa.Sim.VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 c.σ.sailOutput m0 mpc c' ∧
        VarPostCallPin SL sp m0 mpc) ∧
    Vsa.Sim.LeafReturnWiden g N A SL φf φc st v sp r sret m0

/-- The landed residual is the projection of its pinned sibling (drop the pin). -/
theorem varLeafResid_of_F (st : SpecSt) (x : String) (v : Value)
    (hR : VarLeafResidF st x v) : VarLeafResid st x v := by
  intro g N A SL φf φc d env sp r sret aEnv aExpr m0 c hlookup hc
  obtain ⟨hvsd, hsad, hegc, hegsd, hvs, htsd, hfoundF, hW⟩ :=
    hR g N A SL φf φc d env sp r sret aEnv aExpr m0 c hlookup hc
  refine ⟨hvsd, hsad, hegc, hegsd, hvs, htsd, ?_, hW⟩
  intro c' hpre
  obtain ⟨c'', hs, mpc, v8, v9, v18, hVPC, _⟩ := hfoundF c' hpre
  exact ⟨c'', hs, mpc, v8, v9, v18, hVPC⟩

/-- **The variable leaf at `EvalIHF noArenaFoot`.**  The arm's whole delta from the
entry memory is `env_get`'s own frame (inside `[SL.lo, sp)`, by the pin) followed by
the epilogue's three-word copy into `[sret, sret+24)` (`evalVarSimQ`'s retained
window) — exactly `noArenaFoot`, the family the four literal leaves land at. -/
theorem evalVarIHF (hR : ∀ st x v, VarLeafResidF st x v)
    (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
    (hlookup : st.store.get? env x = some v) :
    Vsa.Sim.EvalIHF Vsa.Sim.noArenaFoot st d env (Expr.var x) st v := by
  refine Vsa.Sim.EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  intro c hc
  obtain ⟨hvsd, hsad, hegc, hegsd, hvs, htsd, hfoundF, hW⟩ :=
    hR st x v g N A SL φf φc d env sp r sret aEnv aExpr m0 c hlookup hc
  have hfound : Triple
      (fun c' => ∃ ment v8 v9 v18,
        Vsa.Sim.ArmEntryK g N A SL φf φc st (0x80003434#64) Vsa.Sim.Code.Env_getLoaded (.var x)
          sp r sret aExpr aEnv v8 v9 v18 c.σ.sailOutput m0 ment c' ∧
        c'.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf env)))
      (fun c' => ∃ mpc v8 v9 v18,
        Vsa.Sim.VarPostCall g N A SL φf φc st v sp r sret v8 v9 v18 c.σ.sailOutput m0 mpc c') := by
    intro c' hpre
    obtain ⟨c'', hs, mpc, v8, v9, v18, hVPC, _⟩ := hfoundF c' hpre
    exact ⟨c'', hs, mpc, v8, v9, v18, hVPC⟩
  have hEntry : Vsa.Sim.EvalVarEntry g N A SL φf φc st d env x v sp r sret aEnv aExpr m0 c :=
    { good := hc.good, tick := hc.tick, pc := hc.pc, a0 := hc.a0, a1 := hc.a1, a2 := hc.a2,
      ra := hc.ra, ra_align := hc.ra_align, spReg := hc.spReg, stackOK := hc.stackOK,
      stackBudget := hc.stackBudget, expr_bodies := hc.expr_bodies,
      store_bodies := hc.store_bodies, minstret := hc.minstret, mem := hc.mem,
      code := hc.code, expr := hc.expr, store := hc.store,
      store_survives := hc.store_survives, out := hc.out, frame := hc.frame,
      code_stack_disjoint := hc.code_stack_disjoint,
      expr_stack_disjoint := hc.expr_stack_disjoint,
      expr_ram := hc.expr_ram, expr_win := hc.expr_win,
      sret_align := hc.sret_align, sret_ram := hc.sret_ram, sret_win := hc.sret_win,
      sret_vicode_disjoint := hc.sret_vicode_disjoint_int,
      sret_stack_disjoint := hc.sret_stack_disjoint,
      sret_evalcode_disjoint := hc.sret_evalcode_disjoint, stack_ram := hc.stack_ram,
      stack_win := hc.stack_win, spill_defined := hc.spill_defined,
      x13_defined := hc.x13_defined, envReg := hc.envReg,
      var_stack_disjoint := hvsd, sret_arena_disjoint := hsad, env_get_code := hegc,
      env_get_stack_disjoint := hegsd, var_slot := hvs, table_stack_disjoint := htsd,
      env_get_found := hfound }
  obtain ⟨c', hs, hExit, hval, mpc, hpin, hagree⟩ :=
    Vsa.Sim.evalVarSimQ (VarPostCallPin SL sp m0) g N A SL φf φc st d env x v
      sp r sret aEnv aExpr m0 c hEntry hfoundF
  refine ⟨c', hs, Vsa.Sim.evalExitD_of_evalExit hExit hW.toLeafWiden (hc.mem ▸ hc.sret_words),
    ⟨fun k hk => ?_⟩⟩
  have hstk : ¬ (SL.lo ≤ k ∧ k < sp.toNat) := fun h => hk (Or.inl h)
  have hsr : ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) := fun h => hk (Or.inr h)
  exact (hagree k hsr).symm.trans (hpin k hstk)

/-- **Slot-verify** — `evalVarIHF` at the generator's `hVar` field type for the
`Footprint` clause (motive `EvalIHF noArenaFoot`): the landed `mEvalE` result of the
case is consumed for free. -/
theorem eval_var_rowF (hR : ∀ st x v, VarLeafResidF st x v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value)
      (a : st.store.get? env x = some v),
      mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a) →
      Vsa.Sim.EvalIHF Vsa.Sim.noArenaFoot st d env (Expr.var x) st v :=
  fun st d env x v a _ => evalVarIHF hR st d env x v a

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.varLeafResid_of_F
#print axioms Vsa.Sim.Rows.evalVarIHF
#print axioms Vsa.Sim.Rows.eval_var_rowF
