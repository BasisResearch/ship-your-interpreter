import Vsa.Sim.ArmEntryRetained
import Vsa.Sim.EnvGetReflected.EvalVarArm
import Vsa.Sim.EnvGetReflected.EnvGetEntryTransport
import Vsa.Sim.Code.FixedImage_Env_get
import Vsa.Sim.EnvGetReflected.EnvGetRuntimeData
import Vsa.Sim.Code.FixedImage_Strcmp

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The evaluator result retains its exact memory frame and owned value. -/
structure VarEvalResult
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations) (shared : Nat → Prop)
    (st : Vsa.While.St) (v : Vsa.While.Value) (sp ret dst : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  returned : EvalReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
    st v sp ret dst m0
    (fun f c m => StoreOwned m f c alloc shared st.store ∧ ValueOwned m shared dst.toNat v) c
  memory : LeafMemPin SL sp dst m0 c.σ.mem
  value : ValueWordRepr c.σ.mem N phiC dst.toNat v
  owned : ValueOwned c.σ.mem shared dst.toNat v
  runtime : ∃ exts, StoreRuntimeData N A SL phiF phiC alloc exts shared st.store c.σ.mem

/-- Run a variable from the evaluator entry using its owned source store.
Prologue, lookup, and final return share one execution and one representation. -/
theorem eval_var_return
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value} {d fa : Nat}
    {name sp dst ret aExpr aEnv : BitVec 64} {m0 : Mem} {c : Config}
    (entry : EvalEntry g N A SL phiF phiC st d fa (.var query) sp ret dst aEnv aExpr m0 c)
    (D : LookupData N A SL phiF phiC alloc exts shared st.store query name c.σ.mem)
    (hget : st.store.get? fa query = some v)
    (hread : read64 c.σ.mem (aExpr.toNat + 8) = some name.toNat)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    ∃ after, Steps c after ∧
      VarEvalResult g N A SL phiF phiC alloc shared st v sp ret dst m0 after := by
  have hg : EvalGround m0 SL A sp dst aExpr.toNat (.var query) := entry.mem ▸ entry.ground
  have he : ExprRepr m0 aExpr.toNat (.var query) := entry.mem ▸ entry.expr
  have hkind : read32 m0 aExpr.toNat = some 4 := by
    cases he with | var hk _ _ => exact hk
  have hexpr : ∀ m', (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m0[k]? = m'[k]?) →
      ExprRepr m' aExpr.toNat (.var query) := by
    intro m' ha
    obtain ⟨lo, hi, hb⟩ := hg.ast.region
    apply exprRepr_agree_region (lo := lo) (hi := hi) _ hb.nodes he
    intro k hk
    apply ha k
    change lo ≤ k ∧ k < hi at hk
    have := hb.stack_disjoint
    have := entry.stackOK.2.1
    omega
  have hcalleeSurv : ∀ (mem : Mem) (a : Nat) (word : BitVec (8 * 8)),
      SL.lo ≤ a → a + 8 ≤ sp.toNat → Code.Env_getLoaded mem →
      Code.Env_getLoaded (writeMap8 mem a word) := by
    intro mem a word hlo hhi hcode
    apply loaded_env_get_writeMap8 mem a word _ hcode
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := entry.stack_win
    omega
  obtain ⟨arm, hp, out0, ment, r8, r9, r18, reached⟩ :=
    armEntry_retained g N A SL phiF phiC st d fa (.var query)
      4 0x80003434#64 Code.Env_getLoaded sp ret dst aEnv aExpr m0
      (by decide) (by decide) hkind hg.table.slot4 hg.eval_call.image.text.Env_getLoaded
      hcalleeSurv hexpr (by decide) (by
        have := entry.table_stack_disjoint
        change 0x80019f58 + 4 * 4 + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 4 * 4
        omega) c entry
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x80003434#64 Code.Env_getLoaded
    (.var query) sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment arm reached.arm
  have hframe : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → arm.σ.mem[k]? = c.σ.mem[k]? := by
    intro k hk
    rw [entry.mem, p.mem]
    exact p.memFrame k (by have := entry.stackOK.2.1; omega)
  have DA := D.after_stack arena entry.stack_win hframe
  have hsupport : EvalCallSupport arm.σ.mem SL A sp := entry.ground.eval_call.transport_stack hframe
  have hreadA : read64 arm.σ.mem (aExpr.toNat + 8) = some name.toNat := by
    have ha : ∀ k, aExpr.toNat + 8 ≤ k ∧ k < aExpr.toNat + 16 →
        arm.σ.mem[k]? = c.σ.mem[k]? := by
      intro k hk
      rw [entry.mem, p.mem]
      exact p.memFrame k (by have := entry.expr_stack_disjoint; omega)
    exact (read64_agreeP ha (fun k hk => by omega)).trans hread
  obtain ⟨r19, r20, r21, h19, h20, h21⟩ := entry.envset_defined
  have hregs (R : Register) (hR : AbiPreservedNoise R)
      (h8 : (Register.x8 == R) = false) (h9 : (Register.x9 == R) = false)
      (h18 : (Register.x18 == R) = false) (h2 : (Register.x2 == R) = false) :
      arm.σ.regs.get? R = c.σ.regs.get? R :=
    (p.frame R hR h8 h9 h18 h2).trans (entry.frame R hR).symm
  have ha19 := (hregs .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19
  have ha20 := (hregs .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20
  have ha21 := (hregs .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21
  have hroom : SL.lo + 2176 ≤ sp.toNat := entry.stackOK.1
  obtain ⟨after, hr⟩ := var_arm_run reached.arm DA hget reached.environment ha19 ha20 ha21
    hreadA hsupport.image.text.StrcmpLoaded hroom entry.stackOK.2.1 entry.stack_ram.2
    entry.ground.sret_inSL arena
  exact ⟨after, hp.trans hr.steps,
    { returned := hr.at_arm reached.arm reached.presence ha19 ha20 ha21 (by omega) arena
      memory := ⟨reached.presence.trans hr.extendsMemory, fun k hk hd =>
        (hr.outside k (var_lookup_windows (SL := SL) (by omega) k hk) hd).trans
          (by rw [p.mem]; exact p.memFrame k hk)⟩
      value := hr.value, owned := hr.owned
      runtime := ⟨exts, hr.data.runtime arena⟩ }⟩

#print axioms eval_var_return

end Vsa.Sim.EnvGetReflected
