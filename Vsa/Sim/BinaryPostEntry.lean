import Vsa.Sim.BinaryEntry
import Vsa.Sim.DeriveMetaTowers

open LeanRV64DExecutable Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Retain the entry image at the actual return of both binary children. -/
theorem EvalEntry.binaryReturnImage
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : BinOp} {st st' st'' : Vsa.While.St} {d env : Nat} {el er : Expr}
    {vl vr : Value} {sp r sret aEnv aExpr v8 v9 v18 : BitVec 64}
    {m0 : Mem} {c c' : Vsa.Machine.Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.binary op el er)
      sp r sret aEnv aExpr m0 c)
    (hret : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size st' st'' vl vr sp r sret v8 v9 v18 m0 c') :
    StaticImageSupport c'.σ.mem SL A := by
  have hImage : StaticImageSupport m0 SL A := h.mem ▸ h.ground.eval_call.image
  have hs := h.stackBudget
  have parts := TwoSubReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size st' st'' vl vr sp r sret v8 v9 v18 m0 c' hret
  apply hImage.transport
  intro k hk
  have hstack := hImage.outsideStack hk
  exact parts.p18 k (by change StackOK SL sp _ at hs; unfold StackOK at hs; omega)
    (hImage.outsideArena hk)

/-- The operator word remains the represented source token after both children. -/
theorem EvalEntry.binaryReturnToken
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : BinOp} {st st' st'' : Vsa.While.St} {d env : Nat} {el er : Expr}
    {vl vr : Value} {sp r sret aEnv aExpr v8 v9 v18 : BitVec 64}
    {m0 : Mem} {c c' : Vsa.Machine.Config}
    (h : EvalEntry g N A SL phiF phiC st d env (.binary op el er)
      sp r sret aEnv aExpr m0 c)
    (hret : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size st' st'' vl vr sp r sret v8 v9 v18 m0 c') :
    read32 c'.σ.mem (aExpr.toNat + 8) = some (binOpTok op) := by
  have he : ExprRepr m0 aExpr.toNat (.binary op el er) := h.mem ▸ h.expr
  have hop : read32 m0 (aExpr.toNat + 8) = some (binOpTok op) := by
    cases he with
    | binary _ hop _ _ _ _ => exact hop
  have hg : EvalGround m0 SL A sp sret aExpr.toNat (.binary op el er) :=
    h.mem ▸ h.ground
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hn := exprIn_node spec.nodes
  have hnlo := hn.lo_le
  have hnhi := hn.hi_ge
  have hsp := h.stackOK
  unfold StackOK at hsp
  have parts := TwoSubReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size st' st'' vl vr sp r sret v8 v9 v18 m0 c' hret
  have hag : AgreeP (regionP lo hi) m0 c'.σ.mem := by
    intro k hk
    change lo ≤ k ∧ k < hi at hk
    apply (parts.p18 k ?_ ?_).symm
    · rcases spec.stack_disjoint with hd | hd <;> omega
    · rcases spec.arena_disjoint with hd | hd <;> omega
  rw [← read32_agreeP hag (fun k hk => by
    change lo ≤ aExpr.toNat + 8 + k ∧ aExpr.toNat + 8 + k < hi
    omega)]
  exact hop

#print axioms EvalEntry.binaryReturnToken

#print axioms EvalEntry.binaryReturnImage
end Vsa.Sim
