import Vsa.Sim.BinaryLeftStage
import Vsa.Sim.DeriveMetaTowers

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim

/-- Facts carried from binary dispatch, with both children's stack and body bounds. -/
structure BinaryArmReady
    (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (d env : Nat) (op : BinOp) (el er : Expr)
    (sp ret dst node interp left right envReg v8 v9 v18 v19 : BitVec 64)
    (out : Array String) (m0 : Mem) (before : Config) : Prop where
  arm : ArmEntryK g N A SL phiF phiC st 0x800034e8#64 UnaryArmCallee
    (.binary op el er) sp ret dst node interp v8 v9 v18 out m0 before.σ.mem before
  geometry : BinExtras N A SL el er before.σ.mem sp dst node left right
  recursion : BinaryRecContext gpre phiF st env envReg
  environment : before.σ.regs.get? Register.x13 = some envReg
  saved19 : before.σ.regs.get? Register.x19 = some v19
  frame : ∀ R, AbiPreservedNoise R → before.σ.regs.get? R = gpre R
  ghostNode : gpre Register.x8 = some node
  ghostInterp : gpre Register.x18 = some interp
  ghost19 : gpre Register.x19 = some v19
  leftRead : read64 before.σ.mem (node.toNat + 16) = some left.toNat
  rightRead : read64 before.σ.mem (node.toNat + 24) = some right.toNat
  presence : MemExtends m0 before.σ.mem
  ground : EvalGround before.σ.mem SL A sp dst node.toNat (.binary op el er)
  leftBudget : StackOK SL (sp - 1088#64)
    (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  rightBudget : StackOK SL (sp - 1088#64)
    (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088)
  leftBodies : Expr.bodiesBound Vsa.While.perCallBudget el = true
  rightBodies : Expr.bodiesBound Vsa.While.perCallBudget er = true
  storeBodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget

/-- The reflected left prefix consumes the reached arm facts directly. -/
theorem BinaryArmReady.stage_left
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {d env : Nat} {op : BinOp} {el er : Expr}
    {sp ret dst node interp left right envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {m0 : Mem} {before : Config}
    (h : BinaryArmReady g gpre N A SL phiF phiC st d env op el er
      sp ret dst node interp left right envReg v8 v9 v18 v19 out m0 before) :
    LandedN 4 before (BinaryLeftStaged gpre N A SL phiF phiC st d env el
      sp ret dst node interp left envReg v8 v9 v18 v19 out before) := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800034e8#64 UnaryArmCallee
    (.binary op el er) sp ret dst node interp v8 v9 v18 out m0 before.σ.mem before h.arm
  have leftRepr : ExprRepr before.σ.mem left.toNat el :=
    h.geometry.lexpr_surv before.σ.mem (fun _ _ => rfl)
  have rightRepr : ExprRepr before.σ.mem right.toNat er :=
    h.geometry.rexpr_surv before.σ.mem (fun _ _ _ => rfl)
  exact blockB_binary_leftStaged g gpre N A SL phiF phiC st d env op el er
    sp ret dst node interp left right envReg v8 v9 v18 v19 out m0 before h.recursion
    ⟨before.σ.mem, h.arm, h.geometry, p.a1, h.environment, h.recursion.env_addr,
      h.saved19, h.frame, ⟨node, h.ghostNode⟩, ⟨interp, h.ghostInterp⟩,
      h.ghostNode, h.ghostInterp, h.ghost19, h.leftRead, leftRepr,
      h.rightRead, rightRepr, h.presence, h.ground,
      h.leftBudget, h.leftBodies, h.storeBodies⟩

#print axioms BinaryArmReady.stage_left

end Vsa.Sim
