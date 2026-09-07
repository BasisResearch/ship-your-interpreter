import Vsa.Sim.EvalReturn
import Vsa.Sim.EvalNegSim

open LeanRV64DExecutable Sail Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- Execute the existing recursive call splice with a coherent child contract.
Its extra result retains the call's entry maps and selected return ownership. -/
def armTail_rec_coherent
    {Owned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st st' : Vsa.While.St) (d env : Nat) (esub : Expr) (vsub : Value)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem)
    (hjaltgt : callPC + LeanRV64DExecutable.Functions.sign_extend (m := 64) jalImm =
      BitVec.ofNat 64 evalExprEntry)
    (hlink : BitVec.addInt callPC 4 = retPC) (hretAl : retPC.toNat % 4 = 0)
    (henvValid : EnvValid st env)
    (hjalSite : ∀ (sigma : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState sigma → sigma.regs.get? Register.PC = some callPC →
      sigma.regs.get? Register.minstret = some vmi → Eval_exprLoaded sigma.mem → i < 2 →
      ∃ (sigma' : MState) (i' : Nat),
        Step ⟨sigma, i, u⟩ ⟨sigma', i', u + 1⟩ ∧ i' < 2 ∧ GoodState sigma' ∧
        sigma'.mem = sigma.mem ∧
        ReadsLikePost sigma' (sigmaPost_jal sigma callPC vmi jalImm
          Register.x1 (BitVec.addInt callPC 4)))
    (hIH : EvalReturnIH Owned st d env esub st' vsub) :=
  armTail_rec_with gpre N A SL phiF phiC st st' d env esub vsub
    callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall
    hjaltgt hlink hretAl henvValid hjalSite hIH.withMaps

/-- Unary dispatch, argument setup, and child call retain one coherent return.
The memory and representation evidence describe the same reached execution. -/
def blockB_unary_coherent
    {Owned : NativeAddrs → Arena → (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st st' : Vsa.While.St) (d env : Nat) (op : UnOp) (esub : Expr) (vsub : Value)
    (sp r sret aExpr aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (m0 : Mem) (henvValid : EnvValid st env)
    (henvset : ∃ v19 v20 v21 : BitVec 64,
      gpre Register.x19 = some v19 ∧ gpre Register.x20 = some v20 ∧
      gpre Register.x21 = some v21)
    (hIH : EvalReturnIH Owned st d env esub st' vsub) :=
  blockB_unary_with gouter gpre N A SL phiF phiC st st' d env op esub vsub
    sp r sret aExpr aIn aOperand v8 v9 v18 out0 m0 henvValid henvset hIH.withMaps

#print axioms armTail_rec_coherent
#print axioms blockB_unary_coherent

end Vsa.Sim
