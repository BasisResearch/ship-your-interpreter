import Vsa.Sim.ArmEntryWiden
import Vsa.Sim.DeriveMetaTowers

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Retain the prologue's presence and environment register at its arm endpoint. -/
structure ArmEntryRetained
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (armPC : BitVec 64) (callee : Mem → Prop) (e : Expr)
    (sp ret dst aExpr aEnv r8 r9 r18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config) : Prop where
  arm : ArmEntryK g N A SL phiF phiC st armPC callee e
    sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c
  presence : MemExtends m0 c.σ.mem
  environment : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (phiF env))

/-- The existing dispatch execution supplies all retained facts together. -/
theorem armEntry_retained
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (phiF phiC : Addr → Nat)
    (st : Vsa.While.St) (d env : Nat) (e : Expr)
    (k : Nat) (armPC : BitVec 64) (callee : Mem → Prop)
    (sp ret dst aEnv aExpr : BitVec 64) (m0 : Mem)
    (hkle : k ≤ 10) (hklt : k < 128)
    (hkind : read32 m0 aExpr.toNat = some k)
    (hslot : KindSlotPinned k armPC m0) (hcallee : callee m0)
    (hcalleeSurv : ∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
      SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → callee mem → callee (writeMap8 mem a8 dd))
    (hexprSurv : ∀ m' : Mem,
      (∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) → ExprRepr m' aExpr.toNat e)
    (harmAl : armPC.toNat % 4 = 0)
    (htableStk : jumpTableBase + 4 * k + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * k) :
    Triple
      (EvalEntry g N A SL phiF phiC st d env e sp ret dst aEnv aExpr m0)
      (fun c => ∃ out0 ment r8 r9 r18,
        ArmEntryRetained g N A SL phiF phiC st env armPC callee e
          sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c) := by
  intro c hc
  obtain ⟨after, hs, ment, r8, r9, r18, _, hArm, hPresence, hEnv⟩ :=
    blockA_k g N A SL phiF phiC st env e k armPC callee
      sp ret dst aEnv aExpr m0 c.σ.sailOutput
      hkle hklt hkind hslot hcallee hcalleeSurv hexprSurv harmAl htableStk c
      ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint_int,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        ⟨hc.spill_defined.1, hc.spill_defined.2.1, hc.spill_defined.2.2, hc.envReg⟩⟩, rfl⟩
  have p := ArmEntryK.destruct g N A SL phiF phiC st armPC callee e
    sp ret dst aExpr aEnv r8 r9 r18 c.σ.sailOutput m0 ment after hArm
  exact ⟨after, hs, c.σ.sailOutput, ment, r8, r9, r18,
    hArm, by rw [p.mem]; exact hPresence, hEnv⟩

#print axioms armEntry_retained

end Vsa.Sim
