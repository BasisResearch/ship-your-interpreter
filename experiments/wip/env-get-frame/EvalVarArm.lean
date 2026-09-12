import EvalVarReturn

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Caller geometry and saved words supplied by the reached evaluator arm. -/
structure VarArmData (A : Arena) (SL : StackLayout) (m : Mem)
    (sp dst ret r8 r9 r18 : BitVec 64) : Prop where
  window : CallerTailWindow A SL ((sp - 1088#64) + 240#64) ((sp - 1088#64) - 64#64)
  tail : ValueTailGeom (sp - 1088#64) dst
  saved : ValueTailSaved m (sp - 1088#64) ret r8 r9 r18
  gap : tohostAddr + 64 ≤ (sp - 1088#64).toNat - 64

theorem var_arm_data
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {st : Vsa.While.St}
    {sp dst ret r8 r9 r18 aExpr aEnv armPC : BitVec 64}
    {callee : Mem → Prop} {e : Vsa.While.Expr} {out0 : Array String}
    {m0 ment : Mem} {c : Config}
    (entry : ArmEntryK g N A SL phiF phiC st armPC callee e
      sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c)
    (hroom : SL.lo + 2176 ≤ sp.toNat) (hspHi : sp.toNat ≤ SL.hi)
    (hSLHi : SL.hi ≤ 0x100000000)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    VarArmData A SL c.σ.mem sp dst ret r8 r9 r18 := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st armPC callee e
    sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c entry
  have h1088 : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have := sp.isLt
    change ((2^64 - 1088) + sp.toNat) % 2^64 = sp.toNat - 1088
    omega
  have h64 := sp_sub64_toNat (sp - 1088#64) (by rw [h1088]; omega)
  have hout : ((sp - 1088#64) + 240#64).toNat = sp.toNat - 848 := by
    rw [BitVec.toNat_add, h1088]
    have := sp.isLt
    change (sp.toNat - 1088 + 240) % 2^64 = sp.toNat - 848
    omega
  have hstkLo := p.stackLo
  have hstkWin := p.stackWin
  have hspAl := p.spAlign
  have hdst := p.sretStack
  have hs : ValueTailSaved c.σ.mem (sp - 1088#64) ret r8 r9 r18 := by
    rw [p.mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [h1088, show sp.toNat - 1088 + 1080 = sp.toNat - 8 by omega] using p.slotRa
    · simpa only [h1088, show sp.toNat - 1088 + 1072 = sp.toNat - 16 by omega] using p.slotS0
    · simpa only [h1088, show sp.toNat - 1088 + 1064 = sp.toNat - 24 by omega] using p.slotS1
    · simpa only [h1088, show sp.toNat - 1088 + 1056 = sp.toNat - 32 by omega] using p.slotS2
  exact
    { window :=
        { ram := ⟨hstkLo, hSLHi⟩, htif := hstkWin
          output := by rw [hout]; omega
          spill := by rw [h64, h1088]; omega
          outputAlign := by rw [hout]; omega
          outputSpill := by rw [hout, h64, h1088]; omega
          arena := arena }
      tail :=
        { stackLo := by rw [h1088]; omega
          stackHi := by rw [h1088]; omega
          stackHtif := by rw [h1088]; omega
          destLo := p.sretLo, destHi := p.sretHi, destHtif := p.sretWin
          destAlign := p.sretAlign
          savedDisjoint := by rw [h1088]; omega }
      saved := hs
      gap := by rw [h1088]; omega }

/-- Run the variable arm through its owned lookup, copy, and evaluator exit.
All extra premises describe the reached entry, not an arbitrary callee post. -/
theorem var_arm_run
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value} {fa : Nat}
    {name sp dst ret r8 r9 r18 r19 r20 r21 aExpr aEnv : BitVec 64}
    {out0 : Array String} {m0 ment : Mem} {c : Config}
    (entry : ArmEntryK g N A SL phiF phiC st 0x80003434#64 Code.Env_getLoaded (.var query)
      sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c)
    (D : LookupData N A SL phiF phiC alloc exts shared st.store query name c.σ.mem)
    (hget : st.store.get? fa query = some v)
    (henv : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (phiF fa)))
    (h19 : c.σ.regs.get? Register.x19 = some r19)
    (h20 : c.σ.regs.get? Register.x20 = some r20)
    (h21 : c.σ.regs.get? Register.x21 = some r21)
    (hread : read64 c.σ.mem (aExpr.toNat + 8) = some name.toNat)
    (hstrcmp : Code.StrcmpLoaded c.σ.mem)
    (hroom : SL.lo + 2176 ≤ sp.toNat) (hspHi : sp.toNat ≤ SL.hi)
    (hSLHi : SL.hi ≤ 0x100000000)
    (hslot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    ∃ after, VarReturnResult N A SL phiF phiC alloc exts shared st.store query v
      name (sp - 1088#64) dst ret r8 r9 r18 r19 r20 r21 c after := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x80003434#64
    Code.Env_getLoaded (.var query) sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c entry
  have geometry := var_arm_data entry hroom hspHi hSLHi arena
  have hL : GHolds c.σ (varCallInput aExpr (BitVec.ofNat 64 (phiF fa)) (sp - 1088#64)) :=
    ⟨p.a2, henv, p.spReg, trivial⟩
  have hs : GHolds c.σ (varSavedInput aExpr dst aEnv r19 r20 r21) :=
    ⟨p.node, p.s1, p.env, h19, h20, h21, trivial⟩
  have hcode : Code.Eval_exprLoaded c.σ.mem := by rw [p.mem]; exact p.code
  have hlookup : Code.Env_getLoaded c.σ.mem := by rw [p.mem]; exact p.callee
  obtain ⟨call, hr⟩ := var_lookup aExpr name (sp - 1088#64) aExpr dst aEnv r19 r20 r21 c
    D hget p.good p.pc p.tick hL hs hcode hlookup hstrcmp
    (by have := p.exprLo; omega) p.exprHi (by right; have := p.exprWin; omega)
    hread geometry.window geometry.gap
  obtain ⟨after, ht⟩ := var_lookup_tail hr geometry.window ret r8 r9 r18
    geometry.tail hslot geometry.saved p.retAlign hcode
  exact ⟨after, ht⟩

/-- Project the owned evaluator exit from the same complete arm execution. -/
theorem var_arm_return
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {st : Vsa.While.St}
    {query : String} {v : Vsa.While.Value} {fa : Nat}
    {name sp dst ret r8 r9 r18 r19 r20 r21 aExpr aEnv : BitVec 64}
    {out0 : Array String} {m0 ment : Mem} {c : Config}
    (entry : ArmEntryK g N A SL phiF phiC st 0x80003434#64 Code.Env_getLoaded (.var query)
      sp ret dst aExpr aEnv r8 r9 r18 out0 m0 ment c)
    (D : LookupData N A SL phiF phiC alloc exts shared st.store query name c.σ.mem)
    (hget : st.store.get? fa query = some v)
    (henv : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (phiF fa)))
    (h19 : c.σ.regs.get? Register.x19 = some r19)
    (h20 : c.σ.regs.get? Register.x20 = some r20)
    (h21 : c.σ.regs.get? Register.x21 = some r21)
    (hread : read64 c.σ.mem (aExpr.toNat + 8) = some name.toNat)
    (hstrcmp : Code.StrcmpLoaded c.σ.mem)
    (presence : MemExtends m0 c.σ.mem)
    (hroom : SL.lo + 2176 ≤ sp.toNat) (hspHi : sp.toNat ≤ SL.hi)
    (hSLHi : SL.hi ≤ 0x100000000)
    (hslot : SL.lo ≤ dst.toNat ∧ dst.toNat + 24 ≤ SL.hi)
    (arena : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo) :
    ∃ after, Steps c after ∧
      EvalReturn g N A SL phiF phiC st.store.frames.size st.store.closures.size
        st v sp ret dst m0
        (fun f c m => StoreOwned m f c alloc shared st.store ∧ ValueOwned m shared dst.toNat v)
        after := by
  obtain ⟨after, ht⟩ := var_arm_run entry D hget henv h19 h20 h21 hread hstrcmp
    hroom hspHi hSLHi hslot arena
  exact ⟨after, ht.steps,
    ht.at_arm entry presence h19 h20 h21 (by omega) arena⟩

#print axioms var_arm_data
#print axioms var_arm_run
#print axioms var_arm_return

end Vsa.Sim.EnvGetReflected
