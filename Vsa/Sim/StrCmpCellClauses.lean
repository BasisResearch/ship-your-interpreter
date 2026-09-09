import Vsa.Sim.SharedGeometry
import Vsa.Sim.StrCmpCellFootprint
import Vsa.Sim.rows.StrCmpCellInstances
import Vsa.Sim.IHClauseFootprintMeta
import Vsa.Sim.IHClauseGeneric
import Vsa.Sim.WordLoadData
import Vsa.Sim.ValuePayloadCoverage

/-!
# `StrCmpCellClauses` — the string-comparison cells from clause-shaped facts (IH tower, Level 2)

The four string-comparison cells (`StrCmpCell.lean`) are closed down to two
residuals stated over the whole entry world: `StrCmpOperandsSupply` (both
payloads are `strcmp`-admissible regions) and `StrLeftSurvivesSupply` (the left
temporary survives the right child, quantified over ALL memory pairs — false for
arena payloads).  This file replaces both by clause-shaped facts:

* **operands from ownership** — `SharedGeom shared SL` is the geometry of the
  shared byte set (RAM above the static image, above the HTIF window, outside
  the stack); `strCmpOperandsAt_of_owned` derives `StrCmpOperandsAt` from the
  two returned values being owned (`ValueOwned`, `RuntimeOwnership.lean`) —
  the `Owned` index of `EvalReturn`.  `strCmpOperandsSupply_of_owned` reduces
  residual 1 to `StrCmpOwnedOperands` (ownership at the actual return).
  This needs the alignment-free seam (`StrcmpSpecCond.lean`): a literal's
  payload is not 8-aligned.
* **left survival from the right child's footprint** — the head consumes the
  left child at the product clause `EvalIHFP noArenaFoot` (footprint ∧ payload
  covered outside the whole stack) and the right child at
  `EvalIHF noArenaFoot`; `strLeftSurvives_of_footprint`
  (`IHClauseFootprintMeta.lean`) closes the survival at the ACTUAL memories.
  The head with that hypothesis shape is `BinaryHeadFootprintSupplyCov`, now
  DISCHARGED by `binaryHeadFootprintSupplyCov` from the parametric head
  `blockB_binary_footprint_gen` (`EvalBinSim.lean`) at the left child's payload
  coverage; `evalStrCmpSimF_cov` / `binRow_strcmpF_cov` /
  `binStrCmpCell_of_clauses` are the pilot's chain over it, and
  `field_hStr{Lt,Le,Gt,Ge}_of_clauses` produce the EXACT `BinDispatchRow` fields
  from `StrCmpOwnedOperands` and the two closed clause recursions
  (`FootprintPayloadClause` for the left child, `FootprintClause` for the right).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.RuntimeOwnership (SharedCString ValueOwned)

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## 1. Operand regions from ownership -/

/-- A byte range `[p, p + len]` inside the shared set is a `strcmp` operand
region relative to any spill slot `sp'` inside the stack. -/
theorem strCmpRegion_of_shared {shared : Nat → Prop} {SL : StackLayout}
    (hG : SharedGeom shared SL) {sp' p : BitVec 64} {len : Nat}
    (hsplo : SL.lo ≤ sp'.toNat) (hsphi : sp'.toNat + 8 ≤ SL.hi)
    (hbytes : ∀ k, k ≤ len → shared (p.toNat + k)) : StrCmpRegion sp' p len := by
  have h0 := hG.ram _ (hbytes 0 (Nat.zero_le _))
  have hl := hG.ram _ (hbytes len (Nat.le_refl _))
  have ht := hG.htif _ (hbytes 0 (Nat.zero_le _))
  have htv : tohostAddr = 0x8001ad00 := rfl
  refine ⟨⟨by omega, by omega, by omega, Or.inr (by omega), Or.inr (by omega)⟩, ?_⟩
  rcases hG.stack _ (hbytes 0 (Nat.zero_le _)) with hlo | hhi
  · by_cases hend : p.toNat + len < SL.lo
    · exact Or.inl (by omega)
    · exfalso
      have hk := hG.stack _ (hbytes (SL.lo - p.toNat) (by omega))
      omega
  · exact Or.inr (by omega)

theorem sp_sub1088_toNat (sp : BitVec 64) (h : 1088 ≤ sp.toNat) :
    (sp - 1088#64).toNat = sp.toNat - 1088 := by
  rw [BitVec.toNat_sub]
  have h1 : (1088#64 : BitVec 64).toNat = 1088 := by decide
  rw [h1]; have := sp.isLt; omega

/-- **`strCmpOperandsAt_of_owned`** — both operand regions from the two returned
string values being owned at their slots `sp - 968` / `sp - 944`. -/
theorem strCmpOperandsAt_of_owned {shared : Nat → Prop} {SL : StackLayout}
    {sp : BitVec 64} {m : Mem} {sl sr : String}
    (hG : SharedGeom shared SL) (hsp : SL.lo + 1088 ≤ sp.toNat) (hspHi : sp.toNat ≤ SL.hi)
    (hl : ValueOwned m shared (sp.toNat - 968) (.str sl))
    (hr : ValueOwned m shared (sp.toNat - 944) (.str sr)) :
    StrCmpOperandsAt sp m := by
  have hsub := sp_sub1088_toNat sp (by omega)
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hs⟩ := hl
    have hptr : (strLeftPtr m sp).toNat = p := by
      unfold strLeftPtr
      exact bytesT8_toNat_of_read64
        (by rw [show sp.toNat - 960 = sp.toNat - 968 + 8 by omega]; exact hp)
    intro cs hcs
    obtain ⟨cs0, hcs0, hsl⟩ := hs.repr
    rw [hptr] at hcs
    have hceq := cstr_unique_eg9 m p cs cs0 hcs hcs0
    subst hceq
    refine strCmpRegion_of_shared hG (by rw [hsub]; omega) (by rw [hsub]; omega) ?_
    intro k hk
    rw [hptr]
    exact hs.bytes k (by rw [hsl, String.length_ofList]; exact hk)
  · obtain ⟨p, hp, hs⟩ := hr
    have hptr : (strRightPtr m sp).toNat = p := by
      unfold strRightPtr
      exact bytesT8_toNat_of_read64
        (by rw [show sp.toNat - 936 = sp.toNat - 944 + 8 by omega]; exact hp)
    intro cs hcs
    obtain ⟨cs0, hcs0, hsr⟩ := hs.repr
    rw [hptr] at hcs
    have hceq := cstr_unique_eg9 m p cs cs0 hcs hcs0
    subst hceq
    refine strCmpRegion_of_shared hG (by rw [hsub]; omega) (by rw [hsub]; omega) ?_
    intro k hk
    rw [hptr]
    exact hs.bytes k (by rw [hsr, String.length_ofList]; exact hk)

/-- Both returned string operands owned at one shared set with its geometry. -/
structure OwnedOperands (shared : Nat → Prop) (SL : StackLayout) (sp : BitVec 64)
    (m : Mem) (sl sr : String) : Prop where
  geom : SharedGeom shared SL
  left : ValueOwned m shared (sp.toNat - 968) (.str sl)
  right : ValueOwned m shared (sp.toNat - 944) (.str sr)

/-- **Residual 1, clause-shaped** — at every actual return of both children under a
represented string-comparison entry, the two returned values are owned (the
`Owned` index of `EvalReturn`: `ValueOwned` at the two result slots) at a shared
set with `SharedGeom`.  Supplier: the ownership index of the recursive return
(`ReturnRepr`/`EvalReturn … Owned`) at the string values, plus the shared set's
geometry from `HeapOwned`/`EvalGround` (arena and AST region). -/
def StrCmpOwnedOperands : Prop :=
  ∀ (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d env : Nat) (op : BinOp) (el er : Expr) (sl sr : String)
    (sp r sret aEnv aExpr v8 v9 v18 v19 : BitVec 64) (m0 : Mem) (c c' : Config),
    EvalEntry g N A SL φf φc st d env (.binary op el er) sp r sret aEnv aExpr m0 c →
    BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
    TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c' →
    ∃ shared, OwnedOperands shared SL sp c'.σ.mem sl sr

/-- Residual 1 from ownership at the actual return. -/
theorem strCmpOperandsSupply_of_owned (h : StrCmpOwnedOperands) : StrCmpOperandsSupply := by
  intro g gpre N A SL φf φc st st' st'' d env op el er sl sr sp r sret aEnv aExpr
    v8 v9 v18 v19 m0 c c' hc hf hret
  obtain ⟨shared, hO⟩ := h g gpre N A SL φf φc st st' st'' d env op el er sl sr
    sp r sret aEnv aExpr v8 v9 v18 v19 m0 c c' hc hf hret
  have hsp := hc.stackOK
  exact strCmpOperandsAt_of_owned hO.geom (by have := hsp.1; omega) hsp.2.1 hO.left hO.right

/-! ## 2. Left survival from the right child's footprint -/

/-- The product clause: footprint `F` AND the returned value's payload covered
outside the whole stack (`EvalPayloadIH`'s fact) at the same actual return. -/
abbrev EvalIHFP (F : FootFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (fun _ A SL _ _ sp sret m0 c =>
      MemFootprint (F SL A sp.toNat sret.toNat) m0 c.σ.mem ∧
      ValuePayloadCovered (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) c.σ.mem sret.toNat v)
    st d env e st' v

theorem EvalIHFP.footprint {F : FootFam} {st st' : Vsa.While.St} {d env : Nat} {e : Expr}
    {v : Value} (h : EvalIHFP F st d env e st' v) : EvalIHF F st d env e st' v :=
  EvalIHWithM.mono (fun _ _ _ _ _ _ _ _ _ hp => hp.1) h

/-- The string literal at the product clause: the same pinned run as
`IHClauseGeneric.footprint.hStr` and `evalStrPayloadIH`. -/
theorem evalStrPayloadIHF (st : Vsa.While.St) (d env : Nat) (s : String) :
    EvalIHFP noArenaFoot st d env (.str s) st (.str s) where
  run := by
    intro g N A SL φf φc sp r sret aEnv aExpr m0 c hc
    obtain ⟨c', hs, hExit, hPin⟩ :=
      evalStrSimP_exact g N A SL φf φc st d env s sp r sret aEnv aExpr m0 c
        (evalStrEntry_of_entry hc)
    have hW := leafWidenP_of_entry (v := .str s) hc
    have hD := evalExitD_of_pinnedExit ⟨hExit, hPin.memory⟩ hW (hc.mem ▸ hc.sret_words)
    refine ⟨c', hs, hD, ⟨fun k hk =>
      hPin.memory.agree k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))⟩, ?_⟩
    change ∀ p, read64 c'.σ.mem (sret.toNat + 8) = some p →
      ∀ k, k ≤ s.length → ¬ (SL.lo ≤ p + k ∧ p + k < SL.hi)
    have hg : EvalGround m0 SL A sp sret aExpr.toNat (.str s) := hc.mem ▸ hc.ground
    obtain ⟨lo, hi, spec⟩ := hg.ast.region
    intro p hp k hk hstack
    have hp0 : read64 m0 (aExpr.toNat + 8) = some p := hPin.pointer.symm.trans hp
    obtain ⟨_, hlo, hhi⟩ := exprIn_str_payload spec.nodes p hp0
    rcases spec.stack_disjoint with hd | hd <;> omega

/-- **The head with the left survival derived at the actual memories.**  The
parametric head `blockB_binary_footprint_gen` (`EvalBinSim.lean`) at the left
child's product clause `EvalIHFP Fl` (footprint ∧ payload covered outside the
whole stack), the right child at `EvalIHF noArenaFoot`, and NO `hVlSurv`: where
the head consumed `hVlSurv` (`hvalL_R`, the left `ValueRepr` at `cL.σ.mem`
transported to `cR.σ.mem`) it now hands out the left return's retained fact and
the composed footprint of the argument respill at `sp-1088` and the right child,
and `valueSurvives_of_covered` closes the transport.  DISCHARGED by
`binaryHeadFootprintSupplyCov` below. -/
def BinaryHeadFootprintSupplyCov (Fl : FootFam) : Prop :=
  ∀ (gouter gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr)
    (op : BinOp) (el er : Expr) (vl vr : Value)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalE st d env el st' vl →
    EvalIHFP Fl st d env el st' vl →
    EvalIHF noArenaFoot st' d env er st'' vr →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary op el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget)
      (ReturnedWith
        (TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' vl vr sp r sret v8 v9 v18 m0)
        (fun c => BinaryReturnData SL sp sret c ∧
          MemFootprint (binaryHeadFoot Fl noArenaFoot SL A sp.toNat) m0 c.σ.mem))

/-- **`valueSurvives_of_covered`** — the general-value form of
`strLeftSurvives_of_footprint` at the head's composed family: the left temporary at
`sp - 968` (header inside the parent frame, payload covered outside the WHOLE stack)
survives the argument respill at `sp - 1088` and a NON-allocating right child. -/
theorem valueSurvives_of_covered {N : NativeAddrs} {SL : StackLayout} {A : Arena}
    {sp : Nat} {φ : Addr → Nat} {mm mm' : Mem} {v : Value}
    (hsp : SL.lo + 1088 ≤ sp) (hspHi : sp ≤ SL.hi)
    (hv : ValueRepr mm N φ (sp - 968) v)
    (hcov : ValuePayloadCovered (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) mm (sp - 968) v)
    (hfoot : MemFootprint (fun k => word8 (sp - 1088) k ∨
      noArenaFoot SL A (sp - 1088) (sp - 944) k) mm mm') :
    ValueRepr mm' N φ (sp - 968) v := by
  refine hfoot.valueRepr hv ?_ (hcov.mono ?_)
  · intro k hk hF
    unfold valHeader at hk
    unfold word8 noArenaFoot stackWin resultSlot at hF
    omega
  · intro k hk hF
    unfold word8 noArenaFoot stackWin resultSlot at hF
    omega

/-- **`binaryHeadFootprintSupplyCov`** — the covered head premise, DISCHARGED from
the parametric head at the left child's payload coverage. -/
theorem binaryHeadFootprintSupplyCov (Fl : FootFam) : BinaryHeadFootprintSupplyCov Fl :=
  fun gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr =>
    blockB_binary_footprint_gen Fl noArenaFoot
      (fun SL m a => ValuePayloadCovered (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) m a vl)
      gouter gpre N A SL φf φc st st' st'' d env op el er vl vr
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr
      (fun hsproom hspSLhi _ _φ _m _m' hQ hv _hag hfoot =>
        valueSurvives_of_covered (by omega) hspSLhi hv hQ hfoot)

/-- `evalStrCmpSimF` (pilot A) over the survival-free head. -/
theorem evalStrCmpSimF_cov (D : StrCmpOp) (C : D.Cert) (Fl : FootFam)
    (hHead : BinaryHeadFootprintSupplyCov Fl)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (sl sr : String)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.str sl))
    (hIHl : EvalIHFP Fl st d env el st' (.str sl))
    (hIHr : EvalIHF noArenaFoot st' d env er st'' (.str sr))
    (hEvalE : EvalE st d env (.binary D.op el er) st'' (.bool (D.bres sl sr)))
    (hResid : ∀ c2 : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 →
      StrCmpResid D gpre N A SL sp r sret aExpr c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary D.op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary D.op el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitF (strCmpNodeFoot Fl noArenaFoot) g N A SL φf φc
        st.store.frames.size st.store.closures.size
        st'' (.bool (D.bres sl sr)) sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  obtain ⟨c2, hs2, hReturned⟩ :=
    hHead gouter gpre N A SL φf φc st st' st'' d env D.op el er (.str sl) (.str sr)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  obtain ⟨hData, hHeadFoot⟩ := hReturned.extra
  have hR : StrCmpResid D gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 hTS).p8
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD, hCellFoot⟩ :=
    blockC_strcmp_footprint D C gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' sl sr sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0 c2.σ.mem
      c2 ⟨hTS, hR, hData, hOutC2, rfl, hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge, rfl⟩
  obtain ⟨c4, hs4, hExitDe, hFoot⟩ :=
    blockD_v_rec_footprint (strCmpNodeFoot Fl noArenaFoot SL A sp.toNat sret.toNat)
      g N A SL φfe φce st'' (.bool (D.bres sl sr)) sp r sret v8 v9 v18
      c2.σ.sailOutput m0 c3 ⟨mpre, hPreD, hHeadFoot.trans hCellFoot⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono hEvalE
  have hleftMono := evalE_store_mono hLeft
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hleftMono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hleftMono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size :=
    hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.bool (D.bres sl sr)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  refine ⟨c4, ((hs2.trans hs3).trans hs4), ?_, hFoot⟩
  exact ⟨hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- `binRow_strcmpF` (pilot A) over the survival-free head: from the recursor
entry, both children non-allocating, to `EvalExitF noArenaFoot`. -/
theorem binRow_strcmpF_cov (D : StrCmpOp) (C : D.Cert)
    (hHead : BinaryHeadFootprintSupplyCov noArenaFoot)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (sl sr : String)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.str sl))
    (hIHl : EvalIHFP noArenaFoot st d env el st' (.str sl))
    (hIHr : EvalIHF noArenaFoot st' d env er st'' (.str sr))
    (hEvalE : EvalE st d env (.binary D.op el er) st'' (.bool (D.bres sl sr)))
    (hResid : ∀ c : Config,
      EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c →
      ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c2 : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 →
      StrCmpResid D gpre N A SL sp r sret aExpr c2) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c)
      (EvalExitF noArenaFoot g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (D.bres sl sr)) sp r sret m0) := by
  intro c hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env D.op el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExitF⟩ :=
    evalStrCmpSimF_cov D C noArenaFoot hHead g gpre' g N A SL φf φc st st' st'' d env
      el er sl sr sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE (hResid c hc gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR,
        hArmFrame.saved8, hArmFrame.saved9, hArmFrame.saved18, hArmFrame.savedSp,
        hArmFrame.saved19, hArmFrame.bridge⟩
  have hsproom : SL.lo + 1088 ≤ sp.toNat := by have := hBE.sproom; omega
  exact ⟨c2, hs1.trans hs2, hExitF.result,
    hExitF.extra.mono (strCmpNodeFoot_noArena hsproom)⟩

/-! ## 3. The four field suppliers from clauses -/

/-- The closed footprint clause over every derivation: what
`IHClause.Footprint.of_residuals` yields once its residual record is inhabited
(at `noArenaFoot` only for a non-allocating family; see `IHClauseGeneric.lean`). -/
def FootprintClause : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (st' : Vsa.While.St) (v : Value),
    EvalE st d env e st' v → EvalIHF noArenaFoot st d env e st' v

/-- The closed product clause (footprint ∧ payload coverage) over every derivation. -/
def FootprintPayloadClause : Prop :=
  ∀ (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (st' : Vsa.While.St) (v : Value),
    EvalE st d env e st' v → EvalIHFP noArenaFoot st d env e st' v

/-- **The cell supplier from clauses.**  The children's clause facts come from the
closed clause recursions at the children's own derivations, so the EXACT landed
cell shape `BinStrCmpCell` (children at `EvalIH`) is produced. -/
theorem binStrCmpCell_of_clauses (D : StrCmpOp) (C : D.Cert)
    (hOps : StrCmpOwnedOperands)
    (hCL : FootprintPayloadClause) (hCR : FootprintClause) :
    BinStrCmpCell D.op D.bres := by
  intro st d env el er st' st'' sl sr hEl hEr _ _
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact binRow_strcmpF_cov D C (binaryHeadFootprintSupplyCov noArenaFoot)
    g N A SL φf φc st st' st'' d env el er sl sr
    sp r sret aEnv aExpr m0 hEl (hCL st d env el st' (.str sl) hEl)
    (hCR st' d env er st'' (.str sr) hEr)
    (EvalE.binary st d env D.op el er st' st'' (.str sl) (.str sr) _ hEl hEr (C.sem _ _ _))
    (fun c hc gpre v8 v9 v18 v19 hf c2 hTS => by
      obtain ⟨_, hO⟩ := hOps g gpre N A SL φf φc st st' st'' d env D.op el er sl sr
        sp r sret aEnv aExpr v8 v9 v18 v19 m0 c c2 hc hf hTS
      exact strCmpResid_of_entry D C hc hf hTS
        (strCmpOperandsAt_of_owned hO.geom (by have := hc.stackOK.1; omega) hc.stackOK.2.1
          hO.left hO.right))
    |>.conseq (fun _ hp => hp) (fun _ hp => hp.result)

theorem ScaffoldRows.field_hStrLt_of_clauses (hOps : StrCmpOwnedOperands)
    (hCL : FootprintPayloadClause) (hCR : FootprintClause) :
    BinStrCmpCell .lt (fun sl sr => sl < sr) :=
  binStrCmpCell_of_clauses strCmpLt strCmpLt_cert hOps hCL hCR

theorem ScaffoldRows.field_hStrLe_of_clauses (hOps : StrCmpOwnedOperands)
    (hCL : FootprintPayloadClause) (hCR : FootprintClause) :
    BinStrCmpCell .le (fun sl sr => sl < sr || sl == sr) :=
  binStrCmpCell_of_clauses strCmpLe strCmpLe_cert hOps hCL hCR

theorem ScaffoldRows.field_hStrGt_of_clauses (hOps : StrCmpOwnedOperands)
    (hCL : FootprintPayloadClause) (hCR : FootprintClause) :
    BinStrCmpCell .gt (fun sl sr => sr < sl) :=
  binStrCmpCell_of_clauses strCmpGt strCmpGt_cert hOps hCL hCR

theorem ScaffoldRows.field_hStrGe_of_clauses (hOps : StrCmpOwnedOperands)
    (hCL : FootprintPayloadClause) (hCR : FootprintClause) :
    BinStrCmpCell .ge (fun sl sr => sr < sl || sl == sr) :=
  binStrCmpCell_of_clauses strCmpGe strCmpGe_cert hOps hCL hCR

#print axioms strCmpRegion_of_shared
#print axioms strCmpOperandsAt_of_owned
#print axioms strCmpOperandsSupply_of_owned
#print axioms evalStrPayloadIHF
#print axioms valueSurvives_of_covered
#print axioms binaryHeadFootprintSupplyCov
#print axioms evalStrCmpSimF_cov
#print axioms binRow_strcmpF_cov
#print axioms binStrCmpCell_of_clauses
#print axioms ScaffoldRows.field_hStrLt_of_clauses
#print axioms ScaffoldRows.field_hStrLe_of_clauses
#print axioms ScaffoldRows.field_hStrGt_of_clauses
#print axioms ScaffoldRows.field_hStrGe_of_clauses

end Vsa.Sim
