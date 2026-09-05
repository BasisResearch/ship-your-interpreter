import Vsa.Sim.rows.AssignArmStagePre
import Vsa.Sim.EvalValueReturnTail

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

/-- The assignment-specific facts that survive the recursive RHS evaluation.
The name proof is transported through the actual `SubEvalReturn.memFrame`, not
assumed at the post-call memory. -/
structure AssignRhsPostCarry
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (v : Value) (x : String) (e : Expr)
    (sp r sret aExpr subsret aIn : BitVec 64) (v8 v9 v18 : BitVec 64)
    (mcall : Mem) (c : Config) : Prop where
  sub : SubEvalReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
    st' v sp r sret subsret 0x8000348c#64 v8 v9 v18 mcall c
  parentS0 : c.σ.regs.get? Register.x8 = some aExpr
  interpS2 : c.σ.regs.get? Register.x18 = some aIn
  parentName : ∃ p, read64 c.σ.mem (aExpr.toNat + 8) = some p ∧ CString c.σ.mem p x

/-- The actual three words loaded by the post-RHS assignment code. -/
theorem AssignRhsPostCarry.resultWords
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {v : Value} {x : String} {e : Expr}
    {sp r sret aExpr subsret aIn : BitVec 64} {v8 v9 v18 : BitVec 64}
    {mcall : Mem} {c : Config}
    (h : AssignRhsPostCarry gpre N A SL φf φc st st' v x e sp r sret aExpr
      subsret aIn v8 v9 v18 mcall c) :
    ∃ (φc' : Addr → Nat) (d0 d1 d2 : BitVec 64),
      PhiExtends φc φc' st.store.closures.size ∧
      ValueRepr c.σ.mem N φc' subsret.toNat v ∧
      read64 c.σ.mem subsret.toNat = some d0.toNat ∧
      read64 c.σ.mem (subsret.toNat + 8) = some d1.toNat ∧
      read64 c.σ.mem (subsret.toNat + 16) = some d2.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hresult, _, _, _, _, _, _, _, _⟩ := h.sub
  obtain ⟨φc', hφc', hrepr⟩ := hresult
  obtain ⟨d0, d1, d2, h0, h1, h2⟩ := hrepr.raw
  exact ⟨φc', d0, d1, d2, hφc', hrepr.repr, h0, h1, h2⟩

/-- The coherent post-RHS correspondence maps and represented store. -/
theorem AssignRhsPostCarry.resultStore
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {v : Value} {x : String} {e : Expr}
    {sp r sret aExpr subsret aIn : BitVec 64} {v8 v9 v18 : BitVec 64}
    {mcall : Mem} {c : Config}
    (h : AssignRhsPostCarry gpre N A SL φf φc st st' v x e sp r sret aExpr
      subsret aIn v8 v9 v18 mcall c) :
    ∃ φf' φc', PhiExtends φf φf' st.store.frames.size ∧
      PhiExtends φc φc' st.store.closures.size ∧
      StoreRepr c.σ.mem N A φf' φc' st'.store ∧
      ∀ m', (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf' φc' st'.store := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hstore, _, _, _, _, _, _, _⟩ := h.sub
  exact hstore

/-- Transport the retained parent assignment/name across the recursive child
using the child exit's concrete stack/arena/result framing. -/
theorem AssignRhsCarry.afterRun
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {x : String} {e : Expr}
    {v : Value} {sp r sret aExpr subsret aIn aOperand : BitVec 64}
    {v8 v9 v18 : BitVec 64} {out0 : Array String} {mcall : Mem}
    {cCall cRet : Config}
    (h : AssignRhsCarry gpre N A SL φf φc st d env x e sp r sret aExpr
      subsret aIn aOperand v8 v9 v18 out0 mcall cCall)
    (hRet : SubEvalReturn gpre N A SL φf φc
      st.store.frames.size st.store.closures.size st' v sp r sret subsret
      0x8000348c#64 v8 v9 v18 mcall cRet) :
    AssignRhsPostCarry gpre N A SL φf φc st st' v x e sp r sret aExpr
      subsret aIn v8 v9 v18 mcall cRet := by
  obtain ⟨hG, htick, hpc, ha0, hra, hs1, hsp, hmi, hout, hframe,
    hresult, hstore, hcode, hslotRa, hslotS0, hslotS1, hslotS2,
    hmemFrame, hExt⟩ := hRet
  obtain ⟨pName, hpName, hcstring⟩ := h.parentName
  obtain ⟨lo, hi, hAst⟩ := h.parentGround.ast.region
  have hspNat := h.loweredSpNat
  have hspHi := h.spLeStackHi
  have hAgreeAst : ∀ k, lo ≤ k → k < hi → cRet.σ.mem[k]? = mcall[k]? := by
    intro k hklo hkhi
    have hoffStack : ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1088) := by
      rcases hAst.stack_disjoint with hb | ha <;> omega
    have hoffArena : ¬ (A.lo ≤ k ∧ k < A.hi) := by
      rcases hAst.arena_disjoint with hb | ha <;> omega
    rcases hmemFrame k hoffStack hoffArena with hsub | heq
    · rcases h.subsretInStack with ⟨hsubLo, hsubHi⟩
      rcases hAst.stack_disjoint with hb | ha <;> omega
    · exact heq
  have hpNameRet : read64 cRet.σ.mem (aExpr.toNat + 8) = some pName := by
    have hn : NodeIn lo hi aExpr.toNat := exprIn_node hAst.nodes
    rw [read64_agreeP
      (P := fun k => aExpr.toNat + 8 ≤ k ∧ k < aExpr.toNat + 16)
      (m := cRet.σ.mem) (m' := mcall)
      (fun k hk => hAgreeAst k (by have := hn.lo_le; omega)
        (by have := hn.hi_ge; omega))
      (fun _ hk => by omega)]
    exact hpName
  have hcstringRet : CString cRet.σ.mem pName x := by
    have hnameIn : StrIn lo hi pName x := hAst.nodes.2.1 pName hpName
    exact cstring_agreeP
      (P := fun k => lo ≤ k ∧ k < hi)
      (fun k hk => (hAgreeAst k hk.1 hk.2).symm)
      hcstring
      (fun k hk => ⟨by have := hnameIn.lo_le; omega,
        by have := hnameIn.hi_ge; omega⟩)
  exact
    { sub := ⟨hG, htick, hpc, ha0, hra, hs1, hsp, hmi, hout, hframe,
        hresult, hstore, hcode, hslotRa, hslotS0, hslotS1, hslotS2,
        hmemFrame, hExt⟩
      parentS0 := (hframe Register.x8 (by decide)).trans h.parentS0
      interpS2 := (hframe Register.x18 (by decide)).trans h.interpS2
      parentName := ⟨pName, hpNameRet, hcstringRet⟩ }

#print axioms AssignRhsCarry.afterRun

/-- Marshal a post-RHS state into the exact reflected assignment staging
entry.  Only the three additional callee-saved registers actually read by
`env_set` must be supplied as defined frame values. -/
theorem AssignRhsPostCarry.toStageEntry
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {v : Value} {x : String} {e : Expr}
    {sp r sret aExpr subsret aIn : BitVec 64} {v8 v9 v18 : BitVec 64}
    {mcall : Mem} {c : Config}
    (h : AssignRhsPostCarry gpre N A SL φf φc st st' v x e sp r sret aExpr
      subsret aIn v8 v9 v18 mcall c)
    (r19 r20 r21 d0 d1 d2 envMach : BitVec 64)
    (h19 : gpre Register.x19 = some r19)
    (h20 : gpre Register.x20 = some r20)
    (h21 : gpre Register.x21 = some r21) :
    ∃ name, read64 c.σ.mem (aExpr.toNat + 8) = some name ∧
      CString c.σ.mem name x ∧
      AssignArmStageEntry aExpr (sp - 1088#64) sret name d0 d1 d2 envMach
        aExpr aIn r19 r20 r21 c.σ.mem c.σ.sailOutput c := by
  obtain ⟨hG, htick, hpc, ha0, hra, hs1, hsp, hmi, hout, hframe,
    hresult, hstore, hcode, hslotRa, hslotS0, hslotS1, hslotS2,
    hmemFrame, hExt⟩ := h.sub
  obtain ⟨name, hname, hcstring⟩ := h.parentName
  refine ⟨name, hname, hcstring, ?_⟩
  exact
    { good := hG
      tick := htick
      pc := hpc
      minstret := hmi
      mem := rfl
      output := rfl
      s0 := h.parentS0
      sp := hsp
      sret := hs1
      cs18 := h.interpS2
      cs19 := (hframe Register.x19 (by decide)).trans h19
      cs20 := (hframe Register.x20 (by decide)).trans h20
      cs21 := (hframe Register.x21 (by decide)).trans h21 }

#print axioms AssignRhsPostCarry.toStageEntry

end Vsa.Sim
