import Vsa.Sim.BinaryPostEntry
import Vsa.Sim.BinaryArmFrame
import Vsa.Sim.rows.ArmPostGeom

open LeanRV64DExecutable Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- Binary tails obtain their geometry from the parent entry and actual return. -/
theorem EvalEntry.binaryPostGeom
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {op : BinOp} {st st' st'' : Vsa.While.St} {d env : Nat} {el er : Expr}
    {vl vr : Value} {sp r sret aEnv aExpr v8 v9 v18 v19 : BitVec 64}
    {m0 : Mem} {c c' : Vsa.Machine.Config}
    {slotDef valLoaded : Mem → Prop} {viLo viHi tblOff : Nat}
    (h : EvalEntry g N A SL phiF phiC st d env (.binary op el er)
      sp r sret aEnv aExpr m0 c)
    (hframe : BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19)
    (hret : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size st' st'' vl vr sp r sret v8 v9 v18 m0 c')
    (hslot : ∀ m, FixedRodataLoaded m → slotDef m)
    (hcode : ∀ m, FixedTextLoaded m → valLoaded m)
    (hvlo : 0x80000000 ≤ viLo) (hvhi : viHi ≤ 0x8001acf0)
    (htable : tblOff ≤ 52) :
    ArmPostGeomV gpre N A SL (binOpTok op) slotDef valLoaded viLo viHi tblOff
      sp r sret aExpr c' := by
  have himage := h.binaryReturnImage hret
  have hs := h.stackOK
  unfold StackOK at hs
  have hsr := h.ground.sret_inSL
  have hv := himage.stack_disjoint hvlo hvhi
  have ht := himage.stack_disjoint (lo := opTableBase) (hi := opTableBase + tblOff)
    (by decide) (by simp only [opTableBase]; omega)
  refine
    { gx8 := hframe.node
      opTokRead := h.binaryReturnToken hret
      slot := hslot _ himage.rodata
      exprLo := h.expr_ram.1
      exprHi := h.expr_ram.2
      exprWin := by have := h.expr_win; omega
      exprSL := h.expr_stack_disjoint
      sretAl := h.sret_align
      sretLo := h.sret_ram.1
      sretHi := h.sret_ram.2
      sretWin := h.sret_win
      sretVi := by rcases hv with hv | hv <;> omega
      sretStk := h.sret_stack_disjoint
      sretEvalCode := h.sret_evalcode_disjoint
      raAl := h.ra_align
      vloaded := hcode _ himage.text
      codeStk := h.code_stack_disjoint
      viStk := by rcases hv with hv | hv <;> omega
      tableStk := by rcases ht with ht | ht <;> omega
      sretInSL := hsr
      SLloSp := by omega
      SLlo := h.stack_ram.1
      SLwin := h.stack_win
      sphiRam := by have := h.stack_ram.2; omega
      sp8 := by omega
      SLhiRam := h.stack_ram.2
      spSLhi := hs.2.1 }

#print axioms EvalEntry.binaryPostGeom
end Vsa.Sim
