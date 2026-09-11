import Vsa.Sim.EqBoxMemory
import Vsa.Sim.Code.FixedImage_Eval_expr

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim

/-- Parent entry geometry and reached saved words supply equality's boxing entry. -/
theorem EqNeBoxPre.of_entry
    {op : EqNeOp} {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC tailF tailC : Addr → Nat}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {sp ret dst interp node v8 v9 v18 v19 : BitVec 64} {m0 : Mem}
    {before operands dispatch : Config}
    (entry : EvalEntry g N A SL phiF phiC st d env (.binary op.operator el er)
      sp ret dst interp node m0 before)
    (frame : BinaryArmFrame g gpre sp node v8 v9 v18 v19)
    (returned : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size middle final vl vr sp ret dst v8 v9 v18 m0 operands)
    (memory : BinaryReturnMemory SL dst operands)
    (image : StaticImageSupport dispatch.σ.mem SL A)
    (presence : MemExtends operands.σ.mem dispatch.σ.mem)
    (outside : ∀ k, k < (sp - 1088#64).toNat + 32 ∨ (sp - 1088#64).toNat + 88 ≤ k →
      dispatch.σ.mem[k]? = operands.σ.mem[k]?)
    (survives : ∀ m', AgreeP (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) dispatch.σ.mem m' →
      StoreRepr m' N A tailF tailC final.store) :
    EqNeBoxPre g N A SL tailF tailC final sp ret dst v8 v9 v18 v19 v19
      operands.σ.sailOutput m0 dispatch.σ.mem := by
  have parts := TwoSubReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size middle final vl vr sp ret dst v8 v9 v18 m0 operands returned
  obtain ⟨left, right, geometry⟩ := entry.binaryExtras
  have room := geometry.sproom
  have high := geometry.spSLhi
  have ram := geometry.SLhiRam
  have aligned := geometry.sp16
  have stackLow := entry.stack_ram.1
  have stackHtif := entry.stack_win
  have room1088 : SL.lo + 1088 ≤ sp.toNat := by omega
  have spHtif : tohostAddr + 16 + 1088 ≤ sp.toNat :=
    Nat.le_trans (Nat.add_le_add_right stackHtif 1088) room1088
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1088 ≤ sp.toNat; omega)
  have slots : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat)
      operands.σ.mem dispatch.σ.mem := by
    intro k hk
    exact (outside k (by rw [lowered]; omega)).symm
  have saved (offset : Nat) (lo : 8 ≤ offset) (hi : offset ≤ 40) :
      read64 dispatch.σ.mem (sp.toNat - offset) = read64 operands.σ.mem (sp.toNat - offset) :=
    (read64_agreeP slots (fun j hj => by constructor <;> omega)).symm
  have ghost19 : gpre Register.x19 = some v19 :=
    (frame.bridge .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      frame.saved19
  obtain ⟨saved19, ghostSaved, readSaved⟩ := parts.p10
  have same19 : saved19 = v19 := Option.some.inj (ghostSaved.symm.trans ghost19)
  subst saved19
  have resultStack := geometry.sret_inSL
  have boolCode := image.stack_disjoint (lo := 0x800027f8) (hi := 0x8000280c)
    (by decide) (by decide)
  refine
    { hVboolEnt := image.text.Value_boolLoaded
      hcodeEnt := image.text.Eval_exprLoaded
      hBoolRegion := ⟨entry.sret_align, entry.sret_ram.1, entry.sret_ram.2,
        entry.sret_win, by omega⟩
      houtStr := parts.p8
      hSurvSL0 := survives
      hs3Ent := (saved 40 (by decide) (by decide)).trans readSaved
      hslotRa0 := (saved 8 (by decide) (by decide)).trans parts.p13
      hslotS00 := (saved 16 (by decide) (by decide)).trans parts.p14
      hslotS10 := (saved 24 (by decide) (by decide)).trans parts.p15
      hslotS20 := (saved 32 (by decide) (by decide)).trans parts.p16
      hgv8 := frame.saved8, hgv9 := frame.saved9, hgv18 := frame.saved18
      hgv2 := frame.savedSp, hgx19 := frame.saved19, hw19 := rfl
      hMemExt0 := parts.p17.trans presence
      hWordsEnt := ValueWordsTotal.mono presence memory.sret_words
      hmemframe0 := ?_
      hsretEvalCode := entry.sret_evalcode_disjoint
      hsretStk := entry.sret_stack_disjoint
      hsretInSL := resultStack
      hSLlo40 := by omega, hSLlo32 := by omega, hSLloSp := by omega
      hspSLhi := high, hsp1088 := by omega, hspRam := by omega
      hspLo := by omega, hspHtif := spHtif, hsp8 := by omega
      hraAl := entry.ra_align }
  intro k hs ha
  exact Or.inr ((outside k (by rw [lowered]; omega)).trans (parts.p18 k hs ha))

#print axioms EqNeBoxPre.of_entry

end Vsa.Sim
