import Vsa.Sim.EqAllocatorDispatch
import Vsa.Sim.EqCaseImage

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Sim.Code

namespace Vsa.Sim

/-- The helper scratch writes preserve every saved word and boxing premise. -/
theorem EqNeBoxPre.after_helper
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {final : Vsa.While.St} {sp ret dst v8 v9 v18 v19 w19 : BitVec 64}
    {out : Array String} {m0 m m' : Mem}
    (box : EqNeBoxPre g N A SL phiF phiC final sp ret dst v8 v9 v18 v19 w19 out m0 m)
    (presence : MemExtends m m')
    (outside : ∀ k, ¬ (sp.toNat - 1104 ≤ k ∧ k < sp.toNat - 1088) → m'[k]? = m[k]?) :
    EqNeBoxPre g N A SL phiF phiC final sp ret dst v8 v9 v18 v19 w19 out m0 m' := by
  have room := box.hSLloSp
  have high := box.hspSLhi
  have lower := box.hsp1088
  have htif := box.hspHtif
  have tohost : tohostAddr = 0x8001ad00 := rfl
  have slots : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) m m' :=
    fun k hk => (outside k (by omega)).symm
  have saved (offset : Nat) (lo : 8 ≤ offset) (hi : offset ≤ 40) :
      read64 m' (sp.toNat - offset) = read64 m (sp.toNat - offset) :=
    (read64_agreeP slots (fun j hj => by constructor <;> omega)).symm
  refine
    { box with
      hVboolEnt := loaded_bool_agreeP m m' (fun k hk => (outside k (by
        rw [tohost] at htif; omega)).symm) box.hVboolEnt
      hcodeEnt := loaded_eval_expr_agreeP m m' (fun k hk => (outside k (by
        rw [tohost] at htif; omega)).symm) box.hcodeEnt
      hs3Ent := (saved 40 (by decide) (by decide)).trans box.hs3Ent
      hslotRa0 := (saved 8 (by decide) (by decide)).trans box.hslotRa0
      hslotS00 := (saved 16 (by decide) (by decide)).trans box.hslotS00
      hslotS10 := (saved 24 (by decide) (by decide)).trans box.hslotS10
      hslotS20 := (saved 32 (by decide) (by decide)).trans box.hslotS20
      hMemExt0 := box.hMemExt0.trans presence
      hWordsEnt := ValueWordsTotal.mono presence box.hWordsEnt
      hSurvSL0 := fun memory agreement => box.hSurvSL0 memory
        (fun k hk => (outside k (by omega)).symm.trans (agreement k hk))
      hmemframe0 := ?_ }
  intro k hs ha
  rcases box.hmemframe0 k hs ha with slot | same
  · exact Or.inl slot
  · exact Or.inr ((outside k (by omega)).trans same)

#print axioms EqNeBoxPre.after_helper

end Vsa.Sim
