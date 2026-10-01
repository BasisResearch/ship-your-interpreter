import Vsa.Compiler.SimLeaf
import Vsa.Compiler.R6Row
import Vsa.Compiler.R6Scope

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The key-register fiber of `MS`: the five key registers holding their abstract values. -/
structure Keys (R : GRegs) (h hF e sp d : Nat) : Prop where
  ho : Has R hpO (BitVec.ofNat 64 h)
  hf : Has R hpF (BitVec.ofNat 64 hF)
  henv : Has R envR (BitVec.ofNat 64 e)
  hsp : Has R spR (BitVec.ofNat 64 sp)
  hdep : Has R depR (BitVec.ofNat 64 d)

theorem MS.keys {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) :
    Keys A.regs V.h V.hF (V.fa env) sp d := ⟨hm.ho, hm.hf, hm.henv, hm.hsp, hm.hdep⟩

/-- The fiber as a register row (literal keys), for `wp_simp [hK.row.wp]`. -/
theorem Keys.row {R : GRegs} {h hF e sp d : Nat} (hK : Keys R h hF e sp d) :
    Models R [hpO, hpF, envR, spR, depR]
      [BitVec.ofNat 64 h, BitVec.ofNat 64 hF, BitVec.ofNat 64 e, BitVec.ofNat 64 sp, BitVec.ofNat 64 d] :=
  .cons hK.ho <| .cons hK.hf <| .cons hK.henv <| .cons hK.hsp <| .cons hK.hdep (.nil R)

/-- Gauge rule: the environment register moves in lockstep with its abstract field. -/
theorem Keys.setEnv {R : GRegs} {h hF e sp d : Nat} (hK : Keys R h hF e sp d) (e' : Nat) :
    Keys (gset R envR (BitVec.ofNat 64 e')) h hF e' sp d :=
  ⟨hK.ho.set_other (by decide), hK.hf.set_other (by decide), Has.set_self _ _ (by decide) (by decide),
    hK.hsp.set_other (by decide), hK.hdep.set_other (by decide)⟩

/-- Reseat: `MS` at `B` from `MS` at `A`, the same memory and output, a chain for the new scope,
and the fiber at `B`. -/
theorem MS.reseat {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env env' : Addr}
    {Γ Γ' : List (List String)} {sp fs : Nat} {A B : AM} (hm : MS code T V st d env Γ sp fs A)
    (hmem : B.mem = A.mem) (hout : B.out = A.out) (hc : ChainL V.F st.store env' Γ')
    (hK : Keys B.regs V.h V.hF (V.fa env') sp d) : MS code T V st d env' Γ' sp fs B where
  rel := hmem ▸ hm.rel
  img := hmem ▸ hm.img
  clo := hmem ▸ hm.clo
  chn := hc
  out := hout ▸ hm.out
  ho := hK.ho
  hf := hK.hf
  henv := hK.henv
  hsp := hK.hsp
  hdep := hK.hdep
  stk := hm.stk
  hfal := hm.hfal

/-- What popping the innermost scope `inner` (parent `env`) exposes at its frame address `f`. -/
structure PopScope (V : View) (s : Store) (m : Mem) (inner env : Addr) (Γ : List (List String)) (f : Nat) :
    Prop where
  fa : V.fa inner = f
  nat : (BitVec.ofNat 64 f).toNat = f
  ld : LdOK f
  word : rdW m f = BitVec.ofNat 64 (V.fa env)
  chn : ChainL V.F s env Γ

theorem MS.popScope {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env inner : Addr}
    {L : List String} {Γ : List (List String)} {sp fs : Nat} {A : AM}
    (hm : MS code T V st d inner (L :: Γ) sp fs A) {fr : Frame} (hfr : st.store.frames[inner]? = some fr)
    (hpar : fr.parent = some env) : ∃ f, PopScope V st.store A.mem inner env Γ f := by
  obtain ⟨f, hF⟩ := hm.chn.head'
  have Hd := hm.rel.headFrame hfr hF hF
  exact ⟨f, View.fa_eq hF, Hd.nat, Hd.ld, Hd.word hpar, hm.chn.pop hfr hpar⟩

end Vsa.Compiler
