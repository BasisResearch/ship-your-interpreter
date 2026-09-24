import VsaIris.Interp.ConcatCalls
import VsaIris.Interp.World
import VsaIris.Interp.HeapRealloc

/-!
# The concatenation arm's byte facts (lane E2)

* `strOwn_cut`/`blockOwn_of_cut`: an owned C string as its characters and its
  NUL (`memcpy` copies the characters), and back as a block for `free`.
* `ownImg_cat`: the copied left rendering and the right one `strcpy` wrote,
  adjacent, are one C string (`cstrImg_cat`).
* `strAt_of_fresh`: the result, read-only from `value_str` on
  (`strAt_of_owned` with the window from the fresh block).
* `dispRes_of_valOf`: a value's display resources from the store
  (`CatDispSupply` for a closure).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib VsaIris.VsaHeap
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
/-- An owned C string: its characters and its NUL, at one image. -/
theorem strOwn_cut (q : Nat) (x : String) :
    strOwn (GF := GF) q x ⊢ ∃ img, ⌜CStrImg img q x⌝ ∗
      ownImg (InExt (q, x.toList.length)) img ∗ ownImg (InExt (q + x.toList.length, 1)) img := by
  unfold strOwn
  iintro ⟨%img, H, %h⟩
  iexists img
  ihave ⟨H1, H2⟩ := ownImg_ext_split q (x.toList.length + 1) x.toList.length _ 1 img (by omega)
    rfl (by omega) $$ H
  iframe H1 H2
  ipureintro; exact h

omit I in
/-- The two parts of a string's block, back as the block. -/
theorem blockOwn_of_cut (q n : Nat) (f g : Nat → BitVec 8) :
    ownImg (GF := GF) (InExt (q, n)) f ∗ ownImg (InExt (q + n, 1)) g ⊢ blockOwn q (n + 1) := by
  iintro ⟨H1, H2⟩
  ihave H1 := ownSet_forget _ _ $$ H1
  ihave H2 := ownSet_forget _ _ $$ H2
  iapply blockOwn_join q n (q + n) 1 (n + 1) rfl rfl
  unfold blockOwn
  iframe H1 H2

/-- The characters of `x` at `q`, then a C string `y`: the C string `x ++ y`. -/
theorem cstrImg_cat {img : Nat → BitVec 8} {q : Nat} {x y : String}
    (hx : ∀ i (h : i < x.toList.length), img (q + i) = BitVec.ofNat 8 (x.toList[i]).toNat ∧
      0 < (x.toList[i]).toNat ∧ (x.toList[i]).toNat < 128)
    (hy : CStrImg img (q + x.toList.length) y) : CStrImg img q (x ++ y) := by
  have e : (x ++ y).toList = x.toList ++ y.toList := String.toList_append
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [e, List.length_append] at hi
    by_cases h : i < x.toList.length
    · have := hx i h
      simp only [e, List.getElem_append_left h]; exact this
    · have hi' : i - x.toList.length < y.toList.length := by omega
      have := hy.1 (i - x.toList.length) hi'
      rw [show q + x.toList.length + (i - x.toList.length) = q + i by omega] at this
      simp only [e, List.getElem_append_right (Nat.le_of_not_lt h)]; exact this
  · have := hy.2
    rw [show q + x.toList.length + y.toList.length = q + (x ++ y).toList.length by
      simp only [e, List.length_append]; omega] at this
    exact this

omit I in
/-- **The concatenation's bytes**: the left rendering's characters (copied
from `q1`) at `q`, the right rendering (NUL included) after them. -/
theorem ownImg_cat {q q1 : Nat} {x y : String} (f g : Nat → BitVec 8) (hf : CStrImg f q1 x)
    (hg : CStrImg g (q + x.toList.length) y) :
    ownImg (GF := GF) (InExt (q, x.toList.length)) (fun a => f (a - q + q1)) ∗
      ownImg (InExt (q + x.toList.length, y.toList.length + 1)) g ⊢
      strOwn q (x ++ y) := by
  classical
  have hlen : (x ++ y).toList.length = x.toList.length + y.toList.length := by
    rw [String.toList_append, List.length_append]
  let h : Nat → BitVec 8 := fun a => if a < q + x.toList.length then f (a - q + q1) else g a
  iintro ⟨H1, H2⟩
  unfold strOwn
  iexists h
  isplitl [H1 H2]
  · iapply ownSet_iff (S := fun a => InExt (q, x.toList.length) a ∨
        InExt (q + x.toList.length, y.toList.length + 1) a) _ (fun a => by
      rw [hlen]; unfold InExt; dsimp only; omega)
    iapply ownSet_join _ _ _ (fun a (h1 : InExt (q, x.toList.length) a) h2 => by
      unfold InExt at h1 h2; dsimp only at h1 h2; omega)
    isplitl [H1]
    · iapply ownSet_congr (Φ := fun a => a ↦ₘ f (a - q + q1)) (fun a (ha : InExt _ a) => by
        unfold InExt at ha; dsimp only at ha
        simp only [h, show a < q + x.toList.length by omega, ite_true]) $$ H1
    · iapply ownSet_congr (Φ := fun a => a ↦ₘ g a) (fun a (ha : InExt _ a) => by
        unfold InExt at ha; dsimp only at ha
        simp only [h, show ¬ a < q + x.toList.length by omega, ite_false]) $$ H2
  · ipureintro
    refine cstrImg_cat (fun i hi => ?_) ⟨fun i hi => ?_, ?_⟩
    · simp only [h, show q + i < q + x.toList.length by omega, ite_true,
        show q + i - q + q1 = q1 + i by omega]
      exact hf.1 i hi
    · simp only [h, show ¬ q + x.toList.length + i < q + x.toList.length by omega, ite_false]
      exact hg.1 i hi
    · simp only [h, show ¬ q + x.toList.length + y.toList.length < q + x.toList.length by omega,
        ite_false]
      exact hg.2

omit I in
/-- A fresh heap block's C string, read-only from now on. -/
theorem strAt_of_fresh {H : List (Nat × Nat)} {q : Nat} {x : String}
    (hf : FreshBlock vsaLayoutP H q (x.toList.length + 1)) :
    strOwn (GF := GF) q x ⊢ |==> strAt q x := by
  obtain ⟨-, hlo, hhi, -⟩ := hf.destruct
  have hlo' : Vsa.Sim.DlHeap.heapStart ≤ q := hlo
  have hhi' : q + (x.toList.length + 1) ≤ Vsa.Sim.DlHeap.heapEnd := hhi
  unfold Vsa.Sim.DlHeap.heapStart at hlo'; unfold Vsa.Sim.DlHeap.heapEnd at hhi'
  unfold strOwn
  iintro ⟨%img, H, %h⟩
  iapply strAt_of_owned h ⟨by omega, by omega, by unfold htifLo; omega⟩ $$ H

/-- **A value's display resources**, from the store (a closure's through
`CatDispSupply`; every other value's are `emp`). -/
theorem dispRes_of_valOf {N : NativeAddrs} (hd : CatDispSupply (GF := GF) N) (st : Store)
    (B : List (Nat × Nat)) (v : Value) (w0 w1 w2 : BitVec 64) :
    storeRepr (GF := GF) N st B ∗ □ valOf N v w0 w1 w2 ⊢ storeRepr N st B ∗ dispRes st v := by
  cases v with
  | closure ca =>
    unfold valOf
    iintro ⟨Hs, #⟨-, Hc⟩⟩
    iapply (hd st B ca _) $$ [Hs Hc]
    iframe Hs Hc
  | _ =>
    iintro ⟨Hs, -⟩
    iframe Hs
    unfold dispRes; iempintro

/-- **The `+` arm's string test** (`0x80003888`): a string right operand
(`a0`, its kind) or a string left one (`a6`) branches to the concatenation
at `0x80003a20`; `a5` is scratch. -/
theorem concat_route {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ interpText, live p.1)
    (hK : R 10 + 18446744073709551613#64 = 0#64 ∨ R 16 + 18446744073709551613#64 = 0#64)
    (hk : ∀ v, IW live Dt DA S Q 0x80003a20#64 (upd R 15 v) Mt) :
    IW live Dt DA S Q 0x80003888#64 R Mt := by
  have hse : LeanRV64DExecutable.Functions.sign_extend (m := 64) (0xffd#12) = 18446744073709551613#64 := by
    decide
  have huu : ∀ (a b : BitVec 64), upd (upd R 15 a) 15 b = upd R 15 b := fun a b => by
    funext x; simp only [upd_apply]; split <;> rfl
  refine it_80003888 hlive (it_8000388c hlive (fun _ => hk _) fun h1 =>
    it_80003890 hlive (it_80003894 hlive (fun _ => ?_) fun h2 => ?_))
  · rw [huu]; exact hk _
  · exfalso
    simp only [upd_apply, ite_true, show (16 : Nat) ≠ 15 from by decide, ite_false, hse] at h1 h2
    rcases hK with h | h
    · exact h1 h
    · exact h2 h

/-- A fresh block lies in the arena `[0x8001c170, 0x87800000)`. -/
theorem fresh_arena {H : List (Nat × Nat)} {q n : Nat} (h : FreshBlock vsaLayoutP H q n) :
    0x8001c170 ≤ q ∧ q + n ≤ 0x87800000 := by
  obtain ⟨-, hlo, hhi, -⟩ := h.destruct
  have hlo' : Vsa.Sim.DlHeap.heapStart ≤ q := hlo
  have hhi' : q + n ≤ Vsa.Sim.DlHeap.heapEnd := hhi
  unfold Vsa.Sim.DlHeap.heapStart at hlo'; unfold Vsa.Sim.DlHeap.heapEnd at hhi'
  exact ⟨hlo', hhi'⟩

/-- String `+` is charged `concatCost`. -/
theorem binOpCost_concat {st : Store} {lv rv : Value} (h : valTag lv = 3 ∨ valTag rv = 3) :
    binOpCost st .add lv rv = concatCost st lv rv := by
  cases lv <;> cases rv <;> simp_all [valTag, binOpCost]

/-- The concatenation buffer's charge (`interp.c:118`: `la + lb + 1`). -/
def catBufCost (st : Store) (lv rv : Value) : Nat :=
  roundUp16 ((lv.catDisplay st).length + (rv.catDisplay st).length + 1)

theorem concatCost_eq (st : Store) (lv rv : Value) :
    concatCost st lv rv = stringifyCost st lv + stringifyCost st rv + catBufCost st lv rv := rfl

/-- `stringify`'s request is charged its rendering's `stringifyCost`. -/
theorem stringifyChg (st : Store) (v : Value) :
    vsaChg ((strRender st v).toList.length + 1) (stringifyCost st v) := by
  refine ⟨by omega, ?_⟩
  unfold stringifyCost; rw [strRender_eq, String.length_toList]; exact Nat.le_refl _

/-- The buffer's request is charged `catBufCost`. -/
theorem catBufChg (st : Store) (lv rv : Value) :
    vsaChg ((strRender st lv).toList.length + (strRender st rv).toList.length + 1)
      (catBufCost st lv rv) := by
  refine ⟨by omega, ?_⟩
  unfold catBufCost; rw [strRender_eq, strRender_eq, String.length_toList, String.length_toList]
  exact Nat.le_refl _

end

/-- The frame words the concatenation arm restores: the prologue's spills and
its own `s5` spill (`sp + 1032`). -/
structure CatSaved (M : Mem) (s ret : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  saved : EvalSaved M s ret (rv 8) (rv 9) (rv 18) (rv 19)
  s5 : ldv .ld M (s.toNat - 1088 + 1032) = rv 21

theorem CatSaved.agree {M M' : Mem} {s ret : BitVec 64} {rv : Nat → BitVec 64}
    (h : CatSaved M s ret rv)
    (hag : ∀ k, s.toNat - 1088 + 1032 ≤ k → k < s.toNat - 1088 + 1088 → imgM M' k = imgM M k) :
    CatSaved M' s ret rv :=
  ⟨h.saved.agree fun k h1 h2 => hag k (by omega) h2,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s5⟩

theorem CatSaved.eq {M M' : Mem} {s ret : BitVec 64} {rv : Nat → BitVec 64}
    (h : CatSaved M s ret rv) (e : M' = M) : CatSaved M' s ret rv := e ▸ h

section World

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The world's parts the concatenation's tail does not touch after the two
`stringify` calls. -/
def catRest (N : NativeAddrs) (inp d : Nat) (st : St) (H B : List (Nat × Nat)) : IProp GF :=
  iprop(storeRepr N st.store B ∗ consoleOwn st.out ∗ Stdio.stdioOwn ∗
    interpCtxE inp d (errAny inp) ∗ ⌜∀ b ∈ B, b ∈ H⌝)

/-- The world again, with a heap that keeps every block of the old one. -/
theorem world_of_catRest (N : NativeAddrs) (inp d : Nat) (st : St) (ρ : Regime)
    {H H' B : List (Nat × Nat)} (hH : ∀ b ∈ H, b ∈ H') :
    heapRes (GF := GF) vsaLayoutP vsaRoomB ρ H' ∗ catRest N inp d st H B ⊢
      world N vsaLayoutP vsaRoomB inp ρ st d := by
  unfold catRest world worldE
  iintro ⟨Hh, Hs, Hc, Hio, Hi, %hB⟩
  iexists H', B
  iframe Hh Hs Hc Hio Hi
  ipureintro; exact fun b hb => hH b (hB b hb)

end World

end VsaIris.Interp
