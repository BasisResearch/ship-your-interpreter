import Vsa.Compiler.SimLeaf

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem Room.mono {V : View} {n n' : Nat} (h : Room V n') (hn : n ≤ n') : Room V n :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem Room.of_within {V V' : View} {n1 n2 : Nat} (hw : Within V V' n1) (h : Room V (n1 + n2)) :
    Room V' n2 := ⟨by have := h.1; have := hw.1; omega, by have := h.2; have := hw.2; omega⟩

theorem Within.add {V V1 V2 : View} {n1 n2 : Nat} (h1 : Within V V1 n1) (h2 : Within V1 V2 n2) :
    Within V V2 (n1 + n2) := ⟨by have := h1.1; have := h2.1; omega, by have := h1.2; have := h2.2; omega⟩

theorem Within.mono {V V' : View} {n n' : Nat} (h : Within V V' n) (hn : n ≤ n') : Within V V' n' :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem VGrow.trans {V V1 V2 : View} {s s1 s2 : Store} (h1 : VGrow V s V1 s1) (h2 : VGrow V1 s1 V2 s2) :
    VGrow V s V2 s2 :=
  ⟨h1.grows.trans h2.grows, h1.hpre.trans h2.hpre, Nat.le_trans h1.hle h2.hle, Nat.le_trans h1.le h2.le⟩

theorem ObjAgree.trans {m1 m2 m3 : Mem} {h h' : Nat} (h1 : ObjAgree m1 m2 h) (h2 : ObjAgree m2 m3 h')
    (hh : h ≤ h') : ObjAgree m1 m3 h := fun a ha h3 h4 => (h2 a ha h3 (by omega)).trans (h1 a ha h3 h4)

theorem StackKeep.trans {m1 m2 m3 : Mem} {sp fs k : Nat} (h1 : StackKeep m1 m2 sp fs k)
    (h2 : StackKeep m2 m3 sp fs k) : StackKeep m1 m3 sp fs k := ⟨h1.low.trans h2.low, h1.high.trans h2.high⟩

theorem StackKeep.mono {m1 m2 : Mem} {sp fs k k' : Nat} (h : StackKeep m1 m2 sp fs k') (hk : k ≤ k') :
    StackKeep m1 m2 sp fs k := ⟨h.low.mono (Nat.le_refl _) (by omega), h.high⟩

theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {x : α}
    (hx : l[i]? = some x) : l'[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx

theorem VRepr.grow {H H' : CloMap} {m m' : Mem} {h h' : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) (hH : H <+: H') (hag : ObjAgree m m' h) (hh : h ≤ h') : VRepr H' m' h' v t p := by
  cases v <;> simp only [VRepr] at hv ⊢
  all_goals first
    | exact hv
    | exact ⟨hv.1, hv.2.mono hag hh⟩
    | exact ⟨hv.1, getElem?_of_prefix hH hv.2⟩

def InTmp (H : CloMap) (m : Mem) (h sp j : Nat) (v : Value) : Prop :=
  VRepr H m h v (rdW m (sp + 16 + 16 * j)) (rdW m (sp + 16 + 16 * j + 8))

theorem InTmp.grow {H H' : CloMap} {m m' : Mem} {h h' sp fs k j : Nat} {v : Value}
    (hv : InTmp H m h sp j v) (hH : H <+: H') (hag : ObjAgree m m' h) (hh : h ≤ h')
    (hk : StackKeep m m' sp fs k) (hj : j < k) (hal : sp % 8 = 0) : InTmp H' m' h' sp j v := by
  unfold InTmp at hv ⊢
  rw [hk.low _ (by omega) (by omega) (by omega), hk.low _ (by omega) (by omega) (by omega)]
  exact hv.grow hH hag hh

theorem Seg.cast {code : List Ins} {pos pos' : Nat} {is : List Ins} (h : Seg code pos is) (e : pos = pos') :
    Seg code pos' is := e ▸ h

theorem reaches_pc {code : List Ins} {q q' : Nat} {L : GRegs} {m : Mem} {o : Array String} {P : AM → Prop}
    (e : q = q') (h : Reaches code ⟨pcOf q', L, m, o⟩ P) : Reaches code ⟨pcOf q, L, m, o⟩ P := e ▸ h

theorem ESpec.bind {code : List Ins} {T : List String} {st : St} {d : Nat} {env : Addr} {e : Expr}
    {st1 : St} {v1 : Value} {n1 : Nat} (hE : ESpec code T st d env e st1 v1 n1) {V : View}
    {Γ : List (List String)} {sp fs k pos : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A)
    (hA : A.pc = pcOf pos) (hwf : WfE T Γ e) (hseg : Seg code pos (gexpr T Γ k pos e))
    (hP : PosOK (pos + (gexpr T Γ k pos e).length)) (htmp : 16 + 16 * (k + tE e) ≤ fs)
    {Q : AM → Prop} (herr : ∀ B, B.pc = pcOf errPos → ¬ Room V n1 → Q B)
    (hk : ∀ V1 B, B.pc = pcOf (pos + (gexpr T Γ k pos e).length) →
      EPost code T V st d env Γ sp fs k A n1 st1 v1 V1 B → Reaches code B Q) :
    Reaches code A Q :=
  ex_bind (hE V Γ sp fs k pos A hm hA hwf hseg hP htmp) fun B hB => by
    rcases hB with ⟨h1, h2⟩ | ⟨h1, V1, h2⟩
    · exact reach_here (herr B h1 h2)
    · exact hk V1 B h1 h2

end Vsa.Compiler
