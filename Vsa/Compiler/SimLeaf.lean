import Vsa.Compiler.SimInv
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def ESpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St)
    (v : Value) (n : Nat) : Prop :=
  ∀ (V : View) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → WfE T Γ e →
    Seg code pos (gexpr T Γ k pos e) → PosOK (pos + (gexpr T Γ k pos e).length) →
    16 + 16 * (k + tE e) ≤ fs →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      (B.pc = pcOf (pos + (gexpr T Γ k pos e).length) ∧
        ∃ V', EPost code T V st d env Γ sp fs k A n st' v V' B))

theorem run_whole {code : List Ins} {P : AM → Prop} (hfit : Fits code) {pos : Nat} {is : List Ins}
    (hseg : Seg code pos is) {L : GRegs} {m : Mem} {o : Array String}
    (h : WP code P pos is (fun L' m' o' => Reaches code ⟨pcOf (pos + is.length), L', m', o'⟩ P) L m o) :
    Reaches code ⟨pcOf pos, L, m, o⟩ P :=
  WP_sound hfit _ _ _ L m o hseg (fun _ _ _ h => h) h

theorem run_from {code : List Ins} {P : AM → Prop} (hfit : Fits code) {b : Nat} {c : List Ins}
    (hseg : Seg code b c) (k j : Nat) (hj : b + k = j) (hk : k ≤ c.length) {L : GRegs} {m : Mem}
    {o : Array String}
    (h : WP code P j (c.drop k) (fun L' m' o' => Reaches code ⟨pcOf (b + c.length), L', m', o'⟩ P) L m o) :
    Reaches code ⟨pcOf j, L, m, o⟩ P := by
  subst hj
  exact WP_sound hfit _ _ _ L m o (hseg.drop k) (fun L' m' o' h' => by
    rw [List.length_drop, show b + k + (c.length - k) = b + c.length by omega]; exact h') h

theorem ChainL.head' {F : FrMap} {s : Store} {a : Addr} {Γ : List (List String)} (h : ChainL F s a Γ) :
    ∃ f, F[a]? = some (f, Γ.headD []) := by
  cases h with
  | top _ _ hF => exact ⟨_, hF⟩
  | cons _ _ hF _ => exact ⟨_, hF⟩

theorem ChainL.frame {F : FrMap} {s : Store} {a : Addr} {Γ : List (List String)} (h : ChainL F s a Γ) :
    ∃ fr, s.frames[a]? = some fr := by
  cases h with
  | top hfr _ _ => exact ⟨_, hfr⟩
  | cons hfr _ _ _ => exact ⟨_, hfr⟩

theorem View.fa_eq {V : View} {a : Addr} {f : Nat} {L : List String} (h : V.F[a]? = some (f, L)) :
    V.fa a = f := by simp [View.fa, parOf, h]

theorem walkCode_length (x : String) (fin w : Nat) (here : String → List String → Nat → Nat → List Ins)
    (hl : ∀ l p, (here x l p fin).length = hereLen w x l) :
    ∀ (Γ : List (List String)) (pos : Nat),
      (walkCode (fun l p => here x l p fin) pos Γ).length = walkLen (hereLen w x) Γ
  | [], _ => rfl
  | [l], pos => by simp [walkCode, walkLen, hl]
  | l :: l' :: g, pos => by
    simp only [walkCode, walkLen, List.length_append, List.length_singleton, hl]
    rw [walkCode_length x fin w here hl (l' :: g)]

theorem readHere_length (x : String) (l : List String) (p fin : Nat) :
    (readHere x l p fin).length = hereLen 7 x l := by
  unfold readHere hereLen; cases slotOf l x <;> rfl

theorem writeHere_length (x : String) (l : List String) (p fin : Nat) :
    (writeHere x l p fin).length = hereLen 8 x l := by
  unfold writeHere hereLen; cases slotOf l x <;> rfl

theorem gexpr_var_length (T : List String) (Γ : List (List String)) (k pos : Nat) (x : String) :
    (gexpr T Γ k pos (.var x)).length = 1 + walkLen (hereLen 7 x) Γ := by
  simp only [gexpr, varCode, List.length_append, List.length_singleton]
  rw [walkCode_length x _ 7 readHere (fun l p => readHere_length x l p _)]

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sInt (st : St) (d : Nat) (env : Addr) (n : Int) : ESpec code T st d env (.int n) st (.int n) 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits hseg
  wp_simp [gexpr]
  refine reach_here (.inr ⟨rfl, V, epost_regs hm (S := [a0, a1]) (by decide) ?_ rfl rfl ?_⟩)
  · reg_simp []; exact Keep.refl _ _
  · exact ⟨_, _, by reg_simp [], by reg_simp [], rfl, rfl, hwf⟩

theorem sBool (st : St) (d : Nat) (env : Addr) (b : Bool) : ESpec code T st d env (.bool b) st (.bool b) 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits hseg
  cases b
  all_goals
    wp_simp [gexpr]
    refine reach_here (.inr ⟨rfl, V, epost_regs hm (S := [a0, a1]) (by decide) ?_ rfl rfl ?_⟩)
    · reg_simp []; exact Keep.refl _ _
    · exact ⟨_, _, by reg_simp [], by reg_simp []; rfl, rfl, by simp⟩

theorem sNull (st : St) (d : Nat) (env : Addr) : ESpec code T st d env .null st .null 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits hseg
  wp_simp [gexpr]
  refine reach_here (.inr ⟨rfl, V, epost_regs hm (S := [a0, a1]) (by decide) ?_ rfl rfl ?_⟩)
  · reg_simp []; exact Keep.refl _ _
  · exact ⟨_, _, by reg_simp [], by reg_simp [], rfl, rfl⟩

theorem sStr (st : St) (d : Nat) (env : Addr) (s : String) : ESpec code T st d env (.str s) st (.str s) 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  have hsb := hm.img.strs s hwf.2
  have hob : objEnd = 0xE0000000 := rfl
  have hlt : strAddr T s < 2 ^ 64 := by have := hsb.hi; have := hm.img.ptr.hi; omega
  apply run_whole hR.fits hseg
  wp_simp [gexpr, liN]
  refine reach_here (.inr ⟨rfl, V, epost_regs hm (S := [a0, a1]) (by decide) ?_ rfl rfl ?_⟩)
  · reg_simp []; exact Keep.refl _ _
  · refine ⟨3, BitVec.ofNat 64 (strAddr T s), by reg_simp [], by reg_simp [], rfl, ?_⟩
    rw [toNat_ofNat_lt hlt]; exact hsb

theorem sVar (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) (hget : st.store.get? env x = some v) :
    ESpec code T st d env (.var x) st v 0 := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨f, hFa⟩ := hm.chn.head'
  obtain ⟨fr, hfr⟩ := hm.chn.frame
  have hlt : env < st.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr).1
  have hlen := gexpr_var_length T Γ k pos x
  rw [hlen] at hP ⊢
  have he := hm.henv
  rw [View.fa_eq hFa] at he
  simp only [gexpr, varCode] at hseg
  obtain ⟨s1, s2⟩ := hseg.append
  apply run_whole hR.fits s1
  wp_simp [he.wp]
  refine reaches_mono (walk_read hR.fits hm.rel x (pos + 1 + walkLen (hereLen 7 x) Γ)
    (by rw [Nat.add_assoc]; exact hP) hm.chn
    (pos + 1) f _ o hFa s2 (by reg_simp [])) ?_
  rintro B ⟨hmB, hoB, hk, hB⟩
  rw [← get?_eq hm.rel.parents hlt x, hget] at hB
  obtain ⟨hpc, hv⟩ := hB
  refine .inr ⟨by rw [hpc]; congr 1; omega, V, epost_regs hm (S := walkClob) (by decide)
    ((Keep.gset (Keep.refl _ L) (by decide : 5 ∈ walkClob)).trans hk) hmB hoB hv⟩

end

end Vsa.Compiler
