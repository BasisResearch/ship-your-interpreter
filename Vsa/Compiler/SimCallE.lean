import Vsa.Compiler.SimArgs
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem tArgs_shift : ∀ (es : List Expr) (j c : Nat), tArgs (j + c) es ≤ tArgs j es + c
  | [], _, _ => by simp [tArgs]
  | e :: es, j, c => by
    simp only [tArgs]
    have := tArgs_shift es (j + 1) c
    rw [show j + c + 1 = j + 1 + c by omega]
    omega

theorem evalArgsCost_length : ∀ {es : List Expr} {st : St} {d : Nat} {env : Addr} {st' : St}
    {vs : List Value} {n : Nat}, EvalArgsCost st d env es st' vs n → vs.length = es.length
  | [], _, _, _, _, _, _, h => by cases h; rfl
  | _ :: _, _, _, _, _, _, _, h => by
    cases h with
    | cons _ _ _ _ _ _ _ _ _ _ _ _ hes => simp [evalArgsCost_length hes]

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sCall {st : St} {d : Nat} {env : Addr} {f : Expr} {args : List Expr} {st1 st2 st3 : St}
    {fv : Value} {vs : List Value} {v : Value} {nf na nc : Nat} (hE : ESpec code T st d env f st1 fv nf)
    (hmax : args.length ≤ maxArgs) (hA : ASpec code T st1 d env args st2 vs na) (hvl : vs.length = args.length)
    (hC : CSpec code T st2 d fv vs st3 v nc) :
    ESpec code T st d env (.call f args) st3 v (nf + na + nc) := by
  intro V Γ sp fs k pos A hm hpc hwf hseg hP htmp
  obtain ⟨hwf1, hwa⟩ := hwf
  simp only [tE] at htmp
  have hal := hm.stk.al
  have hsh : tArgs (k + 1) args ≤ tArgs 1 args + k := by
    have := tArgs_shift args 1 k; rwa [Nat.add_comm 1 k] at this
  have h := And.intro hseg hP
  simp only [gexpr, show ¬ maxArgs < args.length by omega, if_false, storeTmp, List.append_assoc, ↓segP_app,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  simp only [gexpr, show ¬ maxArgs < args.length by omega, if_false, storeTmp, List.length_append,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, ⟨s3, p3⟩, s4, p4⟩ := h
  refine hE.bind hm hpc hwf1 s1 p1 (by omega)
    (fun B h1 h2 => .inl ⟨h1, Room.not_mono h2 (by omega)⟩) fun V1 B1 hpc1 hp1 => ?_
  obtain ⟨t1, q1, h10, h11, hv1⟩ := hp1.val
  obtain ⟨pc1, L1, m1, o1⟩ := B1
  simp only at hpc1 h10 h11 hv1; subst hpc1
  refine run_storeTmp hR.fits s2 hp1.ms.hsp hp1.ms.stk (by omega) h10 h11 fun L2 hk2 => ?_
  obtain ⟨hmC, hoC⟩ := hp1.ms.stored (pc := pcOf (pos + (gexpr T Γ k pos f).length + 4)) (j := k) (by omega)
    (S := [t6]) (by decide) hk2 (t := t1) (p := q1)
  have hlt := InTmp.stored hv1 hal hoC
  refine ex_bind (hA V1 Γ sp fs (k + 1) _ _ hmC rfl hwa s3 p3 (by omega) (by omega)) ?_
  rintro D (⟨h1, h2⟩ | ⟨hpcD, V2, hp2⟩)
  · exact reach_here (.inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩)
  have hlt2 := hlt.grow hp2.grow.hpre hp2.obj hp2.grow.le hp2.stack (by omega) (by omega)
  obtain ⟨pcD, LD, mD, oD⟩ := D
  simp only at hpcD; subst hpcD
  refine ex_bind (hC V2 env Γ sp fs k _ _ hp2.ms rfl hlt2 hp2.tmps (by omega) (hvl ▸ s4)
    (by rw [hvl]; exact p4) (by omega)) ?_
  rintro E (⟨h1, h2⟩ | ⟨hpcE, V3, hp3⟩)
  · exact reach_here (.inl ⟨h1, Room.not_within h2 (hp1.within.add hp2.within) (by omega)⟩)
  refine reach_here (.inr ⟨by rw [hpcE, hvl]; congr 1 <;> omega, V3, ?_⟩)
  exact {
    ms := hp3.ms
    val := hp3.val
    grow := hp1.grow.trans (hp2.grow.trans hp3.grow)
    within := (hp1.within.add hp2.within).add hp3.within
    stack := hp1.stack.trans ((StackKeep.stored hal (Nat.le_refl _) (by omega)).trans
      ((hp2.stack.mono (by omega)).trans (hp3.stack.mono (by omega))))
    obj := hp1.obj.trans (hoC.trans (hp2.obj.trans hp3.obj hp2.grow.le) (Nat.le_refl _)) hp1.grow.le }

end

end Vsa.Compiler
