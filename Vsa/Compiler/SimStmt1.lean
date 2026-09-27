import Vsa.Compiler.SimDecl

/-!
# Forward simulation: simple statements

Expression statements, declarations, `return`, `break` and `continue`.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- A statement post from an expression post whose state also completes the statement. -/
theorem SPost.of_epost {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {C : GCtx} {sp fs fin : Nat} {A B : AM} {n n' : Nat} {st' : St} {v : Value} {V' : View}
    (hp : EPost code T V st d env C.Γ sp fs 0 A n st' v V' B) (hpc : B.pc = pcOf fin) (hn : n ≤ n') :
    SPost code T V st d env C sp fs fin A n' st' .normal V' B :=
  ⟨⟨hpc, hp.ms⟩, hp.grow, hp.within.mono hn, hp.stack, hp.obj⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sExpr {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env e st' v n) : SSpec code T st d env (.expr e) st' .normal n := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  refine reaches_mono (hE V C.Γ sp fs 0 pos A hm hA hwf hseg hP (by simpa [tS] using htmp)) ?_
  rintro B (⟨h1, h2⟩ | ⟨h1, V', hp⟩)
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨V', SPost.of_epost hp (by rw [h1]; rfl) (Nat.le_refl _)⟩

theorem sBrk (st : St) (d : Nat) (env : Addr) : SSpec code T st d env .brk st .brk 0 := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  refine reaches_mono (run_exitTo hR hm hA hctx hctx.brk hseg hP) ?_
  rintro B ⟨hx, hmB, hoB, hk⟩
  exact .inr ⟨V, hx, VGrow.refl _ _, Within.refl _ _, by rw [hmB]; exact StackKeep.refl _ _ _ _,
    by rw [hmB]; exact ObjAgree.refl _ _⟩

theorem sCont (st : St) (d : Nat) (env : Addr) : SSpec code T st d env .cont st .cont 0 := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  refine reaches_mono (run_exitTo hR hm hA hctx hctx.cont hseg hP) ?_
  rintro B ⟨hx, hmB, hoB, hk⟩
  exact .inr ⟨V, hx, VGrow.refl _ _, Within.refl _ _, by rw [hmB]; exact StackKeep.refl _ _ _ _,
    by rw [hmB]; exact ObjAgree.refl _ _⟩

theorem sRet {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env e st' v n) : SSpec code T st d env (.ret (some e)) st' (.ret v) n := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append] at hP
  refine hE.bind hm hA hwf s1 (posOK_le hP (by omega)) (by simpa [tS] using htmp)
    (fun B h1 h2 => .inl ⟨h1, h2⟩) fun V1 B hpc hp => ?_
  refine reaches_mono (run_exitTo hR hp.ms hpc hctx hctx.ret s2 (by rw [← Nat.add_assoc] at hP; exact hP)) ?_
  rintro B' ⟨hx, hmB, hoB, hk⟩
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  refine .inr ⟨V1, ⟨hx, t, p, hk.has (by decide) h10, hk.has (by decide) h11, by rw [hmB]; exact hv⟩,
    hp.grow, hp.within, by rw [hmB]; exact hp.stack, by rw [hmB]; exact hp.obj⟩

theorem sRetNull (st : St) (d : Nat) (env : Addr) : SSpec code T st d env (.ret none) st (.ret .null) 0 := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hP s2 ⊢
  obtain ⟨pc0, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits s1
  wp_simp []
  have hm' := hm.transport (B := ⟨pcOf (pos + 2), gset (gset L 10 0) 11 0, m, o⟩) (S := [a0, a1]) (by decide)
    (by reg_simp []; exact Keep.refl _ _) (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
  refine reaches_mono (run_exitTo hR hm' rfl hctx hctx.ret s2 (by rw [← Nat.add_assoc] at hP; exact hP)) ?_
  rintro B' ⟨hx, hmB, hoB, hk⟩
  refine .inr ⟨V, ⟨hx, 0, 0, hk.has (by decide) (by reg_simp []), hk.has (by decide) (by reg_simp []), rfl, rfl⟩,
    VGrow.refl _ _, Within.refl _ _, by rw [hmB]; exact StackKeep.refl _ _ _ _, by rw [hmB]; exact ObjAgree.refl _ _⟩

theorem sVarNull (st : St) (d : Nat) (env : Addr) (x : String) :
    SSpec code T st d env (.varDecl x none) ⟨st.store.define env x .null, st.out⟩ .normal
      (defineCost st.store env x) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append, List.length_cons, List.length_nil] at hP s2
  obtain ⟨pc0, L, m, o⟩ := A
  simp only at hA; subst hA
  apply run_whole hR.fits s1
  wp_simp []
  have hm' := hm.transport (B := ⟨pcOf (pos + 2), gset (gset L 10 0) 11 0, m, o⟩) (S := [a0, a1]) (by decide)
    (by reg_simp []; exact Keep.refl _ _) (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
  refine reaches_mono (run_storeSlot hR hm' rfl hwf.1 (s2.cast (by omega)) (by reg_simp []) (by reg_simp [])
    (v := .null) ⟨rfl, rfl⟩) ?_
  rintro B ⟨hpc, hmB, hoB, hout, hk, hsh⟩
  have hb := hm.stk.bounds
  refine .inr ⟨V, ⟨by rw [hpc]; congr 1 <;> simp [storeSlot] <;> omega, hmB⟩, ⟨Grows.of_shape hsh, List.prefix_refl _,
    Nat.le_refl _, Nat.le_refl _⟩, Within.mono (Within.refl _ _) (Nat.zero_le _),
    hout.stack hm.rel.top hb.1, hout.obj hm.rel.top⟩

theorem sVarInit {st : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env e st' v n) :
    SSpec code T st d env (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩ .normal
      (n + defineCost st'.store env x) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨s1, s2⟩ := hseg.append
  simp only [List.length_append] at hP s2
  refine hE.bind hm hA hwf.2 s1 (posOK_le hP (by omega)) (by simpa [tS] using htmp)
    (fun B h1 h2 => .inl ⟨h1, Room.not_mono h2 (by omega)⟩) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  refine reaches_mono (run_storeSlot hR hp.ms hpc hwf.1 s2 h10 h11 hv) ?_
  rintro B' ⟨hpc', hmB, hoB, hout, hk, hsh⟩
  have hb := hm.stk.bounds
  refine .inr ⟨V1, ⟨by rw [hpc']; congr 1 <;> simp [storeSlot] <;> omega, hmB⟩, hp.grow.trans ⟨Grows.of_shape hsh,
    List.prefix_refl _, Nat.le_refl _, Nat.le_refl _⟩, hp.within.mono (by omega),
    hp.stack.trans (hout.stack hp.ms.rel.top hb.1), hp.obj.trans (hout.obj hp.ms.rel.top) hp.grow.le⟩

end

end Vsa.Compiler
