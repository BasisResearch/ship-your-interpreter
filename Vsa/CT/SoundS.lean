import Vsa.CT.Sound

namespace Vsa.CT

open Vsa.While

theorem ctS_print {sec : String → Bool} {f : String} {args : List Expr}
    (h : ctS sec (.expr (.call (.var f) args)) = true) :
    (f = "print" ∨ f = "println") ∧ sec f = false ∧ args.length ≤ maxArgs ∧
      args.all (intArg sec) = true := by
  simp only [ctS, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ctS_varInit {sec : String → Bool} {x : String} {e : Expr}
    (h : ctS sec (.varDecl x (some e)) = true) :
    isNat x = false ∧ ∃ l, ctE sec e = some (.int, l) ∧ (sec x = false → l = false) := by
  simp only [ctS, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i l he
    refine ⟨l, he, fun hs => ?_⟩
    cases l
    · rfl
    · simp [hs] at h2
  · cases h2

theorem natOK_print {v : Value} {f : String} (h : NatOK v f) (hf : f = "print" ∨ f = "println") :
    v = .native .print ∨ v = .native .println := by
  rcases hf with rfl | rfl
  · exact .inl (h.2.1 rfl)
  · exact .inr (h.2.2 rfl)

theorem good_closure {s : Store} (g : Good s) {a : Addr} {cd : ClosureData}
    (h : s.closures[a]? = some cd) : False := by
  have ha : a < s.closures.size := by
    rcases Nat.lt_or_ge a s.closures.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  rw [g.1] at ha
  exact Nat.not_lt_zero a ha

mutual

theorem execL_ni (sec : String → Bool) : ∀ {st1 : St} {d : Nat} {env : Addr} {s : Stmt} {st1' : St}
    {t : Status} {l1 : SL}, ExecL st1 d env s st1' t l1 → ∀ {st2 : St}, ctS sec s = true →
    Low sec st1 st2 →
    ∃ st2' l2, ExecL st2 d env s st2' t l2 ∧ Low sec st1' st2' ∧ l1.skel = l2.skel ∧
      (st1.out = st2.out → l1.outs = l2.outs → st1'.out = st2'.out)
  | st1, _, _, _, _, _, _, .expr _ d env e st1' v l he, st2, hct, hlow => by
    by_cases hcall : ∃ f args, e = .call f args
    · obtain ⟨f, args, rfl⟩ := hcall
      cases f with
        | var fname =>
          obtain ⟨hf, hsf, hlen, hall⟩ := ctS_print hct
          cases he with
          | call _ _ _ _ _ stf sta _ fv vs _ lf la lc hfv _ hargs hcall =>
            cases hfv with
            | var _ _ _ _ _ hg =>
              have hn1 := get_good hlow.2.1 _ hg
              obtain ⟨fv2, hg2, heq, -⟩ := get_low hlow.1 hlow.2.2 hg
              cases heq hsf
              obtain ⟨sta2, vs2, hargs2, hlowa, hoa1, hoa2, hvs1, hvs2⟩ :=
                evalArgsL_ni sec args hall hlow hargs
              rcases natOK_print hn1 hf with rfl | rfl
              · cases hcall with
                | print =>
                  refine ⟨⟨sta2.store, sta2.out ++ printArgs sta2.store vs2⟩, _,
                    .expr _ _ _ _ _ _ _ (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.var _ _ _ _ _ hg2) hlen
                      hargs2 (.print _ _ _)),
                    ⟨hlowa.1, hlowa.2.1, hlowa.2.2⟩, by simp [SL.skel, EL.skel, CL.skel], fun ho hout => ?_⟩
                  simp only [SL.outs, EL.outs, CL.outs, List.append_assoc, List.append_cancel_left_eq,
                    List.cons.injEq, and_true] at hout
                  subst hout
                  show sta.out ++ printArgs sta.store vs = sta2.out ++ printArgs sta2.store vs
                  rw [hoa1, hoa2, ho, printArgs_store sta.store sta2.store vs hvs1]
              · cases hcall with
                | println =>
                  refine ⟨⟨sta2.store, sta2.out ++ printArgs sta2.store vs2 ++ "\n"⟩, _,
                    .expr _ _ _ _ _ _ _ (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (.var _ _ _ _ _ hg2) hlen
                      hargs2 (.println _ _ _)),
                    ⟨hlowa.1, hlowa.2.1, hlowa.2.2⟩, by simp [SL.skel, EL.skel, CL.skel], fun ho hout => ?_⟩
                  simp only [SL.outs, EL.outs, CL.outs, List.append_assoc, List.append_cancel_left_eq,
                    List.cons.injEq, and_true] at hout
                  subst hout
                  show sta.out ++ printArgs sta.store vs ++ "\n" = sta2.out ++ printArgs sta2.store vs ++ "\n"
                  rw [hoa1, hoa2, ho, printArgs_store sta.store sta2.store vs hvs1]
        | _ => simp [ctS, ctE] at hct
    · have hct' : (ctE sec e).isSome = true := by
        cases e with
        | call f args => exact absurd ⟨f, args, rfl⟩ hcall
        | _ => simpa [ctS] using hct
      obtain ⟨⟨ty, lab⟩, hce⟩ := Option.isSome_iff_exists.mp hct'
      obtain ⟨st2', v2, he2, hlow', ho1, ho2, -, -, -⟩ := evalL_ni sec _ hce hlow he
      exact ⟨st2', _, .expr _ _ _ _ _ _ _ he2, hlow', rfl, fun ho _ => by rw [ho1, ho2, ho]⟩
  | st1, _, _, _, _, _, _, .varInit _ d env x e st1' v l he, st2, hct, hlow => by
    obtain ⟨hx, lab, hce, hsx⟩ := ctS_varInit hct
    obtain ⟨st2', v2, he2, hlow', ho1, ho2, heq, ⟨n1, rfl⟩, ⟨n2, rfl⟩⟩ := evalL_ni sec e hce hlow he
    refine ⟨⟨st2'.store.define env x (.int n2), st2'.out⟩, _, .varInit _ _ _ _ _ _ _ _ he2,
      ⟨define_low hlow'.1 env x (fun h => heq (hsx h)), define_good hlow'.2.1 env x (natOK_of_int hx),
        define_good hlow'.2.2 env x (natOK_of_int hx)⟩, rfl, fun ho _ => ?_⟩
    show st1'.out = st2'.out
    rw [ho1, ho2, ho]
  | _, _, _, _, _, _, _, .varNull .., _, hct, _ => by simp [ctS] at hct
  | st1, _, _, _, _, _, _, .block _ d env ss store' inner st1' t ls halloc hseq, st2, hct, hlow => by
    have hct' : ctSeq sec ss = true := by simpa [ctS] using hct
    obtain ⟨ha, hi⟩ := alloc_low hlow.1 (some env)
    simp only [halloc] at ha hi
    have hlow0 : Low sec ⟨store', st1.out⟩ ⟨(st2.store.allocFrame (some env)).1, st2.out⟩ := by
      refine ⟨ha, ?_, alloc_good hlow.2.2 _⟩
      have := alloc_good hlow.2.1 (some env); rw [halloc] at this; exact this
    obtain ⟨st2', ls2, hseq2, hlow', hsk, hout⟩ := execSeqL_ni sec hseq hct' hlow0
    refine ⟨st2', _, .block _ _ _ _ _ _ _ _ _ (by rw [hi]) hseq2, hlow', by simp [SL.skel, hsk],
      fun ho h => hout ho (by simpa [SL.outs] using h)⟩
  | st1, _, _, _, _, _, _, .ifTrue _ d env c th el st1' st1'' v t lc lt hc htr hth, st2, hct, hlow => by
    have hct' : pubC sec c = true ∧ ctS sec th = true := by
      cases el <;> simp only [ctS, Bool.and_eq_true] at hct <;> first | exact hct | exact hct.1
    obtain ⟨ty, hce⟩ := pubC_ct hct'.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    obtain ⟨st2'', l2, hth2, hlow'', hsk, hout⟩ := execL_ni sec hth hct'.2 hlow'
    refine ⟨st2'', _, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ hc2 htr hth2, hlow'', by simp [SL.skel, hsk],
      fun ho h => ?_⟩
    simp only [SL.outs, List.append_cancel_left_eq] at h
    exact hout (by rw [ho1, ho2, ho]) h
  | st1, _, _, _, _, _, _, .ifFalse _ d env c th el st1' st1'' v t lc le hc hfa hel, st2, hct, hlow => by
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    obtain ⟨st2'', l2, hel2, hlow'', hsk, hout⟩ := execL_ni sec hel hct.2 hlow'
    refine ⟨st2'', _, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ hc2 hfa hel2, hlow'', by simp [SL.skel, hsk],
      fun ho h => ?_⟩
    simp only [SL.outs, List.append_cancel_left_eq] at h
    exact hout (by rw [ho1, ho2, ho]) h
  | st1, _, _, _, _, _, _, .ifNone _ d env c th st1' v lc hc hfa, st2, hct, hlow => by
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    exact ⟨st2', _, .ifNone _ _ _ _ _ _ _ _ hc2 hfa, hlow', rfl, fun ho _ => by rw [ho1, ho2, ho]⟩
  | st1, _, _, _, _, _, _, .whileFalse _ d env c b st1' v lc hc hfa, st2, hct, hlow => by
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    exact ⟨st2', _, .whileFalse _ _ _ _ _ _ _ _ hc2 hfa, hlow', rfl, fun ho _ => by rw [ho1, ho2, ho]⟩
  | st1, _, _, _, _, _, _, .whileBreak _ d env c b st1' st1'' v lc lb hc htr hb, st2, hct, hlow => by
    have hct0 := hct
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    obtain ⟨st2'', l2, hb2, hlow'', hsk, hout⟩ := execL_ni sec hb hct.2 hlow'
    refine ⟨st2'', _, .whileBreak _ _ _ _ _ _ _ _ _ _ hc2 htr hb2, hlow'', by simp [SL.skel, hsk],
      fun ho h => ?_⟩
    simp only [SL.outs, List.append_cancel_left_eq] at h
    exact hout (by rw [ho1, ho2, ho]) h
  | st1, _, _, _, _, _, _, .whileRet _ d env c b st1' st1'' v rv lc lb hc htr hb, st2, hct, hlow => by
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    obtain ⟨st2'', l2, hb2, hlow'', hsk, hout⟩ := execL_ni sec hb hct.2 hlow'
    refine ⟨st2'', _, .whileRet _ _ _ _ _ _ _ _ _ _ _ hc2 htr hb2, hlow'', by simp [SL.skel, hsk],
      fun ho h => ?_⟩
    simp only [SL.outs, List.append_cancel_left_eq] at h
    exact hout (by rw [ho1, ho2, ho]) h
  | st1, _, _, _, _, _, _, .whileLoop _ d env c b st1' st1'' st1''' v t t' lc lb lr hc htr hb hst hr,
      st2, hct, hlow => by
    have hct0 := hct
    simp only [ctS, Bool.and_eq_true] at hct
    obtain ⟨ty, hce⟩ := pubC_ct hct.1
    obtain ⟨st2', v2, hc2, hlow', ho1, ho2, heq, -, -⟩ := evalL_ni sec c hce hlow hc
    cases heq rfl
    obtain ⟨st2'', l2, hb2, hlow'', hsk, hout⟩ := execL_ni sec hb hct.2 hlow'
    obtain ⟨st2''', l3, hr2, hlow''', hsk', hout'⟩ := execL_ni sec hr hct0 hlow''
    refine ⟨st2''', _, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc2 htr hb2 hst hr2, hlow''',
      by simp [SL.skel, hsk, hsk'], fun ho h => ?_⟩
    simp only [SL.outs, List.append_assoc, List.append_cancel_left_eq] at h
    have hl := (SL.inj lb l2 hsk).1
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact hout' (hout (by rw [ho1, ho2, ho]) h1) h2
  | _, _, _, _, _, _, _, .forStart .., _, hct, _ => by simp [ctS] at hct
  | _, _, _, _, _, _, _, .ret .., _, hct, _ => by simp [ctS] at hct
  | _, _, _, _, _, _, _, .retNull .., _, hct, _ => by simp [ctS] at hct
  | _, _, _, _, _, _, _, .brk .., st2, _, hlow => ⟨st2, _, .brk .., hlow, rfl, fun ho _ => ho⟩
  | _, _, _, _, _, _, _, .cont .., st2, _, hlow => ⟨st2, _, .cont .., hlow, rfl, fun ho _ => ho⟩

theorem execSeqL_ni (sec : String → Bool) : ∀ {st1 : St} {d : Nat} {env : Addr} {ss : List Stmt}
    {st1' : St} {t : Status} {l1 : List SL}, ExecSeqL st1 d env ss st1' t l1 → ∀ {st2 : St},
    ctSeq sec ss = true → Low sec st1 st2 →
    ∃ st2' l2, ExecSeqL st2 d env ss st2' t l2 ∧ Low sec st1' st2' ∧ skelSs l1 = skelSs l2 ∧
      (st1.out = st2.out → outsSs l1 = outsSs l2 → st1'.out = st2'.out)
  | _, _, _, _, _, _, _, .nil .., st2, _, hlow => ⟨st2, _, .nil .., hlow, rfl, fun ho _ => ho⟩
  | _, _, _, _, _, _, _, .consNormal _ _ _ s ss _ _ _ l ls h1 h2, st2, hct, hlow => by
    simp only [ctSeq, Bool.and_eq_true] at hct
    obtain ⟨st2', l2, h1', hlow', hsk, hout⟩ := execL_ni sec h1 hct.1 hlow
    obtain ⟨st2'', ls2, h2', hlow'', hsk', hout'⟩ := execSeqL_ni sec h2 hct.2 hlow'
    refine ⟨st2'', _, .consNormal _ _ _ _ _ _ _ _ _ _ h1' h2', hlow'', by simp [skelSs, hsk, hsk'],
      fun ho h => ?_⟩
    simp only [outsSs] at h
    obtain ⟨e1, e2⟩ := List.append_inj h (SL.inj l l2 hsk).1
    exact hout' (hout ho e1) e2
  | _, _, _, _, _, _, _, .consAbrupt _ _ _ s ss _ _ l h1 hne, st2, hct, hlow => by
    simp only [ctSeq, Bool.and_eq_true] at hct
    obtain ⟨st2', l2, h1', hlow', hsk, hout⟩ := execL_ni sec h1 hct.1 hlow
    refine ⟨st2', _, .consAbrupt _ _ _ _ _ _ _ _ h1' hne, hlow', by simp [skelSs, hsk],
      fun ho h => hout ho (by simpa [outsSs] using h)⟩

end

end Vsa.CT
