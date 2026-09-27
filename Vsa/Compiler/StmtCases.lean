import Vsa.Compiler.StmtFrag

/-!
# Simple statements

Expression statements and `print`/`println` calls: their code either completes
normally with the unique semantic result, or reaches the runtime-error exit while
the statement has no execution.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- What running a statement's code achieves in one case: the unique execution
and the relation at the exit it reaches. -/
def StmtOK (code : List Ins) (C : Ctx) (pos : Nat) (s : Stmt) (st : St) (d : Nat) (env : Addr)
    (B : AM) : Prop :=
  (∃ st' t, ExecS st d env s st' t ∧ (∀ st'' t', ExecS st d env s st'' t' → st'' = st' ∧ t' = t) ∧
      B.pc = pcOf (exitPos C (pos + (cstmt C pos s).1.length) t) ∧ SR C.Γ env st' B ∧
      SameParents st.store st'.store ∧ (∀ v, t ≠ .ret v)) ∨
    (astep code B = some (.halt 70) ∧ ∀ st' t, ¬ ExecS st d env s st' t)

theorem cargs_end (Γ : Scope) : ∀ (args : List Expr) (k pos : Nat),
    (cargs Γ k pos args).2 = pos + (cargs Γ k pos args).1.length
  | [], _, _ => by simp [cargs]
  | e :: es, k, pos => by
    have := cargs_end Γ es (k + 1) (pos + (cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length)
    simp only [cargs, List.length_append] at this ⊢
    omega

theorem printArgs_ints (s : Store) (ns : List Int) :
    printArgs s (ns.map Value.int) = String.intercalate " " (ns.map intToString) := by
  simp [printArgs, Function.comp_def, Value.display]

theorem vals_ints : ∀ (vs : List Value), (∀ v ∈ vs, ∃ n, v = .int n ∧ InRange n) →
    ∃ ns : List Int, vs = ns.map Value.int ∧ ∀ x ∈ ns, InRange x
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: vs, h => by
    obtain ⟨n, rfl, hn⟩ := h v (List.mem_cons_self ..)
    obtain ⟨ns, rfl, hns⟩ := vals_ints vs (fun w hw => h w (List.mem_cons_of_mem _ hw))
    exact ⟨n :: ns, rfl, by
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hn
      · exact hns x hx⟩

section
variable {code : List Ins}

theorem sim_exprStmt {C : Ctx} {pos : Nat} {e : Expr} {st : St} {d : Nat} {env : Addr} {A : AM}
    (hAt : At code C pos) (he : CondE C.Γ.names e) (hnc : ∀ f args, e ≠ .call f args)
    (hseg : Seg code pos (cstmt C pos (.expr e)).1) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A) :
    ∃ B, Star code A B ∧ StmtOK code C pos (.expr e) st d env B := by
  have hce : cstmt C pos (.expr e) = (cexpr C.Γ 0 pos e, C.next) := by
    cases e with
    | call f args => exact absurd rfl (hnc f args)
    | _ => rfl
  rw [hce] at hseg
  dsimp only at hseg
  have hs := CondE.simple he
  have hend := Seg.end_ok hAt.fits hseg (List.ne_nil_of_length_pos (cexpr_pos C.Γ e 0 pos hs))
  obtain ⟨B, r, hB⟩ := sim_expr hAt.lay hAt.nd hAt.slot_bound e hs 0 pos st d env A he
    (by have := tdepth_le C.Γ e 0 pos hs; have := hend.small; omega) hseg hend hA hsr.1
  refine ⟨B, r, ?_⟩
  rcases hB with ⟨v, st', hev, -, hout, hBo, hBpc, -, hBc, -⟩ | ⟨hh, hne⟩
  · refine .inl ⟨st', .normal, .expr _ _ _ _ _ _ hev, fun st'' t h => ?_, by rw [hce]; exact hBpc,
      ⟨hBc, by rw [outStr, hBo, hout]; exact hsr.2⟩, EvalE.sameParents e hs hev, by simp⟩
    cases h with | expr _ _ _ _ _ _ he' =>
    exact ⟨(EvalE.det e hs he' hev).1, rfl⟩
  · refine .inr ⟨hh, fun st' t h => ?_⟩
    cases h with | expr _ _ _ _ _ _ he' => exact hne _ _ he'

theorem EvalArgs.length_eq : ∀ {args : List Expr} {st : St} {d : Nat} {env : Addr} {st' : St}
    {vs : List Value}, EvalArgs st d env args st' vs → vs.length = args.length
  | [], _, _, _, _, _, h => by cases h; rfl
  | _ :: _, _, _, _, _, _, h => by
    cases h with | cons _ _ _ _ _ _ _ _ _ _ hr => simp [EvalArgs.length_eq hr]

theorem native_entry (f : String) (hf : f = "print" ∨ f = "println") :
    ∃ q, nativeVars.find? (·.1 == f) = some (f, q) ∧
      q = (if f = "println" then .native .println else .native .print) := by
  rcases hf with rfl | rfl <;> exact ⟨_, rfl, rfl⟩

theorem sim_printStmt {C : Ctx} {pos : Nat} {f : String} {args : List Expr} {st : St} {d : Nat}
    {env : Addr} {A : AM} (hAt : At code C pos) (hs : SupS C.Γ.names false (.expr (.call (.var f) args)))
    (hseg : Seg code pos (cstmt C pos (.expr (.call (.var f) args))).1)
    (hpos : PosOK (pos + (cstmt C pos (.expr (.call (.var f) args))).1.length))
    (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A) :
    ∃ B, Star code A B ∧ StmtOK code C pos (.expr (.call (.var f) args)) st d env B := by
  obtain ⟨hf, hlen, hargs⟩ := hs
  have hce : cstmt C pos (.expr (.call (.var f) args)) =
      ((cargs C.Γ 0 pos args).1 ++ printLoop 0 (cargs C.Γ 0 pos args).2 args.length ++
        (if f = "println" then putc '\n' else []), C.next) := rfl
  rw [hce] at hseg hpos
  dsimp only at hseg hpos
  obtain ⟨hs12, hs3⟩ := hseg.append
  obtain ⟨hs1, hs2⟩ := hs12.append
  have hmax : maxArgs = 32 := rfl
  -- the callee is the native
  obtain ⟨q, hq, hqv⟩ := native_entry f hf
  have hget : st.store.get? env f = some q :=
    hsr.1.native _ hsr.1.env_lt (fun fr hfr => hAt.nat fr hfr f (by rcases hf with h | h <;> simp [IsNative, h])) hq
  -- the arguments
  have hend : (cargs C.Γ 0 pos args).2 = pos + (cargs C.Γ 0 pos args).1.length := cargs_end _ _ _ _
  obtain ⟨B1, r1, hB1⟩ := sim_args (d := d) (env := env) hAt.lay hAt.nd hAt.slot_bound args 0 pos st A hargs
    (by omega) hs1 (by rw [hend]; unfold PosOK at *; simp only [List.length_append] at hpos; omega) hA hsr.1
  -- the result state of the call
  let outOf (s : St) (vs : List Value) : St :=
    ⟨s.store, s.out ++ printArgs s.store vs ++ (if f = "println" then "\n" else "")⟩
  have hcall : ∀ (s : St) (vs : List Value), Call s d q vs (outOf s vs) .null := by
    intro s vs
    by_cases hp : f = "println"
    · rw [hqv, if_pos hp]; simp only [outOf, if_pos hp]; exact .println _ _ _
    · rw [hqv, if_neg hp]; simp only [outOf, if_neg hp, String.append_empty]; exact .print _ _ _
  have huniq : ∀ (s s' : St) (vs : List Value) (v : Value), Call s d q vs s' v → s' = outOf s vs := by
    intro s s' vs v h
    by_cases hp : f = "println"
    · rw [hqv, if_pos hp] at h; cases h; simp [outOf, hp]
    · rw [hqv, if_neg hp] at h; cases h; simp [outOf, hp]
  have hderiv : ∀ {s' : St} {t : Status}, ExecS st d env (.expr (.call (.var f) args)) s' t →
      ∃ st2 vs, EvalArgs st d env args st2 vs ∧ s' = outOf st2 vs ∧ t = .normal := by
    intro s' t h
    cases h with | expr _ _ _ _ _ v he =>
    cases he with | call _ _ _ _ _ _ _ _ fv vs _ hv _ ha hc =>
    cases hv with | var _ _ _ _ _ hg =>
    rw [hget] at hg; cases hg
    exact ⟨_, vs, ha, huniq _ _ _ _ hc, rfl⟩
  rcases hB1 with ⟨vs, st'', hevs, hvs, hB1pc, hB1o, hout'', hB1c, hsp, hB1t, -⟩ | ⟨hh, hne⟩
  rotate_left
  · refine ⟨B1, r1, .inr ⟨hh, fun s' t h => ?_⟩⟩
    obtain ⟨st2, vs, ha, -, -⟩ := hderiv h
    exact hne _ _ ha
  have hvl := EvalArgs.length_eq hevs
  obtain ⟨ns, rfl, hns⟩ := vals_ints vs hvs
  simp only [List.length_map] at hB1t hvl
  rw [← hvl] at hs2 hpos hs3 hce
  simp only [List.length_append] at hpos
  have hs2' : Seg code (cargs C.Γ 0 pos args).2 (printLoop 0 (cargs C.Γ 0 pos args).2 ns.length) :=
    Seg.pos_eq hend.symm hs2
  have hpl := printLoop_length 0 (cargs C.Γ 0 pos args).2 (pos + (cargs C.Γ 0 pos args).1.length) ns.length
  obtain ⟨B2, r2, hB2pc, hB2o, hB2m⟩ := run_printLoop hAt.lay ns 0 _ B1
    (fun j hj => by simpa [word] using hB1t j hj) hns (by have := hvl; rw [hmax] at hlen; omega)
    hs2' (by unfold PosOK at *; have := hend; have := hpl; omega) hB1pc
  have hc2 : Chain st''.store B2.mem env C.Γ := hB1c.transport fun i hi => by
    unfold slotV
    rw [hB2m _ (.inr (by
      have := hAt.slot_bound i hi; unfold varAddr varBase bufBase; omega))]
  have hlen' : (ns.map Value.int).length = ns.length := by simp
  have hexec : ExecS st d env (.expr (.call (.var f) args)) (outOf st'' (ns.map Value.int)) .normal :=
    .expr _ _ _ _ _ .null (.call _ _ _ _ _ _ _ _ q _ .null (.var _ _ _ _ _ hget) hlen hevs (hcall _ _))
  have hfin : ∀ B, Star code A B → B.pc = pcOf (pos + ((cargs C.Γ 0 pos args).1 ++
        printLoop 0 (cargs C.Γ 0 pos args).2 ns.length ++
        (if f = "println" then putc '\n' else [])).length) →
      Chain st''.store B.mem env C.Γ →
      outStr B = st''.out ++ printArgs st''.store (ns.map Value.int) ++
        (if f = "println" then "\n" else "") →
      ∃ B, Star code A B ∧ StmtOK code C pos (.expr (.call (.var f) args)) st d env B := by
    intro B r hpc hc hob
    refine ⟨B, r, .inl ⟨_, .normal, hexec, fun s' t h => ?_, by rw [hce]; exact hpc,
      ⟨hc, hob⟩, hsp, by simp⟩⟩
    obtain ⟨st2, vs, ha, rfl, rfl⟩ := hderiv h
    obtain ⟨rfl, rfl⟩ := EvalArgs.det args (fun e he => IntE.simple (SupArgs.intE hargs e he)) ha hevs
    exact ⟨rfl, rfl⟩
  have hout2 : outStr B2 = st''.out ++ printArgs st''.store (ns.map Value.int) := by
    rw [hB2o, printArgs_ints, outStr, hB1o, hout'']; rw [← hsr.2]; rfl
  by_cases hp : f = "println"
  · have hs3' : Seg code ((cargs C.Γ 0 pos args).2 + (printLoop 0 (cargs C.Γ 0 pos args).2 ns.length).length)
        (putc '\n') := by
      rw [if_pos hp] at hs3; exact Seg.pos_eq (by simp only [List.length_append]; have := hend; have := hpl; omega) hs3
    obtain ⟨L3, r3⟩ := run_putc hAt.fits (by decide) hs3' hB2pc
    refine hfin _ (r1.trans (r2.trans r3)) ?_ hc2 ?_
    · congr 1; simp only [List.length_append, if_pos hp]; congr 1; have := hend; omega
    · rw [outStr_push, if_pos hp, hout2]; rfl
  · refine hfin B2 (r1.trans r2) ?_ hc2 ?_
    · rw [hB2pc]; congr 1; simp only [List.length_append, if_neg hp, List.length_nil]; have := hend; have := hpl; omega
    · rw [if_neg hp, hout2]; simp

end

end Vsa.Compiler
