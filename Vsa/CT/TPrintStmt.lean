import Vsa.CT.TStmt

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

def PrintSpec : Prop :=
  ∀ n : BitVec 64, ∃ τ : List Obs, ∀ {code : List Ins} {k : Nat} {A : AM} {r : BitVec 64},
    Fits code → Seg code printPos printCode → A.pc = pcOf printPos → Has A.regs a0 n →
    Has A.regs ra r → r = pcOf k → PosOK k →
    ReachesT code A τ fun B => B.pc = r ∧ outStr B = outStr A ++ intToString n.toInt ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a

def argsTr (Γ : Scope) : Nat → Nat → List Expr → List EL → List Obs
  | k, pos, e :: es, l :: ls =>
    etr Γ k pos e l ++ stTr (pos + (cexpr Γ k pos e).length) (tempAddr k) ++
      argsTr Γ (k + 1) (pos + (cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length) es ls
  | _, _, _, _ => []

section
variable {code : List Ins}

theorem sim_argsT (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {d : Nat} {env : Addr} :
    ∀ (args : List Expr) (k pos : Nat) (st st'' : St) (vs : List Value) (ls : List EL) (A : AM),
    SupArgs Γ.names args → k + args.length ≤ 64 → Seg code pos (cargs Γ k pos args).1 →
    PosOK (cargs Γ k pos args).2 → A.pc = pcOf pos → Chain st.store A.mem env Γ →
    EvalArgsL st d env args st'' vs ls →
    ∃ B, StarT code (argsTr Γ k pos args ls) A B ∧
      (∀ v ∈ vs, ∃ n, v = .int n ∧ InRange n) ∧
      B.pc = pcOf (cargs Γ k pos args).2 ∧ B.out = A.out ∧ st''.out = st.out ∧
      Chain st''.store B.mem env Γ ∧ SameParents st.store st''.store ∧
      (∀ j (hj : j < vs.length), rdW B.mem (tempAddr (k + j)) = word vs[j]) ∧
      (∀ j < k, rdW B.mem (tempAddr j) = rdW A.mem (tempAddr j)) ∧ EvalArgs st d env args st'' vs
  | [], k, pos, st, st'', vs, ls, A, _, _, _, _, hA, hc, h => by
    cases h
    exact ⟨A, .refl _, by simp, by simp [cargs, hA], rfl, rfl, hc, .refl _, fun j hj => by simp at hj,
      fun _ _ => rfl, .nil _ _ _⟩
  | e :: es, k, pos, st, st'', vs, ls, A, hs, hk, hseg, hpos, hA, hc, h => by
    cases h with
    | cons _ _ _ _ _ st1 _ v vs' l ls' he hes =>
    have hce : cargs Γ k pos (e :: es) = ((cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]) ++
        (cargs Γ (k + 1) (pos + (cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length) es).1,
        (cargs Γ (k + 1) (pos + (cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length) es).2) := rfl
    rw [hce] at hseg hpos
    obtain ⟨hs12, hs3⟩ := hseg.append
    have hend := Seg.end_ok hL.1 hs12 (by simp)
    rw [List.append_assoc] at hs12
    obtain ⟨hs1, hs2⟩ := hs12.append
    have hsimple := IntE.simple hs.1
    have htd := tdepth_le Γ e k pos hsimple
    obtain ⟨B1, r1, hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ := simT_expr hL hnd hsl e hsimple k pos st d
      env A st1 v l (.inl hs.1)
      (by have := hend.small; simp only [List.length_append] at this; simp at hk; omega) hs1
      (by have := hend; unfold PosOK at *; simp only [List.length_append] at this; omega) hA hc he
    obtain ⟨n, rfl, hn⟩ := hty.1 hs.1
    have r2 := run_stAT hL.1 hs2 hBpc hB0 (by decide) (tempAddr_st (k := k) (by simp at hk; omega))
    have hc2 : Chain st1.store (applyW B1.mem (tempAddr k, 8, word (.int n))) env Γ :=
      hBc.transport fun i _ => slotV_write_low _ _ _ _ (tempAddr_low (k := k) (by simp at hk; omega))
    obtain ⟨B3, r3, hvs, hB3pc, hB3o, hout3, hB3c, hsp, hB3t, hB3l, hevs⟩ := sim_argsT hL hnd hsl es (k + 1) _
      st1 st'' vs' ls'
      ⟨pcOf (pos + (cexpr Γ k pos e).length + (liN s2 (tempAddr k)).length + 1),
        gset B1.regs s2 (BitVec.ofNat 64 (tempAddr k)),
        applyW B1.mem (tempAddr k, 8, word (.int n)), B1.out⟩ hs.2 (by simp at hk; omega)
      (by simpa using hs3) hpos (by simp only; congr 1; simp; omega) hc2 hes
    refine ⟨B3, by simpa [argsTr, List.append_assoc] using r1.trans (r2.trans r3), ?_, hB3pc,
      by rw [hB3o]; exact hBo, hout3.trans hout, hB3c,
      (EvalE.sameParents e hsimple hev).trans hsp, ?_, ?_, .cons _ _ _ _ _ _ _ _ _ hev hevs⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨n, rfl, hn⟩
      · exact hvs v hv
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hB3l k (by omega)]; exact rdW_write _ _ _
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show k + (j + 1) = k + 1 + j by omega]
        exact hB3t j (by simpa using hj)
    · intro j hj
      rw [hB3l j (by omega), rdW_write_other _ _ _ _ (by unfold tempAddr; omega), hBt j hj]

theorem run_printLoopT (hP : PrintSpec) : ∀ (ns : List Int) (k pos : Nat), ∃ τ : List Obs,
    ∀ {code : List Ins} {A : AM}, Layout code →
    (∀ j (hj : j < ns.length), rdW A.mem (tempAddr (k + j)) = BitVec.ofInt 64 ns[j]) →
    (∀ x ∈ ns, InRange x) → k + ns.length ≤ 64 → Seg code pos (printLoop k pos ns.length) →
    PosOK (pos + (printLoop k pos ns.length).length) → A.pc = pcOf pos →
    ReachesT code A τ fun B => B.pc = pcOf (pos + (printLoop k pos ns.length).length) ∧
      outStr B = outStr A ++ String.intercalate " " (ns.map intToString) ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a
  | [], k, pos => ⟨[], fun {code} {A} _ _ _ _ _ _ hA => ⟨_, .refl _, by simp [printLoop, hA],
      by simp [String.intercalate], fun _ _ => rfl⟩⟩
  | x :: xs, k, pos => by
    obtain ⟨τp, hτp⟩ := hP (BitVec.ofInt 64 x)
    let q := pos + (liN s2 (tempAddr k)).length + 1
    let sep : List Ins := if xs.length = 0 then [] else putc ' '
    obtain ⟨τr, hτr⟩ := run_printLoopT hP xs (k + 1) (q + 1 + sep.length)
    refine ⟨ldTr pos (tempAddr k) ++ [pobs q] ++ τp ++
        (if xs.length = 0 then [] else putcTr (q + 1) (BitVec.ofNat 8 ' '.toNat)) ++ τr,
      fun {code} {A} hL hv hr hk hseg hpos hA => ?_⟩
    have hb : codeBase = 0x80004800 := rfl
    have ht : tohostAddr = 0x8001ad00 := rfl
    have hpl : printLoop k pos (x :: xs).length = (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]) ++
        [Ins.jal ra (jOff (pos + (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]).length) printPos)] ++
        (if xs.length = 0 then [] else putc ' ') ++
        printLoop (k + 1) (pos + (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]).length + 1 +
          (if xs.length = 0 then [] else putc ' ').length) xs.length := rfl
    rw [hpl] at hseg hpos
    obtain ⟨h123, hs4, p4⟩ := segP_app.mp ⟨hseg, hpos⟩
    obtain ⟨h12, hs3, -⟩ := segP_app.mp h123
    obtain ⟨⟨hs1, -⟩, hs2, hq⟩ := segP_app.mp h12
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc] at hs2 hs3 hs4 p4 hq
    have hqd : pos + (liN s2 (tempAddr k)).length + 1 = q := rfl
    rw [hqd] at hs2 hs3 hs4 p4 hq
    simp only [List.length_cons] at hk
    have r1 := run_ldAT hL.1 hs1 hA (by decide) (tempAddr_ld (k := k) (by omega))
    have hx : rdW A.mem (tempAddr k) = BitVec.ofInt 64 x := by
      have := hv 0 (by simp); rw [List.getElem_cons_zero, Nat.add_zero] at this; exact this
    rw [hx, hqd] at r1
    have hj := pcOf_jump q printPos (by unfold PosOK at *; omega) printPos_ok
    have e2 := step_call hL.1 hs2.head
      (A := ⟨pcOf q, gset (gset A.regs s2
      (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 x), A.mem, A.out⟩) rfl
      (by rw [hj, printPos_toNat]; decide)
      (by rw [hj, printPos_toNat]; decide)
    rw [hj] at e2
    have s2' := stepM hL.1 hs2.head rfl e2 (.refl _)
    have hnl : ¬ (ra = 1 ∧ isLibT (pcOf q + (sign_extend (evenJ (jOff q printPos)) : BitVec 64)).toNat) := by
      rw [hj, printPos_toNat]
      have hcb : codeBase = 0x80004800 := rfl
      intro ⟨_, h⟩
      unfold isLibT mulPC divPC modPC at h
      omega
    simp only [insObs, hnl, if_false] at s2'
    obtain ⟨B2, r2, hB2pc, hB2o, hB2m⟩ := hτp (code := code) (k := q + 1)
      (A := ⟨pcOf printPos, gset (gset (gset A.regs s2 (BitVec.ofNat 64 (tempAddr k))) a0
        (BitVec.ofInt 64 x)) 1 (pcOf (q + 1)), A.mem, A.out⟩) hL.1 hL.2.2 rfl
      ((Has.set_self (rd := a0) _ _ (by decide) (by decide)).set_other (rd := ra) (by decide))
      (Has.set_self (rd := ra) _ _ (by decide) (by decide)) rfl hq
    rw [toInt_ofInt_range (hr x (List.mem_cons_self ..))] at hB2o
    have hB2o' : outStr B2 = outStr A ++ intToString x := hB2o
    have run12 : StarT code (ldTr pos (tempAddr k) ++ [pobs q] ++ τp) A B2 := by
      have := r1.trans (s2'.trans r2)
      simpa [pobs, List.append_assoc] using this
    have htemp : ∀ j, rdW B2.mem (tempAddr j) = rdW A.mem (tempAddr j) := fun j =>
      hB2m _ (.inr (by unfold tempAddr tempBase bufBase; omega))
    by_cases hxs : xs = []
    · subst hxs
      have hsep0 : sep.length = 0 := by simp [sep]
      rw [hsep0, Nat.add_zero] at hτr
      obtain ⟨B4, r4, hB4pc, hB4o, hB4m⟩ := hτr (code := code) (A := B2) hL (by simp) (by simp)
        (by simp; omega) (by simpa using hs4) (by simpa using p4) hB2pc
      refine ⟨B4, by simpa using run12.trans r4, ?_, ?_, ?_⟩
      · rw [hB4pc]; congr 1; simp [printLoop, sep]; omega
      · rw [hB4o, hB2o']; simp only [List.map_cons, List.map_nil]; rw [intercalate_cons]; simp
      · intro a ha; rw [hB4m a ha, hB2m a ha]
    · have hsep : sep = putc ' ' := by simp [sep, hxs]
      have hsep' : (if xs.length = 0 then ([] : List Ins) else putc ' ') = putc ' ' := by
        simp [hxs]
      rw [hsep'] at hs3 hs4 p4
      obtain ⟨L3, r3⟩ := run_putcT hL.1 (by decide) hs3 hB2pc
      have hv' : ∀ j (hj : j < xs.length), rdW B2.mem (tempAddr (k + 1 + j)) = BitVec.ofInt 64 xs[j] := by
        intro j hj
        rw [htemp, show k + 1 + j = k + (j + 1) by omega, hv (j + 1) (by simp; omega)]
        simp
      obtain ⟨B4, r4, hB4pc, hB4o, hB4m⟩ := hτr (code := code)
        (A := ⟨pcOf (q + 1 + (putc ' ').length), L3, B2.mem, B2.out.push (toString ' ')⟩) hL hv'
        (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (by omega) (by rw [hsep]; exact hs4)
        (by rw [hsep]; exact p4) (by rw [hsep])
      have hif : (if xs.length = 0 then [] else putcTr (q + 1) (BitVec.ofNat 8 ' '.toNat)) =
          putcTr (q + 1) (BitVec.ofNat 8 ' '.toNat) := by simp [hxs]
      rw [hif]
      refine ⟨B4, by simpa [List.append_assoc] using run12.trans (r3.trans r4), ?_, ?_, ?_⟩
      · rw [hB4pc]; congr 1
        rw [hpl]
        simp only [List.length_append, List.length_cons, List.length_nil, hsep']
        have h1 := printLoop_length (k + 1) (pos + ((liN s2 (tempAddr k)).length + (0 + 1)) + 1 +
          (putc ' ').length) (q + 1 + sep.length) xs.length
        have h2 : sep.length = (putc ' ').length := by rw [hsep]
        simp only [q] at h1 ⊢
        omega
      · rw [hB4o, outStr_push, hB2o']
        simp only [List.map_cons]
        rw [intercalate_cons, if_neg (by simpa using hxs)]
        simp [String.append_assoc]
      · intro a ha; rw [hB4m a ha, hB2m a ha]

def _root_.Vsa.CT.CL.vals : CL → List Value
  | .print vs => vs
  | .println vs => vs
  | _ => []

def toI : Value → Int
  | .int n => n
  | _ => 0

theorem ints_toI : ∀ (vs : List Value), (∀ v ∈ vs, ∃ n, v = .int n ∧ InRange n) →
    vs = (vs.map toI).map Value.int ∧ ∀ x ∈ vs.map toI, InRange x
  | [], _ => ⟨rfl, by simp⟩
  | v :: vs, h => by
    obtain ⟨n, rfl, hn⟩ := h v (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ints_toI vs (fun w hw => h w (List.mem_cons_of_mem _ hw))
    refine ⟨by simp only [List.map_cons, toI]; rw [← h1], ?_⟩
    intro x hx
    simp only [List.map_cons, toI, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hn
    · exact h2 x hx

theorem tPrintT (hP : PrintSpec) {C : Ctx} {pos : Nat} {f : String} {args : List Expr} {la : List EL}
    {cl : CL} : STr C pos (.expr (.call (.var f) args)) (.expr (.call .leaf la cl)) := by
  let ns := cl.vals.map toI
  obtain ⟨τl, hτl⟩ := run_printLoopT hP ns 0 (cargs C.Γ 0 pos args).2
  let p3 := (cargs C.Γ 0 pos args).2 + (printLoop 0 (cargs C.Γ 0 pos args).2 args.length).length
  refine ⟨argsTr C.Γ 0 pos args la ++ τl ++
      (if f = "println" then putcTr p3 (BitVec.ofNat 8 '\n'.toNat) else []),
    fun code st d env st'' t loop A D hAt hs hseg hpos hloop hA hsr => ?_⟩
  have hs' : SupS C.Γ.names false (.expr (.call (.var f) args)) := hs
  obtain ⟨hf, hlen, hargs⟩ := hs'
  have hce : cstmt C pos (.expr (.call (.var f) args)) =
      ((cargs C.Γ 0 pos args).1 ++ printLoop 0 (cargs C.Γ 0 pos args).2 args.length ++
        (if f = "println" then putc '\n' else []), C.next) := rfl
  rw [hce] at hseg hpos ⊢
  dsimp only at hseg hpos ⊢
  obtain ⟨⟨hs12, p12⟩, hs3, -⟩ := segP_app.mp ⟨hseg, hpos⟩
  obtain ⟨⟨hs1, p1⟩, hs2, p2⟩ := segP_app.mp ⟨hs12, p12⟩
  have hmax : maxArgs = 32 := rfl
  obtain ⟨q, hq, hqv⟩ := native_entry f hf
  have hget : st.store.get? env f = some q :=
    hsr.1.native _ hsr.1.env_lt (fun fr hfr => hAt.nat fr hfr f (by rcases hf with h | h <;> simp [IsNative, h])) hq
  have hend : (cargs C.Γ 0 pos args).2 = pos + (cargs C.Γ 0 pos args).1.length := cargs_end _ _ _ _
  cases D with
  | expr _ _ _ _ _ v _ he =>
  cases he with
  | call _ _ _ _ _ st1 st2 _ fv vs _ _ _ _ hfv _ hargsL hcall =>
  cases hfv with
  | var _ _ _ _ _ hg =>
  rw [hget] at hg; cases hg
  obtain ⟨B1, r1, hvs, hB1pc, hB1o, hout'', hB1c, hsp, hB1t, -, hevs⟩ := sim_argsT (d := d) (env := env)
    hAt.lay hAt.nd hAt.slot_bound args 0 pos st st2 vs la A hargs (by omega) hs1 (by rw [hend]; exact p1)
    hA hsr.1 hargsL
  have hcv : cl.vals = vs ∧ st'' = ⟨st2.store, st2.out ++ printArgs st2.store vs ++
      (if f = "println" then "\n" else "")⟩ := by
    by_cases hp : f = "println"
    · rw [hqv, if_pos hp] at hcall; cases hcall; simp [CL.vals, hp]
    · rw [hqv, if_neg hp] at hcall; cases hcall; simp [CL.vals, hp]
  obtain ⟨hcv, rfl⟩ := hcv
  have hvl := EvalArgs.length_eq hevs
  obtain ⟨hvs', hns⟩ := ints_toI vs hvs
  have hnsv : ns = vs.map toI := by simp only [ns, hcv]
  rw [← hnsv] at hvs' hns
  have hnl : ns.length = args.length := by rw [hnsv, List.length_map, hvl]
  have hs2' : Seg code (cargs C.Γ 0 pos args).2 (printLoop 0 (cargs C.Γ 0 pos args).2 ns.length) := by
    rw [hnl]; exact Seg.pos_eq hend.symm hs2
  have hpl := printLoop_length 0 (cargs C.Γ 0 pos args).2 (pos + (cargs C.Γ 0 pos args).1.length) ns.length
  obtain ⟨B2, r2, hB2pc, hB2o, hB2m⟩ := hτl hAt.lay
    (fun j hj => by
      have := hB1t j (by rw [← hnl] at *; simpa [hnsv] using hj)
      rw [this]; simp only [hnsv, List.getElem_map]
      obtain ⟨n, hn, -⟩ := hvs vs[j] (List.getElem_mem _)
      rw [hn]; rfl)
    hns (by rw [hnl]; rw [hmax] at hlen; omega) hs2' (by rw [hnl]; rwa [hend] at p2 ⊢) hB1pc
  have hc2 : Chain st2.store B2.mem env C.Γ := hB1c.transport fun i hi => by
    unfold slotV
    rw [hB2m _ (.inr (by
      have := hAt.slot_bound i hi; unfold varAddr varBase bufBase; omega))]
  have hout2 : outStr B2 = st2.out ++ printArgs st2.store vs := by
    rw [hB2o, hvs', printArgs_ints, outStr, hB1o, hout'']; rw [← hsr.2]; rfl
  have hsp' : SameParents st.store st2.store := hsp
  have hpc_eq : (cargs C.Γ 0 pos args).2 + (printLoop 0 (cargs C.Γ 0 pos args).2 ns.length).length =
      pos + ((cargs C.Γ 0 pos args).1.length + (printLoop 0 (cargs C.Γ 0 pos args).2 args.length).length) := by
    rw [hnl]; omega
  by_cases hp : f = "println"
  · have hs3' : Seg code p3 (putc '\n') := by
      rw [if_pos hp] at hs3
      exact Seg.pos_eq (by simp only [p3, List.length_append]; have := hend; omega) hs3
    obtain ⟨L3, r3⟩ := run_putcT hAt.fits (by decide) hs3' (by rw [hB2pc, hnl])
    simp only [hp, ite_true]
    refine ⟨_, (r1.trans r2).trans r3, ?_, ⟨?_, ?_⟩, hsp', by simp, fun _ => rfl⟩
    · simp only [exitPos, p3, List.length_append, if_pos hp]; congr 1; omega
    · exact hc2.transport fun i hi => rfl
    · rw [outStr_push, hout2]; rfl
  · simp only [hp, ite_false, List.append_nil]
    refine ⟨B2, r1.trans r2, ?_, ⟨hc2, ?_⟩, hsp', by simp, fun _ => rfl⟩
    · rw [hB2pc]; simp only [exitPos, if_neg hp, List.length_append, List.length_nil]
      rw [hnl]; congr 1; omega
    · simp [hout2]

theorem STr_vac {C : Ctx} {pos : Nat} {s : Stmt} {ℓ : SL}
    (h : ∀ st d env st' t loop, ExecL st d env s st' t ℓ → SupS C.Γ.names loop s → False) :
    STr C pos s ℓ :=
  ⟨[], fun _ _ _ _ _ _ _ _ D _ hs _ _ _ _ _ => (h _ _ _ _ _ _ D hs).elim⟩

theorem QTr_vac {C : Ctx} {pos : Nat} {ss : List Stmt} {ℓ : List SL}
    (h : ∀ st d env st' t loop, ExecSeqL st d env ss st' t ℓ → SupSeq C.Γ.names loop ss → False) :
    QTr C pos ss ℓ :=
  ⟨[], fun _ _ _ _ _ _ _ _ _ _ D _ _ hs _ _ _ _ _ => (h _ _ _ _ _ _ D hs).elim⟩

theorem noLeaf {st : St} {d : Nat} {env : Addr} {fn : String} {args : List Expr} {st' : St} {t : Status}
    {lf : EL} {la : List EL} {cl : CL}
    (D : ExecL st d env (.expr (.call (.var fn) args)) st' t (.expr (.call lf la cl))) (h : lf ≠ .leaf) :
    False := by
  cases D with
  | expr _ _ _ _ _ _ _ he =>
    cases he with
    | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf => cases hf; exact h rfl

theorem noCall {st : St} {d : Nat} {env : Addr} {fn : String} {args : List Expr} {st' : St} {t : Status}
    {l : EL} (D : ExecL st d env (.expr (.call (.var fn) args)) st' t (.expr l))
    (h : ∀ lf la cl, l ≠ .call lf la cl) : False := by
  cases D with
  | expr _ _ _ _ _ _ _ he =>
    cases he with
    | call => exact h _ _ _ rfl

theorem noDecl {st : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {ss : List Stmt} {st' : St}
    {t : Status} {l : SL} {ls : List SL}
    (D : ExecSeqL st d env (.varDecl x (some e) :: ss) st' t (l :: ls)) (h : ∀ le, l ≠ .varInit le) :
    False := by
  cases D with
  | consNormal _ _ _ _ _ _ _ _ _ _ h1 _ => cases h1; exact h _ rfl
  | consAbrupt _ _ _ _ _ _ _ _ h1 _ => cases h1; exact h _ rfl

end

mutual

theorem stmtTr (hP : PrintSpec) : ∀ (ℓ : SL) (C : Ctx) (pos : Nat) (s : Stmt), STr C pos s ℓ
  | .expr l, C, pos, s => by
    cases s with
    | expr e =>
      by_cases hcall : ∃ f args, e = .call f args
      · obtain ⟨f, args, rfl⟩ := hcall
        cases f with
        | var fn =>
          cases l with
          | call lf la cl =>
            cases lf with
            | leaf => exact tPrintT hP
            | _ => exact STr_vac fun _ _ _ _ _ _ D _ => noLeaf D (by simp)
          | _ => exact STr_vac fun _ _ _ _ _ _ D _ => noCall D (by simp)
        | _ => exact STr_vac fun _ _ _ _ _ _ _ hs => by simp [SupS, CondE, IntE, BoolE] at hs
      · exact tExprT (fun f args h => hcall ⟨f, args, h⟩)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .varInit l, C, pos, s => STr_vac fun _ _ _ _ _ _ D hs => by
      cases D; exact hs.elim
  | .varNull, C, pos, s => STr_vac fun _ _ _ _ _ _ D hs => by
      cases D; exact hs.elim
  | .block ls, C, pos, s => by
    cases s with
    | block ss => exact tBlockT (seqTr hP ls _ pos ss)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .ifT lc lt, C, pos, s => by
    cases s with
    | ifStmt c th el =>
      cases el with
      | none => exact tIfTNoneT (stmtTr hP lt _ _ th)
      | some el => exact tIfTSomeT (stmtTr hP lt _ _ th)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .ifF lc le, C, pos, s => by
    cases s with
    | ifStmt c th el =>
      cases el with
      | none => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
      | some el => exact tIfFT (stmtTr hP le _ _ el)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .ifN lc, C, pos, s => by
    cases s with
    | ifStmt c th el =>
      cases el with
      | none => exact tIfNT
      | some el => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .whileF lc, C, pos, s => by
    cases s with
    | whileStmt c b => exact tWhileFT
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .whileBrk lc lb, C, pos, s => by
    cases s with
    | whileStmt c b => exact tWhileBrkT (stmtTr hP lb _ _ b)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .whileRet lc lb, C, pos, s => by
    cases s with
    | whileStmt c b => exact tWhileRetT (stmtTr hP lb _ _ b)
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .whileLoop lc lb lr, C, pos, s => by
    cases s with
    | whileStmt c b => exact tWhileLoopT (stmtTr hP lb _ _ b) (stmtTr hP lr C pos (.whileStmt c b))
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .forS _ _, C, pos, s => STr_vac fun _ _ _ _ _ _ D hs => by cases D; exact hs.elim
  | .ret _, C, pos, s => STr_vac fun _ _ _ _ _ _ D hs => by cases D; exact hs.elim
  | .retNull, C, pos, s => STr_vac fun _ _ _ _ _ _ D hs => by cases D; exact hs.elim
  | .brk, C, pos, s => by
    cases s with
    | brk => exact tBrkT
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D
  | .cont, C, pos, s => by
    cases s with
    | cont => exact tContT
    | _ => exact STr_vac fun _ _ _ _ _ _ D _ => by cases D

theorem seqTr (hP : PrintSpec) : ∀ (ℓ : List SL) (C : Ctx) (pos : Nat) (ss : List Stmt), QTr C pos ss ℓ
  | [], C, pos, ss => by
    cases ss with
    | nil => exact sNilT
    | cons s ss => exact QTr_vac fun _ _ _ _ _ _ D _ => by cases D
  | l :: ls, C, pos, ss => by
    cases ss with
    | nil => exact QTr_vac fun _ _ _ _ _ _ D _ => by cases D
    | cons s ss =>
      by_cases hd : ∃ x e, s = .varDecl x (some e)
      · obtain ⟨x, e, rfl⟩ := hd
        cases l with
        | varInit le => exact sConsDeclT (seqTr hP ls _ _ ss)
        | _ => exact QTr_vac fun _ _ _ _ _ _ D _ => noDecl D (by simp)
      · exact sConsStmtT (fun x e h => hd ⟨x, e, h⟩) (stmtTr hP l C pos s) (seqTr hP ls _ _ ss)

end

end Vsa.Compiler
