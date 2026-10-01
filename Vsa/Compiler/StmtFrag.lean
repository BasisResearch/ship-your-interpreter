import Vsa.Compiler.StmtRel
import Vsa.Compiler.CompileFacts
import Vsa.Compiler.Fail

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure At (code : List Ins) (C : Ctx) (pos : Nat) : Prop where
  lay : Layout code
  ne : C.Γ ≠ []
  nd : C.Γ.slots.Nodup
  lt : ∀ i ∈ C.Γ.slots, i < C.next
  nat : ∀ f ∈ C.Γ, ∀ x, IsNative x → f.lookup x = none
  nextle : C.next ≤ pos
  posok : PosOK pos

theorem At.after {code : List Ins} {C : Ctx} {pos : Nat} (hAt : At code C pos) {p : Nat} (s : Stmt) (hp : pos ≤ p) {q : Nat}
    (hq : p + (cstmt C p s).1.length ≤ q) (hq' : PosOK q) : At code ⟨C.Γ, (cstmt C p s).2, C.brk, C.cont⟩ q :=
  have hn := cstmt_next C p s
  ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi) hn.1, hAt.nat,
    by show (cstmt C p s).2 ≤ q; have := hAt.nextle; omega, hq'⟩

def SR (Γ : Scope) (env : Addr) (st : St) (A : AM) : Prop :=
  Chain st.store A.mem env Γ ∧ outStr A = st.out

def exitPos (C : Ctx) (e : Nat) : Status → Nat
  | .normal => e
  | .brk => C.brk
  | .cont => C.cont
  | .ret _ => 0

theorem At.fits {code : List Ins} {C : Ctx} {pos : Nat} (h : At code C pos) : Fits code := h.lay.1

theorem At.slot_bound {code : List Ins} {C : Ctx} {pos : Nat} (h : At code C pos) :
    ∀ i ∈ C.Γ.slots, i < 2 ^ 24 := by
  intro i hi
  have h1 := h.lt i hi
  have h2 := h.nextle
  have h3 := h.posok
  unfold PosOK at h3
  have : tohostAddr = 0x8001ad00 := rfl
  have : codeBase = 0x80004800 := rfl
  omega

theorem Seg.end_ok {code : List Ins} {pos : Nat} {s : List Ins} (hfit : Fits code)
    (hs : Seg code pos s) (hne : s ≠ []) : PosOK (pos + s.length) := by
  have hl : pos + s.length ≤ code.length := by
    have := hs (s.length - 1) (by cases s <;> simp_all)
    have hget : s[s.length - 1]? ≠ none := by
      cases s with
      | nil => exact absurd rfl hne
      | cons a t => simp
    rw [← this] at hget
    rcases Nat.lt_or_ge (pos + (s.length - 1)) code.length with h | h
    · cases s with
      | nil => exact absurd rfl hne
      | cons a t => simp at h ⊢; omega
    · exact absurd (List.getElem?_eq_none h) hget
  unfold PosOK; unfold Fits at hfit; omega

section
variable {code : List Ins}

theorem run_cond₀ (hfit : Fits code) {q L : Nat} {A : AM} {w : BitVec 64}
    (hseg : Seg code q [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (q + 1) L)])
    (hA : A.pc = pcOf q) (hq : PosOK (q + 2)) (hL : PosOK L) (h0 : Has A.regs a0 w) :
    Star code A ⟨pcOf (if w = 0 then L else q + 2), A.regs, A.mem, A.out⟩ := by
  have hb : codeBase = 0x80004800 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hs := pcOf_skip q 1 (by unfold PosOK at *; omega) (by decide)
  have e1 := step_br hfit hseg.head hA h0 (Has.zero _)
    (by rw [hs, pcOf_toNat (by unfold PosOK at *; omega)]; omega)
  rw [hs] at e1
  by_cases hw : w = 0
  · subst hw
    have hg : guardB BrOp.ne.bop (0 : BitVec 64) 0 = false := by decide
    rw [hg] at e1
    simp only [Bool.false_eq_true, if_false] at e1
    rw [if_pos rfl]
    exact Star.step e1 (Star.single (step_jump hfit hseg.tail.head rfl (by unfold PosOK at *; omega) hL))
  · have hg : guardB BrOp.ne.bop w 0 = true := by simp only [BrOp.bop, guardB]; simpa using hw
    rw [hg, if_pos rfl] at e1
    rw [if_neg hw]
    exact Star.single e1

end

theorem word_truthy {Γn : NScope} {e : Expr} {v : Value} (he : CondE Γn e) (hv : ValTy Γn e v) :
    (word v = 0) ↔ v.truthy = false := by
  rcases he with hi | hb
  · obtain ⟨n, rfl, hn⟩ := hv.1 hi
    simp only [word, Value.truthy, bne_eq_false_iff_eq]
    constructor
    · intro h; have := congrArg BitVec.toInt h; rwa [toInt_ofInt_range hn] at this
    · intro h; subst h; decide
  · obtain ⟨b, rfl⟩ := hv.2 hb
    cases b <;> decide

theorem EvalArgs.det : ∀ (args : List Expr), (∀ e ∈ args, Simple e) →
    ∀ {st : St} {d : Nat} {env : Addr} {s1 s2 : St} {v1 v2 : List Value},
    EvalArgs st d env args s1 v1 → EvalArgs st d env args s2 v2 → s1 = s2 ∧ v1 = v2
  | [], _, _, _, _, _, _, _, _, h1, h2 => by cases h1; cases h2; exact ⟨rfl, rfl⟩
  | e :: es, hs, _, _, _, _, _, _, _, h1, h2 => by
    cases h1 with | cons _ _ _ _ _ _ _ _ _ he1 hr1 =>
    cases h2 with | cons _ _ _ _ _ _ _ _ _ he2 hr2 =>
    obtain ⟨rfl, rfl⟩ := EvalE.det e (hs e (List.mem_cons_self ..)) he1 he2
    obtain ⟨rfl, rfl⟩ := EvalArgs.det es (fun e' h => hs e' (List.mem_cons_of_mem _ h)) hr1 hr2
    exact ⟨rfl, rfl⟩

theorem SupArgs.intE {Γn : NScope} : ∀ {args : List Expr}, SupArgs Γn args → ∀ e ∈ args, IntE Γn e
  | [], _, _, h => by simp at h
  | e :: es, h, e', he' => by
    rcases List.mem_cons.mp he' with rfl | he'
    · exact h.1
    · exact SupArgs.intE h.2 e' he'

theorem PosOK.small {x : Nat} (h : PosOK x) : x ≤ 27456 := by
  unfold PosOK at h
  have : tohostAddr = 0x8001ad00 := rfl
  have : codeBase = 0x80004800 := rfl
  omega

section
variable {code : List Ins}

theorem sim_args (hL : Layout code) {Γ : Scope} (hnd : Γ.slots.Nodup)
    (hsl : ∀ i ∈ Γ.slots, i < 2 ^ 24) {d : Nat} {env : Addr} :
    ∀ (args : List Expr) (k pos : Nat) (st : St) (A : AM),
    SupArgs Γ.names args → k + args.length ≤ 64 → Seg code pos (cargs Γ k pos args).1 →
    PosOK (cargs Γ k pos args).2 → A.pc = pcOf pos → Chain st.store A.mem env Γ →
    ∃ B, Star code A B ∧
      ((∃ vs st'', EvalArgs st d env args st'' vs ∧ (∀ v ∈ vs, ∃ n, v = .int n ∧ InRange n) ∧
          B.pc = pcOf (cargs Γ k pos args).2 ∧ B.out = A.out ∧ st''.out = st.out ∧
          Chain st''.store B.mem env Γ ∧ SameParents st.store st''.store ∧
          (∀ j (hj : j < vs.length), rdW B.mem (tempAddr (k + j)) = word vs[j]) ∧
          (∀ j < k, rdW B.mem (tempAddr j) = rdW A.mem (tempAddr j))) ∨
        (astep code B = some (.halt 70) ∧ ∀ vs st'', ¬ EvalArgs st d env args st'' vs))
  | [], k, pos, st, A, _, _, _, _, hA, hc =>
    ⟨A, Star.refl _ _, .inl ⟨[], st, .nil _ _ _, by simp, by simp [cargs, hA], rfl, rfl, hc,
      .refl _, fun j hj => by simp at hj, fun _ _ => rfl⟩⟩
  | e :: es, k, pos, st, A, hs, hk, hseg, hpos, hA, hc => by
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
    obtain ⟨B1, r1, hB1⟩ := sim_expr hL hnd hsl e hsimple k pos st d env A (.inl hs.1)
      (by have := hend.small; simp only [List.length_append] at this; simp at hk; omega) hs1
      (by have := hend; unfold PosOK at *; simp only [List.length_append] at this; omega) hA hc
    rcases hB1 with ⟨v, st1, hev, hty, hout, hBo, hBpc, hB0, hBc, hBt⟩ | ⟨hh, hne⟩
    · obtain ⟨n, rfl, hn⟩ := hty.1 hs.1
      have r2 := run_stA hL.1 hs2 hBpc hB0 (by decide) (tempAddr_st (k := k) (by simp at hk; omega))
      have hc2 : Chain st1.store (applyW B1.mem (tempAddr k, 8, word (.int n))) env Γ :=
        hBc.transport fun i _ => slotV_write_low _ _ _ _ (tempAddr_low (k := k) (by simp at hk; omega))
      obtain ⟨B3, r3, hB3⟩ := sim_args hL hnd hsl es (k + 1) _ st1
        ⟨pcOf (pos + (cexpr Γ k pos e).length + (liN s2 (tempAddr k)).length + 1),
          gset B1.regs s2 (BitVec.ofNat 64 (tempAddr k)),
          applyW B1.mem (tempAddr k, 8, word (.int n)), B1.out⟩ hs.2 (by simp at hk; omega)
        (by simpa using hs3) hpos (by simp only; congr 1; simp; omega) hc2
      rcases hB3 with ⟨vs, st'', hevs, hvs, hB3pc, hB3o, hout3, hB3c, hsp, hB3t, hB3l⟩ | ⟨hh, hne⟩
      · refine ⟨B3, r1.trans (r2.trans r3), .inl ⟨.int n :: vs, st'', .cons _ _ _ _ _ _ _ _ _ hev hevs,
          ?_, hB3pc, by rw [hB3o]; exact hBo, hout3.trans hout, hB3c,
          (EvalE.sameParents e hsimple hev).trans hsp, ?_, ?_⟩⟩
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
      · refine ⟨B3, r1.trans (r2.trans r3), .inr ⟨hh, fun vs' st3 h => ?_⟩⟩
        cases h with | cons _ _ _ _ _ _ _ _ _ he hr =>
        obtain ⟨rfl, rfl⟩ := EvalE.det e hsimple he hev
        exact hne _ _ hr
    · refine ⟨B1, r1, .inr ⟨hh, fun vs st'' h => ?_⟩⟩
      cases h with | cons _ _ _ _ _ _ _ _ _ he _ => exact hne _ _ he

theorem intercalate_cons (a : String) (l : List String) :
    String.intercalate " " (a :: l) = a ++ (if l = [] then "" else " " ++ String.intercalate " " l) := by
  cases l with
  | nil => simp
  | cons b l => simp [String.intercalate_cons_cons, String.append_assoc]

theorem printLoop_length (k p p' : Nat) : ∀ n, (printLoop k p n).length = (printLoop k p' n).length := by
  intro n
  induction n generalizing k p p' with
  | zero => rfl
  | succ n ih =>
    simp only [printLoop, List.length_append, List.length_cons, List.length_nil]
    congr 1
    exact ih _ _ _

theorem printPos_ok : PosOK printPos := by decide

theorem printPos_toNat : (pcOf printPos).toNat = codeBase + 4 * printPos := pcOf_toNat (by decide)

theorem run_printLoop₀ (hL : Layout code) : ∀ (ns : List Int) (k pos : Nat) (A : AM),
    (∀ j (hj : j < ns.length), rdW A.mem (tempAddr (k + j)) = BitVec.ofInt 64 ns[j]) →
    (∀ x ∈ ns, InRange x) → k + ns.length ≤ 64 → Seg code pos (printLoop k pos ns.length) →
    PosOK (pos + (printLoop k pos ns.length).length) → A.pc = pcOf pos →
    ∃ B, Star code A B ∧ B.pc = pcOf (pos + (printLoop k pos ns.length).length) ∧
      outStr B = outStr A ++ String.intercalate " " (ns.map intToString) ∧
      ∀ a, (a + 8 ≤ bufBase ∨ bufBase + 8 * 20 ≤ a) → rdW B.mem a = rdW A.mem a
  | [], k, pos, A, _, _, _, _, _, hA =>
    ⟨A, Star.refl _ _, by simp [printLoop, hA], by simp [String.intercalate], fun _ _ => rfl⟩
  | x :: xs, k, pos, A, hv, hr, hk, hseg, hpos, hA => by
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
    generalize hqd : pos + (liN s2 (tempAddr k)).length + 1 = q at hs2 hs3 hs4 p4 hq
    generalize hsp : (if xs.length = 0 then [] else putc ' ') = sep at hs3 hs4 p4
    have hq0 : q = pos + ((liN s2 (tempAddr k)).length + 1) := by omega
    simp only [List.length_cons] at hk

    have r1 := run_ldA hL.1 hs1 hA (by decide) (tempAddr_ld (k := k) (by omega))
    have hx : rdW A.mem (tempAddr k) = BitVec.ofInt 64 x := by
      have := hv 0 (by simp); rw [List.getElem_cons_zero, Nat.add_zero] at this; exact this
    rw [hx, show pos + (liN s2 (tempAddr k)).length + 1 = q by omega] at r1

    have hj := pcOf_jump q printPos (by unfold PosOK at *; omega) printPos_ok
    have e2 := step_call hL.1 hs2.head
      (A := ⟨pcOf q, gset (gset A.regs s2
      (BitVec.ofNat 64 (tempAddr k))) a0 (BitVec.ofInt 64 x), A.mem, A.out⟩) rfl
      (by rw [hj, printPos_toNat]; decide)
      (by rw [hj, printPos_toNat]; decide)
    rw [hj] at e2
    obtain ⟨B2, r2, hB2pc, hB2o, hB2m⟩ := run_print hL.1 hL.2.2 (k := q + 1)
      (A := ⟨pcOf printPos, gset (gset (gset A.regs s2 (BitVec.ofNat 64 (tempAddr k))) a0
        (BitVec.ofInt 64 x)) 1 (pcOf (q + 1)), A.mem, A.out⟩) rfl
      ((Has.set_self (rd := a0) _ _ (by decide) (by decide)).set_other (rd := ra) (by decide))
      (Has.set_self (rd := ra) _ _ (by decide) (by decide)) rfl hq
    rw [toInt_ofInt_range (hr x (List.mem_cons_self ..))] at hB2o
    have hB2o' : outStr B2 = outStr A ++ intToString x := hB2o
    have run12 : Star code A B2 := r1.trans (Star.step e2 r2)
    have htemp : ∀ j, rdW B2.mem (tempAddr j) = rdW A.mem (tempAddr j) := fun j =>
      hB2m _ (.inr (by unfold tempAddr tempBase bufBase; omega))
    by_cases hxs : xs = []
    · subst hxs
      have hsep : sep = [] := by rw [← hsp]; rfl
      subst hsep
      refine ⟨B2, run12, ?_, ?_, hB2m⟩
      · rw [hB2pc]; congr 1; simp [printLoop]; omega
      · rw [hB2o']; simp only [List.map_cons, List.map_nil]; rw [intercalate_cons]; simp
    · have hsep : sep = putc ' ' := by
        rw [← hsp, if_neg (by simpa using hxs)]
      subst hsep
      obtain ⟨L3, r3⟩ := run_putc hL.1 (by decide) hs3 hB2pc
      have hv' : ∀ j (hj : j < xs.length), rdW B2.mem (tempAddr (k + 1 + j)) = BitVec.ofInt 64 xs[j] := by
        intro j hj
        rw [htemp, show k + 1 + j = k + (j + 1) by omega, hv (j + 1) (by simp; omega)]
        simp
      obtain ⟨B4, r4, hB4pc, hB4o, hB4m⟩ := run_printLoop₀ hL xs (k + 1) (q + 1 + (putc ' ').length)
        ⟨pcOf (q + 1 + (putc ' ').length), L3, B2.mem, B2.out.push (toString ' ')⟩ hv'
        (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (by omega) hs4 p4 rfl
      refine ⟨B4, run12.trans (r3.trans r4), ?_, ?_, ?_⟩
      · rw [hB4pc]; congr 1
        rw [hpl, hsp]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have := printLoop_length (k + 1) (pos + ((liN s2 (tempAddr k)).length + (0 + 1)) + 1 +
          (putc ' ').length) (q + 1 + (putc ' ').length) xs.length
        omega
      · rw [hB4o, outStr_push, hB2o']
        simp only [List.map_cons]
        rw [intercalate_cons, if_neg (by simpa using hxs)]
        simp [String.append_assoc]
      · intro a ha; rw [hB4m a ha, hB2m a ha]

end

end Vsa.Compiler
