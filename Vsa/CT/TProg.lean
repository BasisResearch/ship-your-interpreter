import Vsa.CT.TPrintStmt
import Vsa.CT.TPrint
import Vsa.CT.Prog
import Vsa.Compiler.Correct

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem printSpec : PrintSpec := fun n => run_printT n

def QTrW (τ : List Obs) (C : Ctx) (pos : Nat) (ss : List Stmt) (ℓ : List SL) : Prop :=
  ∀ (code : List Ins) (st : St) (d : Nat) (env : Addr) (st' : St) (t : Status)
    (loop : Bool) (A : AM) (f : List (String × Nat)) (g : Scope), ExecSeqL st d env ss st' t ℓ →
    C.Γ = f :: g → At code C pos → SupSeq C.Γ.names loop ss →
    Seg code pos (cseq C pos ss).1 → PosOK (pos + (cseq C pos ss).1.length) →
    (loop = true → PosOK C.brk ∧ PosOK C.cont) → A.pc = pcOf pos → SR C.Γ env st A →
    ReachesT code A τ (QPost C pos ss g st env st' t loop)

theorem sConsDeclW {C : Ctx} {pos : Nat} {x : String} {e : Expr} {ss : List Stmt} {l : EL} {ls : List SL}
    {τ : List Obs}
    (hτ : QTrW τ ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩ (pos + (declCode C pos x e).length)
      ss ls) :
    QTrW (etr C.Γ 0 pos e l ++ stTr (pos + (cexpr C.Γ 0 pos e).length) (varAddr (declInfo C x).2.1) ++ τ)
      C pos (.varDecl x (some e) :: ss) (.varInit l :: ls) := by
  intro code st d env st'' t loop A f g D hΓ hAt hs hseg hpos hloop hA hsr
  obtain ⟨hnat, he, hss⟩ := hs
  cases D with
  | consNormal _ _ _ _ _ st1 _ _ _ _ h1 h2 =>
    cases h1 with
    | varInit _ _ _ _ _ st' v _ hev =>
    unfold QPost
    rw [cseq_decl] at hseg hpos ⊢
    dsimp only at hseg hpos ⊢
    obtain ⟨⟨hs1, -⟩, hs2, hp2⟩ := segP_app.mp ⟨hseg, hpos⟩
    obtain ⟨B1, r1, hpc1, hsr1, hsp1, hAt1⟩ := sim_declT hAt hnat he hs1 hA hsr hev
    have hf1 := declInfo_cons x hΓ
    simp only [List.length_append]
    obtain ⟨B2, r2, hpc2, hout2, hsp2, hret2, hnorm2, f', hc2, hΓ2⟩ :=
      hτ code _ d env st'' t loop B1 _ g h2 hf1 hAt1
        (by rw [declInfo_names C x hAt.ne]; exact hss) hs2 hp2 hloop hpc1 hsr1
    refine ⟨B2, r1.trans r2, by rw [hpc2]; cases t <;> simp only [exitPos] <;> congr 1 <;> omega,
      hout2, hsp1.trans hsp2, hret2, hnorm2, f', hc2, hΓ2⟩
  | consAbrupt _ _ _ _ _ _ _ _ h1 hne =>
    cases h1 with | varInit => exact absurd rfl hne

def inExpr (sec : String → Bool) (x : String) (n : Int) : Expr := if sec x then encLit n else .int n

def inL (sec : String → Bool) (x : String) : EL := if sec x then encL 5 else .leaf

def declCtx (C : Ctx) (x : String) : Ctx := ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩

def ctxAfter (C : Ctx) : List (String × Int) → Ctx
  | [] => C
  | (x, _) :: r => ctxAfter (declCtx C x) r

def posAfter (sec : String → Bool) (C : Ctx) (pos : Nat) : List (String × Int) → Nat
  | [] => pos
  | (x, n) :: r => posAfter sec (declCtx C x) (pos + (declCode C pos x (inExpr sec x n)).length) r

def inTr (sec : String → Bool) (C : Ctx) (pos : Nat) : List (String × Int) → List Obs
  | [] => []
  | (x, n) :: r =>
    etr C.Γ 0 pos (inExpr sec x n) (inL sec x) ++
      stTr (pos + (cexpr C.Γ 0 pos (inExpr sec x n)).length) (varAddr (declInfo C x).2.1) ++
      inTr sec (declCtx C x) (pos + (declCode C pos x (inExpr sec x n)).length) r

def inLs (sec : String → Bool) (ins : List (String × Int)) : List SL :=
  ins.map fun p => .varInit (inL sec p.1)

theorem prefixW (sec : String → Bool) (body : Program) (τb : List Obs) (ℓb : List SL) :
    ∀ (ins : List (String × Int)) (C : Ctx) (pos : Nat),
      QTrW τb (ctxAfter C ins) (posAfter sec C pos ins) body ℓb →
      QTrW (inTr sec C pos ins ++ τb) C pos (prog sec ins body) (inLs sec ins ++ ℓb)
  | [], C, pos, h => by simpa [prog, inTr, inLs, ctxAfter, posAfter] using h
  | (x, n) :: r, C, pos, h => by
    have ih := prefixW sec body τb ℓb r (declCtx C x) _ h
    have := sConsDeclW (l := inL sec x) ih
    simpa [prog, inTr, inLs, inDecl, inExpr, List.append_assoc] using this

theorem li_len_small (c : Int) (h1 : -2048 ≤ c) (h2 : c < 2048) : (li a0 (BitVec.ofInt 64 c)).length = 1 := by
  have : (BitVec.ofInt 64 c).toInt = c := toInt_ofInt_range ⟨by omega, by omega⟩
  simp [li, this, h2, h1]

theorem chunk_small (n : Int) (j : Nat) : 0 ≤ chunkI n j ∧ chunkI n j < 2048 := by
  unfold chunkI
  have := Nat.mod_lt ((BitVec.ofInt 64 n).toNat / 2 ^ (11 * (5 - j))) (show 0 < 2048 by decide)
  omega

theorem int_chunk_len (Γ : Scope) (k pos : Nat) (n : Int) (j : Nat) :
    (cexpr Γ k pos (.int (chunkI n j))).length = 1 := by
  have := chunk_small n j
  exact li_len_small _ (by omega) this.2

theorem encAux_inv (n1 n2 : Int) (Γ : Scope) : ∀ (j k pos : Nat),
    (cexpr Γ k pos (encAux n1 j)).length = (cexpr Γ k pos (encAux n2 j)).length ∧
      etr Γ k pos (encAux n1 j) (encL j) = etr Γ k pos (encAux n2 j) (encL j)
  | 0, k, pos => by
    refine ⟨by simp only [encAux]; rw [int_chunk_len, int_chunk_len], ?_⟩
    simp only [encAux, encL, etr]
    rw [show (li a0 (BitVec.ofInt 64 (chunkI n1 0))).length = 1 from int_chunk_len Γ k pos n1 0,
      show (li a0 (BitVec.ofInt 64 (chunkI n2 0))).length = 1 from int_chunk_len Γ k pos n2 0]
  | j + 1, k, pos => by
    have ih := fun k pos => encAux_inv n1 n2 Γ j k pos
    have hl : ∀ (i : Nat) (m : Int), (li a0 (BitVec.ofInt 64 (chunkI m i))).length = 1 :=
      fun i m => int_chunk_len Γ 0 0 m i
    constructor
    · simp only [encAux, cexpr, List.length_append, (ih _ _).1, hl]
    · simp only [encAux, encL, etr, (ih _ _).1, (ih _ _).2, hl, cexpr, List.length_append]

theorem inExpr_inv (sec : String → Bool) (x : String) (n1 n2 : Int) (h : sec x = false → n1 = n2)
    (Γ : Scope) (k pos : Nat) :
    (cexpr Γ k pos (inExpr sec x n1)).length = (cexpr Γ k pos (inExpr sec x n2)).length ∧
      etr Γ k pos (inExpr sec x n1) (inL sec x) = etr Γ k pos (inExpr sec x n2) (inL sec x) := by
  by_cases hs : sec x = true
  · simp only [inExpr, inL, hs, ite_true]
    exact encAux_inv n1 n2 Γ 5 k pos
  · rw [h (by simpa using hs)]
    exact ⟨rfl, rfl⟩

theorem prefix_inv (sec : String → Bool) : ∀ {ins1 ins2 : List (String × Int)}, LowIns sec ins1 ins2 →
    ∀ (C : Ctx) (pos : Nat), ctxAfter C ins1 = ctxAfter C ins2 ∧
      posAfter sec C pos ins1 = posAfter sec C pos ins2 ∧ inTr sec C pos ins1 = inTr sec C pos ins2 ∧
      inLs sec ins1 = inLs sec ins2
  | _, _, .nil, C, pos => ⟨rfl, rfl, rfl, rfl⟩
  | _, _, .cons (x := x) (a := a) (b := b) hab hr, C, pos => by
    obtain ⟨h1, h2⟩ := inExpr_inv sec x a b hab C.Γ 0 pos
    have hdc : (declCode C pos x (inExpr sec x a)).length = (declCode C pos x (inExpr sec x b)).length := by
      simp only [declCode, List.length_append, h1]
    obtain ⟨i1, i2, i3, i4⟩ := prefix_inv sec hr (declCtx C x) (pos + (declCode C pos x (inExpr sec x b)).length)
    refine ⟨i1, ?_, ?_, ?_⟩
    · simp only [posAfter, hdc, i2]
    · simp only [inTr, hdc, i3, h1, h2]
    · simp only [inLs, List.map_cons] at i4 ⊢; rw [i4]

theorem prog_len (sec : String → Bool) (body : Program) : ∀ (ins : List (String × Int)) (C : Ctx) (pos : Nat),
    pos + (cseq C pos (prog sec ins body)).1.length =
      posAfter sec C pos ins + (cseq (ctxAfter C ins) (posAfter sec C pos ins) body).1.length
  | [], C, pos => rfl
  | (x, n) :: r, C, pos => by
    have ih := prog_len sec body r (declCtx C x) (pos + (declCode C pos x (inExpr sec x n)).length)
    show pos + (cseq C pos (.varDecl x (some (inExpr sec x n)) :: prog sec r body)).1.length = _
    rw [cseq_decl]
    simp only [List.length_append, posAfter, ctxAfter]
    rw [← ih, declCtx]
    omega

def progTr (sec : String → Bool) (ins : List (String × Int)) (body : Program) (τb : List Obs) : List Obs :=
  [pobs 0] ++ (inTr sec ctx0 mainPos₀ ins ++ τb) ++
    exitTr (posAfter sec ctx0 mainPos₀ ins + (cseq (ctxAfter ctx0 ins) (posAfter sec ctx0 mainPos₀ ins) body).1.length) 0

theorem run_progT {sec : String → Bool} {body : Program} {ins : List (String × Int)} {τb : List Obs}
    {ℓb : List SL} (hW : QTrW τb (ctxAfter ctx0 ins) (posAfter sec ctx0 mainPos₀ ins) body ℓb)
    (hsup : Supported (prog sec ins body)) (hfit : Fits (compile (prog sec ins body))) (m : Mem)
    (o : Array String) (ho : String.join o.toList = "") {st' : St}
    (D : ExecSeqL initSt 0 0 (prog sec ins body) st' .normal (inLs sec ins ++ ℓb)) :
    ∃ B, StarT (compile (prog sec ins body)) (progTr sec ins body τb) (A0 m o) B ∧
      astep (compile (prog sec ins body)) B = some (.halt 0) ∧ String.join B.out.toList = st'.out := by
  have hW' := prefixW sec body τb ℓb ins ctx0 mainPos₀ hW
  obtain ⟨h1, -, -, h4, h5⟩ := compile_segs (prog sec ins body)
  have hAt := at0 (prog sec ins body) hfit
  have hpos := Seg.end_ok hfit h5 (by simp [exitCode])
  have hbl : (Compiler.body (prog sec ins body)).length = (cseq ctx0 mainPos₀ (prog sec ins body)).1.length := rfl
  have e0 := jumpT hfit h1.head (A := A0 m o) rfl (by decide) hAt.posok
  obtain ⟨B, r, hpc, hout, -, -, -, -⟩ := hW' (compile (prog sec ins body)) initSt 0 0 st' .normal false
    ⟨pcOf mainPos₀, [], m, o⟩ [] [] D rfl hAt hsup h4 (by unfold PosOK at *; omega)
    (fun h => by cases h) rfl (sr0 m o ho)
  have hend := prog_len sec body ins ctx0 mainPos₀
  simp only [exitPos] at hpc
  rw [hbl, hend] at h5
  obtain ⟨B', r', hBm, hBo, hh⟩ := run_exitT hfit (by decide : (0 : Nat) = 0 ∨ 0 = 70) h5 (by rw [hpc, hend])
  refine ⟨B', ?_, hh, by rw [hBo]; exact hout⟩
  have := e0.trans (r.trans r')
  simpa [progTr, List.append_assoc, pobs, A0] using this

theorem prog_leak (sec : String → Bool) (body : Program) : ∀ (ins : List (String × Int)) {st : St} {d : Nat}
    {env : Addr} {st' : St} {t : Status} {ℓ : List SL}, ExecSeqL st d env (prog sec ins body) st' t ℓ →
    ∃ ℓb, ℓ = inLs sec ins ++ ℓb
  | [], _, _, _, _, _, ℓ, _ => ⟨ℓ, rfl⟩
  | (x, n) :: r, _, _, _, _, _, _, h => by
    have h' : ExecSeqL _ _ _ (.varDecl x (some (if sec x then encLit n else .int n)) :: prog sec r body) _ _ _ := h
    obtain ⟨st1, v, l, ls, he, hseq, rfl⟩ := seq_cons_inv h'
    obtain ⟨rfl, -, -⟩ := input_leak sec x n he
    obtain ⟨ℓb, rfl⟩ := prog_leak sec body r hseq
    exact ⟨ℓb, rfl⟩

theorem am_ct_core {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hlow : LowIns sec ins1 ins2)
    (hsup1 : Supported (prog sec ins1 body)) (hsup2 : Supported (prog sec ins2 body))
    (hfit1 : Fits (compile (prog sec ins1 body))) (hfit2 : Fits (compile (prog sec ins2 body)))
    {o1 o2 : String} {ℓ : List SL} (h1 : BigStepL (prog sec ins1 body) o1 ℓ)
    (h2 : BigStepL (prog sec ins2 body) o2 ℓ) :
    ∃ τ : List Obs, ∀ (m : Mem) (o : Array String), String.join o.toList = "" →
      (∃ B, StarT (compile (prog sec ins1 body)) τ (A0 m o) B ∧
        astep (compile (prog sec ins1 body)) B = some (.halt 0) ∧ String.join B.out.toList = o1) ∧
      (∃ B, StarT (compile (prog sec ins2 body)) τ (A0 m o) B ∧
        astep (compile (prog sec ins2 body)) B = some (.halt 0) ∧ String.join B.out.toList = o2) := by
  obtain ⟨st1, D1, hout1⟩ := h1
  obtain ⟨st2, D2, hout2⟩ := h2
  obtain ⟨ℓb, hℓ⟩ := prog_leak sec body ins1 D1
  obtain ⟨i1, i2, i3, i4⟩ := prefix_inv sec hlow ctx0 mainPos₀
  have D2' : ExecSeqL initSt 0 0 (prog sec ins2 body) st2 .normal (inLs sec ins2 ++ ℓb) := by
    rw [← i4, ← hℓ]; exact D2
  rw [hℓ] at D1
  obtain ⟨τb, hτb⟩ := seqTr printSpec ℓb (ctxAfter ctx0 ins1) (posAfter sec ctx0 mainPos₀ ins1) body
  have hW1 : QTrW τb (ctxAfter ctx0 ins1) (posAfter sec ctx0 mainPos₀ ins1) body ℓb := hτb
  have hW2 : QTrW τb (ctxAfter ctx0 ins2) (posAfter sec ctx0 mainPos₀ ins2) body ℓb := by
    rw [← i1, ← i2]; exact hτb
  have htr : progTr sec ins2 body τb = progTr sec ins1 body τb := by
    simp only [progTr, i1, i2, i3]
  refine ⟨progTr sec ins1 body τb, fun m o ho => ⟨?_, ?_⟩⟩
  · obtain ⟨B, r, hh, hB⟩ := run_progT hW1 hsup1 hfit1 m o ho D1
    exact ⟨B, r, hh, hB.trans hout1⟩
  · obtain ⟨B, r, hh, hB⟩ := run_progT hW2 hsup2 hfit2 m o ho D2'
    exact ⟨B, htr ▸ r, hh, hB.trans hout2⟩

theorem am_ct {sec : String → Bool} {body : Program} {ins1 ins2 : List (String × Int)}
    (hct : ctSeq sec body = true) (hnat : ∀ p ∈ ins1, isNat p.1 = false) (hlow : LowIns sec ins1 ins2)
    (hsup1 : Supported (prog sec ins1 body)) (hsup2 : Supported (prog sec ins2 body))
    (hfit1 : Fits (compile (prog sec ins1 body))) (hfit2 : Fits (compile (prog sec ins2 body)))
    {o1 : String} {ℓ1 : List SL} (h1 : BigStepL (prog sec ins1 body) o1 ℓ1) :
    ∃ o2 ℓ2, BigStepL (prog sec ins2 body) o2 ℓ2 ∧ skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ τ : List Obs, ∀ (m : Mem) (o : Array String),
        String.join o.toList = "" →
        (∃ B, StarT (compile (prog sec ins1 body)) τ (A0 m o) B ∧
          astep (compile (prog sec ins1 body)) B = some (.halt 0) ∧ String.join B.out.toList = o1) ∧
        (∃ B, StarT (compile (prog sec ins2 body)) τ (A0 m o) B ∧
          astep (compile (prog sec ins2 body)) B = some (.halt 0) ∧ String.join B.out.toList = o2)) := by
  obtain ⟨o2, ℓ2, h2, hsk, heq⟩ := ct_sound hct hnat hlow h1
  refine ⟨o2, ℓ2, h2, hsk, fun ho => ?_⟩
  obtain ⟨rfl, rfl⟩ := heq ho
  refine ⟨rfl, ?_⟩
  obtain ⟨st1, D1, hout1⟩ := h1
  obtain ⟨st2, D2, hout2⟩ := h2
  obtain ⟨ℓb, hℓ⟩ := prog_leak sec body ins1 D1
  obtain ⟨i1, i2, i3, i4⟩ := prefix_inv sec hlow ctx0 mainPos₀
  have D2' : ExecSeqL initSt 0 0 (prog sec ins2 body) st2 .normal (inLs sec ins2 ++ ℓb) := by
    rw [← i4, ← hℓ]; exact D2
  rw [hℓ] at D1
  obtain ⟨τb, hτb⟩ := seqTr printSpec ℓb (ctxAfter ctx0 ins1) (posAfter sec ctx0 mainPos₀ ins1) body
  have hW1 : QTrW τb (ctxAfter ctx0 ins1) (posAfter sec ctx0 mainPos₀ ins1) body ℓb := hτb
  have hW2 : QTrW τb (ctxAfter ctx0 ins2) (posAfter sec ctx0 mainPos₀ ins2) body ℓb := by
    rw [← i1, ← i2]; exact hτb
  have htr : progTr sec ins2 body τb = progTr sec ins1 body τb := by
    simp only [progTr, i1, i2, i3]
  refine ⟨progTr sec ins1 body τb, fun m o ho => ⟨?_, ?_⟩⟩
  · obtain ⟨B, r, hh, hB⟩ := run_progT hW1 hsup1 hfit1 m o ho D1
    exact ⟨B, r, hh, hB.trans hout1⟩
  · obtain ⟨B, r, hh, hB⟩ := run_progT hW2 hsup2 hfit2 m o ho D2'
    exact ⟨B, htr ▸ r, hh, hB.trans hout2⟩

end Vsa.Compiler
