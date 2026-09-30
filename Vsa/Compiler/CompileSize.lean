import Vsa.Compiler.StmtCases

namespace Vsa.Compiler

open Vsa.While

def exprSize : Expr → Nat
  | .int _ => 11
  | .bool _ => 1
  | .var _ => 12
  | .assign _ e => exprSize e + 12
  | .binary _ l r => exprSize l + exprSize r + 30
  | .unary _ e => exprSize e + 4
  | _ => 0

def argsSize : List Expr → Nat
  | [] => 0
  | e :: es => exprSize e + 12 + argsSize es

mutual
def stmtSize : Stmt → Nat
  | .expr e => exprSize e + argsSize (match e with | .call _ args => args | _ => []) +
      36 * (match e with | .call _ args => args.length | _ => 0) + 23
  | .block ss => seqSize ss
  | .ifStmt c t none => exprSize c + 2 + stmtSize t
  | .ifStmt c t (some e) => exprSize c + 3 + stmtSize t + stmtSize e
  | .whileStmt c b => exprSize c + 3 + stmtSize b
  | .brk | .cont => 1
  | _ => 0

def seqSize : List Stmt → Nat
  | [] => 0
  | .varDecl _ (some e) :: ss => exprSize e + 12 + seqSize ss
  | s :: ss => stmtSize s + seqSize ss
end

theorem li_length_le (rd : Nat) (n : BitVec 64) : (li rd n).length ≤ 11 := by
  unfold li; split <;> simp [List.range, List.range.loop]

theorem putc_length_le (c : Char) : (putc c).length ≤ 23 := by
  have h1 := li_length_le s3 (putcWord (BitVec.ofNat 8 c.toNat))
  have h2 := li_length_le s2 tohostW
  simp only [putc, List.length_append, List.length_cons, List.length_nil]; omega

theorem cbin_length_le (p : Nat) (op : BinOp) : (cbin p op).length ≤ 5 := by
  cases op <;> simp [cbin, libc, cmpBranch]

theorem cexpr_length_le (Γ : Scope) : ∀ (e : Expr) (k pos : Nat), (cexpr Γ k pos e).length ≤ exprSize e
  | .int n, _, _ => li_length_le _ _
  | .bool _, _, _ => by simp [cexpr, exprSize]
  | .var x, _, _ => by
    have := li_length_le s2 (BitVec.ofNat 64 (varAddr ((Γ.resolve x).getD 0)))
    simp only [cexpr, liN, exprSize, List.length_append, List.length_cons, List.length_nil]; omega
  | .assign x e, k, pos => by
    have := cexpr_length_le Γ e k pos
    have := li_length_le s2 (BitVec.ofNat 64 (varAddr ((Γ.resolve x).getD 0)))
    simp only [cexpr, liN, exprSize, List.length_append, List.length_cons, List.length_nil]; omega
  | .binary op l r, k, pos => by
    have h1 := cexpr_length_le Γ l k pos
    have h2 := cexpr_length_le Γ r (k + 1)
      (pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length)
    have h3 := li_length_le s2 (BitVec.ofNat 64 (tempAddr k))
    have h4 := cbin_length_le
      (pos + (cexpr Γ k pos l).length + (liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length +
        (cexpr Γ (k + 1) (pos + (cexpr Γ k pos l).length +
          (liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length) r).length +
        ([mv a1 a0] ++ liN s2 (tempAddr k) ++ [Ins.ld a0 s2]).length) op
    simp only [cexpr, liN, exprSize, List.length_append, List.length_cons, List.length_nil] at h2 h4 ⊢
    omega
  | .unary op e, k, pos => by
    have := cexpr_length_le Γ e k pos
    cases op <;> simp only [cexpr, exprSize, List.length_append, List.length_cons, List.length_nil] <;> omega
  | .str _, _, _ => by simp [cexpr]
  | .null, _, _ => by simp [cexpr]
  | .logical _ _ _, _, _ => by simp [cexpr]
  | .call _ _, _, _ => by simp [cexpr]
  | .fn _ _ _, _, _ => by simp [cexpr]

theorem cargs_length_le (Γ : Scope) : ∀ (args : List Expr) (k pos : Nat),
    (cargs Γ k pos args).1.length ≤ argsSize args
  | [], _, _ => by simp [cargs, argsSize]
  | e :: es, k, pos => by
    have h1 := cexpr_length_le Γ e k pos
    have h2 := li_length_le s2 (BitVec.ofNat 64 (tempAddr k))
    have h3 := cargs_length_le Γ es (k + 1)
      (pos + (cexpr Γ k pos e ++ liN s2 (tempAddr k) ++ [Ins.sd a0 s2]).length)
    simp only [cargs, liN, argsSize, List.length_append, List.length_cons, List.length_nil] at h3 ⊢
    omega

theorem printLoop_length_le (k pos : Nat) : ∀ n, (printLoop k pos n).length ≤ 36 * n
  | 0 => by simp [printLoop]
  | n + 1 => by
    have h1 := li_length_le s2 (BitVec.ofNat 64 (tempAddr k))
    have h2 := putc_length_le ' '
    have h3 := printLoop_length_le (k + 1) (pos + (liN s2 (tempAddr k) ++ [Ins.ld a0 s2]).length + 1 +
      (if n = 0 then [] else putc ' ').length) n
    have h4 : (if n = 0 then ([] : List Ins) else putc ' ').length ≤ 23 := by
      split
      · simp
      · exact h2
    simp only [printLoop, liN, List.length_append, List.length_cons, List.length_nil] at h3 ⊢
    omega

mutual

theorem cstmt_length_le (C : Ctx) (pos : Nat) : ∀ (s : Stmt), (cstmt C pos s).1.length ≤ stmtSize s
  | .expr e => by
    cases e with
    | call f args =>
      cases f with
      | var x =>
        have h1 := cargs_length_le C.Γ args 0 pos
        have h2 := printLoop_length_le 0 (cargs C.Γ 0 pos args).2 args.length
        have h3 := putc_length_le '\n'
        have h4 : (if x = "println" then putc '\n' else []).length ≤ 23 := by
          split
          · exact h3
          · simp
        simp only [cstmt, stmtSize, exprSize, List.length_append]
        omega
      | _ => exact Nat.le_trans (cexpr_length_le C.Γ _ 0 pos) (by simp only [stmtSize]; omega)
    | _ => exact Nat.le_trans (cexpr_length_le C.Γ _ 0 pos) (by simp only [stmtSize]; omega)
  | .block ss => by
    have := cseq_length_le ⟨[] :: C.Γ, C.next, C.brk, C.cont⟩ pos ss
    simp only [cstmt, stmtSize]; exact this
  | .ifStmt c t e => by
    have h0 := cexpr_length_le C.Γ c 0 pos
    have h1 := cstmt_length_le C (pos + (cexpr C.Γ 0 pos c).length + 2) t
    cases e with
    | none => simp only [cstmt, stmtSize, List.length_append, List.length_cons, List.length_nil]; omega
    | some e =>
      have h2 := cstmt_length_le ⟨C.Γ, (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).2, C.brk, C.cont⟩
        (pos + (cexpr C.Γ 0 pos c).length + 2 +
          (cstmt C (pos + (cexpr C.Γ 0 pos c).length + 2) t).1.length + 1) e
      simp only [cstmt, stmtSize, List.length_append, List.length_cons, List.length_nil]; omega
  | .whileStmt c b => by
    have h0 := cexpr_length_le C.Γ c 0 pos
    have h1 := cstmt_length_le ⟨C.Γ, C.next, pos + (cexpr C.Γ 0 pos c).length + 2 +
      (cstmt ⟨C.Γ, C.next, 0, 0⟩ (pos + (cexpr C.Γ 0 pos c).length + 2) b).1.length + 1, pos⟩
      (pos + (cexpr C.Γ 0 pos c).length + 2) b
    simp only [cstmt, stmtSize, List.length_append, List.length_cons, List.length_nil]; omega
  | .varDecl _ _ => by simp [cstmt]
  | .forStmt _ _ _ _ => by simp [cstmt]
  | .ret _ => by simp [cstmt]
  | .brk => by simp [cstmt, stmtSize]
  | .cont => by simp [cstmt, stmtSize]

theorem cseq_length_le (C : Ctx) (pos : Nat) : ∀ (ss : List Stmt),
    (cseq C pos ss).1.length ≤ seqSize ss
  | [] => by simp [cseq]
  | s :: ss => by
    by_cases hd : ∃ x e, s = .varDecl x (some e)
    · obtain ⟨x, e, rfl⟩ := hd
      rw [cseq_decl]
      have h1 := cexpr_length_le C.Γ e 0 pos
      have h2 := li_length_le s2 (BitVec.ofNat 64 (varAddr (declInfo C x).2.1))
      have h3 := cseq_length_le ⟨(declInfo C x).1, (declInfo C x).2.2, C.brk, C.cont⟩
        (pos + (declCode C pos x e).length) ss
      simp only [declCode, liN, seqSize, List.length_append, List.length_cons, List.length_nil] at h3 ⊢
      omega
    · rw [cseq_other C pos s ss (fun x e h => hd ⟨x, e, h⟩)]
      have h1 := cstmt_length_le C pos s
      have h2 := cseq_length_le ⟨C.Γ, (cstmt C pos s).2, C.brk, C.cont⟩ (pos + (cstmt C pos s).1.length) ss
      have hs : seqSize (s :: ss) = stmtSize s + seqSize ss := by
        cases s with
        | varDecl x i =>
          cases i with
          | some e => exact absurd ⟨x, e, rfl⟩ hd
          | none => rfl
        | _ => rfl
      simp only [List.length_append, hs]
      omega

end

theorem compile_length_le (p : Program) : (compile p).length ≤ 123 + seqSize p := by
  have h1 := cseq_length_le ⟨[[]], 0, 0, 0⟩ mainPos₀ p
  have h2 : (exitCode 0).length ≤ 23 := by
    have := li_length_le s3 (exitWord (BitVec.ofNat 64 0))
    have := li_length_le s2 tohostW
    simp only [exitCode, List.length_append, List.length_cons, List.length_nil]; omega
  have hm : mainPos₀ = 100 := rfl
  have : (compile p).length = mainPos₀ + (cseq ⟨[[]], 0, 0, 0⟩ mainPos₀ p).1.length + (exitCode 0).length := by
    simp only [compile, List.length_append, List.length_cons, List.length_nil, mainPos₀, printPos, errPos]
    try omega
  omega

end Vsa.Compiler
