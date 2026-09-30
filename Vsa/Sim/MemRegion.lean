import Vsa.Sim.ReprSurvival

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim

structure NodeIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 40 ≤ hi

structure CellIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 8 ≤ hi

structure StrIn (lo hi p : Nat) (s : String) : Prop where
  ne_zero : p ≠ 0
  lo_le : lo ≤ p
  hi_ge : p + s.length + 1 ≤ hi

def ParamsIn (m : Mem) (lo hi : Nat) : Nat → List String → Prop
  | _, [] => True
  | a, x :: xs =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StrIn lo hi p x) ∧
    ParamsIn m lo hi (a + 8) xs

mutual

def ExprIn (m : Mem) (lo hi : Nat) : Nat → Expr → Prop
  | a, .int _ => NodeIn lo hi a
  | a, .str s => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p s)
  | a, .bool _ => NodeIn lo hi a
  | a, .null => NodeIn lo hi a
  | a, .var x => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x)
  | a, .assign x e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ExprIn m lo hi q e)
  | a, .binary _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .logical _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .unary _ e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p e)
  | a, .call f args => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p f) ∧
      (∀ q, read64 m (a + 16) = some q → ExprsIn m lo hi q args)
  | a, .fn ox ps ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p →
        ∀ x, ox = some x → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ParamsIn m lo hi q ps) ∧

      (∀ b, read64 m (a + 32) = some b → NodeIn lo hi b ∧
        (∀ q, read64 m (b + 8) = some q → StmtsIn m lo hi q ss))

def ExprsIn (m : Mem) (lo hi : Nat) : Nat → List Expr → Prop
  | _, [] => True
  | a, e :: es =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → ExprIn m lo hi p e) ∧
    ExprsIn m lo hi (a + 8) es

def OptExprIn (m : Mem) (lo hi addr : Nat) : Option Expr → Prop
  | none => CellIn lo hi addr
  | some e => CellIn lo hi addr ∧
      (∀ p, read64 m addr = some p → ExprIn m lo hi p e)

def StmtIn (m : Mem) (lo hi : Nat) : Nat → Stmt → Prop
  | a, .expr e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p e)
  | a, .varDecl x oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      OptExprIn m lo hi (a + 16) oe
  | a, .block ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StmtsIn m lo hi p ss)
  | a, .ifStmt c t oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p t) ∧
      OptStmtIn m lo hi (a + 24) oe
  | a, .whileStmt c b => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p b)
  | a, .forStmt oi oc os b => NodeIn lo hi a ∧
      OptStmtIn m lo hi (a + 8) oi ∧
      OptExprIn m lo hi (a + 16) oc ∧
      OptExprIn m lo hi (a + 24) os ∧
      (∀ p, read64 m (a + 32) = some p → StmtIn m lo hi p b)
  | a, .ret oe => NodeIn lo hi a ∧ OptExprIn m lo hi (a + 8) oe
  | a, .brk => NodeIn lo hi a
  | a, .cont => NodeIn lo hi a

def StmtsIn (m : Mem) (lo hi : Nat) : Nat → List Stmt → Prop
  | _, [] => True
  | a, s :: ss =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StmtIn m lo hi p s) ∧
    StmtsIn m lo hi (a + 8) ss

def OptStmtIn (m : Mem) (lo hi addr : Nat) : Option Stmt → Prop
  | none => CellIn lo hi addr
  | some s => CellIn lo hi addr ∧
      (∀ p, read64 m addr = some p → StmtIn m lo hi p s)

end

def regionP (lo hi : Nat) : Nat → Prop := fun a => lo ≤ a ∧ a < hi

theorem read64_region {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') {a : Nat}
    (hlo : lo ≤ a) (hhi : a + 8 ≤ hi) : read64 m a = read64 m' a :=
  read64_agreeP h (fun k hk => ⟨by omega, by omega⟩)

theorem paramsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} {ps : List String}, ParamsIn m lo hi a ps → ParamsIn m' lo hi a ps
  | _, [], _ => trivial
  | a, _ :: _, ⟨hc, hs, hrest⟩ =>
    ⟨hc, fun p hp => hs p (by rwa [read64_region h hc.lo_le hc.hi_ge]),
      paramsIn_agreeP h hrest⟩

mutual

theorem exprIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (e : Expr), ExprIn m lo hi a e → ExprIn m' lo hi a e
  | _, .int _, hn => hn
  | _, .str _, ⟨hn, hs⟩ =>
    ⟨hn, fun p hp => hs p (by
      rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
        (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)⟩
  | _, .bool _, hn => hn
  | _, .null, hn => hn
  | _, .var _, ⟨hn, hs⟩ =>
    ⟨hn, fun p hp => hs p (by
      rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
        (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)⟩
  | _, .assign _ e, ⟨hn, hs, he⟩ =>
    ⟨hn, fun p hp => hs p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp),
      fun q hq => exprIn_agreeP h e (he q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq))⟩
  | _, .binary _ l r, ⟨hn, hl, hr⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h l (hl p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => exprIn_agreeP h r (hr p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .logical _ l r, ⟨hn, hl, hr⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h l (hl p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => exprIn_agreeP h r (hr p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .unary _ e, ⟨hn, he⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .call f args, ⟨hn, hf, ha⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h f (hf p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun q hq => exprsIn_agreeP h args (ha q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq))⟩
  | _, .fn _ ps ss, ⟨hn, hx, hps, hb⟩ =>
    ⟨hn, fun p hp x hox => hx p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp) x hox,
      fun q hq => paramsIn_agreeP h (hps q (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hq)),
      fun b hb' => by
        have hb0 := hb b (by
          rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
            (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hb')
        exact ⟨hb0.1, fun q hq => stmtsIn_agreeP h ss (hb0.2 q (by
          rw [read64_region h (show lo ≤ _ by have := hb0.1.lo_le; omega)
            (show _ + 8 ≤ hi by have := hb0.1.hi_ge; omega)]; exact hq))⟩⟩

theorem exprsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (es : List Expr), ExprsIn m lo hi a es → ExprsIn m' lo hi a es
  | _, [], _ => trivial
  | _, e :: es, ⟨hc, he, hrest⟩ =>
    ⟨hc, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h hc.lo_le hc.hi_ge]; exact hp)),
      exprsIn_agreeP h es hrest⟩

theorem optExprIn_agreeP {lo hi addr : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m')
    (hlo : lo ≤ addr) (hhi : addr + 8 ≤ hi) :
    ∀ (oe : Option Expr), OptExprIn m lo hi addr oe → OptExprIn m' lo hi addr oe
  | none, hc => hc
  | some e, ⟨hc, he⟩ => ⟨hc, fun p hp =>
      exprIn_agreeP h e (he p (by rw [read64_region h hlo hhi]; exact hp))⟩

theorem stmtIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (s : Stmt), StmtIn m lo hi a s → StmtIn m' lo hi a s
  | _, .expr e, ⟨hn, he⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h e (he p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .varDecl _ oe, ⟨hn, hs, hoe⟩ =>
    ⟨hn, fun p hp => hs p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp),
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .block ss, ⟨hn, hss⟩ =>
    ⟨hn, fun p hp => stmtsIn_agreeP h ss (hss p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .ifStmt c t oe, ⟨hn, hcnd, ht, hoe⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h c (hcnd p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => stmtIn_agreeP h t (ht p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      optStmtIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .whileStmt c b, ⟨hn, hcnd, hb⟩ =>
    ⟨hn, fun p hp => exprIn_agreeP h c (hcnd p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp)),
      fun p hp => stmtIn_agreeP h b (hb p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .forStmt oi oc os b, ⟨hn, hoi, hoc, hos, hb⟩ =>
    ⟨hn,
      optStmtIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oi hoi,
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) oc hoc,
      optExprIn_agreeP h (by have := hn.lo_le; omega) (by have := hn.hi_ge; omega) os hos,
      fun p hp => stmtIn_agreeP h b (hb p (by
        rw [read64_region h (show lo ≤ _ by have := hn.lo_le; omega)
          (show _ + 8 ≤ hi by have := hn.hi_ge; omega)]; exact hp))⟩
  | _, .ret oe, ⟨hn, hoe⟩ =>
    ⟨hn, optExprIn_agreeP h (by have := hn.lo_le; omega)
      (by have := hn.hi_ge; omega) oe hoe⟩
  | _, .brk, hn => hn
  | _, .cont, hn => hn

theorem stmtsIn_agreeP {lo hi : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m') :
    ∀ {a : Nat} (ss : List Stmt), StmtsIn m lo hi a ss → StmtsIn m' lo hi a ss
  | _, [], _ => trivial
  | _, s :: ss, ⟨hc, hs, hrest⟩ =>
    ⟨hc, fun p hp => stmtIn_agreeP h s (hs p (by
        rw [read64_region h hc.lo_le hc.hi_ge]; exact hp)),
      stmtsIn_agreeP h ss hrest⟩

theorem optStmtIn_agreeP {lo hi addr : Nat} {m m' : Mem}
    (h : AgreeP (regionP lo hi) m m')
    (hlo : lo ≤ addr) (hhi : addr + 8 ≤ hi) :
    ∀ (os : Option Stmt), OptStmtIn m lo hi addr os → OptStmtIn m' lo hi addr os
  | none, hc => hc
  | some s, ⟨hc, hs⟩ => ⟨hc, fun p hp =>
      stmtIn_agreeP h s (hs p (by rw [read64_region h hlo hhi]; exact hp))⟩

end

theorem exprIn_node {m : Mem} {lo hi a : Nat} {e : Expr}
    (h : ExprIn m lo hi a e) : NodeIn lo hi a := by
  cases e with
  | int _ => exact h
  | str _ => exact h.1
  | bool _ => exact h
  | null => exact h
  | var _ => exact h.1
  | assign _ _ => exact h.1
  | binary _ _ _ => exact h.1
  | logical _ _ _ => exact h.1
  | unary _ _ => exact h.1
  | call _ _ => exact h.1
  | fn _ _ _ => exact h.1

end Vsa.Sim
