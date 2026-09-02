import Vsa.Sim.EntryGround

/-!
# `EntryGroundKit` — the child-ground derivation combinators (wave 47i)

The insertion wave threads a CHILD `EvalGround`/`ExecGround` conjunct through
every child-entry ctor tower (`armTail_rec` and its twins).  Suppliers with the
parent entry `hc : EvalEntry …` in scope derive the child bundle in THREE moves,
factored here ONCE (Law 3 — every recursive arm repeats them):

1. **transport** — the pre-call memory agrees with the entry `m0` off the
   scribbled stack window (`EvalGround.survive_stack` with the sret half vacuous);
2. **payload-read agreement** — the node's payload pointer reads back unchanged
   (the AST region is stack-disjoint, `evalGround_ast_read64_agree`);
3. **parameter conversion** — lowered `sp'`, the in-frame `subsret`, and the
   child node via `ExprIn` projection (`EvalGround.child_params`).

`EvalGround.child_at` composes 1+3 (the caller applies 2 to its payload fact and
feeds the projection).  Exec twins for the statement side.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-! ## Move 1 — off-stack transport (sret half vacuous) -/

/-- `EvalGround` transports to any memory agreeing with `m0` OFF the scribbled
stack window `[SL.lo, sp)` alone (the `blockA_k` memframe shape) — the sret
window sits inside the stack region, so the two-window `survive_stack`
hypothesis weakens to this. -/
theorem EvalGround.transport_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (hg : EvalGround m0 SL A sp sret aExpr e)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hspSL : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    EvalGround ment SL A sp sret aExpr e :=
  hg.survive_stack htb hspSL (fun k hk _ => (hmem k hk).symm)

theorem ExecGround.transport_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hspSL : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    ExecGround ment SL A sp aRet aStmt s :=
  hg.survive_stack hspSL (fun k hk _ => (hmem k hk).symm)

/-! ## Move 2 — in-node read agreement (the AST region is stack-disjoint) -/

/-- Any 8-byte read INSIDE the root node slot (`off + 8 ≤ 40`, the `NodeIn`
window) agrees between the entry memory and any off-stack-agreeing memory. -/
theorem evalGround_ast_read64_agree {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (hg : EvalGround m0 SL A sp sret aExpr e)
    (hspSL : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?)
    {off : Nat} (hoff : off + 8 ≤ 40) :
    read64 ment (aExpr + off) = read64 m0 (aExpr + off) := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hnode := exprIn_node spec.nodes
  refine read64_agreeP (P := fun k => lo ≤ k ∧ k < hi) (fun k hk => ?_)
    (fun k hk => ⟨by have := hnode.lo_le; omega, by have := hnode.hi_ge; omega⟩)
  refine hmem k (fun hcon => ?_)
  rcases spec.stack_disjoint with hs | hs <;> omega

/-- The exec twin: an 8-byte read inside the root `Stmt` node slot. -/
theorem execGround_ast_read64_agree {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hspSL : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?)
    {off : Nat} (hoff : off + 8 ≤ 40) :
    read64 ment (aStmt + off) = read64 m0 (aStmt + off) := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hnode := stmtIn_node spec.nodes
  refine read64_agreeP (P := fun k => lo ≤ k ∧ k < hi) (fun k hk => ?_)
    (fun k hk => ⟨by have := hnode.lo_le; omega, by have := hnode.hi_ge; omega⟩)
  refine hmem k (fun hcon => ?_)
  rcases spec.stack_disjoint with hs | hs <;> omega

/-! ## Move 3 — parameter conversion (same memory) -/

/-- **Child-ground parameter conversion**: lowered `sp'`, an in-frame `subsret`,
and the child node by `ExprIn` projection.  The child result slot lives in the
parent's scribble (`[SL.lo, sp)`), so its region/table disjointness re-derive
from the parent's stack facts. -/
theorem EvalGround.child_params {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    {sp' subsret : BitVec 64} {aChild : Nat} {echild : Expr}
    (hproj : ∀ lo hi, ExprIn m lo hi aExpr e → ExprIn m lo hi aChild echild)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hsub_lo : SL.lo ≤ subsret.toNat) (hsub_hi : subsret.toNat + 24 ≤ sp.toNat) :
    EvalGround m SL A sp' subsret aChild echild where
  table := h.table
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, ⟨hproj lo hi spec.nodes, spec.lo_ram, spec.hi_ram, spec.win,
      spec.stack_disjoint, ?_, spec.arena_disjoint⟩⟩
    rcases spec.stack_disjoint with hs | hs
    · left; omega
    · right; omega⟩
  arena_stack := by
    rcases h.arena_stack with ha | ha
    · left; exact ha
    · right; omega
  arena_code := h.arena_code
  arena_vi := h.arena_vi
  sret_inSL := ⟨hsub_lo, by omega⟩
  sret_table_disjoint := by
    rcases htb with ht | ht
    · right; omega
    · left; omega

/-- The exec twin: child statement + in-frame `retslot`. -/
theorem ExecGround.child_params {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    {sp' aRet' : BitVec 64} {aChild : Nat} {schild : Stmt}
    (hproj : ∀ lo hi, StmtIn m lo hi aStmt s → StmtIn m lo hi aChild schild)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hret_al : aRet'.toNat % 8 = 0)
    (hret_lo : SL.lo ≤ aRet'.toNat) (hret_hi : aRet'.toNat + 24 ≤ sp.toNat)
    (hret_scrib : aRet'.toNat + 24 ≤ SL.lo ∨ sp'.toNat ≤ aRet'.toNat)
    (hSL_ram : 0x80000000 ≤ SL.lo) (hSL_win : tohostAddr + 16 ≤ SL.lo)
    (hSLhi_ram : SL.hi ≤ 0x100000000) :
    ExecGround m SL A sp' aRet' aChild schild where
  table := h.table
  table_stack := by
    rcases h.table_stack with ht | ht
    · left; exact ht
    · right; omega
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    refine ⟨lo, hi, ⟨hproj lo hi spec.nodes, spec.lo_ram, spec.hi_ram, spec.win,
      spec.stack_disjoint, ?_, spec.arena_disjoint⟩⟩
    rcases spec.stack_disjoint with hs | hs
    · left; omega
    · right; omega⟩
  arena_stack := by
    rcases h.arena_stack with ha | ha
    · left; exact ha
    · right; omega
  arena_code := h.arena_code
  aret :=
    { align := hret_al
      ram := ⟨by omega, by omega⟩
      win := by omega
      scribble_disjoint := hret_scrib
      inSL := ⟨hret_lo, by omega⟩ }
  aret_table_disjoint := by
    rcases h.table_stack with ht | ht
    · right; simp only [stmtJumpTableBase] at ht ⊢; omega
    · left; simp only [stmtJumpTableBase] at ht ⊢; omega

/-! ## The composed child-at combinator (moves 1 + 3) -/

/-- **The one-call child-ground supplier**: from the parent entry ground (over
`m0`), the pre-call memory's off-stack agreement, and the child parameters,
produce the child bundle over the pre-call memory.  The `hproj` projection is
stated over `ment` — obtain the payload read there via
`evalGround_ast_read64_agree` (move 2). -/
theorem EvalGround.child_at {m0 ment : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (hg : EvalGround m0 SL A sp sret aExpr e)
    {sp' subsret : BitVec 64} {aChild : Nat} {echild : Expr}
    (hproj : ∀ lo hi, ExprIn ment lo hi aExpr e → ExprIn ment lo hi aChild echild)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hsub_lo : SL.lo ≤ subsret.toNat) (hsub_hi : subsret.toNat + 24 ≤ sp.toNat) :
    EvalGround ment SL A sp' subsret aChild echild :=
  (hg.transport_offstack htb hspSL hmem).child_params hproj htb hspSL hsp'
    hsub_lo hsub_hi

theorem ExecGround.child_at {m0 ment : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    {sp' aRet' : BitVec 64} {aChild : Nat} {schild : Stmt}
    (hproj : ∀ lo hi, StmtIn ment lo hi aStmt s → StmtIn ment lo hi aChild schild)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hret_al : aRet'.toNat % 8 = 0)
    (hret_lo : SL.lo ≤ aRet'.toNat) (hret_hi : aRet'.toNat + 24 ≤ sp.toNat)
    (hret_scrib : aRet'.toNat + 24 ≤ SL.lo ∨ sp'.toNat ≤ aRet'.toNat)
    (hSL_ram : 0x80000000 ≤ SL.lo) (hSL_win : tohostAddr + 16 ≤ SL.lo)
    (hSLhi_ram : SL.hi ≤ 0x100000000) :
    ExecGround ment SL A sp' aRet' aChild schild :=
  (hg.transport_offstack hspSL hmem).child_params hproj hspSL hsp'
    hret_al hret_lo hret_hi hret_scrib hSL_ram hSL_win hSLhi_ram


/-! ## Named child projections (the `exprIn_unary_child` family — Law 6) -/

theorem exprIn_binary_left {m : Mem} {lo hi a : Nat} {op : BinOp} {l r : Expr}
    (h : ExprIn m lo hi a (.binary op l r)) :
    ∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l := h.2.1

theorem exprIn_binary_right {m : Mem} {lo hi a : Nat} {op : BinOp} {l r : Expr}
    (h : ExprIn m lo hi a (.binary op l r)) :
    ∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r := h.2.2

theorem exprIn_logical_left {m : Mem} {lo hi a : Nat} {op : LogOp} {l r : Expr}
    (h : ExprIn m lo hi a (.logical op l r)) :
    ∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l := h.2.1

theorem exprIn_logical_right {m : Mem} {lo hi a : Nat} {op : LogOp} {l r : Expr}
    (h : ExprIn m lo hi a (.logical op l r)) :
    ∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r := h.2.2

theorem exprIn_assign_child {m : Mem} {lo hi a : Nat} {x : String} {e : Expr}
    (h : ExprIn m lo hi a (.assign x e)) :
    ∀ q, read64 m (a + 16) = some q → ExprIn m lo hi q e := h.2.2

theorem stmtIn_expr_child {m : Mem} {lo hi a : Nat} {e : Expr}
    (h : StmtIn m lo hi a (.expr e)) :
    ∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p e := h.2


/-- The window-wise variant of `evalGround_ast_read64_agree`: any in-node read
agrees along a per-region agreement closure (the `transport_via` shape). -/
theorem evalGround_ast_read64_agree_via {m m' : Mem} {SL : StackLayout}
    {A : Arena} {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (hg : EvalGround m SL A sp sret aExpr e)
    (hag : ∀ lo hi, AstRegionSpec m SL A sret.toNat aExpr e lo hi →
      ∀ a : Nat, lo ≤ a → a < hi → m[a]? = m'[a]?)
    {off : Nat} (hoff : off + 8 ≤ 40) :
    read64 m' (aExpr + off) = read64 m (aExpr + off) := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  have hnode := exprIn_node spec.nodes
  exact (read64_agreeP (P := fun k => lo ≤ k ∧ k < hi)
    (fun k hk => hag lo hi spec k hk.1 hk.2)
    (fun k hk => ⟨by have := hnode.lo_le; omega, by have := hnode.hi_ge; omega⟩)).symm

/-! ## The raw window-wise transport (arbitrary memory hops)

Consumers crossing a SUB-CALL (memory agrees only off stack ∪ arena ∪
sub-result windows) supply the two window agreements directly — the table
window (disjoint from all three by `tableStk`/`arenaTable` + the sub-result
slot living in the stack), and the AST region (stack/arena-disjoint by its
spec, keyed per witness). -/

theorem EvalGround.transport_via {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    (htab : ∀ a : Nat, jumpTableBase ≤ a → a < jumpTableBase + 44 → m[a]? = m'[a]?)
    (hast : ∀ lo hi, AstRegionSpec m SL A sret.toNat aExpr e lo hi →
      ∀ a : Nat, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    EvalGround m' SL A sp sret aExpr e where
  table := h.table.transport htab
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    exact ⟨lo, hi, spec.transport (hast lo hi spec)⟩⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_vi := h.arena_vi
  sret_inSL := h.sret_inSL
  sret_table_disjoint := h.sret_table_disjoint

theorem ExecGround.transport_via {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (htab : ∀ a : Nat, stmtJumpTableBase ≤ a → a < stmtJumpTableBase + 36 → m[a]? = m'[a]?)
    (hast : ∀ lo hi, StmtRegionSpec m SL A aRet.toNat aStmt s lo hi →
      ∀ a : Nat, lo ≤ a → a < hi → m[a]? = m'[a]?) :
    ExecGround m' SL A sp aRet aStmt s where
  table := h.table.transport htab
  table_stack := h.table_stack
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    exact ⟨lo, hi, spec.transport (hast lo hi spec)⟩⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  aret := h.aret
  aret_table_disjoint := h.aret_table_disjoint


end Vsa.Sim

#print axioms Vsa.Sim.EvalGround.child_at
#print axioms Vsa.Sim.ExecGround.child_at
#print axioms Vsa.Sim.evalGround_ast_read64_agree
#print axioms Vsa.Sim.execGround_ast_read64_agree
