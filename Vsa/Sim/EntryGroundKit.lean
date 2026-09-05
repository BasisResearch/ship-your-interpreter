import Vsa.Sim.EntryGround
import Vsa.Sim.AstTransport

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

open LeanRV64DExecutable

/-- Every address in the stack interval has a stored byte. -/
def StackBytesPresent (m : Mem) (SL : StackLayout) : Prop :=
  ∀ k : Nat, SL.lo ≤ k → k < SL.hi → ∃ b : BitVec 8, m[k]? = some b

/-- The unary/binary arm frame retains the extra registers used by `env_set`. -/
theorem EvalEntry.envset_defined_frame
    {g g' : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {d env : Nat} {e : Expr}
    {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {cfg : Vsa.Machine.Config}
    (h : EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 cfg)
    (hframe : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false → g' R = g R) :
    ∃ v19 v20 v21 : BitVec 64,
      g' Register.x19 = some v19 ∧ g' Register.x20 = some v20 ∧
      g' Register.x21 = some v21 := by
  obtain ⟨v19, v20, v21, h19, h20, h21⟩ := h.envset_defined
  refine ⟨v19, v20, v21, ?_, ?_, ?_⟩
  · exact (hframe Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((h.frame Register.x19 (by decide)).symm.trans h19)
  · exact (hframe Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((h.frame Register.x20 (by decide)).symm.trans h20)
  · exact (hframe Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((h.frame Register.x21 (by decide)).symm.trans h21)

/-- Any 24-byte slot wholly inside the populated eval stack is readable. -/
theorem EvalGround.valueWordsTotal {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    {a : Nat} (hlo : SL.lo ≤ a) (hhi : a + 24 ≤ SL.hi) :
    ValueWordsTotal m a :=
  valueWordsTotal_of_interval h.stack_bytes hlo hhi

/-- Domain extension preserves the entry's populated stack. -/
theorem EvalGround.stack_bytes_extend {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e) (hext : MemExtends m m') :
    StackBytesPresent m' SL := by
  intro k hlo hhi
  obtain ⟨b, hb⟩ := h.stack_bytes k hlo hhi
  exact hext k b hb

/-- Any 24-byte slot wholly inside the populated exec stack is readable. -/
theorem ExecGround.valueWordsTotal {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    {a : Nat} (hlo : SL.lo ≤ a) (hhi : a + 24 ≤ SL.hi) :
    ValueWordsTotal m a :=
  valueWordsTotal_of_interval h.stack_bytes hlo hhi

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
    (hpop : StackBytesPresent ment SL)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    EvalGround ment SL A sp sret aExpr e :=
  hg.survive_stack htb hspSL hpop (fun k hk _ => (hmem k hk).symm)

theorem ExecGround.transport_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hspSL : sp.toNat ≤ SL.hi)
    (hpop : StackBytesPresent ment SL)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) :
    ExecGround ment SL A sp aRet aStmt s :=
  hg.survive_stack hspSL hpop (fun k hk _ => (hmem k hk).symm)

/-- The enclosing statement representation survives an off-stack memory
change.  The hereditary region in `ExecGround` supplies the exact footprint;
no root-only node window is assumed. -/
theorem ExecGround.stmtRepr_offstack {m0 ment : Mem} {SL : StackLayout}
    {A : Arena} {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    (hr : StmtRepr m0 aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ment[a]? = m0[a]?) :
    StmtRepr ment aStmt s := by
  obtain ⟨lo, hi, spec⟩ := hg.ast.region
  apply stmtRepr_agree_region (hin := spec.nodes) (hr := hr)
  intro a ha
  change lo ≤ a ∧ a < hi at ha
  obtain ⟨haLo, haHi⟩ := ha
  exact (hmem a (by
    intro hs
    obtain ⟨hsLo, hsHi⟩ := hs
    rcases spec.stack_disjoint with hd | hd <;> omega)).symm

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
  stack_bytes := h.stack_bytes
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
  arena_table := h.arena_table
  eval_call := h.eval_call.transport (fun _ _ => rfl)
  stack_bytes := h.stack_bytes
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

/-- Project a child statement while lowering the stack pointer and forwarding
the parent's existing return slot.  Unlike `child_params`, this is the ABI
shape used by `while`: the recursive body receives the same `aRet`, which may
sit above the parent's entry `sp` but remains outside the lowered scribble. -/
theorem ExecGround.child_sameRet {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    {sp' : BitVec 64} {aChild : Nat} {schild : Stmt}
    (hproj : ∀ lo hi, StmtIn m lo hi aStmt s →
      StmtIn m lo hi aChild schild)
    (hsp' : sp'.toNat ≤ sp.toNat) :
    ExecGround m SL A sp' aRet aChild schild where
  table := h.table
  table_stack := by
    rcases h.table_stack with ht | ht
    · exact Or.inl ht
    · exact Or.inr (by omega)
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    exact ⟨lo, hi,
      { nodes := hproj lo hi spec.nodes
        lo_ram := spec.lo_ram
        hi_ram := spec.hi_ram
        win := spec.win
        stack_disjoint := spec.stack_disjoint
        ret_disjoint := spec.ret_disjoint
        arena_disjoint := spec.arena_disjoint }⟩⟩
  arena_stack := by
    rcases h.arena_stack with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by omega)
  arena_code := h.arena_code
  arena_table := h.arena_table
  eval_call := h.eval_call.transport (fun _ _ => rfl)
  stack_bytes := h.stack_bytes
  aret :=
    { align := h.aret.align
      ram := h.aret.ram
      win := h.aret.win
      scribble_disjoint := by
        rcases h.aret.scribble_disjoint with hr | hr
        · exact Or.inl hr
        · exact Or.inr (by omega)
      inSL := h.aret.inSL }
  aret_table_disjoint := h.aret_table_disjoint

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
    (hpop : StackBytesPresent ment SL)
    (htb : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hsub_lo : SL.lo ≤ subsret.toNat) (hsub_hi : subsret.toNat + 24 ≤ sp.toNat) :
    EvalGround ment SL A sp' subsret aChild echild :=
  (hg.transport_offstack htb hspSL hpop hmem).child_params hproj htb hspSL hsp'
    hsub_lo hsub_hi

theorem ExecGround.child_at {m0 ment : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (hg : ExecGround m0 SL A sp aRet aStmt s)
    {sp' aRet' : BitVec 64} {aChild : Nat} {schild : Stmt}
    (hproj : ∀ lo hi, StmtIn ment lo hi aStmt s → StmtIn ment lo hi aChild schild)
    (hmem : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?)
    (hpop : StackBytesPresent ment SL)
    (hspSL : sp.toNat ≤ SL.hi)
    (hsp' : sp'.toNat ≤ sp.toNat)
    (hret_al : aRet'.toNat % 8 = 0)
    (hret_lo : SL.lo ≤ aRet'.toNat) (hret_hi : aRet'.toNat + 24 ≤ sp.toNat)
    (hret_scrib : aRet'.toNat + 24 ≤ SL.lo ∨ sp'.toNat ≤ aRet'.toNat)
    (hSL_ram : 0x80000000 ≤ SL.lo) (hSL_win : tohostAddr + 16 ≤ SL.lo)
    (hSLhi_ram : SL.hi ≤ 0x100000000) :
    ExecGround ment SL A sp' aRet' aChild schild :=
  (hg.transport_offstack hspSL hpop hmem).child_params hproj hspSL hsp'
    hret_al hret_lo hret_hi hret_scrib hSL_ram hSL_win hSLhi_ram

/-- The expression ground bundle for a while condition.  Its AST witness is a
projection of the enclosing statement region; all static eval geometry comes
from `EvalCallSupport`. -/
theorem ExecGround.whileCond_evalGround {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet spEval sret aStmt aCond : BitVec 64} {cnd : Expr} {body : Stmt}
    (h : ExecGround m SL A sp aRet aStmt.toNat (.whileStmt cnd body))
    (hread : read64 m (aStmt.toNat + 8) = some aCond.toNat)
    (hspEval : spEval.toNat ≤ sp.toNat)
    (hsret : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) :
    EvalGround m SL A spEval sret aCond.toNat cnd := by
  obtain ⟨_hcode, _hvint, _htruthy, _hint, _hnbs, htable⟩ :=
    h.eval_call.pins m (fun _ _ => rfl)
  refine
    { table := htable
      stack_bytes := h.stack_bytes
      ast := ?_
      arena_stack := ?_
      arena_code := h.eval_call.arena_code
      arena_vi := by
        rcases h.eval_call.arena_vi with hd | hd
        · exact Or.inl hd
        · exact Or.inr (by omega)
      sret_inSL := hsret
      sret_table_disjoint := ?_ }
  · obtain ⟨lo, hi, hr⟩ := h.ast.region
    refine ⟨lo, hi, ?_⟩
    exact
      { nodes := hr.nodes.2.1 aCond.toNat hread
        lo_ram := hr.lo_ram
        hi_ram := hr.hi_ram
        win := hr.win
        stack_disjoint := hr.stack_disjoint
        sret_disjoint := by
          rcases hr.stack_disjoint with hd | hd <;> omega
        arena_disjoint := hr.arena_disjoint }
  · rcases h.arena_stack with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by omega)
  · rcases h.eval_call.table_stack with ht | ht
    · right
      simp only [jumpTableBase] at ht ⊢
      omega
    · left
      simp only [jumpTableBase] at ht ⊢
      omega


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

/-- WAVE 47i: the `.call` callee projection (the arm-dispatch conduits' child). -/
theorem exprIn_call_callee {m : Mem} {lo hi a : Nat} {f : Expr} {args : List Expr}
    (h : ExprIn m lo hi a (.call f args)) :
    ∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p f := h.2.1

/-- **WAVE 47i: child node at the SAME windows** (`sp`/`sret` unchanged): only
the AST node moves, by the hereditary `ExprIn` projection — every window/
sret/arena fact carries verbatim.  `child_params` cannot express this (it
re-derives the sret facts from `subsret + 24 ≤ sp`, false for the parent's
own result slot, which sits ABOVE `sp`). -/
theorem EvalGround.child_node {m : Mem} {SL : StackLayout} {A : Arena}
    {sp sret : BitVec 64} {aExpr : Nat} {e : Expr}
    (h : EvalGround m SL A sp sret aExpr e)
    {aChild : Nat} {echild : Expr}
    (hproj : ∀ lo hi, ExprIn m lo hi aExpr e → ExprIn m lo hi aChild echild) :
    EvalGround m SL A sp sret aChild echild where
  table := h.table
  stack_bytes := h.stack_bytes
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    exact ⟨lo, hi, ⟨hproj lo hi spec.nodes, spec.lo_ram, spec.hi_ram, spec.win,
      spec.stack_disjoint, spec.sret_disjoint, spec.arena_disjoint⟩⟩⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_vi := h.arena_vi
  sret_inSL := h.sret_inSL
  sret_table_disjoint := h.sret_table_disjoint

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
      ∀ a : Nat, lo ≤ a → a < hi → m[a]? = m'[a]?)
    (hpop : StackBytesPresent m' SL) :
    EvalGround m' SL A sp sret aExpr e where
  table := h.table.transport htab
  stack_bytes := hpop
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
      ∀ a : Nat, lo ≤ a → a < hi → m[a]? = m'[a]?)
    (heval : ∀ a : Nat, EvalCallFootprint a → m'[a]? = m[a]?)
    (hpop : StackBytesPresent m' SL) :
    ExecGround m' SL A sp aRet aStmt s where
  table := h.table.transport htab
  table_stack := h.table_stack
  ast := ⟨by
    obtain ⟨lo, hi, spec⟩ := h.ast.region
    exact ⟨lo, hi, spec.transport (hast lo hi spec)⟩⟩
  arena_stack := h.arena_stack
  arena_code := h.arena_code
  arena_table := h.arena_table
  eval_call := h.eval_call.transport heval
  stack_bytes := hpop
  aret := h.aret
  aret_table_disjoint := h.aret_table_disjoint

/-- Transport an enclosing statement ground bundle across a recursive eval
exit.  The eval result window lies in the statement stack, while the statement
table and AST are disjoint from both the stack and allocation arena. -/
theorem ExecGround.transport_evalExit {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet sret : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hsret : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ sp.toNat)
    (hpop : StackBytesPresent m' SL)
    (hframe : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ m'[a]? = m[a]?) :
    ExecGround m' SL A sp aRet aStmt s := by
  apply h.transport_via
  · intro a ha0 ha1
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases h.table_stack with ht | ht <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases h.arena_table with ht | ht <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso
      rcases h.table_stack with ht | ht <;> omega
    · exact heq.symm
  · intro lo hi hspec a ha0 ha1
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases hspec.stack_disjoint with hs | hs <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases hspec.arena_disjoint with hs | hs <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso
      rcases hspec.stack_disjoint with hd | hd <;> omega
    · exact heq.symm
  · intro a ha
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases ha with he | hv | ht
      · rcases h.eval_call.code_stack with hd | hd <;> omega
      · rcases h.eval_call.vi_stack with hd | hd <;> omega
      · rcases h.eval_call.table_stack with hd | hd <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases ha with he | hv | ht
      · rcases h.eval_call.arena_code with hd | hd <;> omega
      · rcases h.eval_call.arena_vi with hd | hd <;> omega
      · rcases h.eval_call.arena_table with hd | hd <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso; omega
    · exact heq
  · exact hpop

/-- Transport an enclosing statement ground bundle across a recursive
statement exit.  The only extra non-frame window is the enclosing retslot,
already disjoint from the statement table and AST in `ExecGround`. -/
theorem ExecGround.transport_execExit {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hpop : StackBytesPresent m' SL)
    (hframe : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ m'[a]? = m[a]?) :
    ExecGround m' SL A sp aRet aStmt s := by
  apply h.transport_via
  · intro a ha0 ha1
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases h.table_stack with ht | ht <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases h.arena_table with ht | ht <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso
      rcases h.aret_table_disjoint with ht | ht <;> omega
    · exact heq.symm
  · intro lo hi hspec a ha0 ha1
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases hspec.stack_disjoint with hs | hs <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases hspec.arena_disjoint with hs | hs <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso
      rcases hspec.ret_disjoint with hd | hd <;> omega
    · exact heq.symm
  · intro a ha
    have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
      intro hc
      rcases ha with he | hv | ht
      · rcases h.eval_call.code_stack with hd | hd <;> omega
      · rcases h.eval_call.vi_stack with hd | hd <;> omega
      · rcases h.eval_call.table_stack with hd | hd <;> omega
    have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      intro hc
      rcases ha with he | hv | ht
      · rcases h.eval_call.arena_code with hd | hd <;> omega
      · rcases h.eval_call.arena_vi with hd | hd <;> omega
      · rcases h.eval_call.arena_table with hd | hd <;> omega
    rcases hframe a hstk harena with hs | heq
    · exfalso
      have hr := h.aret.inSL
      rcases ha with he | hv | ht
      · rcases h.eval_call.code_stack with hd | hd <;> omega
      · rcases h.eval_call.vi_stack with hd | hd <;> omega
      · rcases h.eval_call.table_stack with hd | hd <;> omega
    · exact heq
  · exact hpop

/-- Transport the enclosing statement representation across a recursive eval
exit using the hereditary AST region carried by `ExecGround`. -/
theorem ExecGround.stmtRepr_evalExit {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet sret : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hr : StmtRepr m aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hsret : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ sp.toNat)
    (hframe : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ m'[a]? = m[a]?) :
    StmtRepr m' aStmt s := by
  obtain ⟨lo, hi, spec⟩ := h.ast.region
  apply stmtRepr_agree_region (hin := spec.nodes) (hr := hr)
  intro a ha
  change lo ≤ a ∧ a < hi at ha
  have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
    intro hc
    rcases spec.stack_disjoint with hd | hd <;> omega
  have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
    intro hc
    rcases spec.arena_disjoint with hd | hd <;> omega
  rcases hframe a hstk harena with hs | heq
  · exfalso
    rcases spec.stack_disjoint with hd | hd <;> omega
  · exact heq.symm

/-- Transport the enclosing statement representation across a recursive
statement exit. -/
theorem ExecGround.stmtRepr_execExit {m m' : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet : BitVec 64} {aStmt : Nat} {s : Stmt}
    (h : ExecGround m SL A sp aRet aStmt s)
    (hr : StmtRepr m aStmt s)
    (hsp : sp.toNat ≤ SL.hi)
    (hframe : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ m'[a]? = m[a]?) :
    StmtRepr m' aStmt s := by
  obtain ⟨lo, hi, spec⟩ := h.ast.region
  apply stmtRepr_agree_region (hin := spec.nodes) (hr := hr)
  intro a ha
  change lo ≤ a ∧ a < hi at ha
  have hstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
    intro hc
    rcases spec.stack_disjoint with hd | hd <;> omega
  have harena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
    intro hc
    rcases spec.arena_disjoint with hd | hd <;> omega
  rcases hframe a hstk harena with hs | heq
  · exfalso
    rcases spec.ret_disjoint with hd | hd <;> omega
  · exact heq.symm


end Vsa.Sim

#print axioms Vsa.Sim.EvalGround.child_at
#print axioms Vsa.Sim.ExecGround.child_at
#print axioms Vsa.Sim.evalGround_ast_read64_agree
#print axioms Vsa.Sim.execGround_ast_read64_agree
