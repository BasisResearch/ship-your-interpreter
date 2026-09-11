import Vsa.Sim.CallArgIteration
import Vsa.MemReprReadArrays

namespace Vsa.Sim.CallArgStage

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The call's hereditary AST and argument budgets at the actual child result slot. -/
structure Ground (m : Mem) (SL : StackLayout) (A : Arena) (sp node : BitVec 64)
    (d : Nat) (callee : Expr) (args : List Expr) : Prop where
  ground : EvalGround m SL A sp (sp + 64#64) node.toNat (.call callee args)
  budget : StackOK SL sp (Expr.stackNeedList args + (maxCallDepth - d) * perCallBudget + 1088)
  bodies : Expr.bodiesBoundList perCallBudget args = true

private theorem region_get {m : Mem} {lo hi a : Nat} {args : List Expr}
    (h : ExprsIn m lo hi a args) (index : Nat) (bound : index < args.length) :
    CellIn lo hi (a + 8 * index) ∧
      ∀ p, read64 m (a + 8 * index) = some p → ExprIn m lo hi p args[index] := by
  induction args generalizing a index with
  | nil => simp at bound
  | cons e es ih =>
    cases index with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using And.intro h.1 h.2.1
    | succ i =>
      have tail := ih h.2.2 i (by simpa using bound)
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.getElem_cons_succ] using tail

private theorem body_get {args : List Expr} {P : Nat}
    (h : Expr.bodiesBoundList P args = true) (index : Nat) (bound : index < args.length) :
    Expr.bodiesBound P args[index] = true := by
  induction args generalizing index with
  | nil => simp at bound
  | cons e es ih =>
    have both : e.bodiesBound P = true ∧ Expr.bodiesBoundList P es = true := by
      simpa only [Expr.bodiesBoundList, Bool.and_eq_true] using h
    cases index with
    | zero => exact both.1
    | succ i => exact ih both.2 i (by simpa using bound)

/-- The indexed represented argument supplies both reads and its recursive entry ground. -/
structure Selection (m : Mem) (shared : Nat → Prop) (SL : StackLayout) (A : Arena)
    (sp node base child : BitVec 64) (d index count : Nat) (e : Expr) : Prop where
  baseRead : read64 m (node.toNat + 16) = some base.toNat
  childRead : read64 m (base.toNat + 8 * index) = some child.toNat
  geometry : Geometry node base sp index count
  ground : CallExprGround m SL A sp (sp + 64#64) d child.toNat e
  ast : ExprReprWithin m shared child.toNat e

/-- Select an argument from the actual owned call AST, without a child-read supplier. -/
theorem Ground.select {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {A : Arena}
    {sp node : BitVec 64} {d : Nat} {callee : Expr} {args : List Expr}
    (h : Ground m SL A sp node d callee args)
    (ast : ExprReprWithin m shared node.toNat (.call callee args))
    (caller : BinaryPrefix.Geometry node sp) (index : Nat) (bound : index < args.length)
    (countBound : args.length ≤ 32) :
    ∃ base child, Selection m shared SL A sp node base child d index args.length args[index] := by
  obtain ⟨base, baseRead, array⟩ : ∃ base, read64 m (node.toNat + 16) = some base ∧
      ExprArrayReprWithin m shared base args.length args := by
    cases ast with
    | call _ _ _ _ _ baseRead _ _ _ _ array =>
      have length := array.erase.index_eq_length
      exact ⟨_, baseRead, length ▸ array⟩
  obtain ⟨child, cell⟩ := array.pointers.get index bound
  have baseNat : (BitVec.ofNat 64 base).toNat = base :=
    Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ baseRead)
  have childNat : (BitVec.ofNat 64 child).toNat = child :=
    Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ cell.read)
  have projection (lo hi : Nat) (region : ExprIn m lo hi node.toNat (.call callee args)) :
      CellIn lo hi (base + 8 * index) ∧ ExprIn m lo hi child args[index] := by
    have selected := region_get (region.2.2 base baseRead) index bound
    exact ⟨selected.1, selected.2 child cell.read⟩
  obtain ⟨lo, hi, region⟩ := h.ground.ast.region
  have cellBounds := (projection lo hi region.nodes).1
  have cellLo := cellBounds.lo_le
  have cellHi := cellBounds.hi_ge
  refine ⟨BitVec.ofNat 64 base, BitVec.ofNat 64 child,
    { baseRead := by rw [baseNat]; exact baseRead
      childRead := by rw [baseNat, childNat]; exact cell.read
      geometry :=
        { caller := caller, indexBound := bound, countBound := countBound
          cellLo := by rw [baseNat]; have := region.lo_ram; omega
          cellHi := by rw [baseNat]; have := region.hi_ram; omega
          cellHtif := by rw [baseNat]; have := region.win; omega }
      ground :=
        { ground := by rw [childNat]; exact h.ground.child_node (fun lo hi hin => (projection lo hi hin).2)
          budget := h.budget.mono (by
            have member := Expr.stackNeedList_mem_le (List.getElem_mem bound)
            omega)
          bodies := body_get h.bodies index bound }
      ast := by rw [childNat]; exact cell.target }⟩

/-- Child allocation and caller writes preserve the full argument source ground. -/
theorem Ground.transport_heap_stack
    {m m' : Mem} {SL : StackLayout} {A : Arena} {sp node : BitVec 64}
    {d : Nat} {callee : Expr} {args : List Expr} (h : Ground m SL A sp node d callee args)
    (presence : MemExtends m m')
    (frame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) → m[k]? = m'[k]?) :
    Ground m' SL A sp node d callee args := by
  refine { ground := h.ground.transport_via ?_ ?_ ?_ ?_, budget := h.budget, bodies := h.bodies }
  · intro k hlo hhi
    apply frame k
    · have := h.ground.eval_call.table_stack; omega
    · have off : A.hi ≤ jumpTableBase ∨ jumpTableBase + 44 ≤ A.lo :=
        h.ground.eval_call.image.arena_disjoint (by decide) (by decide)
      omega
  · intro lo hi region k hlo hhi
    exact frame k (by have := region.stack_disjoint; omega) (by have := region.arena_disjoint; omega)
  · apply h.ground.eval_call.transport
    intro k hk
    exact (frame k (h.ground.eval_call.outsideStack hk) (h.ground.eval_call.outsideArena hk)).symm
  · intro k hlo hhi
    obtain ⟨b, hb⟩ := h.ground.stack_bytes k hlo hhi
    exact presence k b hb

end Vsa.Sim.CallArgStage
