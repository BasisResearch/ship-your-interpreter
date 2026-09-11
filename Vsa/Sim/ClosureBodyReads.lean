import Vsa.Sim.ClosureCallData
import Vsa.Sim.SeqSuffixGroundBlock
import Vsa.Sim.ClosureParamFoldBody

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Recover hereditary read ownership from the closure's stored AST footprint. -/
private theorem stmt_owned {m : Mem} {shared : Nat → Prop} {a : Nat} {s : Stmt}
    (h : StmtRepr m a s) (covered : ∀ k, StmtFp m a s k → shared k) :
    StmtReprWithin m shared a s := by
  apply StmtRepr.rec
    (motive_1 := fun a e _ => (∀ k, ExprFp m a e k → shared k) → ExprReprWithin m shared a e)
    (motive_2 := fun a n es _ => (∀ k, ExprArrayFp m a n es k → shared k) → ExprArrayReprWithin m shared a n es)
    (motive_3 := fun a n xs _ => (∀ k, ParamsFp m a n xs k → shared k) → ParamsReprWithin m shared a n xs)
    (motive_4 := fun a s _ => (∀ k, StmtFp m a s k → shared k) → StmtReprWithin m shared a s)
    (motive_5 := fun a s _ => (∀ k, OptStmtFp m a s k → shared k) → OptStmtReprWithin m shared a s)
    (motive_6 := fun a e _ => (∀ k, OptExprFp m a e k → shared k) → OptExprReprWithin m shared a e)
    (motive_7 := fun a n ss _ => (∀ k, StmtArrayFp m a n ss k → shared k) → StmtArrayReprWithin m shared a n ss)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h covered
  all_goals
    intros
    intro coverage
    constructor
    all_goals first
      | assumption
      | (apply_assumption; intro k hk; apply coverage; first
          | exact ExprFp.child8 (by constructor) (by assumption) hk
          | exact ExprFp.child16 (by constructor) (by assumption) hk
          | exact ExprFp.child24 (by constructor) (by assumption) hk
          | exact ExprFp.argArr (by constructor) (by assumption) hk
          | exact ExprFp.paramsArr (by constructor) (by assumption) hk
          | exact ExprFp.body32 (by constructor) (by assumption) hk
          | exact ExprArrayFp.elem (by assumption) hk
          | exact ExprArrayFp.tail hk
          | exact ParamsFp.tail hk
          | exact StmtFp.expr8 (by constructor) (by assumption) hk
          | exact StmtFp.expr16 (by constructor) (by assumption) hk
          | exact StmtFp.stmt16 (by constructor) (by assumption) hk
          | exact StmtFp.stmt24 (by constructor) (by assumption) hk
          | exact StmtFp.stmt32 (by constructor) (by assumption) hk
          | exact StmtFp.blockArr (by constructor) (by assumption) hk
          | exact StmtFp.optStmt8 (by constructor) hk
          | exact StmtFp.optExpr16 (by constructor) hk
          | exact StmtFp.optExpr24 (by constructor) hk
          | exact OptStmtFp.child (by assumption) hk
          | exact OptExprFp.child (by assumption) hk
          | exact StmtArrayFp.elem (by assumption) hk
          | exact StmtArrayFp.tail hk)
      | (intro i hi; apply coverage; first
          | exact ExprFp.tag hi
          | exact ExprFp.off8 (by omega)
          | exact ExprFp.off16 (by omega)
          | exact ExprFp.off24 (by omega)
          | exact ExprFp.off32 (by omega)
          | exact ExprArrayFp.slot hi
          | exact ParamsFp.slot hi
          | exact StmtFp.tag hi
          | exact StmtFp.off8 (by omega)
          | exact StmtFp.off16 (by omega)
          | exact StmtFp.off24 (by omega)
          | exact StmtFp.off32 (by omega)
          | exact OptStmtFp.ptr hi
          | exact OptExprFp.ptr hi
          | exact StmtArrayFp.slot hi)
      | (refine ⟨by assumption, ?_⟩; intro i hi; apply coverage; first
          | exact ExprFp.str8 (by constructor) (by assumption) hi
          | exact ParamsFp.str (by assumption) hi
          | exact StmtFp.str8 (by constructor) (by assumption) hi)

/-- The function's actual body pointer selects an owned block and all its children. -/
theorem ClosureFnReads.body_owned {m : Mem} {shared : Nat → Prop} {fn names body : Nat}
    {cd : ClosureData} (h : ClosureFnReads m shared fn names body cd) :
    StmtReprWithin m shared body (.block cd.body) := stmt_owned h.bodyRepr h.bodyFootprint

private theorem array_count {m : Mem} {shared : Nat → Prop} {a n : Nat} {ss : List Stmt}
    (h : StmtArrayReprWithin m shared a n ss) : n = ss.length := by
  induction ss generalizing a n with
  | nil => cases h; rfl
  | cons s ss ih =>
    cases h with
    | cons _ _ _ tail => exact congrArg Nat.succ (ih tail)

/-- The stored body determines its header, owned suffix, and execution resources. -/
theorem ClosureFnReads.body_data
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {shared : Nat → Prop}
    {store : Store} {ca fn names body d : Nat} {cd : ClosureData}
    {sp interp : BitVec 64} {before : Config}
    (h : ClosureFnReads before.σ.mem shared fn names body cd)
    (source : store.closures[ca]? = some cd)
    (bodies : StoreBodiesBound store perCallBudget)
    (ground : ExecGround before.σ.mem SL A sp (sp + 144#64) body (.block cd.body))
    (budget : StackOK SL sp (perCallBudget + (maxCallDepth - d) * perCallBudget + 1088))
    (placement : BindingArena A SL) (fnBound : fn < 2^64) (bodyAlign : body % 4 = 0)
    (present : EnvDefineSavedPresent before.σ.regs.get?)
    (interpReg : before.σ.regs.get? Register.x18 = some interp) :
    ∃ base, ClosureParam.FoldBodyData N A SL shared store d cd.body sp
      (BitVec.ofNat 64 fn) (BitVec.ofNat 64 body) base interp before := by
  have fnNat : (BitVec.ofNat 64 fn).toNat = fn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fnBound]
  have bodyNat : (BitVec.ofNat 64 body).toNat = body := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ h.bodyRead)]
  have bodyBound := bodies ca cd source
  have childBudget : StackOK SL sp
      (Stmt.stackNeedList cd.body + (maxCallDepth - d) * perCallBudget + 1088) :=
    StackOK.mono (by have := bodyBound.1; omega) budget
  have owned := h.body_owned
  cases owned with
  | block tag tagCovered baseRead baseCovered countRead countCovered array =>
    rename_i base count
    have length := array_count array
    have project (lo hi : Nat) (nodes : StmtIn before.σ.mem lo hi body (.block cd.body)) :=
      nodes.2 _ baseRead
    have suffix := SeqSuffixGround.of_parent_array ground (Nat.le_refl _) array.erase
      project childBudget bodyBound.2
    obtain ⟨lo, hi, region⟩ := ground.ast.region
    have node : NodeIn lo hi body := region.nodes.1
    have countBound : cd.body.length < 2^31 := by
      cases eq : cd.body with
      | nil => simp
      | cons s ss =>
        have nodes := project lo hi region.nodes
        rw [eq] at nodes
        have range := stmtsIn_range nodes (by intro bad; cases bad)
        have := region.hi_ram
        omega
    have baseNat : (BitVec.ofNat 64 base).toNat = base := by
      exact Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ baseRead)
    refine ⟨BitVec.ofNat 64 base,
      { bodyRead := by rw [fnNat, bodyNat]; exact h.bodyRead
        bodyCovered := by rw [fnNat]; exact h.bodyCovered
        baseRead := by rw [bodyNat, baseNat]; exact baseRead
        countRead := by rw [bodyNat]; simpa only [length] using countRead
        countBound := countBound
        suffix := ?_
        resources :=
          { baseCovered := by rw [bodyNat]; exact baseCovered
            countCovered := by rw [bodyNat]; exact countCovered
            arenaBelow := placement.upper
            bodyLo := by rw [bodyNat]; have := node.lo_le; have := region.lo_ram; omega
            bodyHi := by rw [bodyNat]; have := node.hi_ge; have := region.hi_ram; omega
            bodyWin := by rw [bodyNat]; have := node.lo_le; have := region.win; omega
            bodyAlign := by rw [bodyNat]; exact bodyAlign
            spill9 := ?_, spill20 := ?_, spill21 := ?_ }
        interpReg := interpReg, storeBodies := bodies }⟩
    · rw [baseNat]
      exact ⟨by simpa only [length] using array, suffix⟩
    · exact Option.isSome_iff_exists.mp present.s1
    · exact Option.isSome_iff_exists.mp present.s4
    · exact Option.isSome_iff_exists.mp present.s5

end Vsa.Sim
