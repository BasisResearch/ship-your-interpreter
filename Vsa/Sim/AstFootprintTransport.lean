import Vsa.Sim.AstTransport

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim

private theorem footprint_read {m m' : Mem} {P : Nat → Prop} {a p : Nat}
    (ha : AgreeP P m m') (hc : ∀ i, i < 8 → P (a + i))
    (hr : read64 m' a = some p) : read64 m a = some p :=
  (read64_agreeP ha hc).trans hr

/-- Agreement on the original footprint prevents any new pointer path.
The induction covers expressions, statements, arrays, parameters, and options. -/
theorem ExprFp.pullback {m m' : Mem} {P : Nat → Prop} {a k : Nat} {e : Expr}
    (h : ExprFp m' a e k) (ha : AgreeP P m m')
    (hc : ∀ j, ExprFp m a e j → P j) : ExprFp m a e k := by
  apply ExprFp.rec
    (motive_1 := fun a e k _ => (∀ j, ExprFp m a e j → P j) → ExprFp m a e k)
    (motive_2 := fun a n es k _ => (∀ j, ExprArrayFp m a n es j → P j) → ExprArrayFp m a n es k)
    (motive_3 := fun a n xs k _ => (∀ j, ParamsFp m a n xs j → P j) → ParamsFp m a n xs k)
    (motive_4 := fun a s k _ => (∀ j, StmtFp m a s j → P j) → StmtFp m a s k)
    (motive_5 := fun a s k _ => (∀ j, OptStmtFp m a s j → P j) → OptStmtFp m a s k)
    (motive_6 := fun a e k _ => (∀ j, OptExprFp m a e j → P j) → OptExprFp m a e k)
    (motive_7 := fun a n ss k _ => (∀ j, StmtArrayFp m a n ss j → P j) → StmtArrayFp m a n ss k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_  ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_  ?_ ?_  ?_ ?_ ?_ h hc
  · intro a e k hi hc
    exact .tag hi
  · intro a e k hi hc
    exact .off8 hi
  · intro a e k hi hc
    exact .off16 hi
  · intro a e k hi hc
    exact .off24 hi
  · intro a e k hi hc
    exact .off32 hi
  · intro a e s p k hs hr hi hc
    exact .str8 hs (footprint_read ha (fun i hi => hc _ (.off8 hi)) hr) hi
  · intro a e ec p k hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off8 hi)) hr
    exact .child8 hs hr0 (ih (fun j hj => hc j (.child8 hs hr0 hj)))
  · intro a e ec p k hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off16 hi)) hr
    exact .child16 hs hr0 (ih (fun j hj => hc j (.child16 hs hr0 hj)))
  · intro a e ec p k hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off24 hi)) hr
    exact .child24 hs hr0 (ih (fun j hj => hc j (.child24 hs hr0 hj)))
  · intro a e args argc k es hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off16 hi)) hr
    exact .argArr hs hr0 (ih (fun j hj => hc j (.argArr hs hr0 hj)))
  · intro a e params paramc k ps hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off16 hi)) hr
    exact .paramsArr hs hr0 (ih (fun j hj => hc j (.paramsArr hs hr0 hj)))
  · intro a e body k ss hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off32 hi)) hr
    exact .body32 hs hr0 (ih (fun j hj => hc j (.body32 hs hr0 hj)))
  · intro a n e es k hi hc
    exact .slot hi
  · intro a p n k e es hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.slot hi)) hr
    exact .elem hr0 (ih (fun j hj => hc j (.elem hr0 hj)))
  · intro a n k e es ht ih hc
    exact .tail (ih (fun j hj => hc j (.tail hj)))
  · intro a n x xs k hi hc
    exact .slot hi
  · intro a p n k x xs hr hi hc
    exact .str (footprint_read ha (fun i hi => hc _ (.slot hi)) hr) hi
  · intro a n k x xs ht ih hc
    exact .tail (ih (fun j hj => hc j (.tail hj)))
  · intro a s k hi hc
    exact .tag hi
  · intro a s k hi hc
    exact .off8 hi
  · intro a s k hi hc
    exact .off16 hi
  · intro a s k hi hc
    exact .off24 hi
  · intro a s k hi hc
    exact .off32 hi
  · intro a s x p k hs hr hi hc
    exact .str8 hs (footprint_read ha (fun i hi => hc _ (.off8 hi)) hr) hi
  · intro a s p k e hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off8 hi)) hr
    exact .expr8 hs hr0 (ih (fun j hj => hc j (.expr8 hs hr0 hj)))
  · intro a s p k e hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off16 hi)) hr
    exact .expr16 hs hr0 (ih (fun j hj => hc j (.expr16 hs hr0 hj)))
  · intro a s p k t hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off16 hi)) hr
    exact .stmt16 hs hr0 (ih (fun j hj => hc j (.stmt16 hs hr0 hj)))
  · intro a s p k t hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off24 hi)) hr
    exact .stmt24 hs hr0 (ih (fun j hj => hc j (.stmt24 hs hr0 hj)))
  · intro a s p k t hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off32 hi)) hr
    exact .stmt32 hs hr0 (ih (fun j hj => hc j (.stmt32 hs hr0 hj)))
  · intro a s stmts count k ss hs hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.off8 hi)) hr
    exact .blockArr hs hr0 (ih (fun j hj => hc j (.blockArr hs hr0 hj)))
  · intro a s os k hs ht ih hc
    exact .optStmt8 hs (ih (fun j hj => hc j (.optStmt8 hs hj)))
  · intro a s oe k hs ht ih hc
    exact .optExpr16 hs (ih (fun j hj => hc j (.optExpr16 hs hj)))
  · intro a s oe k hs ht ih hc
    exact .optExpr24 hs (ih (fun j hj => hc j (.optExpr24 hs hj)))
  · intro a s k hi hc
    exact .ptr hi
  · intro a p k s hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.ptr hi)) hr
    exact .child hr0 (ih (fun j hj => hc j (.child hr0 hj)))
  · intro a e k hi hc
    exact .ptr hi
  · intro a p k e hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.ptr hi)) hr
    exact .child hr0 (ih (fun j hj => hc j (.child hr0 hj)))
  · intro a n s ss k hi hc
    exact .slot hi
  · intro a p n k s ss hr ht ih hc
    have hr0 := footprint_read ha (fun i hi => hc _ (.slot hi)) hr
    exact .elem hr0 (ih (fun j hj => hc j (.elem hr0 hj)))
  · intro a n k s ss ht ih hc
    exact .tail (ih (fun j hj => hc j (.tail hj)))

/-- The protected expression footprint is equal in both memories. -/
theorem ExprFp.agree_iff {m m' : Mem} {P : Nat → Prop} {a k : Nat} {e : Expr}
    (ha : AgreeP P m m') (hc : ∀ j, ExprFp m a e j → P j) :
    ExprFp m a e k ↔ ExprFp m' a e k := by
  have back : ∀ j, ExprFp m' a e j → ExprFp m a e j :=
    fun _ h => h.pullback ha hc
  exact ⟨fun h => h.pullback ha.symm (fun j hj => hc j (back j hj)), back k⟩

#print axioms ExprFp.pullback
#print axioms ExprFp.agree_iff

end Vsa.Sim
