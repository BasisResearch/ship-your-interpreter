import Vsa.Sim.rows.AllocClosureInhab
import Vsa.Sim.AllocOff

/-!
# `ClosureBuildSupply` — inhabiting the closure build's memory premises

`rows/AllocClosureInhab.lean` fixed `AllocBuildEntry`'s memory premises, which
had been uninhabitable: they excluded the ARENA from their agreement, while the
store's frames and the `fn` AST node both live in it.  They now state agreement
off `BuildOff p sret`, the build's own write window.

Fixing a premise is not discharging it, so this module supplies the two repaired
fields from the ownership layer, which is what makes the repair worth having:

* `closureBuildOld_of_owned` gives `hOld` — the OLD store represented at the
  extended closure map in the post-build memory;
* `closureBuildExpr_of_owned` gives `hExprRepr` — the `fn` node still
  represented there.

Both go through `HeapOwned.ownedOff` (`Vsa/Sim/AllocOff.lean`): every owned
extent byte and every shared byte lies outside the stack region, the
allocator-private set and the fresh block, and the result slot is inside the
stack region, so all of them satisfy `BuildOff`.  The build writes only inside
that window, so nothing the store or the AST occupies can move.
-/

namespace Vsa.Sim

open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership

/-- The result slot is a caller stack slot, so `AllocOff` refines `BuildOff`. -/
theorem buildOff_of_allocOff {SL : StackLayout} {priv : Nat → Prop}
    {p : Nat} {sret : BitVec 64}
    (hsret : ∀ k, sret.toNat ≤ k → k < sret.toNat + 24 → SL.lo ≤ k ∧ k < SL.hi)
    {k : Nat} (h : AllocOff SL priv [(p, 16)] k) : BuildOff p sret k := by
  refine ⟨?_, ?_⟩
  · have := h.2.2 (p, 16) List.mem_cons_self
    change ¬ (p ≤ k ∧ k < p + 16) at this
    exact this
  · intro hin
    exact h.1 (hsret k hin.1 hin.2)

/-- **`hOld`, supplied.**  The old store survives the closure build at the
extended closure map: its bytes are owned or shared, hence outside the build's
write window, and `φc'` agrees with `φc` on the allocated prefix. -/
theorem closureBuildOld_of_owned
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φc' : Addr → Nat}
    {st : Vsa.While.St} {exts : List Extent} {alloc : Allocations}
    {shared readable writes priv : Nat → Prop}
    {mMalloc : Mem} {p : Nat} {sret : BitVec 64}
    (hown : HeapOwned A exts mMalloc φf φc alloc shared readable writes st.store)
    (hr : StoreRepr mMalloc N A φf φc st.store)
    (hwrites : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    (hpriv : ∀ e ∈ exts, ∀ k < e.2, ¬ priv (e.1 + k))
    (priv_arena : ∀ a, priv a → A.lo ≤ a ∧ a < A.hi)
    (arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (hA : A.contains p 16) (hf : ∀ e ∈ exts, ExtDisjoint (p, 16) e)
    (hsret : ∀ k, sret.toNat ≤ k → k < sret.toNat + 24 → SL.lo ≤ k ∧ k < SL.hi)
    (hext : PhiExtends φc φc' st.store.closures.size) :
    ∀ mpre : Mem, (∀ a : Nat, BuildOff p sret a → mpre[a]? = mMalloc[a]?) →
      StoreRepr mpre N A φf φc' st.store := by
  intro mpre hag
  have hoff : OwnedOff SL priv [(p, 16)] alloc shared :=
    hown.ownedOff hwrites hpriv priv_arena arena_stack (freshExtents_single hA hf)
  have hagP : AgreeP (BuildOff p sret) mMalloc mpre := fun a ha => (hag a ha).symm
  have hold : StoreRepr mpre N A φf φc st.store :=
    hown.store.repr_transport hr hagP
      (fun role q n hq k hk =>
        buildOff_of_allocOff hsret (hoff.alloc role q n hq k hk))
      (fun k hk => buildOff_of_allocOff hsret (hoff.shared k hk))
  exact storeRepr_phic_mono hown.store.valueClosures hext hold

/-- **`hExprRepr`, supplied.**  The `fn` node survives the build: its bytes are
shared (the parser's AST, covered by `StoreOwned.closureAsts` at the producer),
hence outside the build's write window. -/
theorem closureBuildExpr_of_owned
    {SL : StackLayout} {priv : Nat → Prop} {shared : Nat → Prop}
    {mMalloc : Mem} {p : Nat} {sret aExpr : BitVec 64} {e : Expr}
    (hrepr : ExprRepr mMalloc aExpr.toNat e)
    (hfp : ∀ k, ExprFp mMalloc aExpr.toNat e k → shared k)
    (hsharedOff : ∀ k, shared k → AllocOff SL priv [(p, 16)] k)
    (hsret : ∀ k, sret.toNat ≤ k → k < sret.toNat + 24 → SL.lo ≤ k ∧ k < SL.hi) :
    ∀ mpre : Mem, (∀ a : Nat, BuildOff p sret a → mpre[a]? = mMalloc[a]?) →
      ExprRepr mpre aExpr.toNat e := by
  intro mpre hag
  have hagP : AgreeP (BuildOff p sret) mMalloc mpre := fun a ha => (hag a ha).symm
  exact exprRepr_agreeP hagP
    (fun addr haddr => buildOff_of_allocOff hsret (hsharedOff addr (hfp addr haddr))) hrepr

#print axioms buildOff_of_allocOff
#print axioms closureBuildOld_of_owned
#print axioms closureBuildExpr_of_owned

end Vsa.Sim
