import Vsa.MemReprReadFields
import Vsa.Sim.Regions

namespace Vsa.MemRepr

/-- A nonempty covered read lies entirely on one side of an excluded interval. -/
theorem Covers.avoidsInterval {P : Nat → Prop} {a width lo hi : Nat}
    (h : Covers P a width) (hwidth : 0 < width) (hwindow : lo < hi)
    (hout : ∀ k, P k → ¬ (lo ≤ k ∧ k < hi)) :
    a + width ≤ lo ∨ hi ≤ a := by
  by_cases hleft : a + width ≤ lo
  · exact Or.inl hleft
  by_cases hright : hi ≤ a
  · exact Or.inr hright
  exfalso
  by_cases ha : a ≤ lo
  · have hp : P lo := by
      have hc := h (lo - a) (by omega)
      simpa [Nat.add_sub_of_le ha] using hc
    exact hout lo hp ⟨Nat.le_refl _, hwindow⟩
  · have hp : P a := by simpa using h 0 hwidth
    exact hout a hp ⟨by omega, by omega⟩

end Vsa.MemRepr

namespace Vsa.Sim
open Vsa.MemRepr Vsa.While Vsa.Alloc

/-- Bounds of one positive-width AST read, derived from shared-byte ownership. -/
structure AstReadGeometry (SL : StackLayout) (a width : Nat) : Prop where
  positive : 0 < width
  ram_lo : ramLo ≤ a
  ram_hi : a + width ≤ ramHi
  htif : a + width ≤ tohostAddr ∨ tohostAddr + 16 ≤ a
  outside_stack : ∀ k, a ≤ k → k < a + width → ¬ (SL.lo ≤ k ∧ k < SL.hi)

/-- Read geometry for a shared byte domain. Heap mutation preservation is
supplied separately by runtime ownership and the actual operation's frame. -/
structure SharedReadDomain (SL : StackLayout) (shared : Nat → Prop) : Prop where
  ram : ∀ k, shared k → ramLo ≤ k ∧ k < ramHi
  outside_htif : ∀ k, shared k → ¬ (tohostAddr ≤ k ∧ k < tohostAddr + 16)
  outside_stack : ∀ k, shared k → ¬ (SL.lo ≤ k ∧ k < SL.hi)

/-- A fixed AST subdomain inherits the runtime payload domain's read geometry. -/
theorem SharedReadDomain.restrict {SL : StackLayout} {shared ast : Nat → Prop}
    (h : SharedReadDomain SL shared) (ha : ∀ k, ast k → shared k) :
    SharedReadDomain SL ast :=
  ⟨fun k hk => h.ram k (ha k hk),
    fun k hk => h.outside_htif k (ha k hk),
    fun k hk => h.outside_stack k (ha k hk)⟩

/-- A stack-only memory change preserves every byte of the common read domain. -/
theorem SharedReadDomain.agree_stack {SL : StackLayout} {shared : Nat → Prop}
    {m m' : Mem} (h : SharedReadDomain SL shared)
    (hm : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) :
    ∀ k, shared k → m[k]? = m'[k]? :=
  fun k hk => hm k (h.outside_stack k hk)

/-- Exact positive-width coverage supplies one scalar read's geometry. -/
theorem AstReadGeometry.of_domain {SL : StackLayout} {shared : Nat → Prop}
    {a width : Nat} (h : SharedReadDomain SL shared)
    (hc : Covers shared a width) (hw : 0 < width) : AstReadGeometry SL a width := by
  have first := h.ram _ (hc 0 hw)
  have last := h.ram _ (hc (width - 1) (by omega))
  simp only [Nat.add_zero] at first
  refine ⟨hw, first.1, by omega, ?_, ?_⟩
  · exact hc.avoidsInterval hw (by omega) h.outside_htif
  · intro k hlo hhi
    have hk : shared k := by
      have hc' := hc (k - a) (by omega)
      simpa [Nat.add_sub_of_le hlo] using hc'
    exact h.outside_stack k hk

/-- The common domain covers every declared expression field. -/
theorem SharedReadDomain.expr_field {SL : StackLayout} {shared : Nat → Prop}
    {m : Mem} {a : Nat} {e : Expr} (h : SharedReadDomain SL shared)
    (hr : ExprReprWithin m shared a e) (f : ReadField) (hf : f ∈ exprReadFields e) :
    AstReadGeometry SL (a + f.offset) f.width :=
  .of_domain h (hr.fieldCovers f hf) f.positive

/-- The common domain covers every declared statement field. -/
theorem SharedReadDomain.stmt_field {SL : StackLayout} {shared : Nat → Prop}
    {m : Mem} {a : Nat} {s : Stmt} (h : SharedReadDomain SL shared)
    (hr : StmtReprWithin m shared a s) (f : ReadField) (hf : f ∈ stmtReadFields s) :
    AstReadGeometry SL (a + f.offset) f.width :=
  .of_domain h (hr.fieldCovers f hf) f.positive

/-- Exact read exclusion gives the interval form used by dispatch contracts. -/
theorem AstReadGeometry.stack_disjoint {SL : StackLayout} {a width : Nat}
    (h : AstReadGeometry SL a width) (hSL : SL.lo < SL.hi) :
    a + width ≤ SL.lo ∨ SL.hi ≤ a := by
  apply Covers.avoidsInterval (P := fun k => a ≤ k ∧ k < a + width)
    (fun i hi => ⟨by omega, by omega⟩) h.positive hSL
  intro k hk
  exact h.outside_stack k hk.1 hk.2

/-- Stack-only writes preserve an exactly bounded AST read. -/
theorem AstReadGeometry.readLE_offstack {SL : StackLayout} {a width sp : Nat}
    {m m' : Mem} (h : AstReadGeometry SL a width) (hsp : sp ≤ SL.hi)
    (hmem : ∀ k, ¬ (SL.lo ≤ k ∧ k < sp) → m'[k]? = m[k]?) :
    readLE m' a width = readLE m a width := by
  apply Covers.readLE_eq (P := fun k => a ≤ k ∧ k < a + width)
  · intro i hi
    exact ⟨by omega, by omega⟩
  · intro k hk
    apply hmem k
    intro hs
    exact h.outside_stack k hk.1 hk.2 ⟨hs.1, by omega⟩

#print axioms Vsa.MemRepr.Covers.avoidsInterval
#print axioms SharedReadDomain.restrict
#print axioms SharedReadDomain.agree_stack
#print axioms AstReadGeometry.of_domain
#print axioms SharedReadDomain.expr_field
#print axioms SharedReadDomain.stmt_field
#print axioms AstReadGeometry.stack_disjoint
#print axioms AstReadGeometry.readLE_offstack
end Vsa.Sim
