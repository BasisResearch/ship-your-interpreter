import Vsa.Sim.AstTransport
import Vsa.Sim.LoopStep

/-!
# Layer-4 — AST-repr survival across in-stack-window writes (the shared loop gap)

This module lands the ONE reusable transport that gates all four loop-shape body
oracles (`seq`/`while`/`for`/`args`). Every loop iteration spills its counter
`i` (`sd i, k(sp)` at some slot inside `[SL.lo, sp)`) and, more generally, may
scribble anywhere in the stack window `[SL.lo, sp)` or the arena `[A.lo, A.hi)`.
The block do-while body reads the current statement's `StmtRepr` (`stmts[i]`) at
the loop head; that `StmtRepr` must SURVIVE the iteration's writes so the next
iteration (and the recursive `exec_stmt` on `stmts[i]`) still sees a valid AST.

The generic per-node transport already exists (`AstTransport.stmtRepr_agreeP` /
`exprRepr_agreeP`, keyed on the footprint predicate `StmtFp`/`ExprFp`). What the
consumers repeatedly re-derived by hand — and what `ExecDispatch.execPrologue`
pushes to its caller as the raw `hfpDisj` obligation — is the *composition*:

> a write landing entirely inside `[SL.lo, sp)` (∪ the arena) preserves any
> `StmtRepr`/`ExprRepr` whose footprint is disjoint from that window.

The AST lives in the read-only script region (`.rodata`, above `sp` or below
`SL.lo`), so its footprint never meets the stack window — that disjointness is
`hfpDisj`, a purely geometric fact the loop-head geometry (`ExecStepGeom`)
already carries per node. This file states the survival ONCE, in two forms:

* `stmtRepr_survives_stackWrite` / `exprRepr_survives_stackWrite` — for a memory
  pair `m`, `m'` that already agrees off the stack window (the caller supplies
  `AgreeP (∉ [SL.lo,sp))`), given the footprint is stack-window-disjoint.
* `stmtRepr_survives_writeLog` / `exprRepr_survives_writeLog` — for the concrete
  reflected loop-body `writeLog` whose windows are `WinsInSA` (every store in the
  stack window or arena), discharging the agreement internally via
  `writeLog_agreeP_disjoint` + `wlogM_width`. This is the form the seq/while/for/
  args body oracles consume directly.

ONE lemma, every spill site, all four loops. NO `sorry`/`axiom`/`native_decide`/
`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc (StackLayout)
open Vsa.RuntimeRepr (Arena)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-! ## The stack window and its complement predicate -/

/-- The C stack window `[SL.lo, sp)` — where callee frames and spills live. Any
runtime write of a loop iteration lands here (or in the heap arena); the AST
script region is disjoint from it. -/
def StackWindow (SL : StackLayout) (sp : Nat) : Nat → Prop :=
  fun a => SL.lo ≤ a ∧ a < sp

/-- The complement footprint predicate: addresses OUTSIDE the stack window. The
AST script region satisfies this; it is the `P` we transport `*Repr` along. -/
def OffStackWindow (SL : StackLayout) (sp : Nat) : Nat → Prop :=
  fun a => ¬ (SL.lo ≤ a ∧ a < sp)

/-! ## Core transport: off-window agreement + off-window footprint ⇒ survival

These are the thin, reusable wrappers over `AstTransport.stmtRepr_agreeP` /
`exprRepr_agreeP` with `P := OffStackWindow SL sp`. The caller provides:
* `hagree` — the two memories agree everywhere off the stack window (any write
  confined to `[SL.lo, sp)` gives this, via `writeLog_agreeP_disjoint` below);
* `hfpDisj` — the node's AST footprint is disjoint from the stack window (the
  geometric "the AST lives in the script region" fact, carried per node by the
  loop-head geometry). -/

/-- **`StmtRepr` survives any write confined to the stack window.** The exemplar
lemma: `stmts[i]`'s AST representation is preserved across the `sd i` counter
spill (and every other in-window store). Serves every loop shape's body oracle. -/
theorem stmtRepr_survives_stackWrite
    {SL : StackLayout} {sp : Nat} {m m' : Mem} {a : Nat} {s : Stmt}
    (hagree : AgreeP (OffStackWindow SL sp) m m')
    (hfpDisj : ∀ addr, StmtFp m a s addr → ¬ (SL.lo ≤ addr ∧ addr < sp))
    (hs : StmtRepr m a s) : StmtRepr m' a s :=
  stmtRepr_agreeP hagree hfpDisj hs

/-- **`ExprRepr` survives any write confined to the stack window.** The `Expr`
twin (loop conditions `while c`, `for c`, arg expressions `f(args…)` read their
`ExprRepr` across the same spill). -/
theorem exprRepr_survives_stackWrite
    {SL : StackLayout} {sp : Nat} {m m' : Mem} {a : Nat} {e : Expr}
    (hagree : AgreeP (OffStackWindow SL sp) m m')
    (hfpDisj : ∀ addr, ExprFp m a e addr → ¬ (SL.lo ≤ addr ∧ addr < sp))
    (he : ExprRepr m a e) : ExprRepr m' a e :=
  exprRepr_agreeP hagree hfpDisj he

/-! ## Off-window agreement from an in-window `writeLog`

`writeLog_agreeP_disjoint` (`BlockAdapter`) already gives agreement off every
store window; here we specialise it to the stack-window complement using the
concrete loop-body geometry: every store lies in `[SL.lo, sp)` or the arena
(`WinsInSA`), and every reflected store has width 1/4/8 (`wlogM_width`). For the
AST survival we need agreement OFF the stack window — so we also require the
arena to be disjoint from the AST footprint, threaded via the same off-window
predicate (the AST is disjoint from BOTH stack and arena; the caller's
`hfpDisj'` states off-both). -/

/-- Off-window (stack ∪ arena) complement predicate — the AST script region
avoids the stack window AND the heap arena. -/
def OffStackArena (SL : StackLayout) (sp : Nat) (A : Arena) : Nat → Prop :=
  fun a => ¬ (SL.lo ≤ a ∧ a < sp) ∧ ¬ (A.lo ≤ a ∧ a < A.hi)

/-- **The entry memory agrees with its post-`writeLog` image everywhere off the
stack window and arena**, provided every store window is `WinsInSA` (in the
stack window or the arena) and every store has width 1/4/8. This is the
agreement `stmtRepr_survives_stackWrite` consumes, produced from the reflected
loop-body log with no per-site hand-threading. -/
theorem writeLog_agreeP_offStackArena
    {SL : StackLayout} {sp : Nat} {A : Arena}
    (m : Mem) (log : List WEntry)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hwins : WinsInSA SL sp A log) :
    AgreeP (OffStackArena SL sp A) m (writeLog m log) := by
  refine writeLog_agreeP_disjoint m log (OffStackArena SL sp A) hw ?_
  intro k hk e he
  -- `k` is off both the stack window and the arena; `e`'s window is in one of them.
  obtain ⟨hkStk, hkArena⟩ := hk
  -- turn the ¬-conjunctions into disjunctive bounds omega can consume
  have hkS : k < SL.lo ∨ sp ≤ k := by
    by_cases h1 : SL.lo ≤ k
    · by_cases h2 : k < sp
      · exact absurd ⟨h1, h2⟩ hkStk
      · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hkA : k < A.lo ∨ A.hi ≤ k := by
    by_cases h1 : A.lo ≤ k
    · by_cases h2 : k < A.hi
      · exact absurd ⟨h1, h2⟩ hkArena
      · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  rcases hwins e he with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · -- store window `[e.1, e.1+e.2.1)` ⊆ stack window `[SL.lo, sp)`
    omega
  · -- store window ⊆ arena `[A.lo, A.hi)`
    omega

/-! ## The consumer-facing forms: `writeLog` body oracle survival

The seq/while/for/args body oracles run a reflected `writeLog` over the loop
body's stores. These lemmas take the raw log + its `WinsInSA` geometry + the
node's off-stack-arena footprint disjointness and deliver the surviving
`*Repr` — the exact shape `hbody` needs to carry the AST from one iteration to
the next. -/

/-- **`StmtRepr` survives a reflected loop-body `writeLog`.** From the log's
window geometry (`WinsInSA`), its 1/4/8 widths, and the statement node's
footprint being disjoint from stack ∪ arena, `stmts[i]`'s representation carries
across the whole iteration's writes. THE lemma the four body oracles reuse. -/
theorem stmtRepr_survives_writeLog
    {SL : StackLayout} {sp : Nat} {A : Arena}
    {m : Mem} {a : Nat} {s : Stmt} (log : List WEntry)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hwins : WinsInSA SL sp A log)
    (hfpDisj : ∀ addr, StmtFp m a s addr →
      ¬ (SL.lo ≤ addr ∧ addr < sp) ∧ ¬ (A.lo ≤ addr ∧ addr < A.hi))
    (hs : StmtRepr m a s) : StmtRepr (writeLog m log) a s :=
  stmtRepr_agreeP (writeLog_agreeP_offStackArena m log hw hwins) hfpDisj hs

/-- **`ExprRepr` survives a reflected loop-body `writeLog`.** The `Expr` twin —
loop-condition / arg-expression survival across the iteration. -/
theorem exprRepr_survives_writeLog
    {SL : StackLayout} {sp : Nat} {A : Arena}
    {m : Mem} {a : Nat} {e : Expr} (log : List WEntry)
    (hw : ∀ ent ∈ log, ent.2.1 = 1 ∨ ent.2.1 = 4 ∨ ent.2.1 = 8)
    (hwins : WinsInSA SL sp A log)
    (hfpDisj : ∀ addr, ExprFp m a e addr →
      ¬ (SL.lo ≤ addr ∧ addr < sp) ∧ ¬ (A.lo ≤ addr ∧ addr < A.hi))
    (he : ExprRepr m a e) : ExprRepr (writeLog m log) a e :=
  exprRepr_agreeP (writeLog_agreeP_offStackArena m log hw hwins) hfpDisj he

/-! ## The single-`writeMap8` spill form (the exact `sd i` counter spill)

The tightest, most direct form: the loop-body's `sd i, k(sp)` counter spill is a
single 8-byte `writeMap8 m tgt d` at an in-window slot `tgt ∈ [SL.lo, sp)`. This
lemma discharges the `StmtRepr mcall …` conjunct `armExec_rec` demands after the
spill (`ExecBlock.lean:224`) with a single `omega` side condition — no `writeLog`
plumbing. It is the exemplar seam the seq body oracle plugs in. -/

/-- **`StmtRepr` survives a single in-window 8-byte spill** `writeMap8 m tgt d`
with `SL.lo ≤ tgt` and `tgt + 8 ≤ sp`. The `sd i` counter-spill form of
`stmtRepr_survives_stackWrite`; the AST footprint being off the stack window
(disjoint from `[tgt, tgt+8)`) is `hfpDisj`. -/
theorem stmtRepr_survives_spill
    {SL : StackLayout} {sp : Nat} {m : Mem} {a : Nat} {s : Stmt}
    (tgt : Nat) (d : BitVec (8 * 8))
    (hin : SL.lo ≤ tgt ∧ tgt + 8 ≤ sp)
    (hfpDisj : ∀ addr, StmtFp m a s addr → ¬ (SL.lo ≤ addr ∧ addr < sp))
    (hs : StmtRepr m a s) : StmtRepr (writeMap8 m tgt d) a s := by
  refine stmtRepr_survives_stackWrite (SL := SL) (sp := sp) ?_ hfpDisj hs
  intro k hk
  -- `k` is off `[SL.lo, sp)`, so off `[tgt, tgt+8) ⊆ [SL.lo, sp)`.
  exact (getElem_writeMap8_disjoint m tgt k d (by
    simp only [OffStackWindow] at hk
    by_cases hc : k < tgt
    · exact Or.inl hc
    · exact Or.inr (by
        by_cases hc2 : k < sp
        · exact absurd ⟨by omega, hc2⟩ hk
        · omega))).symm

/-- **`ExprRepr` survives a single in-window 8-byte spill.** The `Expr` twin. -/
theorem exprRepr_survives_spill
    {SL : StackLayout} {sp : Nat} {m : Mem} {a : Nat} {e : Expr}
    (tgt : Nat) (d : BitVec (8 * 8))
    (hin : SL.lo ≤ tgt ∧ tgt + 8 ≤ sp)
    (hfpDisj : ∀ addr, ExprFp m a e addr → ¬ (SL.lo ≤ addr ∧ addr < sp))
    (he : ExprRepr m a e) : ExprRepr (writeMap8 m tgt d) a e := by
  refine exprRepr_survives_stackWrite (SL := SL) (sp := sp) ?_ hfpDisj he
  intro k hk
  exact (getElem_writeMap8_disjoint m tgt k d (by
    simp only [OffStackWindow] at hk
    by_cases hc : k < tgt
    · exact Or.inl hc
    · exact Or.inr (by
        by_cases hc2 : k < sp
        · exact absurd ⟨by omega, hc2⟩ hk
        · omega))).symm

end Vsa.Sim
