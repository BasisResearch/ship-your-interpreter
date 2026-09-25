import VsaIris.Vsa.Stdout.Fflush
import VsaIris.Vsa.SymBridge

/-!
# Driving `fprintf` runs (lane N5)

`fprintf` on `stdout` runs `_vfprintf_r` twice (on `stdout`, then on
`__sbprintf`'s stack `FILE`), each a few hundred instructions before its
first call. `nx_run` (N1's `Stdout/Tac.lean`) accumulates every register
update in one `upd` chain; past a few dozen updates the normalizer's
recursion depth runs out and branch conditions stop reducing.

`nx_flat` restarts the register file: a fresh `R'` with one fact per owned
register, `R' r = v`, `v` the normalized value (`swp_fresh`). The facts are
locals, which `nx_run`'s normalizer uses (`simp only [*]`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- **A fresh register file** equal to the current one. -/
theorem swp_fresh {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ R' : Nat → BitVec 64, (∀ r, R' r = R r) → SWP live text rs S Q pc R' Mt) :
    SWP live text rs S Q pc R Mt :=
  h R fun _ => rfl

set_option hygiene false in
/-- `nx_flat`: the goal's register file as a fresh `R'` with the facts
`f<r> : R' r = v` for `ra`, `sp`, `t0`–`t6`, `s0`–`s11`, `a0`–`a7`. -/
macro "nx_flat" : tactic => `(tactic| (
  refine swp_fresh fun R' hR' => ?_
  have g1 := hR' 1; have g2 := hR' 2; have g5 := hR' 5; have g6 := hR' 6; have g7 := hR' 7; have g8 := hR' 8
  have g9 := hR' 9; have g10 := hR' 10; have g11 := hR' 11; have g12 := hR' 12; have g13 := hR' 13; have g14 := hR' 14
  have g15 := hR' 15; have g16 := hR' 16; have g17 := hR' 17; have g18 := hR' 18; have g19 := hR' 19; have g20 := hR' 20
  have g21 := hR' 21; have g22 := hR' 22; have g23 := hR' 23; have g24 := hR' 24; have g25 := hR' 25; have g26 := hR' 26
  have g27 := hR' 27; have g28 := hR' 28; have g29 := hR' 29; have g30 := hR' 30; have g31 := hR' 31
  clear hR'
  first
    | simp (config := {failIfUnchanged := false}) only [upd_apply, updAll, Nat.reduceEqDiff, ite_true, ite_false, BitVec.add_assoc, BitVec.reduceAdd, f1, f2, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31] at g1 g2 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31
    | simp (config := {failIfUnchanged := false}) only [upd_apply, updAll, Nat.reduceEqDiff, ite_true, ite_false] at g1 g2 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31
  (try clear f1 f2 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
  have f1 := g1; have f2 := g2; have f5 := g5; have f6 := g6; have f7 := g7; have f8 := g8
  have f9 := g9; have f10 := g10; have f11 := g11; have f12 := g12; have f13 := g13; have f14 := g14
  have f15 := g15; have f16 := g16; have f17 := g17; have f18 := g18; have f19 := g19; have f20 := g20
  have f21 := g21; have f22 := g22; have f23 := g23; have f24 := g24; have f25 := g25; have f26 := g26
  have f27 := g27; have f28 := g28; have f29 := g29; have f30 := g30; have f31 := g31
  clear g1 g2 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31))

set_option hygiene false in
/-- `nf_run [n] h using [facts] at pc…`: `nx_run` with the flat register facts
`f<r>` (`nx_flat`) and the literal-arithmetic simprocs in the normalizer's list
(`nx_run`'s normalizer rewrites with its `using` list only). -/
macro "nf_run " "[" n:num "] " h:term " using " "[" fs:term,* "]" stops:(" at " num+)? : tactic =>
  match stops with
  | some stx =>
    let ss : Array (Lean.TSyntax `num) := stx.raw[1].getArgs.map (⟨·⟩)
    `(tactic| nx_run [$n] $h using [$fs,*, BitVec.reduceSub, BitVec.reduceOr,
      BitVec.reduceAnd, BitVec.reduceHShiftLeft, f1, f2, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
      f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31] at $ss*)
  | none =>
    `(tactic| nx_run [$n] $h using [$fs,*, BitVec.reduceSub, BitVec.reduceOr,
      BitVec.reduceAnd, BitVec.reduceHShiftLeft, f1, f2, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
      f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31])

end VsaIris.Sym

namespace VsaIris.Sym

/-- `nf_go k [n] h using [facts] at pc…`: `k` rounds of `nx_flat; nf_run [n]` on every
open run goal at a literal PC that is not a stop: the register file never grows
past `n` updates (the normalizer's recursion depth bounds the chain it can
reduce). Side goals and stopped runs are left as they are. -/
syntax (name := nfGo) "nf_go " num " [" num "] " term " using " "[" term,* "]" (" at " num+)? : tactic

open Lean Elab Tactic Meta in
@[tactic nfGo] def evalNfGo : Tactic := fun stx => do
  let k := stx[1].isNatLit?.getD 1
  let n : TSyntax `num := ⟨stx[3]⟩
  let h : Term := ⟨stx[5]⟩
  let fs : Syntax.TSepArray `term "," := ⟨stx[8].getArgs⟩
  let stops : Array (TSyntax `num) := if stx[10].isNone then #[] else stx[10][1].getArgs.map (⟨·⟩)
  let stopPCs := stops.toList.map (·.getNat)
  for _ in [0:k] do
    let gs ← getGoals
    let mut out : List MVarId := []
    for g in gs do
      if ← g.isAssigned then continue
      match ← g.withContext (do swpPC? (← instantiateMVars (← g.getType))) with
      | some pc =>
        if stopPCs.contains pc then out := out ++ [g]; continue
        let tac ← if stops.isEmpty then `(tactic| (nx_flat; nf_run [$n] $h using [$fs,*]))
          else `(tactic| (nx_flat; nf_run [$n] $h using [$fs,*] at $stops*))
        let r ← evalTacticAt tac g
        out := out ++ r
      | none => out := out ++ [g]
    setGoals out

end VsaIris.Sym
